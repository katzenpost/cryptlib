/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Util.ConstantTime

namespace Cryptlib.Primitives.Cipher.Polyval

open Cryptlib.Util.ConstantTime (mask and_mask)

/-! # POLYVAL, the GCM-SIV authenticator

RFC 8452 §3: `POLYVAL(H, X₁, …, Xₛ) = Σᵢ Xᵢ • H^(s-i+1)` where `a • b = a·b·x⁻¹²⁸`, over
`GF(2)[x] / (x¹²⁸ + x¹²⁷ + x¹²⁶ + x¹²¹ + 1)`. Field elements are little-endian `Nat`s: byte `j`,
bit `i` is the coefficient of `x^(8j+i)`.

The `Nat` functions and `polyvalSpec` are the specification. `polyval` keeps the hash state and
key in two `UInt64` words and the double-width product in four, runs the same bit-serial
multiplication and reduction with masks in place of branches, and is proved equal to
`polyvalSpec` by `polyval_eq_spec`. It is written without secret-dependent branches or memory
indexing, but Lean compiles through C and neither compiler is proven to preserve that, so the
machine code is not verified to be constant time.
-/

/-- `x¹²⁸ + x¹²⁷ + x¹²⁶ + x¹²¹ + 1`, as bits of a `Nat`. -/
def modulus : Nat := 1 ||| (1 <<< 121) ||| (1 <<< 126) ||| (1 <<< 127) ||| (1 <<< 128)

/-- A 16-byte string as a field element, little-endian per RFC 8452 §3. -/
def ofBytes (v : Vector UInt8 16) : Nat :=
  v.toArray.foldr (fun b acc => (acc <<< 8) ||| b.toNat) 0

/-- A field element as 16 little-endian bytes. Bits at or above `x¹²⁸` are dropped. -/
def toBytes (n : Nat) : Vector UInt8 16 :=
  Vector.ofFn fun i : Fin 16 => UInt8.ofNat ((n >>> (8 * i.val)) % 256)

/-- Carry-less multiplication over `GF(2)`, without reduction. -/
def clmul (a b : Nat) : Nat :=
  (List.range 128).foldl (fun acc i => if a.testBit i then acc ^^^ (b <<< i) else acc) 0

/-- Multiplication by `x⁻¹²⁸`, one division by `x` at a time; also reduces the input below
`x¹²⁸`. -/
def divX128 (c : Nat) : Nat :=
  (List.range 128).foldl
    (fun c _ => if c.testBit 0 then (c ^^^ modulus) >>> 1 else c >>> 1) c

/-- RFC 8452's `dot`: `a • b = a·b·x⁻¹²⁸`. -/
def dot (a b : Nat) : Nat := divX128 (clmul a b)

/-- The 16-byte block at index `i`, read little-endian; a short final block is zero-padded. -/
private def blockAt (b : ByteArray) (i : Nat) : Nat :=
  (b.extract (16 * i) (16 * i + 16)).data.foldr (fun x acc => (acc <<< 8) ||| x.toNat) 0

/-- `POLYVAL(H, X₁ ‖ … ‖ Xₛ)`, in Horner form: `Sⱼ = (Sⱼ₋₁ + Xⱼ) • H`. -/
def polyvalSpec (h : Vector UInt8 16) (blocks : ByteArray) : Vector UInt8 16 :=
  let hf := ofBytes h
  toBytes <| (List.range ((blocks.size + 15) / 16)).foldl
    (fun s i => dot (s ^^^ blockAt blocks i) hf) 0

/-! ## Two- and four-word arithmetic -/

/-- Four words as a 256-bit integer, `w3` on top. -/
private def val4 (w3 w2 w1 w0 : UInt64) : Nat :=
  w3.toNat <<< 192 ||| w2.toNat <<< 128 ||| w1.toNat <<< 64 ||| w0.toNat

private theorem testBit_word (w : UInt64) (i : Nat) (h : 64 ≤ i) : w.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le w.toNat_lt (Nat.pow_le_pow_right (by omega) h))

private theorem testBit_val4 (w3 w2 w1 w0 : UInt64) (i : Nat) :
    (val4 w3 w2 w1 w0).testBit i =
      if i < 64 then w0.toNat.testBit i
      else if i < 128 then w1.toNat.testBit (i - 64)
      else if i < 192 then w2.toNat.testBit (i - 128)
      else w3.toNat.testBit (i - 192) := by
  simp only [val4, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h0 : i < 64
  · simp [h0, show ¬ i ≥ 64 by omega, show ¬ i ≥ 128 by omega, show ¬ i ≥ 192 by omega]
  by_cases h1 : i < 128
  · simp [h0, h1, show i ≥ 64 by omega, show ¬ i ≥ 128 by omega, show ¬ i ≥ 192 by omega,
      testBit_word w0 i (by omega)]
  by_cases h2 : i < 192
  · simp [h0, h1, h2, show i ≥ 64 by omega, show i ≥ 128 by omega, show ¬ i ≥ 192 by omega,
      testBit_word w0 i (by omega), testBit_word w1 (i - 64) (by omega)]
  · simp [h0, h1, h2, show i ≥ 64 by omega, show i ≥ 128 by omega, show i ≥ 192 by omega,
      testBit_word w0 i (by omega), testBit_word w1 (i - 64) (by omega),
      testBit_word w2 (i - 128) (by omega)]

private theorem val4_xor (a3 a2 a1 a0 b3 b2 b1 b0 : UInt64) :
    val4 (a3 ^^^ b3) (a2 ^^^ b2) (a1 ^^^ b1) (a0 ^^^ b0) =
      val4 a3 a2 a1 a0 ^^^ val4 b3 b2 b1 b0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [testBit_val4, Nat.testBit_xor, UInt64.toNat_xor]
  split <;> (try split) <;> (try split) <;> rfl

private theorem val4_and_mask (a3 a2 a1 a0 m : UInt64) :
    val4 (a3 &&& mask m) (a2 &&& mask m) (a1 &&& mask m) (a0 &&& mask m) =
      if m.toNat.testBit 0 then val4 a3 a2 a1 a0 else 0 := by
  simp only [and_mask]; split <;> rfl

private theorem tb_congr (x : Nat) {a b : Nat} (h : a = b) : x.testBit a = x.testBit b := h ▸ rfl

private theorem dand (p : Prop) [Decidable p] (b : Bool) :
    (decide p && b) = if p then b else false := by
  by_cases h : p <;> simp [h]

private theorem val4_shr1 (w3 w2 w1 w0 : UInt64) :
    val4 (w3 >>> 1) ((w2 >>> 1) ||| (w3 <<< 63)) ((w1 >>> 1) ||| (w2 <<< 63))
      ((w0 >>> 1) ||| (w1 <<< 63)) = val4 w3 w2 w1 w0 >>> 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [testBit_val4, Nat.testBit_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_or,
    UInt64.toNat_shiftLeft, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  rw [show UInt64.toNat 1 % 64 = 1 from rfl, show UInt64.toNat 63 % 64 = 63 from rfl]
  simp only [dand]
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [testBit_word, Bool.or_false, Bool.false_or]
       first | done | exact tb_congr _ (by omega))
    | exact tb_congr _ (by omega)

private theorem val4_shl1 (w3 w2 w1 w0 : UInt64) :
    val4 ((w3 <<< 1) ||| (w2 >>> 63)) ((w2 <<< 1) ||| (w1 >>> 63)) ((w1 <<< 1) ||| (w0 >>> 63))
      (w0 <<< 1) = (val4 w3 w2 w1 w0 <<< 1) % 2 ^ 256 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [testBit_val4, Nat.testBit_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_or,
    UInt64.toNat_shiftLeft, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  rw [show UInt64.toNat 1 % 64 = 1 from rfl, show UInt64.toNat 63 % 64 = 63 from rfl]
  simp only [dand]
  repeat' split
  all_goals first
    | omega
    | (simp (disch := omega) only [testBit_word, Bool.or_false, Bool.false_or]
       first | done | exact tb_congr _ (by omega))
    | exact tb_congr _ (by omega)

private theorem val4_lt (w3 w2 w1 w0 : UInt64) : val4 w3 w2 w1 w0 < 2 ^ 256 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_val4]
  repeat' split
  all_goals first | omega | exact testBit_word _ _ (by omega)

private theorem val4_low (w3 w2 w1 w0 : UInt64) (h : val4 w3 w2 w1 w0 < 2 ^ 128) :
    val4 w3 w2 w1 w0 = val4 0 0 w1 w0 := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < 128
  · simp only [testBit_val4]
    repeat' split
    all_goals first | omega | rfl
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp only [testBit_val4]
    repeat' split
    all_goals first | omega | simp

private def divStep (c : Nat) : Nat := if c.testBit 0 then (c ^^^ modulus) >>> 1 else c >>> 1

private theorem divX128_eq (c : Nat) :
    divX128 c = (List.range 128).foldl (fun c _ => divStep c) c := rfl

private theorem modulus_lt : modulus < 2 ^ 129 := by decide

private theorem divStep_lt (c n : Nat) (h : c < 2 ^ (n + 1)) (hn : 129 ≤ n + 1) :
    divStep c < 2 ^ n := by
  have hm : modulus < 2 ^ (n + 1) :=
    Nat.lt_of_lt_of_le modulus_lt (Nat.pow_le_pow_right (by omega) hn)
  unfold divStep
  split
  · rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have := Nat.xor_lt_two_pow h hm
    rw [Nat.pow_succ] at this; omega
  · rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    rw [Nat.pow_succ] at h; omega

private theorem foldl_divStep_lt :
    ∀ (n : Nat) (l : List Nat) (c : Nat), l.length = n → c < 2 ^ (128 + n) →
    l.foldl (fun c _ => divStep c) c < 2 ^ 128
  | 0, [], c, _, h => by simpa using h
  | n + 1, _ :: l, c, hl, h => by
    rw [List.foldl_cons]
    exact foldl_divStep_lt n l _ (by simpa using hl)
      (divStep_lt c _ (by rw [show 128 + n + 1 = 128 + (n + 1) by omega]; exact h) (by omega))

private theorem divX128_lt (c : Nat) (h : c < 2 ^ 256) : divX128 c < 2 ^ 128 :=
  foldl_divStep_lt 128 _ c (by simp) h

/-- Four words, for the double-width product. -/
private structure W4 where
  w3 : UInt64
  w2 : UInt64
  w1 : UInt64
  w0 : UInt64

private def W4.toNat (c : W4) : Nat := val4 c.w3 c.w2 c.w1 c.w0

/-- Bit `i` of `ah ‖ al` in bit 0. -/
private def bitAt (ah al : UInt64) (i : Nat) : UInt64 :=
  if i < 64 then al >>> i.toUInt64 else ah >>> (i - 64).toUInt64

private theorem testBit_shr (w : UInt64) (s : Nat) (hs : s < 64) :
    (w >>> s.toUInt64).toNat.testBit 0 = w.toNat.testBit s := by
  simp [Nat.mod_eq_of_lt hs]

private theorem testBit_bitAt (ah al : UInt64) (i : Nat) (hi : i < 128) :
    (bitAt ah al i).toNat.testBit 0 = (val4 0 0 ah al).testBit i := by
  rw [testBit_val4, bitAt]
  split
  · rw [testBit_shr _ _ (by omega)]
  · rw [testBit_shr _ _ (by omega)]

/-- Steps `i, …, i + n - 1` of `clmul`, with `s = b <<< i`. -/
private def clmulLoop (ah al : UInt64) :
    Nat → Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → W4
  | 0, _, c3, c2, c1, c0, _, _, _, _ => ⟨c3, c2, c1, c0⟩
  | n + 1, i, c3, c2, c1, c0, s3, s2, s1, s0 =>
    let m := mask (bitAt ah al i)
    clmulLoop ah al n (i + 1) (c3 ^^^ (s3 &&& m)) (c2 ^^^ (s2 &&& m)) (c1 ^^^ (s1 &&& m))
      (c0 ^^^ (s0 &&& m)) ((s3 <<< 1) ||| (s2 >>> 63)) ((s2 <<< 1) ||| (s1 >>> 63))
      ((s1 <<< 1) ||| (s0 >>> 63)) (s0 <<< 1)

private def clmulStep (a b : Nat) (acc : Nat) (i : Nat) : Nat :=
  if a.testBit i then acc ^^^ (b <<< i) else acc

private theorem clmul_eq (a b : Nat) : clmul a b = (List.range 128).foldl (clmulStep a b) 0 := rfl

private theorem clmulLoop_spec (ah al : UInt64) (b : Nat) (hb : b < 2 ^ 128) :
    ∀ n i c3 c2 c1 c0 s3 s2 s1 s0, i + n ≤ 128 → val4 s3 s2 s1 s0 = b <<< i →
      (clmulLoop ah al n i c3 c2 c1 c0 s3 s2 s1 s0).toNat =
        (List.range' i n).foldl (clmulStep (val4 0 0 ah al) b) (val4 c3 c2 c1 c0) := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro i c3 c2 c1 c0 s3 s2 s1 s0 hn hs
    have hlt : b <<< (i + 1) < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      calc b * 2 ^ (i + 1) < 2 ^ 128 * 2 ^ (i + 1) :=
            Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)
        _ = 2 ^ (128 + (i + 1)) := (Nat.pow_add _ _ _).symm
        _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
    have hs' : val4 ((s3 <<< 1) ||| (s2 >>> 63)) ((s2 <<< 1) ||| (s1 >>> 63))
        ((s1 <<< 1) ||| (s0 >>> 63)) (s0 <<< 1) = b <<< (i + 1) := by
      rw [val4_shl1, hs, ← Nat.shiftLeft_add]
      exact Nat.mod_eq_of_lt hlt
    rw [clmulLoop, ih _ _ _ _ _ _ _ _ _ (by omega) hs', List.range'_succ, List.foldl_cons]
    refine congrArg
      (fun z => List.foldl (clmulStep (val4 0 0 ah al) b) z (List.range' (i + 1) n)) ?_
    rw [val4_xor, val4_and_mask, testBit_bitAt _ _ _ (by omega), hs, clmulStep]
    split <;> simp

/-- `n` steps of `divX128`. -/
private def divLoop : Nat → UInt64 → UInt64 → UInt64 → UInt64 → W4
  | 0, c3, c2, c1, c0 => ⟨c3, c2, c1, c0⟩
  | n + 1, c3, c2, c1, c0 =>
    let m := mask c0
    let c2 := c2 ^^^ (1 &&& m)
    let c1 := c1 ^^^ (0xC200000000000000 &&& m)
    let c0 := c0 ^^^ (1 &&& m)
    divLoop n (c3 >>> 1) ((c2 >>> 1) ||| (c3 <<< 63)) ((c1 >>> 1) ||| (c2 <<< 63))
      ((c0 >>> 1) ||| (c1 <<< 63))

private theorem modulus_eq : val4 0 1 0xC200000000000000 1 = modulus := by decide

private theorem divLoop_spec : ∀ (n : Nat) (l : List Nat) c3 c2 c1 c0, l.length = n →
    (divLoop n c3 c2 c1 c0).toNat = l.foldl (fun c _ => divStep c) (val4 c3 c2 c1 c0)
  | 0, [], _, _, _, _, _ => rfl
  | n + 1, _ :: l, c3, c2, c1, c0, hl => by
    rw [divLoop, divLoop_spec n l _ _ _ _ (by simpa using hl), List.foldl_cons]
    congr 1
    have hx := val4_xor c3 c2 c1 c0 (0 &&& mask c0) (1 &&& mask c0) (0xC200000000000000 &&& mask c0)
      (1 &&& mask c0)
    rw [val4_and_mask, modulus_eq] at hx
    have h0 : (val4 c3 c2 c1 c0).testBit 0 = c0.toNat.testBit 0 := by
      rw [testBit_val4, if_pos (by omega)]
    simp only [UInt64.zero_and, UInt64.xor_zero] at hx
    rw [divStep, h0, val4_shr1, hx]
    split <;> simp

/-- A field element as its high and low 64 bits. -/
structure Elem where
  hi : UInt64
  lo : UInt64

/-- The element as a 128-bit integer, `hi` on top. -/
def Elem.toNat (a : Elem) : Nat := val4 0 0 a.hi a.lo

theorem Elem.toNat_lt (a : Elem) : a.toNat < 2 ^ 128 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Elem.toNat, testBit_val4]
  repeat' split
  all_goals first | omega | exact testBit_word _ _ (by omega) | simp

def Elem.xor (a b : Elem) : Elem := ⟨a.hi ^^^ b.hi, a.lo ^^^ b.lo⟩

theorem Elem.toNat_xor (a b : Elem) : (a.xor b).toNat = a.toNat ^^^ b.toNat := by
  simp only [Elem.xor, Elem.toNat]
  rw [← val4_xor, UInt64.xor_zero]

/-- `dot` on two-word elements: `clmul` into four words, then 128 masked halvings. -/
def dotCT (a b : Elem) : Elem :=
  let p := clmulLoop a.hi a.lo 128 0 0 0 0 0 0 0 b.hi b.lo
  let c := divLoop 128 p.w3 p.w2 p.w1 p.w0
  ⟨c.w1, c.w0⟩

theorem dotCT_spec (a b : Elem) : (dotCT a b).toNat = dot a.toNat b.toNat := by
  have hp := clmulLoop_spec a.hi a.lo b.toNat b.toNat_lt 128 0 0 0 0 0 0 0 b.hi b.lo (by omega)
    (by rw [Nat.shiftLeft_zero]; rfl)
  simp only [dotCT]
  generalize clmulLoop a.hi a.lo 128 0 0 0 0 0 0 0 b.hi b.lo = P at hp ⊢
  have hP : val4 P.w3 P.w2 P.w1 P.w0 = clmul a.toNat b.toNat := by
    rw [clmul_eq, List.range_eq_range']; exact hp
  have hc := divLoop_spec 128 (List.range 128) P.w3 P.w2 P.w1 P.w0 (by simp)
  rw [← divX128_eq, hP] at hc
  generalize divLoop 128 P.w3 P.w2 P.w1 P.w0 = C at hc ⊢
  have hlt : C.toNat < 2 ^ 128 := hc ▸ divX128_lt _ (hP ▸ val4_lt _ _ _ _)
  rw [dot, ← hc]
  exact (val4_low _ _ _ _ hlt).symm

/-! ## Loading and storing blocks -/

/-- The little-endian value of `f 0, …, f (n - 1)`. -/
private def leNat (f : Nat → UInt8) : Nat → Nat
  | 0 => 0
  | n + 1 => leNat (fun j => f (j + 1)) n <<< 8 ||| (f 0).toNat

private theorem shl8_or (x : Nat) (b : UInt8) : x <<< 8 ||| b.toNat = x * 256 + b.toNat := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt b.toNat_lt, Nat.shiftLeft_eq]

private theorem leNat_lt : ∀ (n : Nat) (f : Nat → UInt8), leNat f n < 2 ^ (8 * n)
  | 0, _ => by simp [leNat]
  | n + 1, f => by
    have ih := leNat_lt n (fun j => f (j + 1))
    have hb := (f 0).toNat_lt
    rw [leNat, shl8_or, show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]
    have : (2:Nat) ^ 8 = 256 := rfl
    rw [this] at hb ⊢
    omega

private theorem leNat_congr : ∀ (n : Nat) (f g : Nat → UInt8), (∀ j, j < n → f j = g j) →
    leNat f n = leNat g n
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    rw [leNat, leNat, leNat_congr n _ (fun j => g (j + 1)) (fun j hj => h _ (by omega)),
      h 0 (by omega)]

private theorem leNat_zero : ∀ (k : Nat) (f : Nat → UInt8), (∀ j, f j = 0) → leNat f k = 0
  | 0, _, _ => rfl
  | k + 1, f, h => by rw [leNat, leNat_zero k _ (fun j => h _), h 0]; rfl

private theorem leNat_extend : ∀ (n k : Nat) (f : Nat → UInt8), (∀ j, n ≤ j → f j = 0) →
    leNat f (n + k) = leNat f n
  | 0, k, f, h => by rw [Nat.zero_add, leNat_zero k f (fun j => h j (by omega))]; rfl
  | n + 1, k, f, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega, leNat, leNat,
      leNat_extend n k _ (fun j hj => h _ (by omega))]

private theorem leNat_split : ∀ (m n : Nat) (f : Nat → UInt8),
    leNat f (m + n) = leNat (fun j => f (m + j)) n <<< (8 * m) ||| leNat f m
  | 0, n, f => by simp [leNat]
  | m + 1, n, f => by
    rw [show m + 1 + n = (m + n) + 1 by omega, leNat, leNat, leNat_split m n,
      Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.or_assoc,
      show 8 * m + 8 = 8 * (m + 1) by omega]
    congr 3
    funext j
    rw [show m + j + 1 = m + 1 + j by omega]

/-- `leNat` in a `UInt64`, for `n ≤ 8`. -/
private def wordLE (f : Nat → UInt8) : Nat → UInt64
  | 0 => 0
  | n + 1 => wordLE (fun j => f (j + 1)) n <<< 8 ||| (f 0).toUInt64

private theorem wordLE_toNat : ∀ (n : Nat) (f : Nat → UInt8), n ≤ 8 → (wordLE f n).toNat = leNat f n
  | 0, _, _ => rfl
  | n + 1, f, hn => by
    have ih := wordLE_toNat n (fun j => f (j + 1)) (by omega)
    have hl := leNat_lt n (fun j => f (j + 1))
    simp only [wordLE, leNat, UInt64.toNat_or, UInt64.toNat_shiftLeft, ih, UInt8.toNat_toUInt64]
    rw [show UInt64.toNat 8 % 64 = 8 from rfl, Nat.mod_eq_of_lt]
    rw [Nat.shiftLeft_eq]
    have : 2 ^ (8 * n) * 2 ^ 8 ≤ 2 ^ 64 := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have : (2:Nat) ^ 8 = 256 := rfl
    have := Nat.mul_lt_mul_of_pos_right hl (show 0 < 2 ^ 8 by omega)
    omega

private theorem foldr_eq (l : List UInt8) :
    l.foldr (fun b acc => (acc <<< 8) ||| b.toNat) 0 = leNat (fun j => l.getD j 0) l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.length_cons, leNat]
    simp

private theorem array_foldr_eq (a : Array UInt8) :
    a.foldr (fun b acc => (acc <<< 8) ||| b.toNat) 0 = leNat (fun j => a.getD j 0) a.size := by
  rcases a with ⟨l⟩
  rw [List.foldr_toArray', foldr_eq, List.size_toArray]
  · apply leNat_congr
    intro j hj
    simp [Array.getD, hj]
  · rfl

/-- The 16 bytes at `off`, little-endian, zero-padded past the end. -/
def load (a : Array UInt8) (off : Nat) : Elem :=
  ⟨wordLE (fun j => a.getD (off + 8 + j) 0) 8, wordLE (fun j => a.getD (off + j) 0) 8⟩

private theorem getD_extract (a : Array UInt8) (off j : Nat) (hj : j < 16) :
    (a.extract off (off + 16)).getD j 0 = a.getD (off + j) 0 := by
  simp only [Array.getD, Array.size_extract]
  by_cases h : off + j < a.size
  · rw [dif_pos (by omega), dif_pos h]; simp
  · rw [dif_neg (by omega), dif_neg h]

theorem load_toNat (a : Array UInt8) (off : Nat) :
    (load a off).toNat =
      (a.extract off (off + 16)).foldr (fun b acc => (acc <<< 8) ||| b.toNat) 0 := by
  have hs : (a.extract off (off + 16)).size ≤ 16 := by simp; omega
  rw [array_foldr_eq, ← leNat_extend _ (16 - (a.extract off (off + 16)).size) _
      (fun j hj => by simp only [Array.getD, dif_neg (Nat.not_lt.mpr hj)]),
    Nat.add_sub_cancel' hs,
    leNat_congr 16 _ (fun j => a.getD (off + j) 0) (fun j hj => getD_extract a off j hj),
    show 16 = 8 + 8 from rfl, leNat_split, load, Elem.toNat,
    ← wordLE_toNat 8 _ (by omega), ← wordLE_toNat 8 _ (by omega)]
  simp [val4, Nat.add_assoc]

/-- An element as 16 little-endian bytes. -/
def store (e : Elem) : Vector UInt8 16 :=
  Vector.ofFn fun i : Fin 16 =>
    if i.val < 8 then (e.lo >>> (8 * i.val).toUInt64).toUInt8
    else (e.hi >>> (8 * (i.val - 8)).toUInt64).toUInt8

theorem store_eq (e : Elem) : store e = toBytes e.toNat := by
  ext i hi
  simp only [store, toBytes, Vector.getElem_ofFn]
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  rw [UInt8.toNat_ofNat', Nat.mod_mod]
  split
  · simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
    simp only [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      Elem.toNat, testBit_val4]
    rw [Nat.mod_eq_of_lt (by omega : 8 * i % 2 ^ 64 < 64),
      Nat.mod_eq_of_lt (by omega : 8 * i < 2 ^ 64)]
    by_cases hj : j < 8
    · rw [if_pos (by omega)]
    · simp [hj]
  · simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
    simp only [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      Elem.toNat, testBit_val4]
    rw [Nat.mod_eq_of_lt (by omega : 8 * (i - 8) % 2 ^ 64 < 64),
      Nat.mod_eq_of_lt (by omega : 8 * (i - 8) < 2 ^ 64)]
    by_cases hj : j < 8
    · rw [if_neg (by omega), if_pos (by omega),
        tb_congr e.hi.toNat (by omega : 8 * (i - 8) + j = 8 * i + j - 64)]
    · simp [hj]

def polyval (h : Vector UInt8 16) (blocks : ByteArray) : Vector UInt8 16 :=
  let hf := load h.toArray 0
  -- `ByteArray.data` copies, so convert once rather than per block
  let b := blocks.data
  store <| (List.range ((blocks.size + 15) / 16)).foldl
    (fun s i => dotCT (s.xor (load b (16 * i))) hf) ⟨0, 0⟩

theorem polyval_eq_spec (h : Vector UInt8 16) (blocks : ByteArray) :
    polyval h blocks = polyvalSpec h blocks := by
  simp only [polyval, polyvalSpec, store_eq]
  congr 1
  refine (List.foldl_hom Elem.toNat (fun y i => ?_)).symm
  rw [dotCT_spec, Elem.toNat_xor, load_toNat, load_toNat]
  have : h.toArray.extract 0 (0 + 16) = h.toArray := by
    apply Array.ext <;> simp
  simp only [blockAt, ofBytes, ByteArray.data_extract, this]

end Cryptlib.Primitives.Cipher.Polyval
