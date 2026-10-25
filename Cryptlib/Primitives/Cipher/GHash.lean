/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Util.ConstantTime

namespace Cryptlib.Primitives.Cipher.GHash

open Cryptlib.Util.ConstantTime (mask and_mask)

/-! # GHASH, the GCM authenticator (NIST SP 800-38D §6.4)

Blocks are read as big-endian 128-bit integers. GCM numbers bits from the most significant end,
so the coefficient of `x⁰` is the integer's top bit and multiplying by `x` is a right shift,
reduced by `R = 0xE1 ‖ 0¹²⁰`.

`mul` and `ghashSpec` over `Nat` are the specification. `ghash` keeps the hash state and key in a
pair of `UInt64` words and runs the same bit-serial multiplication with masks in place of its
branches; `ghash_eq_spec` proves the two equal. It is written without secret-dependent branches
or memory indexing, but Lean compiles through C and neither compiler is proven to preserve that,
so the machine code is not verified to be constant time. -/

def R : Nat := 0xE1 <<< 120

def ofBytes (b : Array UInt8) : Nat := b.foldl (fun acc x => (acc <<< 8) ||| x.toNat) 0

def toBytes (n : Nat) : Vector UInt8 16 :=
  Vector.ofFn fun i : Fin 16 => UInt8.ofNat (n >>> (8 * (15 - i.val)))

/-- Step `i` of SP 800-38D Algorithm 1 on `(Z, V)`. -/
def mulStep (x : Nat) (zv : Nat × Nat) (i : Nat) : Nat × Nat :=
  let (z, v) := zv
  let z := if x.testBit (127 - i) then z ^^^ v else z
  let v := if v.testBit 0 then (v >>> 1) ^^^ R else v >>> 1
  (z, v)

/-- SP 800-38D Algorithm 1, `X • Y` in `GF(2¹²⁸)`. -/
def mul (x y : Nat) : Nat := ((List.range 128).foldl (mulStep x) (0, y)).1

/-- `GHASH_H` over a byte string, a short final block read as zero-padded. -/
def ghashSpec (h : Vector UInt8 16) (blocks : ByteArray) : Vector UInt8 16 :=
  let hf := ofBytes h.toArray
  -- `ByteArray.data` copies, so convert once rather than per block
  let b := blocks.data
  toBytes <| (List.range ((blocks.size + 15) / 16)).foldl (fun y i =>
    let chunk := b.extract (16 * i) (16 * i + 16)
    mul (y ^^^ (ofBytes chunk <<< (8 * (16 - chunk.size)))) hf) 0

/-! ## Two-word field elements -/

/-- A field element as its high and low 64 bits. -/
structure Elem where
  hi : UInt64
  lo : UInt64

/-- The element as a 128-bit integer, `hi` on top. -/
def Elem.toNat (a : Elem) : Nat := a.hi.toNat <<< 64 ||| a.lo.toNat

private theorem testBit_toNat (a : Elem) (i : Nat) :
    a.toNat.testBit i = if i < 64 then a.lo.toNat.testBit i else a.hi.toNat.testBit (i - 64) := by
  simp only [Elem.toNat, Nat.testBit_or, Nat.testBit_shiftLeft]
  split
  · have : ¬ (i ≥ 64) := by omega
    simp [this]
  · have : a.lo.toNat.testBit i = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le a.lo.toNat_lt (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [this]; omega

private theorem toNat_xor (a b : Elem) :
    (Elem.mk (a.hi ^^^ b.hi) (a.lo ^^^ b.lo)).toNat = a.toNat ^^^ b.toNat := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [testBit_toNat, Nat.testBit_xor, UInt64.toNat_xor]
  split <;> rfl

def Elem.xor (a b : Elem) : Elem := ⟨a.hi ^^^ b.hi, a.lo ^^^ b.lo⟩

private def shr1 (v : Elem) : Elem := ⟨v.hi >>> 1, (v.lo >>> 1) ||| (v.hi <<< 63)⟩

private theorem toNat_shr1 (v : Elem) : (shr1 v).toNat = v.toNat >>> 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [testBit_toNat, shr1, Nat.testBit_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_or,
    UInt64.toNat_shiftLeft, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  rw [show UInt64.toNat 1 % 64 = 1 from rfl, show UInt64.toNat 63 % 64 = 63 from rfl]
  rcases Nat.lt_or_ge i 63 with h | h
  · have : ¬ i ≥ 63 := by omega
    simp [this, show i < 64 by omega, Nat.add_comm]
  · rcases Nat.lt_or_ge i 64 with h' | h'
    · have hi : i = 63 := by omega
      subst hi; simp [Nat.testBit_lt_two_pow v.lo.toNat_lt]
    · simp [show ¬ i < 64 by omega, show ¬ 1 + i < 64 by omega]; congr 1; omega

/-- All ones if bit `127 - i` of `xh ‖ xl` is set, else zero. -/
private def bitMask (xh xl : UInt64) (i : Nat) : UInt64 :=
  if i < 64 then mask (xh >>> (63 - i).toUInt64) else mask (xl >>> (127 - i).toUInt64)

/-- Algorithm 1 from step `i`, for `n` more steps, with `Z` and `V` unpacked. -/
private def mulLoop (xh xl : UInt64) : Nat → Nat → UInt64 → UInt64 → UInt64 → UInt64 → Elem
  | 0, _, zh, zl, _, _ => ⟨zh, zl⟩
  | n + 1, i, zh, zl, vh, vl =>
    let m := bitMask xh xl i
    let r := mask vl
    mulLoop xh xl n (i + 1) (zh ^^^ (vh &&& m)) (zl ^^^ (vl &&& m))
      ((vh >>> 1) ^^^ (0xE100000000000000 &&& r)) ((vl >>> 1) ||| (vh <<< 63))

/-- `mul` on two-word elements. -/
def mulCT (x y : Elem) : Elem := mulLoop x.hi x.lo 128 0 0 0 y.hi y.lo

private theorem testBit_shr (w : UInt64) (s : Nat) (hs : s < 64) :
    (w >>> s.toUInt64).toNat.testBit 0 = w.toNat.testBit s := by
  simp [Nat.mod_eq_of_lt hs]

private theorem bitMask_eq (xh xl : UInt64) (i : Nat) (x : UInt64) :
    x &&& bitMask xh xl i = if (Elem.mk xh xl).toNat.testBit (127 - i) then x else 0 := by
  rw [testBit_toNat, bitMask]
  split
  · rw [and_mask, testBit_shr _ _ (by omega)]
    simp only [show ¬ (127 - i < 64) by omega, if_false]
    rw [show 127 - i - 64 = 63 - i by omega]
  · rw [and_mask, testBit_shr _ _ (by omega)]
    simp only [show 127 - i < 64 by omega, if_true]

private theorem toNat_R : (Elem.mk 0xE100000000000000 0).toNat = R := by decide

private theorem mulLoop_spec (xh xl : UInt64) : ∀ n i zh zl vh vl,
    (mulLoop xh xl n i zh zl vh vl).toNat =
      ((List.range' i n).foldl (mulStep (Elem.mk xh xl).toNat)
        ((Elem.mk zh zl).toNat, (Elem.mk vh vl).toNat)).1
  | 0, _, _, _, _, _ => rfl
  | n + 1, i, zh, zl, vh, vl => by
    rw [mulLoop, mulLoop_spec xh xl n, List.range'_succ, List.foldl_cons]
    congr 2
    simp only [mulStep]
    rw [bitMask_eq, bitMask_eq, and_mask]
    have hb : (Elem.mk vh vl).toNat.testBit 0 = vl.toNat.testBit 0 := by
      rw [testBit_toNat, if_pos (by omega)]
    have hz := toNat_xor ⟨zh, zl⟩ ⟨vh, vl⟩
    have hs := toNat_shr1 ⟨vh, vl⟩
    have hR := toNat_xor (shr1 ⟨vh, vl⟩) ⟨0xE100000000000000, 0⟩
    simp only [shr1, toNat_R, UInt64.xor_zero] at hz hs hR
    rw [hb]
    split <;> split <;> simp_all

theorem mulCT_spec (x y : Elem) : (mulCT x y).toNat = mul x.toNat y.toNat := by
  rw [mulCT, mulLoop_spec, mul, List.range_eq_range']
  rfl

/-! ## Loading and storing blocks -/

/-- The big-endian value of `f 0, …, f (n - 1)`. -/
private def bytesNat (f : Nat → UInt8) : Nat → Nat
  | 0 => 0
  | n + 1 => bytesNat f n <<< 8 ||| (f n).toNat

private theorem shl8_or (x : Nat) (b : UInt8) : x <<< 8 ||| b.toNat = x * 256 + b.toNat := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt b.toNat_lt, Nat.shiftLeft_eq]

private theorem bytesNat_lt (f : Nat → UInt8) : ∀ n, bytesNat f n < 2 ^ (8 * n)
  | 0 => by simp [bytesNat]
  | n + 1 => by
    have ih := bytesNat_lt f n
    have hb := (f n).toNat_lt
    rw [bytesNat, shl8_or, show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]
    have : (2:Nat) ^ 8 = 256 := rfl
    rw [this] at hb ⊢
    omega

private theorem bytesNat_congr (f g : Nat → UInt8) :
    ∀ n, (∀ j, j < n → f j = g j) → bytesNat f n = bytesNat g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [bytesNat, bytesNat, bytesNat_congr f g n (fun j hj => h j (by omega)), h n (by omega)]

private theorem ofBytes_eq (a : Array UInt8) : ofBytes a = bytesNat (a.getD · 0) a.size := by
  rcases a with ⟨l⟩
  simp only [ofBytes, List.foldl_toArray', List.size_toArray]
  suffices h : ∀ r : List UInt8, r.reverse.foldl (fun acc x => (acc <<< 8) ||| x.toNat) 0 =
      bytesNat (fun j => r.reverse.toArray.getD j 0) r.reverse.length by
    simpa using h l.reverse
  intro r
  induction r with
  | nil => rfl
  | cons x r ih =>
    rw [List.reverse_cons, List.foldl_append, ih, List.length_append, List.length_singleton,
      bytesNat]
    simp only [List.foldl_cons, List.foldl_nil]
    congr 1
    · congr 1
      apply bytesNat_congr
      intro j hj
      have hj' : j < r.reverse.length + 1 := by omega
      simp only [Array.getD, List.size_toArray, List.length_append, List.length_singleton, hj, hj',
        dite_true, Array.getInternal_eq_getElem, List.getElem_toArray, List.getElem_append_left hj]
    · simp [Array.getD]

private theorem bytesNat_append_zero (f : Nat → UInt8) (n : Nat) (hf : ∀ j, n ≤ j → f j = 0) :
    ∀ k, bytesNat f (n + k) = bytesNat f n <<< (8 * k)
  | 0 => by simp
  | k + 1 => by
    rw [← Nat.add_assoc, bytesNat, bytesNat_append_zero f n hf k, hf _ (by omega)]
    simp [Nat.shiftLeft_add, Nat.mul_add]

private theorem bytesNat_split (f : Nat → UInt8) (m : Nat) :
    ∀ n, bytesNat f (m + n) = bytesNat f m <<< (8 * n) ||| bytesNat (fun j => f (m + j)) n
  | 0 => by simp [bytesNat]
  | n + 1 => by
    rw [← Nat.add_assoc, bytesNat, bytesNat_split f m n, bytesNat, Nat.shiftLeft_or_distrib,
      ← Nat.shiftLeft_add, Nat.or_assoc]
    rfl

/-- `bytesNat` in a `UInt64`, for `n ≤ 8`. -/
private def wordAux (f : Nat → UInt8) : Nat → UInt64
  | 0 => 0
  | n + 1 => wordAux f n <<< 8 ||| (f n).toUInt64

private theorem wordAux_toNat (f : Nat → UInt8) : ∀ n, n ≤ 8 → (wordAux f n).toNat = bytesNat f n
  | 0, _ => rfl
  | n + 1, hn => by
    have ih := wordAux_toNat f n (by omega)
    have hl := bytesNat_lt f n
    simp only [wordAux, bytesNat, UInt64.toNat_or, UInt64.toNat_shiftLeft, ih, UInt8.toNat_toUInt64]
    rw [show UInt64.toNat 8 % 64 = 8 from rfl, Nat.mod_eq_of_lt]
    rw [Nat.shiftLeft_eq]
    have : 2 ^ (8 * n) * 2 ^ 8 ≤ 2 ^ 64 := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have : (2:Nat) ^ 8 = 256 := rfl
    have := Nat.mul_lt_mul_of_pos_right hl (show 0 < 2 ^ 8 by omega)
    omega

/-- The 16 bytes at `off`, zero-padded past the end. -/
def load (a : Array UInt8) (off : Nat) : Elem :=
  ⟨wordAux (fun j => a.getD (off + j) 0) 8, wordAux (fun j => a.getD (off + 8 + j) 0) 8⟩

private theorem getD_extract (a : Array UInt8) (off j : Nat) (hj : j < 16) :
    (a.extract off (off + 16)).getD j 0 = a.getD (off + j) 0 := by
  simp only [Array.getD, Array.size_extract]
  by_cases h : off + j < a.size
  · rw [dif_pos (by omega), dif_pos h]; simp
  · rw [dif_neg (by omega), dif_neg h]

theorem load_toNat (a : Array UInt8) (off : Nat) :
    (load a off).toNat =
      ofBytes (a.extract off (off + 16)) <<< (8 * (16 - (a.extract off (off + 16)).size)) := by
  have hs : (a.extract off (off + 16)).size ≤ 16 := by simp; omega
  rw [ofBytes_eq, ← bytesNat_append_zero _ _
      (fun j hj => by simp only [Array.getD, dif_neg (Nat.not_lt.mpr hj)]),
    Nat.add_sub_cancel' hs,
    bytesNat_congr _ (fun j => a.getD (off + j) 0) 16 (fun j hj => getD_extract a off j hj),
    show 16 = 8 + 8 from rfl, bytesNat_split, Elem.toNat, load, wordAux_toNat _ _ (by omega),
    wordAux_toNat _ _ (by omega)]
  congr 2
  funext j
  rw [Nat.add_assoc]

/-- An element as 16 big-endian bytes. -/
def store (e : Elem) : Vector UInt8 16 :=
  Vector.ofFn fun i : Fin 16 =>
    if i.val < 8 then (e.hi >>> (8 * (7 - i.val)).toUInt64).toUInt8
    else (e.lo >>> (8 * (15 - i.val)).toUInt64).toUInt8

theorem store_eq (e : Elem) : store e = toBytes e.toNat := by
  ext i hi
  simp only [store, toBytes, Vector.getElem_ofFn]
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  split
  · simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt8.toNat_ofNat',
      UInt64.toNat_ofNat']
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, testBit_toNat]
    rw [Nat.mod_eq_of_lt (by omega : 8 * (7 - i) % 2 ^ 64 < 64),
      Nat.mod_eq_of_lt (by omega : 8 * (7 - i) < 2 ^ 64)]
    by_cases hj : j < 8
    · rw [if_neg (by omega)]; simp only [hj, decide_true, Bool.true_and]; congr 1; omega
    · simp [hj]
  · simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt8.toNat_ofNat',
      UInt64.toNat_ofNat']
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, testBit_toNat]
    rw [Nat.mod_eq_of_lt (by omega : 8 * (15 - i) % 2 ^ 64 < 64),
      Nat.mod_eq_of_lt (by omega : 8 * (15 - i) < 2 ^ 64)]
    by_cases hj : j < 8
    · rw [if_pos (by omega)]
    · simp [hj]

/-- `GHASH_H` over a byte string, a short final block read as zero-padded. -/
def ghash (h : Vector UInt8 16) (blocks : ByteArray) : Vector UInt8 16 :=
  let hf := load h.toArray 0
  -- `ByteArray.data` copies, so convert once rather than per block
  let b := blocks.data
  store <| (List.range ((blocks.size + 15) / 16)).foldl
    (fun y i => mulCT (y.xor (load b (16 * i))) hf) ⟨0, 0⟩

theorem ghash_eq_spec (h : Vector UInt8 16) (blocks : ByteArray) :
    ghash h blocks = ghashSpec h blocks := by
  simp only [ghash, ghashSpec, store_eq]
  congr 1
  refine (List.foldl_hom Elem.toNat (fun y i => ?_)).symm
  rw [mulCT_spec, Elem.xor, toNat_xor, load_toNat, load_toNat]
  have : h.toArray.extract 0 16 = h.toArray := by
    apply Array.ext <;> simp
  simp [this]

end Cryptlib.Primitives.Cipher.GHash
