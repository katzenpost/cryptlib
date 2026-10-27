/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify

namespace Cryptlib.Primitives.Cipher.Poly1305

/-! # Poly1305 (RFC 8439 §2.5)

`spec` is the RFC's algorithm over `Nat` modulo `p = 2^130 - 5`. `mac` keeps the accumulator in
five 26-bit limbs held in `UInt64`s, so that no step allocates, and `mac_eq_spec` proves the two
equal. Limbs are reduced with `2^130 ≡ 5 (mod p)`; the accumulator is reduced modulo `p` once, at
the end. -/

def p : Nat := 2 ^ 130 - 5

/-- The little-endian value of a byte string. -/
def le (b : Array UInt8) : Nat := b.foldr (fun x acc => (acc <<< 8) ||| x.toNat) 0

def clamp : Nat := 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- RFC 8439 §2.5 over `Nat`. -/
def spec (otk : Vector UInt8 32) (msg : ByteArray) : Vector UInt8 16 :=
  let r := le (otk.toArray.extract 0 16) &&& clamp
  let s := le (otk.toArray.extract 16 32)
  -- `ByteArray.data` copies, so convert once rather than per chunk
  let m := msg.data
  let acc := (List.range ((msg.size + 15) / 16)).foldl (fun acc i =>
    let chunk := m.extract (16 * i) (16 * i + 16)
    (acc + le chunk + 2 ^ (8 * chunk.size)) * r % p) 0
  let t := (acc + s) % 2 ^ 128
  Vector.ofFn fun i : Fin 16 => UInt8.ofNat (t >>> (8 * i.val))

/-! ## Limbs -/

/-- The little-endian value of `f 0, …, f (n - 1)`. -/
def leNat (f : Nat → UInt8) : Nat → Nat
  | 0 => 0
  | n + 1 => leNat f n + (f n).toNat * 256 ^ n

/-- `leNat` in a `UInt64`, for `n ≤ 8`. -/
def leWord (f : Nat → UInt8) : Nat → UInt64
  | 0 => 0
  | n + 1 => leWord f n + ((f n).toUInt64 <<< (8 * n).toUInt64)

/-- Byte `j` of the block of `len` bytes at `off`, with the `1` that follows the block when it
is short. -/
@[inline] def blockByte (m : ByteArray) (off len j : Nat) : UInt8 :=
  if j < len then m.get! (off + j) else if j = len then 1 else 0

def two26 : UInt64 := 0x4000000

/-- The accumulator `h₀ + h₁·2²⁶ + h₂·2⁵² + h₃·2⁷⁸ + h₄·2¹⁰⁴`, and `r` likewise. -/
structure Limbs where
  h0 : UInt64
  h1 : UInt64
  h2 : UInt64
  h3 : UInt64
  h4 : UInt64

def Limbs.val (l : Limbs) : Nat :=
  l.h0.toNat + l.h1.toNat * 2 ^ 26 + l.h2.toNat * 2 ^ 52 + l.h3.toNat * 2 ^ 78 + l.h4.toNat * 2 ^ 104

def Limbs.ofNat (x : Nat) : Limbs :=
  ⟨(x % 2 ^ 26).toUInt64, (x / 2 ^ 26 % 2 ^ 26).toUInt64, (x / 2 ^ 52 % 2 ^ 26).toUInt64,
   (x / 2 ^ 78 % 2 ^ 26).toUInt64, (x / 2 ^ 104).toUInt64⟩

/-- The 16-byte block at `off`, `len` bytes of it in the message, as limbs: `2^128` is added for a
full block, and the padding byte supplies `2^(8·len)` for a short one. -/
@[inline] def block (m : ByteArray) (off len : Nat) : Limbs :=
  let lo := leWord (fun j => blockByte m off len j) 8
  let hi := leWord (fun j => blockByte m off len (8 + j)) 8
  ⟨lo % two26, lo / two26 % two26, (lo / 0x10000000000000 + hi * 4096) % two26,
   hi / 0x4000 % two26, hi / 0x10000000000 + (if len = 16 then 0x1000000 else 0)⟩

/-- `(h + m) · r`, partly reduced. -/
@[inline] def step (r : Limbs) (h m : Limbs) : Limbs :=
  let h0 := h.h0 + m.h0
  let h1 := h.h1 + m.h1
  let h2 := h.h2 + m.h2
  let h3 := h.h3 + m.h3
  let h4 := h.h4 + m.h4
  let s1 := r.h1 * 5
  let s2 := r.h2 * 5
  let s3 := r.h3 * 5
  let s4 := r.h4 * 5
  let d0 := h0 * r.h0 + h1 * s4 + h2 * s3 + h3 * s2 + h4 * s1
  let d1 := h0 * r.h1 + h1 * r.h0 + h2 * s4 + h3 * s3 + h4 * s2 + d0 / two26
  let d2 := h0 * r.h2 + h1 * r.h1 + h2 * r.h0 + h3 * s4 + h4 * s3 + d1 / two26
  let d3 := h0 * r.h3 + h1 * r.h2 + h2 * r.h1 + h3 * r.h0 + h4 * s4 + d2 / two26
  let d4 := h0 * r.h4 + h1 * r.h3 + h2 * r.h2 + h3 * r.h1 + h4 * r.h0 + d3 / two26
  let e0 := d0 % two26 + d4 / two26 * 5
  ⟨e0 % two26, d1 % two26 + e0 / two26, d2 % two26, d3 % two26, d4 % two26⟩

def mac (otk : Vector UInt8 32) (msg : ByteArray) : Vector UInt8 16 :=
  let r := Limbs.ofNat (le (otk.toArray.extract 0 16) &&& clamp)
  let s := le (otk.toArray.extract 16 32)
  let h := (List.range ((msg.size + 15) / 16)).foldl (fun h i =>
    step r h (block msg (16 * i) (min 16 (msg.size - 16 * i)))) ⟨0, 0, 0, 0, 0⟩
  let t := (h.val % p + s) % 2 ^ 128
  Vector.ofFn fun i : Fin 16 => UInt8.ofNat (t >>> (8 * i.val))

/-! ## `mac` is `spec` -/

/-! ### Bytes -/

theorem leNat_lt (f : Nat → UInt8) : ∀ n, leNat f n < 256 ^ n
  | 0 => by simp [leNat]
  | n + 1 => by
    have ih := leNat_lt f n
    have hb := (f n).toNat_lt
    have : (f n).toNat * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
    rw [leNat, Nat.pow_succ]
    omega

theorem leWord_toNat (f : Nat → UInt8) : ∀ n, n ≤ 8 → (leWord f n).toNat = leNat f n
  | 0, _ => rfl
  | n + 1, hn => by
    have ih := leWord_toNat f n (by omega)
    have hl := leNat_lt f n
    have hb : (f n).toNat < 256 := (f n).toNat_lt
    have hpos : 0 < 256 ^ n := Nat.pow_pos (by decide)
    have hpow : 256 * 256 ^ n ≤ 2 ^ 64 := by
      rw [← Nat.pow_succ', show (2:Nat) ^ 64 = 256 ^ 8 from rfl]
      exact Nat.pow_le_pow_right (by omega) hn
    have hlt : (f n).toNat * 256 ^ n < 256 * 256 ^ n := Nat.mul_lt_mul_of_pos_right hb hpos
    have hshift : ((f n).toUInt64 <<< (8 * n).toUInt64).toNat = (f n).toNat * 256 ^ n := by
      rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, Nat.shiftLeft_eq]
      have h8 : (8 * n).toUInt64.toNat % 64 = 8 * n := by
        rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [h8, Nat.pow_mul, show (2:Nat) ^ 8 = 256 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hle : (f n).toNat * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
    rw [leWord, UInt64.toNat_add, ih, hshift, leNat, Nat.mod_eq_of_lt (by omega)]

theorem leNat_congr (f g : Nat → UInt8) :
    ∀ n, (∀ j, j < n → f j = g j) → leNat f n = leNat g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [leNat, leNat, leNat_congr f g n (fun j hj => h j (by omega)), h n (by omega)]

theorem leNat_split (f : Nat → UInt8) (m : Nat) :
    ∀ n, leNat f (m + n) = leNat f m + leNat (fun j => f (m + j)) n * 256 ^ m
  | 0 => by simp [leNat]
  | n + 1 => by
    rw [← Nat.add_assoc, leNat, leNat_split f m n, leNat, Nat.pow_add]
    ring

/-- Zero bytes past `n` add nothing. -/
theorem leNat_zero (f : Nat → UInt8) (n : Nat) (hf : ∀ j, n ≤ j → f j = 0) :
    ∀ k, leNat f (n + k) = leNat f n
  | 0 => rfl
  | k + 1 => by
    rw [← Nat.add_assoc, leNat, leNat_zero f n hf k, hf _ (by omega)]
    simp

theorem le_eq (a : Array UInt8) : le a = leNat (a.getD · 0) a.size := by
  rcases a with ⟨l⟩
  simp only [le, List.foldr_toArray', List.size_toArray]
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.length_cons, Nat.add_comm l.length 1, leNat_split, leNat]
    simp only [leNat, Array.getD, List.size_toArray, List.length_cons]
    rw [← Nat.shiftLeft_add_eq_or_of_lt x.toNat_lt, Nat.shiftLeft_eq]
    simp only [pow_zero, Nat.zero_lt_succ, dite_true,
      Array.getInternal_eq_getElem, List.getElem_toArray, List.getElem_cons_zero, Nat.mul_one,
      Nat.zero_add, pow_one]
    rw [Nat.add_comm]
    congr 2
    apply leNat_congr
    intro j hj
    simp [hj, Nat.add_comm 1 j]

/-! ### Blocks -/

/-- Limbs below these bounds; a block's are `small 25`, the accumulator's after a step
`small 27`. -/
def Limbs.small (l : Limbs) (top : Nat) : Prop :=
  l.h0.toNat < 2 ^ 26 ∧ l.h1.toNat < 2 ^ 27 ∧ l.h2.toNat < 2 ^ 26 ∧ l.h3.toNat < 2 ^ 26 ∧
    l.h4.toNat < 2 ^ top

theorem block_val (m : ByteArray) (off len : Nat) :
    (block m off len).val = leNat (blockByte m off len) 16 + (if len = 16 then 2 ^ 128 else 0) ∧
      (block m off len).small 25 := by
  have hlo := leWord_toNat (fun j => blockByte m off len j) 8 (by omega)
  have hhi := leWord_toNat (fun j => blockByte m off len (8 + j)) 8 (by omega)
  have hsplit := leNat_split (blockByte m off len) 8 8
  simp only [show 8 + 8 = 16 from rfl] at hsplit
  rw [hsplit]
  have hib : (if len = 16 then (0x1000000 : UInt64) else 0).toNat = if len = 16 then 2 ^ 24 else 0 := by
    split <;> rfl
  have hb : (if len = 16 then 2 ^ 24 else 0) ≤ 2 ^ 24 := by split <;> omega
  have h128 : (if len = 16 then 2 ^ 128 else 0) = (if len = 16 then 2 ^ 24 else 0) * 2 ^ 104 := by
    split <;> rfl
  rw [h128]
  simp only [block, Limbs.val, Limbs.small]
  generalize leWord (fun j => blockByte m off len j) 8 = lo at hlo
  generalize leWord (fun j => blockByte m off len (8 + j)) 8 = hi at hhi
  generalize (if len = 16 then (0x1000000 : UInt64) else 0) = b at hib
  generalize (if len = 16 then 2 ^ 24 else 0) = bn at hib hb
  rw [← hlo, ← hhi]
  have hL := lo.toNat_lt
  have hH := hi.toNat_lt
  simp only [two26, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod, hib,
    UInt64.reduceToNat]
  rw [show (2:Nat) ^ 64 = 18446744073709551616 from rfl] at hL hH ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ### One step -/

/-- The arithmetic of `step` over `Nat`: the five column sums `d`, their carries `q`, and the top
carry folded back in as `5·q₄`, give the product less a multiple of `P = 2^130 - 5`. -/
theorem step_arith (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 d0 d1 d2 d3 d4 m0 m1 m2 m3 m4 q0 q1 q2 q3 q4
    e0 n0 t P : Int)
    (hd0 : d0 = x0 * y0 + x1 * (y4 * 5) + x2 * (y3 * 5) + x3 * (y2 * 5) + x4 * (y1 * 5))
    (hd1 : d1 = x0 * y1 + x1 * y0 + x2 * (y4 * 5) + x3 * (y3 * 5) + x4 * (y2 * 5) + q0)
    (hd2 : d2 = x0 * y2 + x1 * y1 + x2 * y0 + x3 * (y4 * 5) + x4 * (y3 * 5) + q1)
    (hd3 : d3 = x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0 + x4 * (y4 * 5) + q2)
    (hd4 : d4 = x0 * y4 + x1 * y3 + x2 * y2 + x3 * y1 + x4 * y0 + q3)
    (hm0 : d0 = m0 + 2 ^ 26 * q0) (hm1 : d1 = m1 + 2 ^ 26 * q1) (hm2 : d2 = m2 + 2 ^ 26 * q2)
    (hm3 : d3 = m3 + 2 ^ 26 * q3) (hm4 : d4 = m4 + 2 ^ 26 * q4)
    (he : e0 = m0 + q4 * 5) (hn : e0 = n0 + 2 ^ 26 * t) (hp : P + 5 = 2 ^ 130) :
    n0 + (m1 + t) * 2 ^ 26 + m2 * 2 ^ 52 + m3 * 2 ^ 78 + m4 * 2 ^ 104 +
      P * (x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + (x2 * y4 + x3 * y3 + x4 * y2) * 2 ^ 26 +
        (x3 * y4 + x4 * y3) * 2 ^ 52 + x4 * y4 * 2 ^ 78 + q4) =
      (x0 + x1 * 2 ^ 26 + x2 * 2 ^ 52 + x3 * 2 ^ 78 + x4 * 2 ^ 104) *
        (y0 + y1 * 2 ^ 26 + y2 * 2 ^ 52 + y3 * 2 ^ 78 + y4 * 2 ^ 104) := by
  linear_combination (-1) * hn + he - hm0 - 2 ^ 26 * hm1 - 2 ^ 52 * hm2 - 2 ^ 78 * hm3 -
    2 ^ 104 * hm4 + hd0 + 2 ^ 26 * hd1 + 2 ^ 52 * hd2 + 2 ^ 78 * hd3 + 2 ^ 104 * hd4 +
    (x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + (x2 * y4 + x3 * y3 + x4 * y2) * 2 ^ 26 +
      (x3 * y4 + x4 * y3) * 2 ^ 52 + x4 * y4 * 2 ^ 78 + q4) * hp

theorem toNat_add_of_lt {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_mul_of_lt {a b : UInt64} (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt h]

/-- A column of `step`: five products of a limb below `2^28` and one below `2^29` cannot
overflow. -/
theorem dot5 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : UInt64)
    (ha0 : a0.toNat < 2 ^ 28) (ha1 : a1.toNat < 2 ^ 28) (ha2 : a2.toNat < 2 ^ 28)
    (ha3 : a3.toNat < 2 ^ 28) (ha4 : a4.toNat < 2 ^ 28)
    (hb0 : b0.toNat < 2 ^ 29) (hb1 : b1.toNat < 2 ^ 29) (hb2 : b2.toNat < 2 ^ 29)
    (hb3 : b3.toNat < 2 ^ 29) (hb4 : b4.toNat < 2 ^ 29) :
    (a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4).toNat =
        a0.toNat * b0.toNat + a1.toNat * b1.toNat + a2.toNat * b2.toNat + a3.toNat * b3.toNat +
          a4.toNat * b4.toNat ∧
      a0.toNat * b0.toNat + a1.toNat * b1.toNat + a2.toNat * b2.toNat + a3.toNat * b3.toNat +
          a4.toNat * b4.toNat < 2 ^ 60 := by
  have p0 := Nat.mul_lt_mul'' ha0 hb0
  have p1 := Nat.mul_lt_mul'' ha1 hb1
  have p2 := Nat.mul_lt_mul'' ha2 hb2
  have p3 := Nat.mul_lt_mul'' ha3 hb3
  have p4 := Nat.mul_lt_mul'' ha4 hb4
  rw [← Nat.pow_add] at p0 p1 p2 p3 p4
  norm_num at p0 p1 p2 p3 p4
  have e0 : (a0 * b0).toNat = a0.toNat * b0.toNat := toNat_mul_of_lt (by omega)
  have e1 : (a1 * b1).toNat = a1.toNat * b1.toNat := toNat_mul_of_lt (by omega)
  have e2 : (a2 * b2).toNat = a2.toNat * b2.toNat := toNat_mul_of_lt (by omega)
  have e3 : (a3 * b3).toNat = a3.toNat * b3.toNat := toNat_mul_of_lt (by omega)
  have e4 : (a4 * b4).toNat = a4.toNat * b4.toNat := toNat_mul_of_lt (by omega)
  have s1 : (a0 * b0 + a1 * b1).toNat = a0.toNat * b0.toNat + a1.toNat * b1.toNat := by
    rw [toNat_add_of_lt (by rw [e0, e1]; omega), e0, e1]
  have s2 : (a0 * b0 + a1 * b1 + a2 * b2).toNat =
      a0.toNat * b0.toNat + a1.toNat * b1.toNat + a2.toNat * b2.toNat := by
    rw [toNat_add_of_lt (by rw [s1, e2]; omega), s1, e2]
  have s3 : (a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3).toNat =
      a0.toNat * b0.toNat + a1.toNat * b1.toNat + a2.toNat * b2.toNat + a3.toNat * b3.toNat := by
    rw [toNat_add_of_lt (by rw [s2, e3]; omega), s2, e3]
  rw [toNat_add_of_lt (by rw [s3, e4]; omega), s3, e4]
  exact ⟨rfl, by omega⟩

theorem toNat_two26 : two26.toNat = 2 ^ 26 := rfl

theorem step_val (r h m : Limbs) (hr0 : r.h0.toNat < 2 ^ 26) (hr1 : r.h1.toNat < 2 ^ 26)
    (hr2 : r.h2.toNat < 2 ^ 26) (hr3 : r.h3.toNat < 2 ^ 26) (hr4 : r.h4.toNat < 2 ^ 26)
    (hh : h.small 26) (hm : m.small 25) :
    (step r h m).small 26 ∧ ∃ K, (step r h m).val + p * K = (h.val + m.val) * r.val := by
  obtain ⟨hh0, hh1, hh2, hh3, hh4⟩ := hh
  obtain ⟨hm0, hm1, hm2, hm3, hm4⟩ := hm
  have ea0 : (h.h0 + m.h0).toNat = h.h0.toNat + m.h0.toNat := toNat_add_of_lt (by omega)
  have ea1 : (h.h1 + m.h1).toNat = h.h1.toNat + m.h1.toNat := toNat_add_of_lt (by omega)
  have ea2 : (h.h2 + m.h2).toNat = h.h2.toNat + m.h2.toNat := toNat_add_of_lt (by omega)
  have ea3 : (h.h3 + m.h3).toNat = h.h3.toNat + m.h3.toNat := toNat_add_of_lt (by omega)
  have ea4 : (h.h4 + m.h4).toNat = h.h4.toNat + m.h4.toNat := toNat_add_of_lt (by omega)
  have es1 : (r.h1 * 5).toNat = r.h1.toNat * 5 := toNat_mul_of_lt (by simp; omega)
  have es2 : (r.h2 * 5).toNat = r.h2.toNat * 5 := toNat_mul_of_lt (by simp; omega)
  have es3 : (r.h3 * 5).toNat = r.h3.toNat * 5 := toNat_mul_of_lt (by simp; omega)
  have es4 : (r.h4 * 5).toNat = r.h4.toNat * 5 := toNat_mul_of_lt (by simp; omega)
  have hval : h.val + m.val = (h.h0.toNat + m.h0.toNat) + (h.h1.toNat + m.h1.toNat) * 2 ^ 26 +
      (h.h2.toNat + m.h2.toNat) * 2 ^ 52 + (h.h3.toNat + m.h3.toNat) * 2 ^ 78 +
      (h.h4.toNat + m.h4.toNat) * 2 ^ 104 := by
    simp only [Limbs.val]; ring
  rw [hval]
  simp only [step, Limbs.val, Limbs.small]
  generalize h.h0 + m.h0 = a0 at ea0 ⊢
  generalize h.h1 + m.h1 = a1 at ea1 ⊢
  generalize h.h2 + m.h2 = a2 at ea2 ⊢
  generalize h.h3 + m.h3 = a3 at ea3 ⊢
  generalize h.h4 + m.h4 = a4 at ea4 ⊢
  generalize r.h1 * 5 = s1 at es1 ⊢
  generalize r.h2 * 5 = s2 at es2 ⊢
  generalize r.h3 * 5 = s3 at es3 ⊢
  generalize r.h4 * 5 = s4 at es4 ⊢
  rw [← ea0, ← ea1, ← ea2, ← ea3, ← ea4]
  have ha0 : a0.toNat < 2 ^ 28 := by omega
  have ha1 : a1.toNat < 2 ^ 28 := by omega
  have ha2 : a2.toNat < 2 ^ 28 := by omega
  have ha3 : a3.toNat < 2 ^ 28 := by omega
  have ha4 : a4.toNat < 2 ^ 28 := by omega
  have hy0 : r.h0.toNat < 2 ^ 29 := by omega
  have hy1 : r.h1.toNat < 2 ^ 29 := by omega
  have hy2 : r.h2.toNat < 2 ^ 29 := by omega
  have hy3 : r.h3.toNat < 2 ^ 29 := by omega
  have hy4 : r.h4.toNat < 2 ^ 29 := by omega
  have hs1 : s1.toNat < 2 ^ 29 := by omega
  have hs2 : s2.toNat < 2 ^ 29 := by omega
  have hs3 : s3.toNat < 2 ^ 29 := by omega
  have hs4 : s4.toNat < 2 ^ 29 := by omega
  -- the five columns, each with the carry of the one before
  obtain ⟨c0, b0⟩ := dot5 a0 a1 a2 a3 a4 r.h0 s4 s3 s2 s1 ha0 ha1 ha2 ha3 ha4 hy0 hs4 hs3 hs2 hs1
  generalize a0 * r.h0 + a1 * s4 + a2 * s3 + a3 * s2 + a4 * s1 = D0 at c0 ⊢
  obtain ⟨c1, b1⟩ := dot5 a0 a1 a2 a3 a4 r.h1 r.h0 s4 s3 s2 ha0 ha1 ha2 ha3 ha4 hy1 hy0 hs4 hs3 hs2
  have f1 : (a0 * r.h1 + a1 * r.h0 + a2 * s4 + a3 * s3 + a4 * s2 + D0 / two26).toNat =
      (a0 * r.h1 + a1 * r.h0 + a2 * s4 + a3 * s3 + a4 * s2).toNat + D0.toNat / 2 ^ 26 := by
    rw [toNat_add_of_lt, UInt64.toNat_div, toNat_two26]
    rw [UInt64.toNat_div, toNat_two26, c1]; omega
  generalize a0 * r.h1 + a1 * r.h0 + a2 * s4 + a3 * s3 + a4 * s2 + D0 / two26 = D1 at f1 ⊢
  obtain ⟨c2, b2⟩ := dot5 a0 a1 a2 a3 a4 r.h2 r.h1 r.h0 s4 s3 ha0 ha1 ha2 ha3 ha4 hy2 hy1 hy0 hs4 hs3
  have f2 : (a0 * r.h2 + a1 * r.h1 + a2 * r.h0 + a3 * s4 + a4 * s3 + D1 / two26).toNat =
      (a0 * r.h2 + a1 * r.h1 + a2 * r.h0 + a3 * s4 + a4 * s3).toNat + D1.toNat / 2 ^ 26 := by
    rw [toNat_add_of_lt, UInt64.toNat_div, toNat_two26]
    rw [UInt64.toNat_div, toNat_two26, c2, f1, c1]; omega
  generalize a0 * r.h2 + a1 * r.h1 + a2 * r.h0 + a3 * s4 + a4 * s3 + D1 / two26 = D2 at f2 ⊢
  obtain ⟨c3, b3⟩ := dot5 a0 a1 a2 a3 a4 r.h3 r.h2 r.h1 r.h0 s4 ha0 ha1 ha2 ha3 ha4 hy3 hy2 hy1 hy0 hs4
  have f3 : (a0 * r.h3 + a1 * r.h2 + a2 * r.h1 + a3 * r.h0 + a4 * s4 + D2 / two26).toNat =
      (a0 * r.h3 + a1 * r.h2 + a2 * r.h1 + a3 * r.h0 + a4 * s4).toNat + D2.toNat / 2 ^ 26 := by
    rw [toNat_add_of_lt, UInt64.toNat_div, toNat_two26]
    rw [UInt64.toNat_div, toNat_two26, c3, f2, c2, f1, c1]; omega
  generalize a0 * r.h3 + a1 * r.h2 + a2 * r.h1 + a3 * r.h0 + a4 * s4 + D2 / two26 = D3 at f3 ⊢
  obtain ⟨c4, b4⟩ := dot5 a0 a1 a2 a3 a4 r.h4 r.h3 r.h2 r.h1 r.h0 ha0 ha1 ha2 ha3 ha4 hy4 hy3 hy2 hy1 hy0
  have f4 : (a0 * r.h4 + a1 * r.h3 + a2 * r.h2 + a3 * r.h1 + a4 * r.h0 + D3 / two26).toNat =
      (a0 * r.h4 + a1 * r.h3 + a2 * r.h2 + a3 * r.h1 + a4 * r.h0).toNat + D3.toNat / 2 ^ 26 := by
    rw [toNat_add_of_lt, UInt64.toNat_div, toNat_two26]
    rw [UInt64.toNat_div, toNat_two26, c4, f3, c3, f2, c2, f1, c1]; omega
  generalize a0 * r.h4 + a1 * r.h3 + a2 * r.h2 + a3 * r.h1 + a4 * r.h0 + D3 / two26 = D4 at f4 ⊢
  rw [c1] at f1
  rw [c2] at f2
  rw [c3] at f3
  rw [c4] at f4
  -- the top carry, times 5, goes back into the bottom limb
  have g0 : (D0 % two26 + D4 / two26 * 5).toNat = D0.toNat % 2 ^ 26 + D4.toNat / 2 ^ 26 * 5 := by
    have q : (D4 / two26 * 5).toNat = D4.toNat / 2 ^ 26 * 5 := by
      rw [toNat_mul_of_lt] <;> simp only [UInt64.toNat_div, toNat_two26, UInt64.reduceToNat]; omega
    rw [toNat_add_of_lt, q, UInt64.toNat_mod, toNat_two26]
    rw [q, UInt64.toNat_mod, toNat_two26]; omega
  generalize D0 % two26 + D4 / two26 * 5 = E0 at g0 ⊢
  have g1 : (D1 % two26 + E0 / two26).toNat = D1.toNat % 2 ^ 26 + E0.toNat / 2 ^ 26 := by
    rw [toNat_add_of_lt] <;> simp only [UInt64.toNat_mod, UInt64.toNat_div, toNat_two26]; omega
  simp only [UInt64.toNat_mod, toNat_two26]
  rw [g1]
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega⟩, ?_⟩
  refine ⟨a1.toNat * r.h4.toNat + a2.toNat * r.h3.toNat + a3.toNat * r.h2.toNat +
    a4.toNat * r.h1.toNat + (a2.toNat * r.h4.toNat + a3.toNat * r.h3.toNat + a4.toNat * r.h2.toNat) * 2 ^ 26 +
    (a3.toNat * r.h4.toNat + a4.toNat * r.h3.toNat) * 2 ^ 52 + a4.toNat * r.h4.toNat * 2 ^ 78 +
    D4.toNat / 2 ^ 26, ?_⟩
  have key := step_arith a0.toNat a1.toNat a2.toNat a3.toNat a4.toNat r.h0.toNat r.h1.toNat
    r.h2.toNat r.h3.toNat r.h4.toNat D0.toNat D1.toNat D2.toNat D3.toNat D4.toNat
    (D0.toNat % 2 ^ 26 : Nat) (D1.toNat % 2 ^ 26 : Nat) (D2.toNat % 2 ^ 26 : Nat)
    (D3.toNat % 2 ^ 26 : Nat) (D4.toNat % 2 ^ 26 : Nat)
    (D0.toNat / 2 ^ 26 : Nat) (D1.toNat / 2 ^ 26 : Nat) (D2.toNat / 2 ^ 26 : Nat)
    (D3.toNat / 2 ^ 26 : Nat) (D4.toNat / 2 ^ 26 : Nat)
    E0.toNat (E0.toNat % 2 ^ 26 : Nat) (E0.toNat / 2 ^ 26 : Nat) p
    (by rw [c0, es1, es2, es3, es4]; push_cast; ring)
    (by rw [f1, es2, es3, es4]; push_cast; ring)
    (by rw [f2, es3, es4]; push_cast; ring)
    (by rw [f3, es4]; push_cast; ring)
    (by rw [f4]; push_cast; ring)
    (by exact_mod_cast (Nat.mod_add_div _ _).symm) (by exact_mod_cast (Nat.mod_add_div _ _).symm)
    (by exact_mod_cast (Nat.mod_add_div _ _).symm) (by exact_mod_cast (Nat.mod_add_div _ _).symm)
    (by exact_mod_cast (Nat.mod_add_div _ _).symm)
    (by exact_mod_cast g0) (by exact_mod_cast (Nat.mod_add_div _ _).symm)
    (by norm_num [p])
  exact_mod_cast key

/-! ### The key and the blocks -/

theorem ofNat_val (x : Nat) (hx : x < 2 ^ 128) :
    (Limbs.ofNat x).val = x ∧ (Limbs.ofNat x).h0.toNat < 2 ^ 26 ∧
      (Limbs.ofNat x).h1.toNat < 2 ^ 26 ∧ (Limbs.ofNat x).h2.toNat < 2 ^ 26 ∧
      (Limbs.ofNat x).h3.toNat < 2 ^ 26 ∧ (Limbs.ofNat x).h4.toNat < 2 ^ 26 := by
  have t (n : Nat) : n.toUInt64.toNat = n % 2 ^ 64 := by rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  simp only [Limbs.ofNat, Limbs.val, t]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem le_lt (a : Array UInt8) : le a < 256 ^ a.size := by
  rw [le_eq]; exact leNat_lt _ _

/-- A block's limbs are the RFC's chunk with its `1` appended. -/
theorem block_chunk (m : ByteArray) (off : Nat) :
    (block m off (min 16 (m.size - off))).val =
        le (m.data.extract off (off + 16)) + 2 ^ (8 * (m.data.extract off (off + 16)).size) ∧
      (block m off (min 16 (m.size - off))).small 25 := by
  obtain ⟨hv, hs⟩ := block_val m off (min 16 (m.size - off))
  refine ⟨?_, hs⟩
  rw [hv]
  have hms : m.size = m.data.size := rfl
  have hsize : (m.data.extract off (off + 16)).size = min 16 (m.size - off) := by
    rw [Array.size_extract, hms]; omega
  rw [hsize, le_eq, hsize]
  generalize hlen : min 16 (m.size - off) = len
  have hl16 : len ≤ 16 := by omega
  have hsplit := leNat_split (blockByte m off len) len (16 - len)
  rw [Nat.add_sub_cancel' hl16] at hsplit
  rw [hsplit]
  have hfirst : leNat (blockByte m off len) len =
      leNat ((m.data.extract off (off + 16)).getD · 0) len := by
    apply leNat_congr
    intro j hj
    have hj' : off + j < m.data.size := by omega
    have hj'' : j < (m.data.extract off (off + 16)).size := by rw [Array.size_extract]; omega
    simp only [blockByte, ite_eq_left hj, ByteArray.get!, Array.getD, dite_eq_left hj'',
      Array.getInternal_eq_getElem, Array.getElem_extract]
    exact getElem!_pos m.data (off + j) hj'
  rw [hfirst]
  by_cases h16 : len = 16
  · subst h16
    simp [leNat]
  · have hpad : leNat (fun j => blockByte m off len (len + j)) (16 - len) = 1 := by
      have := leNat_zero (fun j => blockByte m off len (len + j)) 1
        (fun j hj => by simp only [blockByte]; rw [ite_eq_right (by omega), ite_eq_right (by omega)])
        (16 - len - 1)
      rw [show 1 + (16 - len - 1) = 16 - len by omega] at this
      rw [this]
      simp [leNat, blockByte]
    rw [hpad, ite_eq_right h16, Nat.pow_mul]
    simp

/-! ### The whole message -/

/-- Over any run of blocks, the limbs stay small and agree with `spec`'s accumulator modulo `p`. -/
theorem fold_val (rN : Nat) (hr : rN < 2 ^ 128) (msg : ByteArray) :
    ∀ (l : List Nat) (acc : Nat) (h : Limbs), h.small 26 → h.val % p = acc →
      (l.foldl (fun h i => step (Limbs.ofNat rN) h (block msg (16 * i) (min 16 (msg.size - 16 * i))))
          h).small 26 ∧
        (l.foldl (fun h i => step (Limbs.ofNat rN) h (block msg (16 * i) (min 16 (msg.size - 16 * i))))
          h).val % p =
        l.foldl (fun acc i => (acc + le (msg.data.extract (16 * i) (16 * i + 16)) +
          2 ^ (8 * (msg.data.extract (16 * i) (16 * i + 16)).size)) * rN % p) acc := by
  obtain ⟨hrv, hr0, hr1, hr2, hr3, hr4⟩ := ofNat_val rN hr
  intro l
  induction l with
  | nil => intro acc h hs hv; exact ⟨hs, hv⟩
  | cons i l ih =>
    intro acc h hs hv
    simp only [List.foldl_cons]
    obtain ⟨hbv, hbs⟩ := block_chunk msg (16 * i)
    obtain ⟨hs', K, hK⟩ := step_val (Limbs.ofNat rN) h _ hr0 hr1 hr2 hr3 hr4 hs hbs
    apply ih _ _ hs'
    have hmod : h.val ≡ acc [MOD p] := by
      show h.val % p = acc % p
      rw [← hv, Nat.mod_mod]
    calc (step (Limbs.ofNat rN) h (block msg (16 * i) (min 16 (msg.size - 16 * i)))).val % p
        = ((step (Limbs.ofNat rN) h (block msg (16 * i) (min 16 (msg.size - 16 * i)))).val +
            p * K) % p := (Nat.add_mul_mod_self_left _ _ _).symm
      _ = ((h.val + (block msg (16 * i) (min 16 (msg.size - 16 * i))).val) * rN) % p := by
          rw [hK, hrv]
      _ = _ := by
          rw [hbv, ← Nat.add_assoc]
          exact ((hmod.add_right _).add_right _).mul_right _

theorem mac_eq_spec (otk : Vector UInt8 32) (msg : ByteArray) : mac otk msg = spec otk msg := by
  have hr : le (otk.toArray.extract 0 16) &&& clamp < 2 ^ 128 := by
    have := le_lt (otk.toArray.extract 0 16)
    have hs : (otk.toArray.extract 0 16).size = 16 := by simp
    rw [hs] at this
    exact Nat.lt_of_le_of_lt Nat.and_le_left this
  have h0 : (⟨0, 0, 0, 0, 0⟩ : Limbs).small 26 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  have hv := (fold_val _ hr msg (List.range ((msg.size + 15) / 16)) 0 ⟨0, 0, 0, 0, 0⟩ h0
    (by decide)).2
  simp only [mac, spec]
  rw [hv]

end Cryptlib.Primitives.Cipher.Poly1305
