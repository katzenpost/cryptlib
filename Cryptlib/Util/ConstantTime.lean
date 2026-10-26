/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

namespace Cryptlib.Util.ConstantTime

/-! # Branch-free helpers

Selection by masks and a byte-string comparison without an early exit, each proved equal to its
branching counterpart. Lengths and loop bounds are treated as public. Lean compiles through C and
neither compiler is proven to preserve the absence of secret-dependent branches, so this is a
property of the source, not a verified property of the machine code. -/

/-- All ones if bit 0 of `b` is set, else zero. -/
def mask (b : UInt64) : UInt64 := 0 - (b &&& 1)

theorem and_one (b : UInt64) : b &&& 1 = if b.toNat.testBit 0 then 1 else 0 := by
  apply UInt64.toNat_inj.mp
  rcases Nat.mod_two_eq_zero_or_one b.toNat with h | h <;>
    simp [Nat.testBit, Nat.and_one_is_mod, h] <;> rfl

theorem and_mask (x b : UInt64) : x &&& mask b = if b.toNat.testBit 0 then x else 0 := by
  rw [mask, and_one]; split <;> simp

/-- The OR of `a[i] ^^^ b[i]` over `i < n`. -/
private def diff (a b : ByteArray) (n : Nat) : UInt8 :=
  Nat.fold n (fun i _ acc => acc ||| (a[i]! ^^^ b[i]!)) 0

/-- Byte-string equality that reads every byte: XOR differences are OR-accumulated over the full
length and tested once at the end. -/
def ctEq (a b : ByteArray) : Bool := a.size == b.size && diff a b a.size == 0

private theorem diff_eq_zero (a b : ByteArray) :
    ∀ n, diff a b n = 0 ↔ ∀ i, i < n → a[i]! = b[i]!
  | 0 => by simp [diff]
  | n + 1 => by
    show (diff a b n ||| (a[n]! ^^^ b[n]!)) = 0 ↔ _
    rw [UInt8.or_eq_zero_iff, diff_eq_zero a b n, UInt8.xor_eq_zero_iff]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem ctEq_iff (a b : ByteArray) : ctEq a b = true ↔ a = b := by
  simp only [ctEq, Bool.and_eq_true, beq_iff_eq, diff_eq_zero]
  constructor
  · rintro ⟨hs, h⟩
    apply ByteArray.ext
    apply Array.ext (by simpa using hs)
    intro i h1 h2
    have h1' : i < a.size := by simpa using h1
    have h2' : i < b.size := by simpa using h2
    have := h i h1'
    rw [getElem!_pos a i h1', getElem!_pos b i h2'] at this
    exact this
  · rintro rfl
    exact ⟨rfl, fun _ _ => rfl⟩

theorem ctEq_eq_decide (a b : ByteArray) : ctEq a b = decide (a = b) := by
  by_cases h : a = b
  · simp [h, (ctEq_iff b b).mpr rfl]
  · simp only [h, decide_false]
    exact Bool.eq_false_iff.mpr fun h' => h ((ctEq_iff a b).mp h')

end Cryptlib.Util.ConstantTime
