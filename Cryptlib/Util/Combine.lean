/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

namespace Cryptlib.Util.Combine

/-! # Combining two schemes

Splitting a concatenated encoding, and running a state action against half of a product state. -/

/-- Run a state action against the left half of a product state. -/
def sliftL {ε σ₁ σ₂ α} (x : EStateM ε σ₁ α) : EStateM ε (σ₁ × σ₂) α :=
  fun (s₁, s₂) => match x s₁ with
    | .ok a s₁' => .ok a (s₁', s₂)
    | .error e s₁' => .error e (s₁', s₂)

/-- Run a state action against the right half of a product state. -/
def sliftR {ε σ₁ σ₂ α} (x : EStateM ε σ₂ α) : EStateM ε (σ₁ × σ₂) α :=
  fun (s₁, s₂) => match x s₂ with
    | .ok a s₂' => .ok a (s₁, s₂')
    | .error e s₂' => .error e (s₁, s₂')

theorem sliftL_ok {ε σ₁ σ₂ α} {x : EStateM ε σ₁ α} {s₁ : σ₁} {s₂ : σ₂} {a : α} {t : σ₁ × σ₂}
    (h : sliftL x (s₁, s₂) = .ok a t) : ∃ t₁, x s₁ = .ok a t₁ ∧ t = (t₁, s₂) := by
  rcases hx : x s₁ with ⟨a', t₁⟩ | ⟨e, t₁⟩ <;> simp [sliftL, hx] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨t₁, rfl, rfl⟩

theorem sliftR_ok {ε σ₁ σ₂ α} {x : EStateM ε σ₂ α} {s₁ : σ₁} {s₂ : σ₂} {a : α} {t : σ₁ × σ₂}
    (h : sliftR x (s₁, s₂) = .ok a t) : ∃ t₂, x s₂ = .ok a t₂ ∧ t = (s₁, t₂) := by
  rcases hx : x s₂ with ⟨a', t₂⟩ | ⟨e, t₂⟩ <;> simp [sliftR, hx] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨t₂, rfl, rfl⟩

/-- The first `a` bytes of a concatenation. -/
def splitL {a b : Nat} (v : Vector UInt8 (a + b)) : Vector UInt8 a :=
  (v.take a).cast (by omega)

/-- The remaining `b` bytes of a concatenation. -/
def splitR {a b : Nat} (v : Vector UInt8 (a + b)) : Vector UInt8 b :=
  (v.drop a).cast (by omega)

theorem splitL_append {a b : Nat} (v : Vector UInt8 a) (w : Vector UInt8 b) :
    splitL (v ++ w) = v := by
  apply Vector.ext; intro i hi; simp [splitL, hi]

theorem splitR_append {a b : Nat} (v : Vector UInt8 a) (w : Vector UInt8 b) :
    splitR (v ++ w) = w := by
  apply Vector.ext; intro i hi; simp [splitR]

end Cryptlib.Util.Combine
