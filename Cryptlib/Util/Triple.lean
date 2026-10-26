/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Std.Tactic.Do

open Std.Do

namespace Cryptlib.Util.Triple

/-! # Hoare triples for `EStateM` -/

/-- Partial-correctness triple: if `x` returns, its result satisfies `p`. -/
theorem EStateM_triple_ok {ε σ α} {p : α → Prop} {x : EStateM ε σ α}
    (h : ∀ t a t', x t = .ok a t' → p a) :
    ⦃⌜True⌝⦄ x ⦃post⟨fun a => ⌜p a⌝, fun _ => ⌜True⌝⟩⦄ := by
  intro t _
  simp only [WP.wp, PredTrans.apply, EStateM.run]
  cases hx : x t with
  | ok a t'    => exact h t a t' hx
  | error e t' => trivial

/-- Total-correctness triple: `x` always returns a result satisfying `p`. -/
theorem EStateM_triple {ε σ α} {p : α → Prop} {x : EStateM ε σ α}
    (h : ∀ t, ∃ a t', x t = .ok a t' ∧ p a) :
    ⦃⌜True⌝⦄ x ⦃post⟨fun a => ⌜p a⌝, fun _ => ⌜False⌝⟩⦄ := by
  intro t _
  obtain ⟨a, t', ht, hp⟩ := h t
  simp only [WP.wp, PredTrans.apply, EStateM.run, ht]
  exact hp

end Cryptlib.Util.Triple
