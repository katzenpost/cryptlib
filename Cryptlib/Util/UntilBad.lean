/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! # Two oracles that agree until a bad query

`abs_sub_le_bad` is the usual step of a game-hopping proof for oracles without state: if two
implementations of an oracle answer every query alike except the bad ones, an adversary tells
them apart with at most the chance that it asks a bad query. That chance is stated on the second
implementation, run with a record of the queries (`logged`), so that a reduction which answers
as the second implementation does can hand the record to its own challenger. -/

namespace Cryptlib.Util.UntilBad

open OracleComp OracleSpec ENNReal

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- `impl`, recording the queries. -/
def logged (impl : QueryImpl spec ProbComp) :
    QueryImpl spec (StateT (List spec.Domain) ProbComp) :=
  fun t => StateT.mk fun l => (fun u => (u, l ++ [t])) <$> impl t

/-- `impl`, with a flag that a bad query raises. -/
def flagged (impl : QueryImpl spec ProbComp) (isBad : spec.Domain → Bool) :
    QueryImpl spec (StateT Bool ProbComp) :=
  fun t => StateT.mk fun b => (fun u => (u, b || isBad t)) <$> impl t

/-- The flag does not change the answers. -/
theorem run'_flagged (impl : QueryImpl spec ProbComp) (isBad : spec.Domain → Bool) {α : Type}
    (oa : OracleComp spec α) (b : Bool) :
    (simulateQ (flagged impl isBad) oa).run' b = simulateQ impl oa := by
  rw [OracleComp.run'_simulateQ_eq_of_query_map_eq (flagged impl isBad)
    (impl.liftTarget (StateT Unit ProbComp)) (fun _ => ()) (fun t s => by simp [flagged]) oa b,
    simulateQ_liftTarget]
  simp

/-- **Agreeing until a bad query.** -/
theorem abs_sub_le_bad (impl₁ impl₂ : QueryImpl spec ProbComp) (isBad : spec.Domain → Bool)
    (h : ∀ t, isBad t = false → impl₁ t = impl₂ t) (oa : OracleComp spec Bool) :
    |(Pr{let x ← simulateQ impl₁ oa}[x = true]).toReal
      - (Pr{let x ← simulateQ impl₂ oa}[x = true]).toReal|
    ≤ (Pr{let z ← (simulateQ (logged impl₂) oa).run []}[z.2.any isBad = true]).toReal := by
  have hagree : ∀ t s, ¬ s = true → ∀ q : spec.Range t × Bool → Prop,
      Pr{let z ← (flagged impl₁ isBad t).run s}[q z ∧ ¬ z.2 = true]
        = Pr{let z ← (flagged impl₂ isBad t).run s}[q z ∧ ¬ z.2 = true] := by
    intro t s _ q
    cases hb : isBad t
    · rw [show flagged impl₁ isBad t = flagged impl₂ isBad t by simp only [flagged, h t hb]]
    · simp [flagged, hb, prEvent_map]
  have hmono : ∀ impl : QueryImpl spec ProbComp, ∀ t s, s = true →
      ∀ z ∈ support ((flagged impl isBad t).run s), z.2 = true := by
    intro impl t s hs z hz
    simp only [flagged, StateT.run_mk, hs, Bool.true_or, support_map, Set.mem_image] at hz
    obtain ⟨u, -, rfl⟩ := hz
    rfl
  have hd := OracleComp.ProgramLogic.Relational.measureETVDist_simulateQ_run'_le_prEvent_bad
    (flagged impl₁ isBad) (flagged impl₂ isBad) (· = true) hagree (hmono impl₁) (hmono impl₂)
    oa false
  rw [run'_flagged, run'_flagged,
    OracleComp.ProgramLogic.Relational.prEvent_simulateQ_run_bad_eq (flagged impl₁ isBad)
      (flagged impl₂ isBad) (· = true) hagree (hmono impl₁) (hmono impl₂) oa false] at hd
  have e : (simulateQ (flagged impl₂ isBad) oa).run false
      = Prod.map id (fun l : List spec.Domain => l.any isBad)
        <$> (simulateQ (logged impl₂) oa).run [] :=
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq (logged impl₂) (flagged impl₂ isBad)
      (fun l => l.any isBad) (fun t s => by simp [logged, flagged]) oa []).symm
  rw [e, prEvent_map] at hd
  refine (abs_prEvent_toReal_sub_le_measureTVDist _ _ (· = true) Measurable.of_discrete).trans ?_
  rw [measureTVDist_eq_toReal_measureETVDist]
  exact ENNReal.toReal_mono (prEvent_ne_top _) hd

end Cryptlib.Util.UntilBad
