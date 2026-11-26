/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import Cryptlib.Protocols.RSOR
import Cryptlib.Primitives.WideBlockCipher.OneQuery

/-! # An honest relay decrypts one block per header

An honest relay processes a header once, and replies only to an onion it has processed. So if
the relay decrypts under one header only, it asks for the decryption of one block. Here that is
shown for the games' oracles: a relay that asks a decryption oracle which answers for one block
only behaves as a relay that decrypts by itself. -/

namespace Cryptlib.Protocols.RSOR

open OracleComp OracleSpec
open Cryptlib.Primitives.WideBlockCipher (decSpec decOnce decFirst simulateQ_decOnce_liftM
  simulateQ_decOnce_query)

variable {S : Scheme} {L : Nat} (H : S.Header) (key : S.Onion → Vector UInt8 L)
  (step : S.Onion → Vector UInt8 L → Option S.Step)
  (rep : S.Msg → S.Onion → Vector UInt8 L → Option (S.Name × S.Onion))
  (proc : Role → S.Onion → Option S.Step)
  (reply : Role → S.Msg → S.Onion → Option (S.Name × S.Onion))

/-- The honest relays, with `.relay` asking a decryption oracle under the header `H`. -/
def viaDec (patch : Patch S) :
    QueryImpl (oracleSpec S) (StateT (Log S) (OracleComp (decSpec L))) :=
  oracle
    (fun h o => if h = .relay ∧ o.1 = H then
        step o <$> (liftM ((Vector UInt8 L →ₒ Vector UInt8 L).query (key o)) :
          OracleComp (decSpec L) _)
      else pure (proc h o))
    (fun h msg o => if h = .relay ∧ o.1 = H then
        rep msg o <$> (liftM ((Vector UInt8 L →ₒ Vector UInt8 L).query (key o)) :
          OracleComp (decSpec L) _)
      else pure (reply h msg o))
    patch

/-- The honest relays, with `.relay` decrypting by `dec` under the header `H`. -/
def withDec (dec : Vector UInt8 L → Vector UInt8 L) (patch : Patch S) :
    QueryImpl (oracleSpec S) (StateT (Log S) ProbComp) :=
  oracle
    (fun h o => pure (if h = .relay ∧ o.1 = H then step o (dec (key o)) else proc h o))
    (fun h msg o => pure (if h = .relay ∧ o.1 = H then rep msg o (dec (key o))
      else reply h msg o))
    patch

/-- **An honest relay decrypts one block per header.** A relay that asks an oracle which
decrypts one block only is a relay that decrypts by itself. -/
theorem viaDec_decOnce (dec : Vector UInt8 L → Vector UInt8 L) (patch : Patch S) {α : Type}
    (oa : OracleComp (oracleSpec S) α) (log : Log S) (hw : log.WF) :
    (simulateQ (decOnce dec)
        ((simulateQ (viaDec H key step rep proc reply patch) oa).run' log)).run' none
      = (simulateQ (withDec H key step rep proc reply dec patch) oa).run' log := by
  let inv : Log S × Option (Vector UInt8 L) → Prop := fun s =>
    s.1.WF ∧ ∀ x, s.2 = some x →
      (Role.relay, H) ∈ s.1.seen ∧ ∀ o, (Role.relay, o) ∈ s.1.held → o.1 = H → key o = x
  let combined : QueryImpl (oracleSpec S) (StateT (Log S × Option (Vector UInt8 L)) ProbComp) :=
    fun q => StateT.mk fun s =>
      (fun r : (_ × Log S) × Option (Vector UInt8 L) => (r.1.1, r.1.2, r.2)) <$>
        (simulateQ (decOnce dec) ((viaDec H key step rep proc reply patch q).run s.1)).run s.2
  have hc := simulateQ_StateT_StateT_compose (viaDec H key step rep proc reply patch)
    (decOnce dec) combined (fun q s c => by
      simp only [combined, StateT.run, StateT.mk, Functor.map_map]
      exact (id_map _).symm) oa log none
  have hinv : ∀ t s, inv s → ∀ y ∈ support ((combined t).run s), inv y.2 := by
    intro t s hs y hy
    obtain ⟨log, memo⟩ := s
    have herase : ∀ x, inv ({ seen := log.seen, held := log.held.erase x }, memo) := fun x =>
      ⟨hs.1.erase x, fun x' hx' => ⟨(hs.2 x' hx').1, fun o' hm he =>
        (hs.2 x' hx').2 o' (List.mem_of_mem_erase hm) he⟩⟩
    rcases t with (u | ⟨h, o⟩) | ⟨h, msg, o⟩
    · simp [combined, viaDec, oracle, simulateQ_decOnce_liftM] at hy
      obtain ⟨_, rfl⟩ := hy
      exact hs
    · by_cases hseen : (h, o.1) ∈ log.seen
      · simp [combined, viaDec, oracle, process, hseen] at hy
        subst hy
        exact hs
      · by_cases hr : h = Role.relay ∧ o.1 = H
        · cases memo with
          | some x =>
            obtain ⟨rfl, rfl⟩ := hr
            exact absurd (hs.2 x rfl).1 hseen
          | none =>
            obtain ⟨rfl, rfl⟩ := hr
            simp [combined, viaDec, oracle, process, hseen,
              simulateQ_decOnce_liftM, simulateQ_decOnce_query, decFirst] at hy
            obtain ⟨_, -, rfl⟩ := hy
            refine ⟨hs.1.cons _ o hseen, fun x hx => ?_⟩
            obtain rfl := Option.some.inj hx
            refine ⟨List.mem_cons_self, fun o' hm he => ?_⟩
            rcases List.mem_cons.1 hm with heq | hm
            · cases heq
              rfl
            · exact absurd (by rw [← he]; exact hs.1.1 _ _ hm) hseen
        · simp [combined, viaDec, oracle, process, hseen, hr,
            simulateQ_decOnce_liftM] at hy
          obtain ⟨_, -, rfl⟩ := hy
          refine ⟨hs.1.cons h o hseen, fun x hx => ?_⟩
          obtain ⟨h1, h2⟩ := hs.2 x hx
          refine ⟨List.mem_cons_of_mem _ h1, fun o' hm he => ?_⟩
          rcases List.mem_cons.1 hm with heq | hm
          · cases heq
            exact absurd ⟨rfl, he⟩ hr
          · exact h2 o' hm he
    · by_cases hheld : (h, o) ∈ log.held
      · by_cases hr : h = Role.relay ∧ o.1 = H
        · cases memo with
          | some x =>
            obtain ⟨rfl, rfl⟩ := hr
            have hx := (hs.2 x rfl).2 o hheld rfl
            simp [combined, viaDec, oracle, answer, hheld,
              simulateQ_decOnce_query, decFirst, hx] at hy
            subst hy
            exact herase _
          | none =>
            obtain ⟨rfl, rfl⟩ := hr
            simp [combined, viaDec, oracle, answer, hheld,
              simulateQ_decOnce_query, decFirst] at hy
            subst hy
            refine ⟨hs.1.erase _, fun x hx => ?_⟩
            obtain rfl := Option.some.inj hx
            refine ⟨hs.1.1 _ _ hheld, fun o' hm he => ?_⟩
            rw [hs.1.2 _ o' o (List.mem_of_mem_erase hm) hheld he]
        · simp [combined, viaDec, oracle, answer, hheld, hr] at hy
          subst hy
          exact herase _
      · simp [combined, viaDec, oracle, answer, hheld] at hy
        subst hy
        exact hs
  have hproj : ∀ t s, inv s → Prod.map id Prod.fst <$> (combined t).run s
      = (withDec H key step rep proc reply dec patch t).run (Prod.fst s) := by
    intro t s hs
    obtain ⟨log, memo⟩ := s
    rcases t with (u | ⟨h, o⟩) | ⟨h, msg, o⟩
    · simp [combined, viaDec, withDec, oracle, simulateQ_decOnce_liftM]
    · by_cases hseen : (h, o.1) ∈ log.seen
      · simp [combined, viaDec, withDec, oracle, process, hseen]
      · by_cases hr : h = Role.relay ∧ o.1 = H
        · cases memo with
          | some x =>
            obtain ⟨rfl, rfl⟩ := hr
            exact absurd (hs.2 x rfl).1 hseen
          | none =>
            obtain ⟨rfl, rfl⟩ := hr
            simp [combined, viaDec, withDec, oracle, process, hseen,
              simulateQ_decOnce_liftM, simulateQ_decOnce_query, decFirst]
        · simp [combined, viaDec, withDec, oracle, process, hseen, hr,
            simulateQ_decOnce_liftM]
    · by_cases hheld : (h, o) ∈ log.held
      · by_cases hr : h = Role.relay ∧ o.1 = H
        · cases memo with
          | some x =>
            obtain ⟨rfl, rfl⟩ := hr
            have hx := (hs.2 x rfl).2 o hheld rfl
            simp [combined, viaDec, withDec, oracle, answer, hheld,
              simulateQ_decOnce_query, decFirst, hx]
          | none =>
            obtain ⟨rfl, rfl⟩ := hr
            simp [combined, viaDec, withDec, oracle, answer, hheld,
              simulateQ_decOnce_query, decFirst]
        · simp [combined, viaDec, withDec, oracle, answer, hheld, hr]
      · simp [combined, viaDec, withDec, oracle, answer, hheld]
  have hp := map_run_simulateQ_eq_of_query_map_eq_inv' combined
    (withDec H key step rep proc reply dec patch) inv Prod.fst hinv hproj oa (log, none)
    ⟨hw, fun x hx => by cases hx⟩
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [hc, ← hp]
  simp [Functor.map_map]

end Cryptlib.Protocols.RSOR
