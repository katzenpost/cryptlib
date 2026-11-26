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

/-! ## A patch that draws once

A relay processes a header once. So a patch that draws only under one header at `.relay` may
draw before the game starts. -/

section Draw

variable {X : Type} (D : ProbComp X) (P : Patch S) (Pe : X → Patch S)
  (procM : Role → S.Onion → ProbComp (Option S.Step))
  (replyM : Role → S.Msg → S.Onion → ProbComp (Option (S.Name × S.Onion)))

/-- What processing an onion does to the log and the answer. -/
theorem oracle_process_run (h : Role) (o : S.Onion) (log : Log S) :
    (oracle procM replyM P (.inl (.inr (h, o)))).run log
      = if (h, o.1) ∈ log.seen then pure (none, log)
        else procM h o >>= fun out => (fun a =>
          (a, ({ seen := (h, o.1) :: log.seen, held := (h, o) :: log.held } : Log S)))
            <$> P.proc h o out := by
  by_cases hs : (h, o.1) ∈ log.seen
  · simp [oracle, process, hs]
  · simp [oracle, process, hs]

/-- What replying to an onion does to the log and the answer. -/
theorem oracle_answer_run (h : Role) (msg : S.Msg) (o : S.Onion) (log : Log S) :
    (oracle procM replyM P (.inr (h, msg, o))).run log
      = if (h, o) ∈ log.held then
          (fun a => (P.reply h msg o a, ({ log with held := log.held.erase (h, o) } : Log S)))
            <$> replyM h msg o
        else pure (none, log) := by
  by_cases hs : (h, o) ∈ log.held
  · simp [oracle, answer, hs]
  · simp [oracle, answer, hs]

variable (hP : ∀ h o out, P.proc h o out =ᵈ D >>= fun g => (Pe g).proc h o out)
  (hH : ∀ g g' h o out, ¬ (h = Role.relay ∧ o.1 = H) →
    (Pe g).proc h o out = (Pe g').proc h o out)
  (hR : ∀ g, (Pe g).reply = P.reply)

include hP hR in
/-- One query to the relays with the patch that draws is a draw, then the query with the patch
that was given the draw. -/
theorem oracle_draw_query (t : (oracleSpec S).Domain) (log : Log S) :
    (oracle procM replyM P t).run log
      =ᵈ D >>= fun g => (oracle procM replyM (Pe g) t).run log := by
  rcases t with (u | ⟨h, o⟩) | ⟨h, msg, o⟩
  · have hu : ∀ g, (oracle procM replyM (Pe g) (.inl (.inl u))).run log
        = (oracle procM replyM P (.inl (.inl u))).run log := fun g => by simp [oracle]
    simp only [hu]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  · simp only [oracle_process_run]
    split_ifs
    · exact (OracleComp.EvalDistEq.bind_const _ _).symm
    · simp only [map_eq_bind_pure_comp]
      refine EvalDistEq.trans (EvalDistEq.bind_right _ fun out => (hP h o out).bind_left _) ?_
      simp only [bind_assoc]
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  · simp only [oracle_answer_run, hR]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm

include hH hR in
/-- Once the relay has seen the header, the draw is not used. -/
theorem oracle_draw_seen (g g' : X) {α : Type} (oa : OracleComp (oracleSpec S) α) (log : Log S)
    (hs : (Role.relay, H) ∈ log.seen) :
    (simulateQ (oracle procM replyM (Pe g)) oa).run log
      = (simulateQ (oracle procM replyM (Pe g')) oa).run log := by
  have h := map_run_simulateQ_eq_of_query_map_eq_inv' (oracle procM replyM (Pe g))
    (oracle procM replyM (Pe g')) (fun s : Log S => (Role.relay, H) ∈ s.seen) id
    (fun t s hs y hy => by
      rcases t with (u | ⟨h, o⟩) | ⟨h, msg, o⟩
      · simp [oracle] at hy
        obtain ⟨_, rfl⟩ := hy
        exact hs
      · rw [oracle_process_run] at hy
        split_ifs at hy
        · simp at hy
          subst hy
          exact hs
        · simp at hy
          obtain ⟨_, -, _, -, rfl⟩ := hy
          exact List.mem_cons_of_mem _ hs
      · rw [oracle_answer_run] at hy
        split_ifs at hy
        · simp at hy
          obtain ⟨_, -, rfl⟩ := hy
          exact hs
        · simp at hy
          subst hy
          exact hs)
    (fun t s hs => by
      rcases t with (u | ⟨h, o⟩) | ⟨h, msg, o⟩
      · simp [oracle]
      · rw [oracle_process_run, oracle_process_run]
        by_cases hseen : (h, o.1) ∈ s.seen
        · simp [hseen]
        · have hne : ¬ (h = Role.relay ∧ o.1 = H) := fun hc => hseen (by rw [hc.1, hc.2]; exact hs)
          simp [hseen, hH g g' h o _ hne]
      · rw [oracle_answer_run, oracle_answer_run, hR g, hR g']
        simp)
    oa log hs
  simpa using h

include hP hH hR in
/-- **A patch that draws under one header may draw first.** If the patch `P` answers as
`Pe g` does for a fresh draw `g`, and `Pe g` uses `g` only at `.relay` under the header `H`,
then the game with `P` is the game that draws `g` first and plays with `Pe g`. -/
theorem oracle_draw {α : Type} (oa : OracleComp (oracleSpec S) α) (log : Log S) :
    (simulateQ (oracle procM replyM P) oa).run log
      =ᵈ D >>= fun g => (simulateQ (oracle procM replyM (Pe g)) oa).run log := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun p => ih p.1 p.2) ?_
    refine EvalDistEq.trans ((oracle_draw_query D P Pe procM replyM hP hR t log).bind_left _) ?_
    simp only [bind_assoc]
    by_cases hc : ∃ o : S.Onion, t = .inl (.inr (Role.relay, o)) ∧ o.1 = H
        ∧ (Role.relay, o.1) ∉ log.seen
    · obtain ⟨o, rfl, ho, hseen⟩ := hc
      refine EvalDistEq.bind_right _ fun g => ?_
      simp only [oracle_process_run, hseen, ↓reduceIte, bind_assoc, bind_map_left]
      refine EvalDistEq.bind_right _ fun out => EvalDistEq.bind_right _ fun a => ?_
      have hs : (Role.relay, H) ∈ (Role.relay, o.1) :: log.seen := by
        rw [ho]
        exact List.mem_cons_self
      refine EvalDistEq.trans (EvalDistEq.bind_right _ fun g' => ?_)
        (OracleComp.EvalDistEq.bind_const D _)
      rw [oracle_draw_seen H P Pe procM replyM hH hR g' g (k a)
        ⟨(Role.relay, o.1) :: log.seen, (Role.relay, o) :: log.held⟩ hs]
    · have hind : ∀ g g', (oracle procM replyM (Pe g) t).run log
          = (oracle procM replyM (Pe g') t).run log := fun g g' => by
        rcases t with (u | ⟨h, o⟩) | ⟨h, msg, o⟩
        · simp [oracle]
        · rw [oracle_process_run, oracle_process_run]
          by_cases hseen : (h, o.1) ∈ log.seen
          · simp [hseen]
          · have hne : ¬ (h = Role.relay ∧ o.1 = H) := fun hx =>
              hc ⟨o, by rw [hx.1], hx.2, by rw [← hx.1]; exact hseen⟩
            simp [hseen, hH g g' h o _ hne]
        · rw [oracle_answer_run, oracle_answer_run, hR g, hR g']
      refine EvalDistEq.trans (EvalDistEq.bind_right _ fun g =>
        (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans
          (EvalDistEq.bind_right _ fun g' => by rw [hind g g'])) ?_
      exact OracleComp.EvalDistEq.bind_const _ _

end Draw

/-- **A patch that does not draw is part of the relays' answers.** Relays with pure answers
and a patch that maps them to pure answers are relays with the patched answers and no patch. -/
theorem oracle_pure_patch (P : Patch S)
    (proc proc' : Role → S.Onion → Option S.Step)
    (reply reply' : Role → S.Msg → S.Onion → Option (S.Name × S.Onion))
    (hp : ∀ h o, P.proc h o (proc h o) = pure (proc' h o))
    (hr : ∀ h m o, P.reply h m o (reply h m o) = reply' h m o) :
    oracle (m := ProbComp) (fun h o => pure (proc h o)) (fun h m o => pure (reply h m o)) P
      = oracle (fun h o => pure (proc' h o)) (fun h m o => pure (reply' h m o)) {} := by
  funext t
  rcases t with (u | ⟨h, o⟩) | ⟨h, msg, o⟩
  · simp [oracle]
  · refine StateT.ext fun log => ?_
    rw [oracle_process_run, oracle_process_run]
    simp [hp]
  · refine StateT.ext fun log => ?_
    rw [oracle_answer_run, oracle_answer_run]
    simp [hr]

namespace ForwardChallenge

variable {hon : Honest S} (c : ForwardChallenge hon)

/-- `patchWith` with the random payload `g` given: what the honest relay answers in the second
world of TLU→ when the payload it draws for a changed onion is `g`. -/
def patchDrawn (next : S.Onion) (r : S.Randomness) (mine : S.Onion) (g : S.Payload) : Patch S where
  proc h o out := pure <|
    if h = .relay ∧ o.1 = mine.1 then
      if hn : c.pos + 1 < c.req.fwd.hops.length then
        some (.forward c.req.fwd.hops[c.pos.val + 1].name
          (if o.2 = mine.2 then next else (next.1, g)))
      else out.map fun _ => .deliver c.req.msg c.req.receiver
    else out
  reply := (c.patchWith next r mine).reply

/-- **The second world of TLU→ may draw its random payload first.** The relay answers the
replacement's header once, so the payload it draws for a changed onion can be drawn before the
game. -/
theorem patchWith_draw (next : S.Onion) (r : S.Randomness) (mine : S.Onion)
    (procM : Role → S.Onion → ProbComp (Option S.Step))
    (replyM : Role → S.Msg → S.Onion → ProbComp (Option (S.Name × S.Onion)))
    {α : Type} (oa : OracleComp (oracleSpec S) α) (log : Log S) :
    (simulateQ (oracle procM replyM (c.patchWith next r mine)) oa).run log
      =ᵈ $ᵗ S.Payload >>= fun g =>
        (simulateQ (oracle procM replyM (c.patchDrawn next r mine g)) oa).run log := by
  refine oracle_draw mine.1 ($ᵗ S.Payload) (c.patchWith next r mine)
    (c.patchDrawn next r mine) procM replyM (fun h o out => ?_)
    (fun g g' h o out hne => ?_) (fun _ => rfl) oa log
  · unfold patchWith patchDrawn
    dsimp only
    by_cases hc : h = Role.relay ∧ o.1 = mine.1
    · rw [ite_eq_left hc]
      simp only [hc, and_self, ↓reduceIte]
      split_ifs with hn ho
      · exact (OracleComp.EvalDistEq.bind_const _ _).symm
      · simp only [bind_pure_comp]
        exact EvalDistEq.rfl
      · exact (OracleComp.EvalDistEq.bind_const _ _).symm
    · rw [ite_eq_right hc]
      simp only [hc, ↓reduceIte]
      exact (OracleComp.EvalDistEq.bind_const _ _).symm
  · unfold patchDrawn
    dsimp only
    rw [ite_eq_right hne, ite_eq_right hne]

end ForwardChallenge

end Cryptlib.Protocols.RSOR
