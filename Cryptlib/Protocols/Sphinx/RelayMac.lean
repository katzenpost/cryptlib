/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxKeyedMac

namespace Cryptlib.Protocols.Sphinx.Relay

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Common (toVecN)
open Cryptlib.Protocols.Sphinx.KEMSphinx (ProcResult procSpec relayImpl
  prEvent_bind_le_add_of_bad_le prEvent_pure_bool_mono)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Util.Bytes (ofVector)

/-! # The MAC step for a relay, whatever the packet format

A relay answers some packets, the challenge packets, with keys the game holds. If it accepts
such a packet only when the tag over the packet's first `off` bytes verifies under its MAC key,
then it may answer the challenge packets under one header only, the header `M` with its tag, at
the cost of a forgery against the MAC. The relay's format enters through two facts: what it
accepts verifies, and under the challenge header it uses the MAC key for that header's tag
only. The game's view may use the MAC key for the challenge header's tag only (`hview`), off
a set of draws that is paid for. -/

section Mac

variable {X V : Type} (macS : MAC) (mx : ProbComp X) (off : ℕ) (M : X → ByteArray)
  (chal : X → ByteArray → Bool) (own : X → ByteArray → ProcResult)
  (procK : X → Vector UInt8 32 → ByteArray → ProcResult)
  (procT : X → Vector UInt8 macS.tagSize → ByteArray → ProcResult)
  (view : X → Vector UInt8 32 → V) (viewT : X → Vector UInt8 macS.tagSize → V)
  (run : X → V → OracleComp procSpec Bool)

/-- The relay's answers: `hand` for a challenge packet, its own otherwise. -/
def ansOf (x : X) (hand : ByteArray → ProcResult) (pkt : ByteArray) : ProcResult :=
  if chal x pkt = true then hand pkt else own x pkt

/-- Answers to challenge packets under the header `M x` with the tag `tag` only. -/
def onlyT (x : X) (tag : Vector UInt8 macS.tagSize) (pkt : ByteArray) : ProcResult :=
  if pkt.extract 0 (off + macS.tagSize) = M x ++ ofVector tag then procT x tag pkt else none

/-- The game with the relay answering every challenge packet with its keys. -/
def gameAll : ProbComp Bool := do
  let km ← $ᵗ (Vector UInt8 32)
  let x ← mx
  simulateQ (relayImpl (ansOf chal own x (procK x km)))
    (run x (view x km))

/-- The game with the relay answering challenge packets under the challenge header only. -/
def gameOnly : ProbComp Bool := do
  let km ← $ᵗ (Vector UInt8 32)
  let x ← mx
  simulateQ (relayImpl (ansOf chal own x (onlyT macS off M procT x (macS.mac (ofVector km) (M x)))))
    (run x (view x km))

/-- What a packet the relay was sent offers as a forgery: the bytes its MAC covers, and its
tag. -/
def attempt : procSpec.Domain → Option (ByteArray × Vector UInt8 macS.tagSize)
  | .inl _ => none
  | .inr pkt => some (pkt.extract 0 off,
      Util.Bytes.toVecN macS.tagSize (pkt.extract off (off + macS.tagSize)))

/-- The forgery adversary: it asks for the tag of the challenge header, runs the game from it,
and offers every packet the relay was sent. -/
def forgeAdv : Primitives.MAC.ForgeAdversary macS where
  St := X
  choose := do
    let x ← mx
    return (M x, x)
  forge x tag := do
    let z ← (simulateQ (Util.UntilBad.logged
        (relayImpl (ansOf chal own x (onlyT macS off M procT x tag))))
      (run x (viewT x tag))).run []
    return z.2.filterMap (attempt macS off)

/-- A challenge packet with another header that the relay accepts. -/
def isBad (x : X) (km : Vector UInt8 32) : procSpec.Domain → Bool
  | .inl _ => false
  | .inr pkt => chal x pkt
      && decide (pkt.extract 0 (off + macS.tagSize)
        ≠ M x ++ ofVector (macS.mac (ofVector km) (M x)))
      && (procK x km pkt).isSome

/-- **The MAC step.** -/
theorem gameAll_sub_gameOnly_le (good : X → Prop)
    (hview : ∀ x km, good x → view x km = viewT x (macS.mac (ofVector km) (M x)))
    (hconst : ∀ x km pkt, pkt.extract 0 (off + macS.tagSize)
        = M x ++ ofVector (macS.mac (ofVector km) (M x)) →
      procK x km pkt = procT x (macS.mac (ofVector km) (M x)) pkt)
    (hforge : ∀ x km pkt, good x → (procK x km pkt).isSome = true →
      pkt.extract 0 (off + macS.tagSize) ≠ M x ++ ofVector (macS.mac (ofVector km) (M x)) →
      pkt.extract 0 off ≠ M x ∧ macS.mac (ofVector km) (pkt.extract 0 off)
        = Util.Bytes.toVecN macS.tagSize (pkt.extract off (off + macS.tagSize))) :
    |(Pr{let b ← gameAll mx chal own procK view run}[b = true]).toReal
      - (Pr{let b ← gameOnly macS mx off M chal own procT view run}[b = true]).toReal|
    ≤ (Pr{let b ← (Primitives.MAC.forgeExp macS
          (forgeAdv macS mx off M chal own procT viewT run))}[b = true]).toReal
      + (Pr{let x ← mx}[¬ good x]).toReal := by
  let badGame : ProbComp Bool := do
    let km ← $ᵗ (Vector UInt8 32)
    let x ← mx
    let z ← (simulateQ (Util.UntilBad.logged (relayImpl (ansOf chal own x
        (onlyT macS off M procT x (macS.mac (ofVector km) (M x))))))
      (run x (view x km))).run []
    return z.2.any (isBad macS off M chal procK x km)
  have hstep := fun (km : Vector UInt8 32) (x : X) =>
    Util.UntilBad.prEvent_le_add_bad (relayImpl (ansOf chal own x (procK x km)))
      (relayImpl (ansOf chal own x (onlyT macS off M procT x (macS.mac (ofVector km) (M x)))))
      (isBad macS off M chal procK x km) (fun t ht => by
        cases t with
        | inl t => rfl
        | inr pkt =>
          refine congrArg (pure : ProcResult → ProbComp ProcResult) ?_
          unfold ansOf onlyT
          by_cases hc : chal x pkt = true
          · simp only [hc, ↓reduceIte]
            by_cases hh : pkt.extract 0 (off + macS.tagSize)
                = M x ++ ofVector (macS.mac (ofVector km) (M x))
            · simp only [hh, ↓reduceIte]
              exact hconst x km pkt hh
            · simp only [hh, ↓reduceIte]
              simpa [isBad, hc, hh] using ht
          · simp only [hc]
            rfl)
      (run x (view x km)) (· = true)
  have h12 : Pr{let b ← gameAll mx chal own procK view run}[b = true]
      ≤ Pr{let b ← gameOnly macS mx off M chal own procT view run}[b = true]
        + Pr{let b ← badGame}[b = true] := by
    refine Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun km => ?_
    refine Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun x => ?_
    simpa only [bind_pure_comp, prEvent_map] using (hstep km x).1
  have h21 : Pr{let b ← gameOnly macS mx off M chal own procT view run}[b = true]
      ≤ Pr{let b ← gameAll mx chal own procK view run}[b = true]
        + Pr{let b ← badGame}[b = true] := by
    refine Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun km => ?_
    refine Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun x => ?_
    simpa only [bind_pure_comp, prEvent_map] using (hstep km x).2
  have hbad : Pr{let b ← badGame}[b = true]
      ≤ Pr{let b ← (Primitives.MAC.forgeExp macS
          (forgeAdv macS mx off M chal own procT viewT run))}[b = true]
        + Pr{let x ← mx}[¬ good x] := by
    have e : Pr{let x ← ($ᵗ (Vector UInt8 32) >>= fun _ => mx)}[¬ good x]
        = Pr{let x ← mx}[¬ good x] :=
      (OracleComp.EvalDistEq.bind_const _ _).prEvent_eq _
    rw [← e]
    unfold Primitives.MAC.forgeExp forgeAdv
    simp only [bind_assoc, pure_bind]
    refine Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun km => ?_
    refine prEvent_bind_le_add_of_bad_le mx _ _ (fun x => ¬ good x) (· = true) fun x hx => ?_
    have hg : good x := not_not.mp hx
    rw [hview x km hg]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z =>
      prEvent_pure_bool_mono _ _ fun hany => ?_
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨t, ht, hb⟩ := hany
    cases t with
    | inl t => simp [isBad] at hb
    | inr pkt =>
      simp only [isBad, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨-, hne⟩, hsome⟩ := hb
      obtain ⟨hpm, htag⟩ := hforge x km pkt hg hsome hne
      refine ⟨_, List.mem_filterMap.2 ⟨.inr pkt, ht, rfl⟩, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨hpm, htag⟩
  have rb := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) hbad
  have r12 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h12
  have r21 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h21
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at rb r12 r21
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

end Mac

/-! ## Answering some packets in front of a relay -/

/-- In front of a relay's oracle: the packets `chal` picks are answered by `f`, and the rest are
passed on. -/
def first (chal : ByteArray → Bool) (f : ByteArray → ProcResult) :
    QueryImpl procSpec (OracleComp procSpec) :=
  QueryImpl.add unifSpec.passthrough fun pkt =>
    if chal pkt = true then pure (f pkt)
    else (liftM ((ByteArray →ₒ ProcResult).query pkt) : OracleComp procSpec ProcResult)

/-- `first` in front of a relay with the answers `ans` is a relay with the answers `f` for the
packets `chal` picks, and `ans` for the rest. -/
theorem relayImpl_comp_first (ans : ByteArray → ProcResult) (chal : ByteArray → Bool)
    (f : ByteArray → ProcResult) :
    relayImpl ans ∘ₛ first chal f
      = relayImpl (fun pkt => if chal pkt = true then f pkt else ans pkt) := by
  funext t
  cases t with
  | inl t =>
    simp [first, relayImpl, QueryImpl.add_eq_hAdd]
    exact (QueryImpl.simulateQ_add_liftM_query_left (QueryImpl.id' unifSpec) _ t).trans (by simp)
  | inr pkt =>
    simp only [first, relayImpl, QueryImpl.apply_compose, QueryImpl.add_eq_hAdd,
      QueryImpl.add_apply_inr]
    split_ifs
    · simp
    · rw [QueryImpl.simulateQ_add_liftM_query_right]

end Cryptlib.Protocols.Sphinx.Relay
