/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxKeyed
import Cryptlib.Primitives.MAC.Forge
import Cryptlib.Protocols.Sphinx.KEMSphinxTagGame

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Protocols.Sphinx.NIKESphinx (HopKeys deriveHopKeys)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.KEM.KEM (KEM)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Key keygen)
open Cryptlib.Util.Bytes (ofVector)

/-! # The MAC step for a node with uniform keys

After `keyedIdeal_sub_onlyHeader_le` the node answers the challenge ciphertext under one header
only, at the cost of the chance that the adversary sends a packet with the challenge ciphertext
and another header which the node accepts. `keyedBadH_le_forge` bounds that chance by the
forgery game for the MAC, for any game whose view uses the node's MAC key for one tag: the tag
of the bytes of the challenge header in front of it. The forgery adversary builds the view from
that tag, runs the node under the "MAC" that returns it, and hands over every packet the node
was sent. -/

section KeyedMac

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- A hop's keys other than its MAC key: the payload key, the IV and the header key. -/
abbrev RestKeys := Vector UInt8 48 × Vector UInt8 16 × Vector UInt8 32

/-- A hop's keys from its MAC key and the others. -/
def withMAC (r : RestKeys) (km : Vector UInt8 32) : KeyTuple := (r.1, r.2.1, km, r.2.2)

/-- A hop's keys other than its MAC key. -/
def restOf (u : KeyTuple) : RestKeys := (u.1, u.2.1, u.2.2.2)

variable {kem} {V R : Type} {S : KeyedSetup kem V R} (A : KeyedAdversary S)

/-- A header: the bytes `M` the node's MAC covers, then their tag. -/
def tagged (M : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → RestKeys → ByteArray)
    {pk : Key kem} (ch : S.Ch pk) (o : S.Oth) (c : kem.Ciphertext) (u : KeyTuple) : ByteArray :=
  M ch o c (restOf u) ++ ofVector (macS.mac (ofVector u.2.2.1) (M ch o c (restOf u)))

/-- The draws of a keyed game before the node's keys are used. -/
structure KeyedDraw where
  k : Key kem × kem.PrivateKey
  cs : S.Ch k.1 × A.St
  s : Vector UInt8 32
  o : S.Oth

/-- The challenge ciphertext of a draw. -/
def KeyedDraw.c {A : KeyedAdversary S} (d : KeyedDraw A) : kem.Ciphertext :=
  (encapOf kem d.k.1.1 d.s).1

def keyedDraw : ProbComp (KeyedDraw A) := do
  let k ← keygen kem
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom k.2) (A.pre k.1)
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  return ⟨k, cs, s, o⟩

/-- What a packet the node was sent offers as a forgery: the bytes its MAC covers, and its
tag. -/
def attempt : procSpec.Domain → Option (ByteArray × Vector UInt8 macS.tagSize)
  | .inl _ => none
  | .inr pkt => some (pkt.extract 0 (2 + kem.ciphertextSize + geom.routingInfoLength),
      Util.Bytes.toVecN macS.tagSize (pkt.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
        (payloadOffset kem geom)))

/-- The run of a keyed game's second phase with a record of the node's queries, for a handler,
a final map and a view. -/
def loggedRun (d : KeyedDraw A) (hand : ByteArray → ProcResult) (fin : R → Bool) (v : V) :
    ProbComp (Bool × List procSpec.Domain) :=
  (simulateQ (Util.UntilBad.logged (procImplF kem cipher macS kdfS streamS geom d.k.2 d.c hand))
    (fin <$> A.post d.cs.2 v)).run []

/-- The forgery adversary: it asks for the tag of the bytes of the challenge header, builds the
view from it, runs the node under the "MAC" that returns it, and offers every packet the node
was sent. -/
def forgeAdv (M : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → RestKeys → ByteArray)
    (viewT : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → RestKeys
      → Vector UInt8 macS.tagSize → V) : Primitives.MAC.ForgeAdversary macS where
  St := RestKeys × KeyedDraw A
  choose := do
    let r ← $ᵗ RestKeys
    let d ← keyedDraw cipher macS kdfS streamS geom A
    return (M d.cs.1 d.o d.c r, r, d)
  forge st tag := do
    let z ← loggedRun cipher macS kdfS streamS geom A st.2
      (fun pkt => if pkt.extract 0 (payloadOffset kem geom)
          = M st.2.cs.1 st.2.o st.2.c st.1 ++ ofVector tag
        then procKeys kem cipher (MAC.const tag) streamS geom (withMAC st.1 default) pkt
        else none)
      (S.final st.2.cs.1 st.2.o st.2.c (withMAC st.1 default))
      (viewT st.2.cs.1 st.2.o st.2.c st.1 tag)
    return z.2.filterMap (attempt (kem := kem) macS geom)

/-- The draws of a keyed game with uniform keys: the node's MAC key, its other keys, and the
rest. -/
def macDraw : ProbComp (Vector UInt8 32 × RestKeys × KeyedDraw A) := do
  let km ← $ᵗ (Vector UInt8 32)
  let r ← $ᵗ RestKeys
  let d ← keyedDraw cipher macS kdfS streamS geom A
  return (km, r, d)

/-- The second phase of `keyedBadH` after its draws: the run with a record of the node's
queries, and whether one was a bad packet carrying the challenge ciphertext. -/
def badRun
    (hand : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → KeyTuple
      → ByteArray → ProcResult)
    (bad : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → KeyTuple → ByteArray → Bool)
    (x : Vector UInt8 32 × RestKeys × KeyedDraw A) : ProbComp Bool := do
  let z ← loggedRun cipher macS kdfS streamS geom A x.2.2
    (hand x.2.2.cs.1 x.2.2.o x.2.2.c (withMAC x.2.1 x.1))
    (S.final x.2.2.cs.1 x.2.2.o x.2.2.c (withMAC x.2.1 x.1))
    (S.view x.2.2.cs.1 x.2.2.o x.2.2.c (withMAC x.2.1 x.1))
  return z.2.any (badQuery kem x.2.2.c (bad x.2.2.cs.1 x.2.2.o x.2.2.c (withMAC x.2.1 x.1)))

/-- `keyedBadH` as its draws, then the run with a record of the node's queries. -/
theorem keyedBadH_evalDistEq
    (hand : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → KeyTuple
      → ByteArray → ProcResult)
    (bad : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → KeyTuple → ByteArray → Bool) :
    keyedBadH cipher macS kdfS streamS geom A hand bad
      =ᵈ macDraw cipher macS kdfS streamS geom A >>= badRun cipher macS kdfS streamS geom A
          hand bad := by
  have hbij : Function.Bijective (Function.uncurry
      fun (km : Vector UInt8 32) (r : RestKeys) => withMAC r km) :=
    Function.bijective_iff_has_inverse.2
      ⟨fun u => (u.2.2.1, restOf u), fun ⟨_, _, _, _⟩ => rfl, fun ⟨_, _, _, _⟩ => rfl⟩
  unfold keyedBadH macDraw keyedDraw
  simp only [badRun, loggedRun, bind_assoc, pure_bind]
  exact (evalDistEq_pair_of_bijective hbij _).symm

/-- The forgery game of `forgeAdv` after its draws. -/
def forgeRun (M : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → RestKeys → ByteArray)
    (viewT : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → RestKeys
      → Vector UInt8 macS.tagSize → V)
    (x : Vector UInt8 32 × RestKeys × KeyedDraw A) : ProbComp Bool := do
  let z ← loggedRun cipher macS kdfS streamS geom A x.2.2
    (fun pkt => if pkt.extract 0 (payloadOffset kem geom)
        = M x.2.2.cs.1 x.2.2.o x.2.2.c x.2.1
          ++ ofVector (macS.mac (ofVector x.1) (M x.2.2.cs.1 x.2.2.o x.2.2.c x.2.1))
      then procKeys kem cipher
        (MAC.const (macS.mac (ofVector x.1) (M x.2.2.cs.1 x.2.2.o x.2.2.c x.2.1)))
        streamS geom (withMAC x.2.1 default) pkt
      else none)
    (S.final x.2.2.cs.1 x.2.2.o x.2.2.c (withMAC x.2.1 default))
    (viewT x.2.2.cs.1 x.2.2.o x.2.2.c x.2.1
      (macS.mac (ofVector x.1) (M x.2.2.cs.1 x.2.2.o x.2.2.c x.2.1)))
  return (z.2.filterMap (attempt (kem := kem) macS geom)).any fun a =>
    decide (a.1 ≠ M x.2.2.cs.1 x.2.2.o x.2.2.c x.2.1) && macS.mac (ofVector x.1) a.1 == a.2

/-- The forgery game of `forgeAdv` as the same draws, then its run. -/
theorem forgeExp_forgeAdv
    (M : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → RestKeys → ByteArray)
    (viewT : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → RestKeys
      → Vector UInt8 macS.tagSize → V) :
    Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom A M viewT)
      = macDraw cipher macS kdfS streamS geom A >>= forgeRun cipher macS kdfS streamS geom A M
          viewT := by
  unfold Primitives.MAC.forgeExp forgeAdv macDraw
  simp only [forgeRun, bind_assoc, pure_bind]
  rfl

set_option maxHeartbeats 1000000 in
/-- **A bad packet is a forgery.** The chance that the adversary sends a packet with the
challenge ciphertext and another header which the node accepts is at most the forgery
adversary's chance, and the chance of a draw that is not `good`. On a good draw the bytes the
MAC covers have the length of a header without its tag, and the view uses the node's MAC key for
their tag only. -/
theorem keyedBadH_le_forge (hmactag : macS.tagSize = macLength)
    (M : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → RestKeys → ByteArray)
    (viewT : {pk : Key kem} → S.Ch pk → S.Oth → kem.Ciphertext → RestKeys
      → Vector UInt8 macS.tagSize → V)
    (good : KeyedDraw A → Prop)
    (hM : ∀ (d : KeyedDraw A) (r : RestKeys), good d →
      (M d.cs.1 d.o d.c r).size = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hview : ∀ (d : KeyedDraw A) (u : KeyTuple), good d →
      S.view d.cs.1 d.o d.c u = viewT d.cs.1 d.o d.c (restOf u)
        (macS.mac (ofVector u.2.2.1) (M d.cs.1 d.o d.c (restOf u))))
    (hfin : ∀ {pk : Key kem} (ch : S.Ch pk) (o : S.Oth) (c : kem.Ciphertext) (u u' : KeyTuple),
      S.final ch o c u = S.final ch o c u') :
    Pr{let x ← (keyedBadH cipher macS kdfS streamS geom A
        (onlyHeader cipher macS streamS geom (tagged macS M))
        (otherHeader cipher macS streamS geom (tagged macS M)))}[x = true]
      ≤ Pr{let x ← (Primitives.MAC.forgeExp macS
          (forgeAdv cipher macS kdfS streamS geom A M viewT))}[x = true]
        + Pr{let d ← keyedDraw cipher macS kdfS streamS geom A}[¬ good d] := by
  have hbad : Pr{let x ← macDraw cipher macS kdfS streamS geom A}[¬ good x.2.2]
      = Pr{let d ← keyedDraw cipher macS kdfS streamS geom A}[¬ good d] := by
    have e : (fun x : Vector UInt8 32 × RestKeys × KeyedDraw A => x.2.2)
        <$> macDraw cipher macS kdfS streamS geom A
          =ᵈ keyedDraw cipher macS kdfS streamS geom A := by
      unfold macDraw
      simp only [map_bind, map_pure, bind_pure]
      exact (OracleComp.EvalDistEq.bind_const _ _).trans (OracleComp.EvalDistEq.bind_const _ _)
    exact (prEvent_map _ (fun x : Vector UInt8 32 × RestKeys × KeyedDraw A => x.2.2)
      (fun d => ¬ good d)).symm.trans (e.prEvent_eq _)
  rw [(keyedBadH_evalDistEq cipher macS kdfS streamS geom A _ _).prEvent_eq (fun x => x = true),
    forgeExp_forgeAdv, ← hbad]
  refine prEvent_bind_le_add_of_bad_le (macDraw cipher macS kdfS streamS geom A)
    (badRun cipher macS kdfS streamS geom A (onlyHeader cipher macS streamS geom (tagged macS M))
      (otherHeader cipher macS streamS geom (tagged macS M)))
    (forgeRun cipher macS kdfS streamS geom A M viewT) (fun x => ¬ good x.2.2) (fun x => x = true)
    fun x hx => ?_
  obtain ⟨km, r, d⟩ := x
  have hg : good d := not_not.mp hx
  have hMs := hM d r hg
  have e1 : S.view d.cs.1 d.o d.c (withMAC r km) = viewT d.cs.1 d.o d.c r
      (macS.mac (ofVector km) (M d.cs.1 d.o d.c r)) := hview d (withMAC r km) hg
  have e2 : S.final d.cs.1 d.o d.c (withMAC r km) = S.final d.cs.1 d.o d.c (withMAC r default) :=
    hfin _ _ _ _ _
  have e3 : onlyHeader cipher macS streamS geom (tagged macS M) d.cs.1 d.o d.c (withMAC r km)
      = fun pkt => if pkt.extract 0 (payloadOffset kem geom)
          = M d.cs.1 d.o d.c r ++ ofVector (macS.mac (ofVector km) (M d.cs.1 d.o d.c r))
        then procKeys kem cipher (MAC.const (macS.mac (ofVector km) (M d.cs.1 d.o d.c r)))
          streamS geom (withMAC r default) pkt
        else none := by
    funext pkt
    show (if pkt.extract 0 (payloadOffset kem geom)
        = M d.cs.1 d.o d.c r ++ ofVector (macS.mac (ofVector km) (M d.cs.1 d.o d.c r))
      then procKeys kem cipher macS streamS geom (withMAC r km) pkt else none) = _
    by_cases hh : pkt.extract 0 (payloadOffset kem geom)
        = M d.cs.1 d.o d.c r ++ ofVector (macS.mac (ofVector km) (M d.cs.1 d.o d.c r))
    · have hfull : (M d.cs.1 d.o d.c r
            ++ ofVector (macS.mac (ofVector km) (M d.cs.1 d.o d.c r))).extract 0
            (payloadOffset kem geom)
          = M d.cs.1 d.o d.c r ++ ofVector (macS.mac (ofVector km) (M d.cs.1 d.o d.c r)) := by
        have hsz : (M d.cs.1 d.o d.c r
            ++ ofVector (macS.mac (ofVector km) (M d.cs.1 d.o d.c r))).size
            = payloadOffset kem geom := by
          rw [ByteArray.size_append, hMs, Util.Bytes.size_ofVector, hmactag]
        rw [← hsz]
        exact ByteArray.extract_zero_size
      have hpre : pkt.extract 0 (2 + kem.ciphertextSize + geom.routingInfoLength) = M d.cs.1
          d.o d.c r := by
        rw [extract_of_prefix_eq (hh.trans hfull.symm) 0 (2 + kem.ciphertextSize +
            geom.routingInfoLength)
          (by unfold payloadOffset; omega), ← hMs]
        exact Util.Bytes.extract_append_left _ _
      simp only [hh, ↓reduceIte]
      rw [procKeys_const kem cipher macS streamS geom (withMAC r km) (withMAC r default) pkt rfl
        rfl rfl, hpre]
      rfl
    · simp only [hh, ↓reduceIte]
  unfold badRun forgeRun
  dsimp only
  rw [e1, e2, e3]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun z => prEvent_pure_bool_mono _ _ fun hany => ?_
  rw [List.any_eq_true] at hany ⊢
  obtain ⟨t, ht, hb⟩ := hany
  cases t with
  | inl t => simp [badQuery] at hb
  | inr pkt =>
    simp only [badQuery, otherHeader, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨-, hne, hsome⟩ := hb
    obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hpm, htag⟩ := procKeys_forgery kem cipher macS streamS geom (withMAC r km) pkt
      (M d.cs.1 d.o d.c r) res hres hne
    refine ⟨_, List.mem_filterMap.2 ⟨.inr pkt, ht, rfl⟩, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨hpm, htag⟩

end KeyedMac

end Cryptlib.Protocols.Sphinx.KEMSphinx
