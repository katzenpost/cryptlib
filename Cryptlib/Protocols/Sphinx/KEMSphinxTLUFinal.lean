/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTLUNext
import Cryptlib.Protocols.Sphinx.KEMSphinxPad

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

/-! # The last step of TLU→

Both worlds have been brought to games where the honest relay's keystreams are uniform. Here
they are compared. -/

section ForwardFinal

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

variable (names : Role → RSOR.Name)

/-! ## The hidden ciphertext -/

/-- The honest relay's own answer to a packet. -/
def ownAns (sk : kem.PrivateKey) (pkt : ByteArray) : ProcResult :=
  procWith kem cipher macS kdfS streamS geom (kemDecap kem (ofVector (kem.encodePrivateKey sk)))
    pkt

/-- Whether the adversary of world 1 sends the honest relay a packet with the ciphertext of
the original's layer at the relay, which it is never shown. -/
def nextHidden (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) : ProbComp Bool := do
  let U' ← $ᵗ (Keystream geom)
  let k ← keygen kem
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
    ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre k.1)
  let s' ← $ᵗ (Vector UInt8 32)
  let x ← nextDraw geom
  let z ← (simulateQ (Util.UntilBad.logged
      (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
        (ownAns kem cipher macS kdfS streamS geom k.2)))
    ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post cs.2
      (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names cs.1 x
        (ofVector U')))).run []
  return z.2.any (badQuery kem (encapOf kem k.1.1 s').1 fun _ => true)

/-- **The hidden ciphertext.** Rejecting the ciphertext of the original's layer at the relay
changes world 1 by at most the chance that the adversary sends it. -/
theorem next_hidden_le (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← (PRGScheme.prgIdealExperiment
          (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal
      - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (nextStreamAdvF kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            (ownAns kem cipher macS kdfS streamS geom) A))}[x = true]).toReal|
    ≤ (Pr{let b ← (nextHidden kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A)}[b = true]).toReal := by
  have hstep : ∀ (k : Key kem × kem.PrivateKey) (s' : Vector UInt8 32)
      (oa : OracleComp procSpec Bool),
      Pr{let x ← (simulateQ (procImplF kem cipher macS kdfS streamS geom k.2
          (encapOf kem k.1.1 s').1 (fun _ => none)) oa)}[x = true]
        ≤ Pr{let x ← (simulateQ (procImplF kem cipher macS kdfS streamS geom k.2
            (encapOf kem k.1.1 s').1 (ownAns kem cipher macS kdfS streamS geom k.2))
            oa)}[x = true]
          + Pr{let b ← (do
              let z ← (simulateQ (Util.UntilBad.logged
                (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
                  (ownAns kem cipher macS kdfS streamS geom k.2))) oa).run []
              return z.2.any (badQuery kem (encapOf kem k.1.1 s').1 fun _ => true))}[b = true]
      ∧ Pr{let x ← (simulateQ (procImplF kem cipher macS kdfS streamS geom k.2
            (encapOf kem k.1.1 s').1 (ownAns kem cipher macS kdfS streamS geom k.2))
            oa)}[x = true]
        ≤ Pr{let x ← (simulateQ (procImplF kem cipher macS kdfS streamS geom k.2
            (encapOf kem k.1.1 s').1 (fun _ => none)) oa)}[x = true]
          + Pr{let b ← (do
              let z ← (simulateQ (Util.UntilBad.logged
                (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
                  (ownAns kem cipher macS kdfS streamS geom k.2))) oa).run []
              return z.2.any (badQuery kem (encapOf kem k.1.1 s').1 fun _ => true))}[b = true] :=
    fun k s' oa => by
      have h := procImplF_le_add_bad kem cipher macS kdfS streamS geom k.2
        (encapOf kem k.1.1 s').1 (fun _ => none) (ownAns kem cipher macS kdfS streamS geom k.2)
        (fun _ => true) (fun _ _ hb => by cases hb) oa (· = true)
      simpa only [bind_pure_comp, prEvent_map, Function.comp_def] using h
  have h12 : Pr{let x ← (PRGScheme.prgIdealExperiment
        (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]
      ≤ Pr{let x ← (PRGScheme.prgIdealExperiment
          (nextStreamAdvF kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            (ownAns kem cipher macS kdfS streamS geom) A))}[x = true]
        + Pr{let b ← (nextHidden kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A)}[b = true] :=
    Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun U' =>
      Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun k =>
        Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun cs =>
          Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun s' =>
            Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun x => (hstep k s' _).1
  have h21 : Pr{let x ← (PRGScheme.prgIdealExperiment
        (nextStreamAdvF kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          (ownAns kem cipher macS kdfS streamS geom) A))}[x = true]
      ≤ Pr{let x ← (PRGScheme.prgIdealExperiment
          (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]
        + Pr{let b ← (nextHidden kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A)}[b = true] :=
    Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun U' =>
      Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun k =>
        Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun cs =>
          Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun s' =>
            Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun x => (hstep k s' _).2
  have r12 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h12
  have r21 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h21
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at r12 r21
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-! ## World 1 as a relay that answers one header -/

/-- With its own answers for the ciphertext `c`, the keyed oracle is the honest node's. -/
theorem procImplF_ownAns (sk : kem.PrivateKey) (c : kem.Ciphertext) :
    procImplF kem cipher macS kdfS streamS geom sk c (ownAns kem cipher macS kdfS streamS geom sk)
      = procImpl kem cipher macS kdfS streamS geom sk := by
  rw [procImplF_eq_relayImpl]
  have h : relayAns kem cipher macS kdfS streamS geom sk c
      (ownAns kem cipher macS kdfS streamS geom sk)
      = ownAns kem cipher macS kdfS streamS geom sk := by
    funext pkt
    unfold relayAns ownAns
    split_ifs <;> rfl
  rw [h]
  rfl

set_option maxHeartbeats 1000000 in
/-- **World 1 after its draws, as a relay that answers one header.** With the honest relay's
own answers for the hidden ciphertext, the second phase of world 1 is the game where the relay
answers the replacement's ciphertext under the replacement's header only, from its MAC key, its
uniform keystream and the ideal payload cipher. -/
theorem nextOwn_run (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (s' : Vector UInt8 32) (x : NextOth geom) (U' : ByteArray)
    (hsz : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
      (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength) :
    simulateQ (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
        (ownAns kem cipher macS kdfS streamS geom k.2))
      ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post st
        (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x U'))
    = (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16
          (fun h => if h = .relay then k.2 else st.2.2 h) (encapOf kem k.1.1 x.2.2.1).1 x.2.1
          (ofVector x.1)
          (Util.Bytes.toVecN _
            (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)
              ++ ofVector (macS.mac (ofVector x.2.1)
                (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                  (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)))))
          (fun y => if y = x.2.2.2.2.1 then
              shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                (ofVector x.1)
            else x.2.2.2.2.2)
          (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x U').1.patch)
        (A.guess st.1 (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x
          U').1.onion)).run' st.2.1 := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  obtain ⟨U, km, s, o, u, v⟩ := x
  obtain ⟨W, hW⟩ : ∃ W,
      W = nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
        (U, km, s, o, u, v) U' := ⟨_, rfl⟩
  rw [procImplF_ownAns, ← hW]
  show simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
    (simulateQ (relayFirst kem W.2.1 W.2.2)
      ((simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 st.2.2 W.1.patch)
        (A.guess st.1 W.1.onion)).run' st.2.1)) = _
  have hcomp : procImpl kem cipher macS kdfS streamS geom k.2 ∘ₛ relayFirst kem W.2.1 W.2.2
      = relayImpl (relayAns kem cipher macS kdfS streamS geom k.2 W.2.1 W.2.2) :=
    relayImpl_comp_relayFirst kem _ W.2.1 W.2.2
  rw [← QueryImpl.simulateQ_compose, hcomp]
  obtain ⟨Hv, hHv⟩ : ∃ Hv : Vector UInt8 geom.headerLength, Hv = Util.Bytes.toVecN _
      (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)
        ++ ofVector (macS.mac (ofVector km)
          (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)))) := ⟨_, rfl⟩
  have hsize : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)
      ++ ofVector (macS.mac (ofVector km)
        (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)))).size = geom.headerLength := by
    rw [ByteArray.size_append, hsz, Cryptlib.Util.Bytes.size_ofVector, hmactag, hhdr]
    rfl
  have hcar : ∀ pkt : ByteArray, pkt.extract 0 (payloadOffset kem geom) = ofVector Hv
      → carries kem (encapOf kem k.1.1 s).1 pkt = true := by
    intro pkt hp
    refine carries_of_extract kem _ pkt ?_
    have h' := congrArg (fun x : ByteArray => x.extract 2 (2 + kem.ciphertextSize)) hp
    simp only [ByteArray.extract_extract] at h'
    rw [Nat.zero_add, Nat.zero_add, Nat.min_eq_left (by unfold payloadOffset; omega)] at h'
    rw [h', hHv, Cryptlib.Util.Bytes.ofVector_toVecN _ hsize,
      Cryptlib.Util.Bytes.extract_append_of_le _ _ (by rw [hsz]; omega)]
    exact relayFrontAt_ct kem cipher macS kdfS streamS geom _ _ _ _ _ _
      (Cryptlib.Util.Bytes.size_ofVector _) hsz
  obtain ⟨skf, hskf⟩ : ∃ skf : Role → kem.PrivateKey,
      skf = fun h => if h = .relay then k.2 else st.2.2 h := ⟨_, rfl⟩
  have hrel' : skf .relay = k.2 := by rw [hskf]; simp
  have hsk : ∀ h, h ≠ Role.relay → st.2.2 h = skf h := fun h hr => by rw [hskf]; simp [hr]
  obtain ⟨Dd, hDd⟩ : ∃ Dd : Block geom → Block geom, Dd = (fun y => if y = u then
          shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o (ofVector U)
        else v) := ⟨_, rfl⟩
  have hW1 : W.2.1 = (encapOf kem k.1.1 s).1 := by rw [hW]; rfl
  have hW2 : W.2.2 = headerHand kem macS geom km (ofVector U) Hv Dd := by
    rw [hW, hHv, hDd]
    rfl
  rw [viaOracle_congr kem cipher macS kdfS streamS geom hvalid hmactag h16 st.2.2 skf hsk, hW1, hW2]
  simp only [StateT.run'_eq, simulateQ_map]
  have hf : ∀ o' : RSOR.Onion geom,
      relayAns kem cipher macS kdfS streamS geom (skf .relay) (encapOf kem k.1.1 s).1
          (headerHand kem macS geom km (ofVector U) Hv Dd) (RSOR.join o')
        = if o'.1 = Hv then procKeysD kem macS geom km (ofVector U)
            (ofVector (Dd o'.2)) (RSOR.join o')
          else relayAns kem cipher macS kdfS streamS geom (skf .relay)
            (encapOf kem k.1.1 s).1 (fun _ => none) (RSOR.join o') := fun o' => by
    rw [hrel']
    exact relayAns_headerHand kem cipher macS kdfS streamS geom hvalid k.2 _ km (ofVector U) Hv Dd
      hcar o'
  have hvo := viaOracle_header kem cipher macS kdfS streamS geom hvalid hmactag h16 skf
    (encapOf kem k.1.1 s).1 (headerHand kem macS geom km (ofVector U) Hv Dd) km (ofVector U)
    Hv Dd hf W.1.patch (A.guess st.1 W.1.onion) st.2.1
  rw [hrel'] at hvo
  rw [hvo]
  rw [hskf, hDd, hHv]

/-! ## World 1 with its random payload drawn first -/

/-- **World 1's relay may draw its random payload first.** The game where the relay answers
one header and the challenger patches its answers as in world 1 is the game that draws the
random payload `g` first and patches with it. -/
theorem headerRelays_patchWith_draw {pk kb ks : Key kem} (names : Role → RSOR.Name)
    (c : Protocols.RSOR.ForwardChallenge (S := 𝒮)
      (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk kb ks))
    (next : RSOR.Onion geom) (r : RSOR.Randomness geom) (mine : RSOR.Onion geom)
    (sk : Role → kem.PrivateKey) (ct : kem.Ciphertext) (km : Vector UInt8 32) (U : ByteArray)
    (Hv : Vector UInt8 geom.headerLength) (D : Block geom → Block geom)
    {α : Type} (oa : OracleComp (Protocols.RSOR.oracleSpec 𝒮) α)
    (log : Protocols.RSOR.Log 𝒮) :
    (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U Hv D
        (c.patchWith next r mine)) oa).run' log
      =ᵈ $ᵗ (Block geom) >>= fun g =>
        (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U Hv
          D
          (c.patchDrawn next r mine g)) oa).run' log := by
  have h := c.patchWith_draw next r mine
    (fun (h : Role) (o : RSOR.Onion geom) => pure (if h = Role.relay ∧ o.1 = Hv then
        RSOR.stepOf geom (procKeysD kem macS geom km U (ofVector (D o.2)) (RSOR.join o))
      else if h = .relay then
        RSOR.stepOf geom
          (relayAns kem cipher macS kdfS streamS geom (sk .relay) ct (fun _ => none) (RSOR.join o))
      else RSOR.proc kem cipher macS kdfS streamS geom (sk h) o))
    (fun (h : Role) (msg : RSOR.Msg geom) (o : RSOR.Onion geom) =>
      pure (if h = Role.relay ∧ o.1 = Hv then
        RSOR.replyOf cipher geom msg
          (procKeysD kem macS geom km U (ofVector (D o.2)) (RSOR.join o))
      else if h = .relay then
        RSOR.replyOf cipher geom msg
          (relayAns kem cipher macS kdfS streamS geom (sk .relay) ct (fun _ => none) (RSOR.join o))
      else RSOR.reply kem cipher macS kdfS streamS geom (sk h) msg o))
    oa log
  have h2 := h.map Prod.fst
  rw [map_bind] at h2
  exact h2

/-! ## Two relays that answer one header alike -/

/-- **A patched relay that answers one header is an unpatched one.** If the patch changes
answers under the header `Hv` at `.relay` only, and there takes the answers from the keystream
`U₁` and the decryption `D₁` to the answers from `U₀` and `D₀`, the two games are the same. -/
theorem headerRelays_patch_eq (sk : Role → kem.PrivateKey) (ct : kem.Ciphertext)
    (km : Vector UInt8 32) (U₀ U₁ : ByteArray) (Hv : Vector UInt8 geom.headerLength)
    (D₀ D₁ : Block geom → Block geom) (patch : Protocols.RSOR.Patch 𝒮)
    (hstep : ∀ o : RSOR.Onion geom, o.1 = Hv →
      patch.proc .relay o (RSOR.stepOf geom
          (procKeysD kem macS geom km U₁ (ofVector (D₁ o.2)) (RSOR.join o)))
        = pure (RSOR.stepOf geom
          (procKeysD kem macS geom km U₀ (ofVector (D₀ o.2)) (RSOR.join o))))
    (hrep : ∀ (m : RSOR.Msg geom) (o : RSOR.Onion geom), o.1 = Hv →
      patch.reply .relay m o (RSOR.replyOf cipher geom m
          (procKeysD kem macS geom km U₁ (ofVector (D₁ o.2)) (RSOR.join o)))
        = RSOR.replyOf cipher geom m
          (procKeysD kem macS geom km U₀ (ofVector (D₀ o.2)) (RSOR.join o)))
    (hproc : ∀ (h : Role) (o : RSOR.Onion geom) out, ¬ (h = .relay ∧ o.1 = Hv) →
      patch.proc h o out = pure out)
    (hreply : ∀ (h : Role) (m : RSOR.Msg geom) (o : RSOR.Onion geom) out,
      ¬ (h = .relay ∧ o.1 = Hv) → patch.reply h m o out = out) :
    headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U₁ Hv D₁ patch
      = headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U₀ Hv D₀ {} := by
  refine Protocols.RSOR.oracle_pure_patch (S := 𝒮) patch _ _ _ _ (fun h o => ?_)
    (fun h m o => ?_)
  · by_cases hc : h = Role.relay ∧ o.1 = Hv
    · obtain ⟨rfl, ho⟩ := hc
      exact (congrArg (patch.proc Role.relay o) (ite_eq_left ⟨rfl, ho⟩)).trans
        ((hstep o ho).trans (congrArg pure (ite_eq_left ⟨rfl, ho⟩).symm))
    · exact (congrArg (patch.proc h o) (ite_eq_right hc)).trans
        ((hproc h o _ hc).trans (congrArg pure (ite_eq_right hc).symm))
  · by_cases hc : h = Role.relay ∧ o.1 = Hv
    · obtain ⟨rfl, ho⟩ := hc
      exact (congrArg (patch.reply Role.relay m o) (ite_eq_left ⟨rfl, ho⟩)).trans
        ((hrep m o ho).trans (ite_eq_left ⟨rfl, ho⟩).symm)
    · exact (congrArg (patch.reply h m o) (ite_eq_right hc)).trans
        ((hreply h m o _ hc).trans (ite_eq_right hc).symm)

/-! ## The truncated path and the mixed randomness -/

namespace RSOR

omit hvalid hmactag h16 in
/-- A hop before the last of a truncated route is the same hop of the route. -/
theorem path_take_getElem! (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last last' : List RoutingCommand) (k i : ℕ) (hi : i + 1 < k) (hk : k ≤ R.hops.length) :
    (path kem (R.take k) last)[i]! = (path kem R last')[i]! := by
  have hl : (R.take k).hops.length = k := by simp [Protocols.RSOR.Route.take]; omega
  rw [path_getElem! kem _ _ _ (by omega), path_getElem! kem _ _ _ (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega)]
  simp [Protocols.RSOR.Route.take]

omit hvalid hmactag h16 in
/-- The last hop of a truncated route has that hop's name and key, and the last commands. -/
theorem path_take_last (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last : List RoutingCommand) (j : ℕ) (hj : j < R.hops.length) :
    (path kem (R.take (j + 1)) last)[j]!
      = ⟨R.hops[j].name, ofVector (kem.encodePublicKey R.hops[j].key.1), last⟩ := by
  have hl : (R.take (j + 1)).hops.length = j + 1 := by simp [Protocols.RSOR.Route.take]; omega
  rw [path_getElem! kem _ _ _ (by omega), ite_eq_left (by omega)]
  simp [Protocols.RSOR.Route.take]

/-- The original's randomness with the seeds of the first `j` forward hops taken from the
replacement's. -/
def mixSeeds (r r' : Randomness geom) (j : ℕ) : Randomness geom :=
  ((Vector.ofFn fun i : Fin geom.nrHops =>
      if i.val < j then r'.1.1[i.val]'i.isLt else r.1.1[i.val]'i.isLt, r.1.2),
    r.2)

omit hvalid hmactag h16 in
theorem mixSeeds_getElem! (r r' : Randomness geom) (j k : ℕ) (hk : k < geom.nrHops) :
    (mixSeeds geom r r' j).1.1.toArray[k]!
      = if k < j then r'.1.1.toArray[k]! else r.1.1.toArray[k]! := by
  rw [getElem!_pos _ _ (by simpa using hk)]
  split_ifs <;> simp [mixSeeds, getElem!_pos, *]

omit hvalid hmactag h16 in
/-- After position `j` the mixed randomness has the original's seeds. -/
theorem mixSeeds_extract_after (r r' : Randomness geom) (j n : ℕ) (hn : n ≤ geom.nrHops) :
    ((mixSeeds geom r r' j).1.1.toArray.extract 0 n).extract (j + 1)
        ((mixSeeds geom r r' j).1.1.toArray.extract 0 n).size
      = (r.1.1.toArray.extract 0 n).extract (j + 1) (r.1.1.toArray.extract 0 n).size := by
  apply Array.ext
  · simp
  · intro i h1 h2
    have hi : j + 1 + i < n := by
      simp at h1
      omega
    simp [mixSeeds, show ¬ (j + 1 + i < j) by omega]

omit hvalid hmactag h16 in
/-- **The layers in front of the relay are the replacement's.** On the original's path with
the mixed randomness, the layers of the hops before the honest relay are those on the
replacement's path with the replacement's randomness. -/
theorem wrapUp_mixSeeds (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last last' : List RoutingCommand) (r r' : Randomness geom) (j : ℕ)
    (hj : j < R.hops.length) (L : ByteArray) :
    wrapUp kem cipher macS kdfS streamS geom (path kem R last) (mixSeeds geom r r' j).1 0 j L
      = wrapUp kem cipher macS kdfS streamS geom (path kem (R.take (j + 1)) last') r'.1 0 j L := by
  have hl : (R.take (j + 1)).hops.length = j + 1 := by simp [Protocols.RSOR.Route.take]; omega
  have hle := R.length_le
  refine wrapUp_congr geom kem kdfS streamS cipher macS _ _ _ _ (by rw [path_size]; exact hle)
    (by rw [path_size, hl]; omega) 0 j L fun k _ hk => ⟨by rw [path_size]; omega,
      by rw [path_size, hl]; omega,
      (path_take_getElem! kem geom R last' last (j + 1) k (by omega) (by omega)).symm, ?_, ?_⟩
  · by_cases hkj : k + 1 < j
    · rw [path_take_getElem! kem geom R last' last (j + 1) (k + 1) (by omega) (by omega)]
    · obtain rfl : k + 1 = j := by omega
      rw [path_take_last kem geom R last' (k + 1) hj, path_getElem! kem R last (k + 1) hj]
  · rw [mixSeeds_getElem! geom r r' j k (by omega), ite_eq_left (by omega)]

omit h16 in
include hvalid hmactag in
set_option maxHeartbeats 1000000 in
/-- **The shifted keystream on the game's paths.** Before the end of the original's path, with
the mixed randomness and the shifted keystream, the honest relay has the next layer the
original has with its own randomness, and the header bytes the replacement has. -/
theorem shiftStream_path (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last last' : List RoutingCommand) (r r' : Randomness geom) (payload : ByteArray) (j : ℕ)
    (c U U' fwd : ByteArray) (hn : j + 1 < R.hops.length)
    (hU : U.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hU' : U'.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hc : c.size = kem.ciphertextSize)
    (hfwd : layerPast kem cipher macS kdfS streamS geom (path kem R last) r.1 payload j U' (j + 1) = .ok fwd)
    (hs' : (relayFrontLast kem kdfS streamS geom (path kem (R.take (j + 1)) last') r'.1 j c U).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength) :
    layerPast kem cipher macS kdfS streamS geom (path kem R last) (mixSeeds geom r r' j).1 payload j
        (shiftStream geom kem kdfS streamS (path kem R last) (path kem (R.take (j + 1)) last')
          r.1 (mixSeeds geom r r' j).1 r'.1 j c U U' fwd) (j + 1) = .ok fwd
      ∧ relayFront kem cipher macS kdfS streamS geom (path kem R last) (mixSeeds geom r r' j).1 payload j c
          (shiftStream geom kem kdfS streamS (path kem R last) (path kem (R.take (j + 1)) last')
            r.1 (mixSeeds geom r r' j).1 r'.1 j c U U' fwd)
        = relayFrontLast kem kdfS streamS geom (path kem (R.take (j + 1)) last') r'.1 j c U := by
  have hl : (R.take (j + 1)).hops.length = j + 1 := by simp [Protocols.RSOR.Route.take]; omega
  have hle := R.length_le
  have hx : ∀ (a : Array (Vector UInt8 32)) (n m : ℕ), m < n → n ≤ a.size →
      (a.extract 0 n)[m]! = a[m]! := fun a n m h1 h2 => by
    rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega)]
    simp
  refine shiftStream_spec geom kem kdfS streamS cipher macS hvalid hmactag _ _ _ _ _ payload j
    c U U' fwd (by rw [path_size]; exact hn) (by rw [path_size]; exact hle)
    (by rw [path_size, hl]) hU hU' hc rfl
    (mixSeeds_extract_after geom r r' j _ (by rw [path_size]; exact hle)) (fun m hm => ?_) ?_ hfwd
    hs'
  · unfold kemHopKeys
    rw [← path_take_getElem! kem geom R last' last (j + 1) m (by omega) (by omega),
      hx _ _ m (by rw [path_size]; omega) (by rw [path_size]; simpa using hle),
      hx _ _ m (by rw [path_size, hl]; omega) (by rw [path_size, hl]; simp; omega),
      mixSeeds_getElem! geom r r' j m (by omega), ite_eq_left hm]
  · rw [path_getElem! kem R last j (by omega), ite_eq_right (by omega)]

end RSOR

/-! ## The exit relay's reply -/

namespace RSOR

omit h16 in
include hvalid hmactag in
/-- **A reply from the sender's own payload is the first layer of the reply onion.** -/
theorem replyOf_body (q : Request kem geom) (r : Randomness geom) (m : Msg geom)
    (hr : Reliable kem cipher macS kdfS streamS geom q r) (hjlt : 0 < q.back.hops.length)
    (tag : Vector UInt8 32) (cmds : List RoutingCommand) :
    replyOf cipher geom m (some (some (body kem macS kdfS streamS geom q r), tag, cmds, none))
      = some (q.back.hops[0].name,
        formBack kem cipher macS kdfS streamS geom q r m ⟨0, hjlt⟩) := by
  obtain ⟨-, x0, keys, hx0, -, -, -, hnp, hP0⟩ :=
    replyPacket_eq kem cipher macS kdfS streamS geom hvalid hmactag q r m hr hjlt
  have hss : (surb kem macS kdfS streamS geom q r).1.size = geom.surbLength := by
    have := hnp
    unfold SURB.newPacketFromSURB at this
    by_contra hne
    simp [hne] at this
    cases this
  have hfl : (body kem macS kdfS streamS geom q r).get! 0 = 1 := by
    have hne : ¬ q.back.hops.isEmpty := by
      rw [List.isEmpty_iff]; exact List.ne_nil_of_length_pos hjlt
    have h2 : (⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ : ByteArray).size = 2 := rfl
    unfold body
    rw [get!_eq_getElem _ 0 (by rw [ByteArray.size_append, ByteArray.size_append, h2]; omega),
      ByteArray.getElem_append_left (by rw [ByteArray.size_append, h2]; omega),
      ByteArray.getElem_append_left (by rw [h2]; omega)]
    simp only [hne]
    rfl
  have hsb : (body kem macS kdfS streamS geom q r).extract 2 (2 + geom.surbLength)
      = (surb kem macS kdfS streamS geom q r).1 := by
    unfold body
    rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
      rw [ByteArray.size_append, hss]; exact Nat.le_refl _)]
    exact extract_append_tail _ _ _ _ rfl (by rw [hss])
  unfold replyOf formBack
  dsimp only
  rw [ite_eq_left hfl, hsb, hnp, hx0]
  dsimp only
  rw [hP0]
  rfl

end RSOR

/-! ## The two worlds before the end of the path -/

omit hvalid hmactag h16 in
/-- A header's bytes followed by a payload split into the two. -/
theorem split_append (P : ByteArray) (x : Block geom) (hP : P.size = geom.headerLength) :
    RSOR.split geom (P ++ ofVector x) = (toVecN _ P, x) := by
  have e1 : (P ++ ofVector x).extract 0 geom.headerLength = P := by
    rw [← hP]
    exact Util.Bytes.extract_append_left P _
  have e2 : (P ++ ofVector x).extract geom.headerLength (P ++ ofVector x).size = ofVector x := by
    rw [← hP, ByteArray.size_append]
    exact Util.Bytes.extract_append_right P _
  unfold RSOR.split
  rw [e1, e2, Cryptlib.Protocols.Sphinx.Common.toVecN_ofVector]

set_option maxHeartbeats 1000000 in
/-- **Before the end of the path, world 1's patched relay is world 0's relay.** World 0's relay
has the header of a path that goes on, and forwards the next layer `fwd` with the payload it
decrypts: the next layer's own payload for the unchanged block, the random block `g`
otherwise. World 1's relay, whatever it would answer, is patched to forward the same. The two
games are the same when the headers agree and world 1's relay would not reply. -/
theorem headerRelays_forward_eq {pk kb ks : Key kem} (names : Role → RSOR.Name)
    (c : Protocols.RSOR.ForwardChallenge (S := 𝒮)
      (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk kb ks))
    (hn : c.pos + 1 < c.req.fwd.hops.length)
    (r : RSOR.Randomness geom) (mine : RSOR.Onion geom) (g : Block geom)
    (sk : Role → kem.PrivateKey) (ct : kem.Ciphertext) (km : Vector UInt8 32)
    (U₀ U₁ : ByteArray) (D₁ : Block geom → Block geom)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (cc fwd : ByteArray)
    (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hU : U₀.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hc : cc.size = kem.ciphertextSize)
    (hfwd : layerPast kem cipher macS kdfS streamS geom hops d payload j U₀ (j + 1) = .ok fwd)
    (hs : (relayFront kem cipher macS kdfS streamS geom hops d payload j cc U₀).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hcmd : (hops[j]!).commands = [])
    (hname : (hops[j + 1]!).id = c.req.fwd.hops[c.pos.val + 1].name)
    (hmine : mine.1 = Util.Bytes.toVecN geom.headerLength
      (relayFront kem cipher macS kdfS streamS geom hops d payload j cc U₀
        ++ ofVector (macS.mac (ofVector km)
          (relayFront kem cipher macS kdfS streamS geom hops d payload j cc U₀))))
    (hrep : ∀ (m : RSOR.Msg geom) (o : RSOR.Onion geom), o.1 = mine.1 →
      RSOR.replyOf cipher geom m
        (procKeysD kem macS geom km U₁ (ofVector (D₁ o.2)) (RSOR.join o)) = none) :
    headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U₁ mine.1 D₁
        (c.patchDrawn (RSOR.split geom fwd) r mine g)
      = headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U₀ mine.1
        (fun y => if y = mine.2 then (RSOR.split geom fwd).2 else g) {} := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  refine headerRelays_patch_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U₀ U₁
    mine.1 _ D₁ _ (fun o ho => ?_) (fun m o ho => ?_) (fun h o out hc => ?_)
    (fun h m o out hc => ?_)
  · obtain ⟨o1, o2⟩ := o
    obtain rfl : o1 = mine.1 := ho
    have hst := stepOf_relayFront geom kem kdfS streamS cipher macS hvalid hmactag hops d payload
      j cc U₀ fwd km (if o2 = mine.2 then (RSOR.split geom fwd).2 else g) o2 hj hlen hU hc hfwd hs
      (by omega) hcmd
    rw [← hmine] at hst
    have hfwd' := hfwd
    unfold layerPast at hfwd'
    have hfsz : fwd.size = geom.packetLength :=
      newKEMPacket_size kem cipher macS kdfS streamS geom _ _ _ _ _ hvalid hmactag hfwd'
        (newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hfwd').1
    have hH : 2 + kem.ciphertextSize + geom.routingInfoLength + macLength = geom.headerLength := by
      rw [hhdr, had]
    rw [hH] at hst
    unfold Protocols.RSOR.ForwardChallenge.patchDrawn
    dsimp only
    rw [hst, hname, split_append geom _ _ (by
      rw [ByteArray.size_extract]
      omega)]
    refine congrArg pure ((ite_eq_left ⟨rfl, rfl⟩).trans ((dite_eq_left hn).trans ?_))
    refine congrArg (fun z => some (Protocols.RSOR.Step.forward _ z)) ?_
    by_cases ho : o2 = mine.2
    · exact (ite_eq_left ho).trans (Prod.ext rfl (ite_eq_left ho).symm)
    · exact (ite_eq_right ho).trans (Prod.ext rfl (ite_eq_right ho).symm)
  · obtain ⟨o1, o2⟩ := o
    obtain rfl : o1 = mine.1 := ho
    have hrp := replyOf_relayFront geom kem kdfS streamS cipher macS hvalid hmactag hops d payload
      j cc U₀ fwd km (if o2 = mine.2 then (RSOR.split geom fwd).2 else g) o2 hj hlen hU hc hfwd hs
      (by omega) hcmd m
    rw [← hmine] at hrp
    have h1 := hrep m (mine.1, o2) rfl
    rw [hrp]
    unfold Protocols.RSOR.ForwardChallenge.patchDrawn Protocols.RSOR.ForwardChallenge.patchWith
    exact (ite_eq_right fun hx => absurd hx.2.2 (by omega)).trans h1
  · unfold Protocols.RSOR.ForwardChallenge.patchDrawn
    exact congrArg pure (ite_eq_right hc)
  · unfold Protocols.RSOR.ForwardChallenge.patchDrawn Protocols.RSOR.ForwardChallenge.patchWith
    exact ite_eq_right fun hx => hc ⟨hx.1, by rw [hx.2.1]⟩

/-! ## The two worlds at the end of the path -/

set_option maxHeartbeats 1000000 in
/-- **At the end of the path, world 1's patched relay is world 0's relay.** Both relays have
the header of a path that ends at them, and deliver when the block they decrypt begins with
the zero tag. The patch puts the original's message and reply in place of the replacement's.
The two games are the same when the headers agree, both senders' blocks begin with the zero
tag, and the random block for a changed payload does not. -/
theorem headerRelays_last_eq {pk kb ks : Key kem} (names : Role → RSOR.Name)
    (c : Protocols.RSOR.ForwardChallenge (S := 𝒮)
      (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk kb ks))
    (hl : c.pos + 1 = c.req.fwd.hops.length)
    (next : RSOR.Onion geom) (r : RSOR.Randomness geom) (mine : RSOR.Onion geom) (g : Block geom)
    (sk : Role → kem.PrivateKey) (ct : kem.Ciphertext) (km : Vector UInt8 32)
    (U₀ U₁ : ByteArray) (hops₀ hops₁ : Array PathHop) (d₀ d₁ : RSOR.Draw geom) (j : ℕ)
    (cc : ByteArray) (rc₁ : Vector UInt8 32) (B₀ B₁ v : Block geom)
    (hj₀ : j + 1 = hops₀.size) (hlen₀ : hops₀.size ≤ geom.nrHops)
    (hj₁ : j + 1 = hops₁.size) (hlen₁ : hops₁.size ≤ geom.nrHops)
    (hU₀ : U₀.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hU₁ : U₁.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hc : cc.size = kem.ciphertextSize)
    (hs₀ : (relayFrontLast kem kdfS streamS geom hops₀ d₀ j cc U₀).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hs₁ : (relayFrontLast kem kdfS streamS geom hops₁ d₁ j cc U₁).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hcmd₀ : (hops₀[j]!).commands = [.recipient c.req.receiver])
    (hcmd₁ : (hops₁[j]!).commands = [.recipient rc₁])
    (hmine₀ : mine.1 = Util.Bytes.toVecN geom.headerLength
      (relayFrontLast kem kdfS streamS geom hops₀ d₀ j cc U₀
        ++ ofVector (macS.mac (ofVector km)
          (relayFrontLast kem kdfS streamS geom hops₀ d₀ j cc U₀))))
    (hmine₁ : mine.1 = Util.Bytes.toVecN geom.headerLength
      (relayFrontLast kem kdfS streamS geom hops₁ d₁ j cc U₁
        ++ ofVector (macS.mac (ofVector km)
          (relayFrontLast kem kdfS streamS geom hops₁ d₁ j cc U₁))))
    (hB₀ : ((ofVector B₀).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
    (hB₁ : ((ofVector B₁).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
    (hv : ¬ ((ofVector v).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
    (hbody : (ofVector B₀).extract geom.payloadTagLength (ofVector B₀).size
      = RSOR.body kem macS kdfS streamS geom c.req r)
    (hmsg : RSOR.msgOf geom (RSOR.body kem macS kdfS streamS geom c.req r) = c.req.msg)
    (hr : RSOR.Reliable kem cipher macS kdfS streamS geom c.req r) :
    headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U₁ mine.1
        (fun y => if y = mine.2 then B₁ else v) (c.patchDrawn next r mine g)
      = headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U₀ mine.1
        (fun y => if y = mine.2 then B₀ else v) {} := by
  have hx : 0 < geom.payloadTagLength + geom.forwardPayloadLength := by omega
  have hjlt : 0 < c.req.back.hops.length :=
    List.length_pos_iff.2 fun h => by simpa [h] using c.sender
  refine headerRelays_patch_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U₀ U₁
    mine.1 _ _ _ (fun o ho => ?_) (fun m o ho => ?_) (fun h o out hc => ?_)
    (fun h m o out hc => ?_)
  · obtain ⟨o1, o2⟩ := o
    obtain rfl : o1 = mine.1 := ho
    have h0 := stepOf_relayFrontLast geom kem kdfS streamS macS hvalid hmactag hops₀ d₀ j cc U₀
      km (if o2 = mine.2 then B₀ else v) o2 hj₀ hlen₀ hU₀ hc hs₀ hx _ hcmd₀
    have h1 := stepOf_relayFrontLast geom kem kdfS streamS macS hvalid hmactag hops₁ d₁ j cc U₁
      km (if o2 = mine.2 then B₁ else v) o2 hj₁ hlen₁ hU₁ hc hs₁ hx _ hcmd₁
    rw [← hmine₀] at h0
    rw [← hmine₁] at h1
    unfold Protocols.RSOR.ForwardChallenge.patchDrawn
    dsimp only
    rw [h0, h1]
    refine congrArg pure ((ite_eq_left ⟨rfl, rfl⟩).trans ((dite_eq_right (by omega)).trans ?_))
    by_cases ho : o2 = mine.2
    · rw [ite_eq_left ho, ite_eq_left ho, ite_eq_left hB₀, ite_eq_left hB₁, hbody, hmsg]
      rfl
    · rw [ite_eq_right ho, ite_eq_right ho, ite_eq_right hv, ite_eq_right hv]
      rfl
  · obtain ⟨o1, o2⟩ := o
    obtain rfl : o1 = mine.1 := ho
    have h0 := replyOf_relayFrontLast geom kem kdfS streamS cipher macS hvalid hmactag hops₀ d₀ j
      cc U₀ km (if o2 = mine.2 then B₀ else v) o2 hj₀ hlen₀ hU₀ hc hs₀ hx _ hcmd₀ m
    have h1 := replyOf_relayFrontLast geom kem kdfS streamS cipher macS hvalid hmactag hops₁ d₁ j
      cc U₁ km (if o2 = mine.2 then B₁ else v) o2 hj₁ hlen₁ hU₁ hc hs₁ hx _ hcmd₁ m
    rw [← hmine₀] at h0
    rw [← hmine₁] at h1
    rw [h0, h1]
    unfold Protocols.RSOR.ForwardChallenge.patchDrawn Protocols.RSOR.ForwardChallenge.patchWith
    by_cases ho : o2 = mine.2
    · subst ho
      refine (ite_eq_left ⟨rfl, rfl, hl⟩).trans ?_
      rw [ite_eq_left rfl, ite_eq_left hB₀, hbody,
        RSOR.replyOf_body kem cipher macS kdfS streamS geom hvalid hmactag c.req r m hr hjlt]
      rfl
    · refine (ite_eq_right fun hx' => ho (congrArg Prod.snd hx'.2.1)).trans ?_
      rw [ite_eq_right ho, ite_eq_right ho, ite_eq_right hv, ite_eq_right hv]
  · unfold Protocols.RSOR.ForwardChallenge.patchDrawn
    exact congrArg pure (ite_eq_right hc)
  · unfold Protocols.RSOR.ForwardChallenge.patchDrawn Protocols.RSOR.ForwardChallenge.patchWith
    exact ite_eq_right fun hx' => hc ⟨hx'.1, by rw [hx'.2.1]⟩

end ForwardFinal

end Cryptlib.Protocols.Sphinx.KEMSphinx
