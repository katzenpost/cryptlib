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
      (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names cs.1 x (ofVector U')))).run []
  return z.2.any (badQuery kem (encapOf kem k.1.1 s').1 fun _ => true)

/-- **The hidden ciphertext.** Rejecting the ciphertext of the original's layer at the relay
changes world 1 by at most the chance that the adversary sends it. -/
theorem next_hidden_le (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← (PRGScheme.prgIdealExperiment
          (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
      - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (nextStreamAdvF kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            (ownAns kem cipher macS kdfS streamS geom) A))}[x = true]).toReal|
    ≤ (Pr{let b ← (nextHidden kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[b = true]).toReal := by
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
        + Pr{let b ← (nextHidden kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[b = true] :=
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
        + Pr{let b ← (nextHidden kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[b = true] :=
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
              shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1 (ofVector x.1)
            else x.2.2.2.2.2)
          (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x U').1.patch)
        (A.guess st.1 (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x U').1.onion)).run' st.2.1 := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  obtain ⟨U, km, s, o, u, v⟩ := x
  obtain ⟨W, hW⟩ : ∃ W,
      W = nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (U, km, s, o, u, v) U' := ⟨_, rfl⟩
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
        (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U Hv D
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
      exact (congrArg (patch.proc Role.relay o) (if_pos ⟨rfl, ho⟩)).trans
        ((hstep o ho).trans (congrArg pure (if_pos ⟨rfl, ho⟩).symm))
    · exact (congrArg (patch.proc h o) (if_neg hc)).trans
        ((hproc h o _ hc).trans (congrArg pure (if_neg hc).symm))
  · by_cases hc : h = Role.relay ∧ o.1 = Hv
    · obtain ⟨rfl, ho⟩ := hc
      exact (congrArg (patch.reply Role.relay m o) (if_pos ⟨rfl, ho⟩)).trans
        ((hrep m o ho).trans (if_pos ⟨rfl, ho⟩).symm)
    · exact (congrArg (patch.reply h m o) (if_neg hc)).trans
        ((hreply h m o _ hc).trans (if_neg hc).symm)

end ForwardFinal

end Cryptlib.Protocols.Sphinx.KEMSphinx
