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
/-- A route truncated within its length has the length it was truncated to. -/
theorem take_length {N : ℕ} {Nm Ky : Type} (R : Protocols.RSOR.Route N Nm Ky) (k : ℕ)
    (hk : k ≤ R.hops.length) : (R.take k).hops.length = k := by
  simp [Protocols.RSOR.Route.take]
  omega

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
      = wrapUp kem cipher macS kdfS streamS geom (path kem (R.take (j + 1)) last') r'.1 0 j
        L := by
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

omit hvalid hmactag h16 in
/-- The hops before the relay have the same keys on the original's path with the mixed
randomness as on the replacement's path with the replacement's randomness. -/
theorem kemHopKeys_mixSeeds (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last last' : List RoutingCommand) (r r' : Randomness geom) (j : ℕ)
    (hj : j < R.hops.length) (m : ℕ) (hm : m < j) :
    kemHopKeys kem kdfS (path kem R last)
        ((mixSeeds geom r r' j).1.1.toArray.extract 0 (path kem R last).size) m
      = kemHopKeys kem kdfS (path kem (R.take (j + 1)) last')
        (r'.1.1.toArray.extract 0 (path kem (R.take (j + 1)) last').size) m := by
  have hl : (R.take (j + 1)).hops.length = j + 1 := take_length R (j + 1) (by omega)
  have hle := R.length_le
  have hx : ∀ (a : Array (Vector UInt8 32)) (n m : ℕ), m < n → n ≤ a.size →
      (a.extract 0 n)[m]! = a[m]! := fun a n m h1 h2 => by
    rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega)]
    simp
  unfold kemHopKeys
  rw [← path_take_getElem! kem geom R last' last (j + 1) m (by omega) (by omega),
    hx _ _ m (by rw [path_size]; omega) (by rw [path_size]; simpa using hle),
    hx _ _ m (by rw [path_size, hl]; omega) (by rw [path_size, hl]; simp; omega),
    mixSeeds_getElem! geom r r' j m (by omega), ite_eq_left hm]

omit hvalid hmactag h16 in
/-- The message is at the end of the sender's payload. -/
theorem msgOf_body (q : Request kem geom) (r : Randomness geom) :
    msgOf geom (body kem macS kdfS streamS geom q r) = q.msg := by
  unfold msgOf body
  rw [ByteArray.size_append, Util.Bytes.size_ofVector, Nat.add_sub_cancel]
  have h := Util.Bytes.extract_append_right
    ((⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ : ByteArray)
      ++ (surb kem macS kdfS streamS geom q r).1) (ofVector q.msg)
  rw [Util.Bytes.size_ofVector] at h
  rw [h, Cryptlib.Protocols.Sphinx.Common.toVecN_ofVector]

omit hvalid hmactag h16 in
/-- A block made of the zero tag and a payload begins with the zero tag and has the payload
behind it. -/
theorem zeroTag_block (X : ByteArray) (hX : X.size = geom.forwardPayloadLength) :
    ((ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ X))).extract 0
        geom.payloadTagLength).data.all (· == 0) = true
      ∧ (ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ X))).extract
            geom.payloadTagLength
            (ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
              ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ X))).size
        = X := by
  have hz : (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray).size
      = geom.payloadTagLength := Array.size_replicate
  rw [Util.Bytes.ofVector_toVecN _ (by rw [ByteArray.size_append, hz, hX])]
  constructor
  · have h := Util.Bytes.extract_append_left
      (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) X
    rw [hz] at h
    rw [h]
    show (Array.replicate geom.payloadTagLength (0 : UInt8)).all (· == 0) = true
    rw [Array.all_eq_true]
    intro i hi
    simp
  · have h := Util.Bytes.extract_append_right
      (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) X
    rw [hz] at h
    rw [ByteArray.size_append, hz, h]

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
    (hfwd : layerPast kem cipher macS kdfS streamS geom (path kem R last) r.1 payload j U'
      (j + 1) = .ok fwd)
    (hs' : (relayFrontLast kem kdfS streamS geom (path kem (R.take (j + 1)) last') r'.1 j c
      U).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength) :
    layerPast kem cipher macS kdfS streamS geom (path kem R last) (mixSeeds geom r r' j).1 payload j
        (shiftStream geom kem kdfS streamS (path kem R last) (path kem (R.take (j + 1)) last')
          r.1 (mixSeeds geom r r' j).1 r'.1 j c U U' fwd) (j + 1) = .ok fwd
      ∧ relayFront kem cipher macS kdfS streamS geom (path kem R last) (mixSeeds geom r r' j).1
          payload j c
          (shiftStream geom kem kdfS streamS (path kem R last) (path kem (R.take (j + 1)) last')
            r.1 (mixSeeds geom r r' j).1 r'.1 j c U U' fwd)
        = relayFrontLast kem kdfS streamS geom (path kem (R.take (j + 1)) last') r'.1 j c U := by
  have hl : (R.take (j + 1)).hops.length = j + 1 := by simp [Protocols.RSOR.Route.take]; omega
  have hle := R.length_le
  refine shiftStream_spec geom kem kdfS streamS cipher macS hvalid hmactag _ _ _ _ _ payload j
    c U U' fwd (by rw [path_size]; exact hn) (by rw [path_size]; exact hle)
    (by rw [path_size, hl]) hU hU' hc rfl
    (mixSeeds_extract_after geom r r' j _ (by rw [path_size]; exact hle))
    (kemHopKeys_mixSeeds kem kdfS geom R last last' r r' j (by omega)) ?_ hfwd hs'
  rw [path_getElem! kem R last j (by omega), ite_eq_right (by omega)]

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

/-! ## World 1 is world 0 under the relabelling, before the end of the path -/

set_option maxHeartbeats 2000000 in
/-- **Before the end of the path, world 1 with its payload drawn is world 0 at the relabelled
draws.** World 0 is played with the mixed randomness, the shifted keystream, and the random
payload `g` in place of the ideal cipher's second block. -/
theorem nextDrawn_eq_forward (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (x : NextOth geom) (U' : Keystream geom) (g : Block geom) (fwd : ByteArray)
    (hn : ch.c.pos + 1 < ch.c.req.fwd.hops.length)
    (hfwd : layerPast kem cipher macS kdfS streamS geom
      (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) x.2.2.2.1.1.1
      (RSOR.body kem macS kdfS streamS geom ch.c.req x.2.2.2.1.1) ch.c.pos (ofVector U')
      (ch.c.pos + 1) = .ok fwd)
    (hsz : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
      (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hnoreply : ∀ (m : RSOR.Msg geom) (o : RSOR.Onion geom),
      o.1 = Util.Bytes.toVecN geom.headerLength
          (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
              (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)
            ++ ofVector (macS.mac (ofVector x.2.1)
              (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)))) →
        RSOR.replyOf cipher geom m (procKeysD kem macS geom x.2.1 (ofVector x.1)
          (ofVector (if o.2 = x.2.2.2.2.1 then
              shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                (ofVector x.1)
            else x.2.2.2.2.2)) (RSOR.join o)) = none) :
    (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16
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
          (ch.c.patchDrawn (RSOR.split geom fwd) x.2.2.2.1.1
            (RSOR.split geom
              (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x)) g))
        (A.guess st.1 (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x
          (ofVector U')).1.onion)).run' st.2.1
      = forwardRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          (RSOR.Randomness geom) ($ᵗ RSOR.Randomness geom)
          (fun ch r c t =>
            { onion := onionK kem cipher macS kdfS streamS geom ch.c.req r ch.c.pos c t 0 }) A
          (forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (forwardViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          x.2.1
          (shiftStream geom kem kdfS streamS
            (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
            (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
              [.recipient (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1).receiver])
            x.2.2.2.1.1.1 (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos).1
            x.2.2.2.1.2.2.2.1 ch.c.pos
            (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 x.2.2.1).1))
            (ofVector x.1) (ofVector U') fwd)
          ⟨k, (ch, st), x.2.2.1, RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos⟩
          x.2.2.2.2.1 g := by
  obtain ⟨U, km, s, ⟨r, msg, nm, r'⟩, u, v⟩ := x
  dsimp only at hfwd hsz hnoreply ⊢
  have hpos : (ch.c.pos : ℕ) < ch.c.req.fwd.hops.length := ch.c.pos.isLt
  have hp1 : (RSOR.path kem (ch.c.short msg nm).fwd
      [.recipient (ch.c.short msg nm).receiver]).size = ch.c.pos + 1 :=
    (RSOR.path_size kem _ _).trans (RSOR.take_length _ _ hn.le)
  have hspec := RSOR.shiftStream_path kem cipher macS kdfS streamS geom hvalid hmactag
    ch.c.req.fwd [.recipient ch.c.req.receiver]
    [.recipient (ch.c.short msg nm).receiver] r r'
    (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U') fwd hn
    (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) hfwd
    (by
      unfold shortMU relayFrontAt at hsz
      dsimp only at hsz
      rw [ite_eq_right (by have := hp1; omega)] at hsz
      exact hsz)
  obtain ⟨hF, hM⟩ := hspec
  have hp0 : ch.c.pos + 1 < (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size :=
    lt_of_lt_of_eq hn (RSOR.path_size kem _ _).symm
  have e1 : forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
      (RSOR.mixSeeds geom r r' ch.c.pos) (encapOf kem k.1.1 s).1
        (shiftStream geom kem kdfS streamS
          (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
            [.recipient (ch.c.short msg nm).receiver])
          r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U')
          fwd)
      = shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r')
        (encapOf kem k.1.1 s).1 (ofVector U) := by
    unfold forwardMU shortMU relayFrontAt
    dsimp only
    rw [ite_eq_left hp0, ite_eq_right (by have := hp1; omega)]
    exact hM
  have e2 : forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
      (RSOR.mixSeeds geom r r' ch.c.pos)
        (shiftStream geom kem kdfS streamS
          (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
            [.recipient (ch.c.short msg nm).receiver])
          r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U')
          fwd)
      = (RSOR.split geom fwd).2 := by
    unfold forwardBlockU relayBackAt
    rw [ite_eq_left hp0]
    unfold relayBack
    refine (congrArg (fun z : Except String ByteArray => Util.Bytes.toVecN _
      (match z with
        | .ok fwd => id (fwd.extract (payloadOffset kem geom) fwd.size)
        | .error _ => ByteArray.empty)) hF).trans ?_
    have hoff : payloadOffset kem geom = geom.headerLength := by
      obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
      unfold payloadOffset
      rw [hhdr]
      rfl
    dsimp only
    rw [hoff]
    rfl
  unfold forwardRunU
  dsimp only [KeyedDraw.c]
  rw [e1, e2]
  obtain ⟨-, -, hrouting, hhdr, -, -⟩ := id hvalid
  have hle0 : (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size
      ≤ geom.nrHops := le_of_eq_of_le (RSOR.path_size kem _ _) ch.c.req.fwd.length_le
  have hcmd0 : ((RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])[(ch.c.pos :
      ℕ)]!).commands = [] :=
    (congrArg (·.commands) (RSOR.path_getElem! kem _ _ _ hpos)).trans
      (ite_eq_right (Nat.ne_of_lt hn))
  have hname : ((RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])[(ch.c.pos : ℕ) + 1]!).id
      = ch.c.req.fwd.hops[(ch.c.pos : ℕ) + 1].name :=
    congrArg (·.id) (RSOR.path_getElem! kem _ _ _ hn)
  have hszM := relayFront_size geom kem kdfS streamS cipher macS hvalid hmactag _ _ _ _
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) _ fwd hp0 hle0
    (Util.Bytes.size_ofVector _) hF hcmd0
  have hUs := shiftStream_size geom kem kdfS streamS hrouting
    (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
    (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg nm).receiver])
    r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U') fwd
    ((Nat.le_of_lt hp0).trans hle0) (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _)
  have hsplit : RSOR.split geom (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16
      names ch (U, km, s, (r, msg, nm, r'), u, v))
      = (Util.Bytes.toVecN geom.headerLength
          (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r')
              (encapOf kem k.1.1 s).1 (ofVector U)
            ++ ofVector (macS.mac (ofVector km)
              (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
                  r') (encapOf kem k.1.1 s).1 (ofVector U)))), u) :=
    split_append geom _ u (by
      rw [ByteArray.size_append, hsz, Util.Bytes.size_ofVector, hmactag, hhdr]
      rfl)
  have honion : (forwardViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
        (RSOR.mixSeeds geom r r' ch.c.pos) (encapOf kem k.1.1 s).1 km
        (shiftStream geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
            [.recipient (ch.c.short msg nm).receiver])
          r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U')
          fwd) u).onion
      = (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (U, km, s, (r,
          msg, nm, r'), u, v) (ofVector U')).1.onion := by
    unfold forwardViewU nextViewU nextLayer shortLayerU
    dsimp only
    rw [e1]
    exact congrArg (RSOR.split geom) (RSOR.wrapUp_mixSeeds kem cipher macS kdfS streamS geom
        ch.c.req.fwd
      _ _ r r' ch.c.pos hpos _)
  rw [honion]
  have hm1 := congrArg Prod.fst hsplit
  have hm2 := congrArg Prod.snd hsplit
  dsimp only at hm1 hm2
  have eM : shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r')
      (encapOf kem k.1.1 s).1 (ofVector U)
      = relayFront kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
          ch.c.req.receiver])
        (RSOR.mixSeeds geom r r' ch.c.pos).1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
        ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
        (shiftStream geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver])
        (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
          [.recipient (ch.c.short msg nm).receiver])
        r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
        (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U')
        fwd) :=
    e1.symm.trans (by
      unfold forwardMU relayFrontAt
      exact ite_eq_left hp0)
  have H := headerRelays_forward_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
    ch.c hn r (RSOR.split geom (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16
        names ch (U, km, s, (r, msg, nm, r'), u, v))) g
    (fun h => if h = .relay then k.2 else st.2.2 h) (encapOf kem k.1.1 s).1 km
    (shiftStream geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
        (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
          [.recipient (ch.c.short msg nm).receiver])
        r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
        (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U')
        fwd) (ofVector U)
    (fun y => if y = u then
        shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r')
            (ofVector U)
      else v)
    (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1
    (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) fwd hp0 hle0 hUs
    (Util.Bytes.size_ofVector _) hF hszM hcmd0 hname
    (hm1.trans (by rw [eM])) (fun m o ho => hnoreply m o (ho.trans hm1))
  rw [hm1, hm2] at H
  exact congrArg (fun impl => (simulateQ impl (A.guess st.1
    (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (U, km, s, (r, msg,
        nm, r'), u, v) (ofVector U')).1.onion)).run' st.2.1) H

/-! ## World 1 is world 0 under the relabelling, at the end of the path -/

set_option maxHeartbeats 2000000 in
/-- **At the end of the path, world 1 with its payload drawn is world 0 at the relabelled
draws.** World 0 is played with the mixed randomness and the keystream with its head shifted.
The two senders' payloads have a payload's length, the original's request is reliable, and the
ideal cipher's second block does not begin with the zero tag. -/
theorem nextDrawn_eq_last (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (x : NextOth geom) (U' : Keystream geom) (g : Block geom) (next : RSOR.Onion geom)
    (hl : ch.c.pos + 1 = ch.c.req.fwd.hops.length)
    (hb₀ : (RSOR.body kem macS kdfS streamS geom ch.c.req x.2.2.2.1.1).size
      = geom.forwardPayloadLength)
    (hb₁ : (RSOR.body kem macS kdfS streamS geom
        (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1) x.2.2.2.1.2.2.2).size
      = geom.forwardPayloadLength)
    (hr : RSOR.Reliable kem cipher macS kdfS streamS geom ch.c.req x.2.2.2.1.1)
    (hv : ¬ ((ofVector x.2.2.2.2.2).extract 0 geom.payloadTagLength).data.all (· == 0) = true) :
    (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16
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
          (ch.c.patchDrawn next x.2.2.2.1.1
            (RSOR.split geom
              (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x)) g))
        (A.guess st.1 (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x
          (ofVector U')).1.onion)).run' st.2.1
      = forwardRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          (RSOR.Randomness geom) ($ᵗ RSOR.Randomness geom)
          (fun ch r c t =>
            { onion := onionK kem cipher macS kdfS streamS geom ch.c.req r ch.c.pos c t 0 }) A
          (forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (forwardViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          x.2.1
          (lastShift geom kem kdfS streamS
            (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
            (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
              [.recipient (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1).receiver])
            (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos).1
            x.2.2.2.1.2.2.2.1 ch.c.pos
            (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 x.2.2.1).1)) (ofVector x.1))
          ⟨k, (ch, st), x.2.2.1, RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos⟩
          x.2.2.2.2.1 x.2.2.2.2.2 := by
  obtain ⟨U, km, s, ⟨r, msg, nm, r'⟩, u, v⟩ := x
  dsimp only at hb₀ hb₁ hr hv ⊢
  obtain ⟨-, -, hrouting, hhdr, -, -⟩ := id hvalid
  have hpos : (ch.c.pos : ℕ) < ch.c.req.fwd.hops.length := ch.c.pos.isLt
  have hp0 : (ch.c.pos : ℕ) + 1 = (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size
      :=
    hl.trans (RSOR.path_size kem _ _).symm
  have hp1 : (ch.c.pos : ℕ) + 1 = (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient
      (ch.c.short msg nm).receiver]).size :=
    ((RSOR.path_size kem _ _).trans (RSOR.take_length _ _ hl.le)).symm
  have hle0 : (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size ≤ geom.nrHops :=
    le_of_eq_of_le (RSOR.path_size kem _ _) ch.c.req.fwd.length_le
  have hcmd0 : ((RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])[(ch.c.pos :
      ℕ)]!).commands = [.recipient ch.c.req.receiver] :=
    (congrArg (·.commands) (RSOR.path_getElem! kem _ _ _ hpos)).trans (ite_eq_left hl)
  have hcmd1 : ((RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg
      nm).receiver])[(ch.c.pos : ℕ)]!).commands = [.recipient (ch.c.short msg nm).receiver] :=
    congrArg (·.commands) (RSOR.path_take_last kem geom ch.c.req.fwd _ ch.c.pos hpos)
  obtain ⟨hUs, hM⟩ := lastShift_spec geom kem kdfS streamS hvalid (RSOR.path kem ch.c.req.fwd
      [.recipient ch.c.req.receiver])
    (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg nm).receiver])
        (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) hp0 hle0 hp1
    (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _)
    (RSOR.kemHopKeys_mixSeeds kem kdfS geom ch.c.req.fwd _ _ r r' ch.c.pos hpos) _ _ hcmd0 hcmd1
  have hnl0 : ¬ (ch.c.pos : ℕ) + 1 < (RSOR.path kem ch.c.req.fwd [.recipient
      ch.c.req.receiver]).size := Nat.not_lt.2 (Nat.le_of_eq hp0.symm)
  have hnl1 : ¬ (ch.c.pos : ℕ) + 1 < (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient
      (ch.c.short msg nm).receiver]).size := Nat.not_lt.2 (Nat.le_of_eq hp1.symm)
  have hle1 : (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg
      nm).receiver]).size ≤ geom.nrHops := le_of_eq_of_le hp1.symm (le_of_eq_of_le hp0 hle0)
  have hs0 := relayFrontLast_size geom kem kdfS streamS hvalid (RSOR.path kem ch.c.req.fwd
      [.recipient ch.c.req.receiver])
    (RSOR.mixSeeds geom r r' ch.c.pos).1 ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem
        k.1.1 s).1)) (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient
        ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient
        (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos (ofVector
        (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) hp0 hle0 hUs
    (Util.Bytes.size_ofVector _) _ hcmd0
  have hs1 := relayFrontLast_size geom kem kdfS streamS hvalid (RSOR.path kem (ch.c.req.fwd.take
      (ch.c.pos + 1)) [.recipient (ch.c.short msg nm).receiver]) r'.1 ch.c.pos (ofVector
      (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
    (ofVector U) hp1 hle1 (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) _ hcmd1
  have eM1 : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
      r') (encapOf kem k.1.1 s).1 (ofVector U)) = relayFrontLast kem kdfS streamS geom (RSOR.path
      kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg nm).receiver]) r'.1
      ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
      (ofVector U) := by
    unfold shortMU relayFrontAt
    exact ite_eq_right hnl1
  have e1 : forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (RSOR.mixSeeds
      geom r r' ch.c.pos) (encapOf kem k.1.1 s).1
      (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg
          nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos (ofVector
          (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) = (shortMU kem cipher macS
          kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r') (encapOf kem k.1.1 s).1
          (ofVector U)) := by
    refine Eq.trans ?_ (hM.trans eM1.symm)
    unfold forwardMU relayFrontAt
    exact ite_eq_right hnl0
  have eM0 : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
      r') (encapOf kem k.1.1 s).1 (ofVector U)) = relayFrontLast kem kdfS streamS geom (RSOR.path
      kem ch.c.req.fwd [.recipient ch.c.req.receiver])
      (RSOR.mixSeeds geom r r' ch.c.pos).1 ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem
          k.1.1 s).1)) (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient
          ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient
          (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) := eM1.trans
          hM.symm
  have hsz : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
      r') (encapOf kem k.1.1 s).1 (ofVector U)).size = 2 + kem.ciphertextSize +
      geom.routingInfoLength := by
    rw [eM1]
    exact hs1
  have eB0 : forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
      (RSOR.mixSeeds geom r r' ch.c.pos) (lastShift geom kem kdfS streamS (RSOR.path kem
      ch.c.req.fwd [.recipient ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos +
      1)) [.recipient (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1
      ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U))
      = Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)
          ++ RSOR.body kem macS kdfS streamS geom ch.c.req r) := by
    unfold forwardBlockU relayBackAt
    rw [ite_eq_right hnl0]
    rfl
  have eB1 : shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
      r') (ofVector U)
      = Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)
          ++ RSOR.body kem macS kdfS streamS geom (ch.c.short msg nm) r') := by
    unfold shortBlockU relayBackAt
    exact congrArg (Util.Bytes.toVecN _) (ite_eq_right hnl1)
  obtain ⟨hB0, hbody⟩ := RSOR.zeroTag_block geom _ hb₀
  obtain ⟨hB1, -⟩ := RSOR.zeroTag_block geom _ hb₁
  rw [← eB0] at hB0 hbody
  rw [← eB1] at hB1
  have hsplit : RSOR.split geom (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16
      names ch (U, km, s, (r, msg, nm, r'), u, v))
      = (Util.Bytes.toVecN geom.headerLength ((shortMU kem cipher macS kdfS streamS geom hvalid
          hmactag h16 names ch (r, msg, nm, r') (encapOf kem k.1.1 s).1 (ofVector U))
          ++ ofVector (macS.mac (ofVector km) (shortMU kem cipher macS kdfS streamS geom hvalid
              hmactag h16 names ch (r, msg, nm, r') (encapOf kem k.1.1 s).1 (ofVector U)))), u) :=
    split_append geom _ u (by
      rw [ByteArray.size_append, hsz, Util.Bytes.size_ofVector, hmactag, hhdr]
      rfl)
  have honion : (forwardViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
      (RSOR.mixSeeds geom r r' ch.c.pos)
        (encapOf kem k.1.1 s).1 km (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd
            [.recipient ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
            [.recipient (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1
            ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U))
            u).onion
      = (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (U, km, s, (r,
          msg, nm, r'), u, v) (ofVector U')).1.onion := by
    unfold forwardViewU nextViewU nextLayer shortLayerU
    dsimp only
    rw [e1]
    exact congrArg (RSOR.split geom) (RSOR.wrapUp_mixSeeds kem cipher macS kdfS streamS geom
        ch.c.req.fwd
      _ _ r r' ch.c.pos hpos _)
  unfold forwardRunU
  dsimp only [KeyedDraw.c]
  rw [e1, honion]
  have hm1 := congrArg Prod.fst hsplit
  have hm2 := congrArg Prod.snd hsplit
  dsimp only at hm1 hm2
  have H := headerRelays_last_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
    ch.c hl next r (RSOR.split geom (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16
        names ch (U, km, s, (r, msg, nm, r'), u, v))) g
    (fun h => if h = .relay then k.2 else st.2.2 h) (encapOf kem k.1.1 s).1 km
    (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
        (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg
        nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos (ofVector
        (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) (ofVector U) (RSOR.path kem
        ch.c.req.fwd [.recipient ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos +
        1)) [.recipient (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1
        ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
    (ch.c.short msg nm).receiver
    (forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (RSOR.mixSeeds
        geom r r' ch.c.pos) (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd
        [.recipient ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
        [.recipient (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1
        ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)))
    (shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r')
        (ofVector U)) v
    hp0 hle0 hp1 hle1 hUs (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) hs0 hs1
    hcmd0 hcmd1 (hm1.trans (by rw [eM0])) (hm1.trans (by rw [eM1])) hB0 hB1 hv hbody
    (RSOR.msgOf_body kem macS kdfS streamS geom ch.c.req r) hr
  rw [hm1, hm2] at H
  exact congrArg (fun impl => (simulateQ impl (A.guess st.1
    (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (U, km, s, (r, msg,
        nm, r'), u, v) (ofVector U')).1.onion)).run' st.2.1) H

end ForwardFinal

end Cryptlib.Protocols.Sphinx.KEMSphinx
