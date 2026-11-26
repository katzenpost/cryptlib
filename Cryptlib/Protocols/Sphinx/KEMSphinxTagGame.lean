/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxHop

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
open Cryptlib.Util.Bytes (ofVector)

/-! # The final hop rejects a changed payload

The payload of a packet is checked once, at the final hop, by the zero tag inside the decrypted
payload. `tagGame` is the game for that check. The final hop is honest. The adversary is given
its public key and its oracle, chooses the hop's commands, the filler and the message, and is
given the packet as it arrives at the final hop. It wins if it returns a packet with the same
header and a different payload that the final hop accepts.

`tagGame_le` bounds its chance of winning by the KEM and KDF terms of `hopChain_le`, the chance
that the encapsulation seed is not `Reliable`, and the chance of winning `tagForgeExp`, a game
about the payload cipher alone.

Together with `procWith_payload_congr` this is the one-bit tagging channel: a mix forwards a
packet whose payload was changed, and the change shows only at the final hop, as a rejection. -/

section Helpers

variable {α β : Type}

/-- `prEvent_bind_le_add_of_bad` with an inequality off the bad set. -/
theorem prEvent_bind_le_add_of_bad_le (mx : ProbComp α) (F G : α → ProbComp β) (bad : α → Prop)
    (q : β → Prop) (h : ∀ x, ¬ bad x → Pr{let y ← F x}[q y] ≤ Pr{let y ← G x}[q y]) :
    Pr{let y ← mx >>= F}[q y] ≤ Pr{let y ← mx >>= G}[q y] + Pr{let x ← mx}[bad x] := by
  classical
  refine (prEvent_bind_le_add_of_bad mx F (fun x => if bad x then G x else F x) bad
    (fun x hx => by simp [hx]) q).trans (add_le_add ?_ le_rfl)
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun x => ?_
  by_cases hx : bad x
  · simp [hx]
  · simpa [hx] using h x hx

/-- Two games that agree off a bad draw differ by at most the chance of a bad draw. -/
theorem abs_prEvent_bind_sub_le_bad (mx : ProbComp α) (F G : α → ProbComp Bool) (bad : α → Prop)
    (h : ∀ x, ¬ bad x → F x = G x) :
    |(Pr{let y ← mx >>= F}[y = true]).toReal - (Pr{let y ← mx >>= G}[y = true]).toReal|
      ≤ (Pr{let x ← mx}[bad x]).toReal := by
  have h12 := prEvent_bind_le_add_of_bad_le mx F G bad (· = true) fun x hx => by rw [h x hx]
  have h21 := prEvent_bind_le_add_of_bad_le mx G F bad (· = true) fun x hx => by rw [h x hx]
  have r12 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h12
  have r21 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h21
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at r12 r21
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

theorem prEvent_pure_bool_mono (a b : Bool) (h : a = true → b = true) :
    Pr{let x ← (pure a : ProbComp Bool)}[x = true] ≤ Pr{let x ← (pure b : ProbComp Bool)}[x = true] := by
  rw [prEvent_pure, prEvent_pure]
  by_cases ha : a = true
  · simp [ha, h ha]
  · simp [ha]

theorem extract_zero_append_extract (a : ByteArray) (n : Nat) :
    a.extract 0 n ++ a.extract n a.size = a := by
  ext1
  simp

end Helpers

section TagGame

open PRGScheme

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- Bytes-level encapsulation to an encoded public key, in terms of `encapOf`. -/
theorem kemEncap_encapOf (pk : kem.PublicKey) (s : Vector UInt8 32) (ct ss : ByteArray)
    (h : kemEncap kem (ofVector (kem.encodePublicKey pk)) s = .ok (ct, ss)) :
    ct = ofVector (kem.encodeCiphertext (encapOf kem pk s).1)
      ∧ ss = ofVector (kem.encodePlaintext (encapOf kem pk s).2) := by
  unfold kemEncap at h
  unfold encapOf
  rw [Cryptlib.Protocols.Sphinx.Common.toVecN_ofVector, kem.decode_encode_pub] at h
  dsimp only at h
  cases hr : kem.encap pk (kem.stateFromSeed s) with
  | ok r a =>
    rw [hr] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩
  | error a b => rw [hr] at h; cases h

/-- The final hop accepts a forward packet. -/
def accepts (sk : ByteArray) (r : ByteArray) : Bool :=
  match procWith kem cipher macS kdfS streamS geom (kemDecap kem sk) r with
  | some (some _, _, cmds, _) => !hasSurbReply cmds
  | _ => false

/-- The score of the game in terms of the final hop's keys: `r` has the challenge's header, is
not the challenge, and its payload decrypts to a zero tag. -/
def tagFinal (ct : ByteArray) (t : KeyTuple) (filler : ByteArray) (hop : PathHop)
    (payload r : ByteArray) : Bool :=
  decide (r.extract 0 (hdr1 kem macS streamS geom ct t.2.1 t.2.2.1 t.2.2.2 filler hop).size
      = hdr1 kem macS streamS geom ct t.2.1 t.2.2.1 t.2.2.2 filler hop)
    && decide (r ≠ pkt1 kem cipher macS streamS geom ct t filler hop payload)
    && tagOK geom (cipher.decrypt t.1.toArray (ofVector t.2.1)
        (r.extract (hdr1 kem macS streamS geom ct t.2.1 t.2.2.1 t.2.2.2 filler hop).size r.size))

/-- The adversary chooses the final hop's record (its public key is replaced by the generated
one), the filler and the message. The challenge is the one-hop packet. -/
def tagSetup : HopSetup kem ByteArray ByteArray where
  Ch := PathHop × ByteArray × ByteArray
  Oth := Unit
  drawOth _ := pure ()
  view pk ch _ c t := pkt1 kem cipher macS streamS geom (ofVector (kem.encodeCiphertext c)) t
    ch.2.1 (honestHop kem ch.1 pk) ch.2.2
  final pk ch _ c t r := tagFinal kem cipher macS streamS geom (ofVector (kem.encodeCiphertext c)) t
    ch.2.1 (honestHop kem ch.1 pk) ch.2.2 r

variable {kem cipher macS streamS geom}
variable (A : HopAdversary (tagSetup kem cipher macS streamS geom))

/-- The game after the challenger's draws: build the packet, run the adversary's second phase,
and score its answer. -/
def tagPost (ks : Vector UInt8 32) (cs : (PathHop × ByteArray × ByteArray) × A.St)
    (s : Vector UInt8 32) : ProbComp Bool :=
  match newKEMPacket kem cipher macS kdfS streamS geom #[s] cs.1.2.1
      #[honestHop kem cs.1.1 (keygenOf kem ks).1] cs.1.2.2 with
  | .error _ => return false
  | .ok pkt => do
    let r ← simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem ks).2
        (encapOf kem (keygenOf kem ks).1 s).1) (A.post cs.2 pkt)
    return (decide (r.extract 0 (payloadOffset kem geom) = pkt.extract 0 (payloadOffset kem geom))
      && decide (r ≠ pkt) && accepts kem cipher macS kdfS streamS geom (skBytes kem ks) r)

/-- `tagPost` with the packet in closed form and the score in terms of the keys the KDF derives
from the encapsulated secret. -/
def tagKeyPost (ks : Vector UInt8 32) (cs : (PathHop × ByteArray × ByteArray) × A.St)
    (s : Vector UInt8 32) : ProbComp Bool := do
  let r ← simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem ks).2
      (encapOf kem (keygenOf kem ks).1 s).1)
    (A.post cs.2 (pkt1 kem cipher macS streamS geom
      (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem ks).1 s).1))
      ((hopKeysPRG kem kdfS).gen (encapOf kem (keygenOf kem ks).1 s).2)
      cs.1.2.1 (honestHop kem cs.1.1 (keygenOf kem ks).1) cs.1.2.2))
  return tagFinal kem cipher macS streamS geom
    (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem ks).1 s).1))
    ((hopKeysPRG kem kdfS).gen (encapOf kem (keygenOf kem ks).1 s).2)
    cs.1.2.1 (honestHop kem cs.1.1 (keygenOf kem ks).1) cs.1.2.2 r

/-- **The game.** The final hop's key pair is generated. The adversary, with the hop's oracle,
chooses the hop's record, the filler and the message. A packet is built for the hop. The
adversary, with the oracle now refusing packets that carry the challenge's KEM ciphertext,
returns a packet. It wins if that packet has the challenge's header, is not the challenge, and
the final hop accepts it as a forward packet. -/
def tagGame : ProbComp Bool := do
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  tagPost kdfS A ks cs s

/-- The draws of the game up to the challenge. -/
def tagDraw : ProbComp (Vector UInt8 32 × ((PathHop × ByteArray × ByteArray) × A.St) × Vector UInt8 32) := do
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  return (ks, cs, s)

/-- The draws the theorem does not cover: the generated private key's own public key is not the
generated public key, or the encapsulation seed is not `Reliable`. -/
def tagBad (kem : KEM) (ks s : Vector UInt8 32) : Prop :=
  ¬ (kemSelfPublicKeyBytes kem (skBytes kem ks) = pkBytes kem ks
      ∧ kem.Reliable (kem.stateFromSeed s))

/-- An adversary against the payload cipher's tag: given the IV, it chooses a message; given the
encryption of the zero tag and the message under a uniform key, it returns a ciphertext. -/
structure TagForgeAdversary where
  St : Type
  choose : Vector UInt8 16 → ProbComp (ByteArray × St)
  forge : St → ByteArray → ProbComp ByteArray

/-- The adversary wins if its ciphertext is not the one it was given and decrypts to a zero
tag. For a strong pseudorandom permutation this happens with probability about
`2^-(8 * payloadTagLength)`. -/
def tagForgeExp (cipher : WideBlockCipher) (geom : Geometry) (B : TagForgeAdversary) :
    ProbComp Bool := do
  let k ← $ᵗ (Vector UInt8 48)
  let iv ← $ᵗ (Vector UInt8 16)
  let ms ← B.choose iv
  let c' ← B.forge ms.2 (cipher.encrypt k.toArray (ofVector iv)
    ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ ms.1))
  return (decide (c' ≠ cipher.encrypt k.toArray (ofVector iv)
      ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ ms.1))
    && tagOK geom (cipher.decrypt k.toArray (ofVector iv) c'))

/-- The tag adversary that `A` gives: it draws the header keys and the key pair itself, builds
the header, and appends the ciphertext it is given. -/
def tagForgeAdv : TagForgeAdversary where
  St := Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 32
    × ((PathHop × ByteArray × ByteArray) × A.St) × Vector UInt8 32
  choose iv := do
    let km ← $ᵗ (Vector UInt8 32)
    let ke ← $ᵗ (Vector UInt8 32)
    let ks ← $ᵗ (Vector UInt8 32)
    let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
      (A.pre (pkBytes kem ks))
    let s ← $ᵗ (Vector UInt8 32)
    return (cs.1.2.2, (iv, km, ke, ks, cs, s))
  forge st c := do
    let r ← simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem st.2.2.2.1).2
        (encapOf kem (keygenOf kem st.2.2.2.1).1 st.2.2.2.2.2).1)
      (A.post st.2.2.2.2.1.2
        (hdr1 kem macS streamS geom
            (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem st.2.2.2.1).1 st.2.2.2.2.2).1))
            st.1 st.2.1 st.2.2.1 st.2.2.2.2.1.1.2.1
            (honestHop kem st.2.2.2.2.1.1.1 (keygenOf kem st.2.2.2.1).1) ++ c))
    return r.extract (hdr1 kem macS streamS geom
        (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem st.2.2.2.1).1 st.2.2.2.2.2).1))
        st.1 st.2.1 st.2.2.1 st.2.2.2.2.1.1.2.1
        (honestHop kem st.2.2.2.2.1.1.1 (keygenOf kem st.2.2.2.1).1)).size r.size

variable [SampleableType kem.Plaintext]

/-- With uniform keys at the final hop, winning the game is winning the tag game of the payload
cipher. -/
theorem hopIdeal_le_tagForge :
    Pr{let x ← hopIdeal cipher macS kdfS streamS geom A}[x = true]
      ≤ Pr{let x ← tagForgeExp cipher geom (tagForgeAdv kdfS A)}[x = true] := by
  have e : hopIdeal cipher macS kdfS streamS geom A =ᵈ (do
      let k ← $ᵗ (Vector UInt8 48)
      let iv ← $ᵗ (Vector UInt8 16)
      let km ← $ᵗ (Vector UInt8 32)
      let ke ← $ᵗ (Vector UInt8 32)
      let ks ← $ᵗ (Vector UInt8 32)
      let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
        (A.pre (pkBytes kem ks))
      let s ← $ᵗ (Vector UInt8 32)
      let r ← simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem ks).2
          (encapOf kem (keygenOf kem ks).1 s).1)
        (A.post cs.2 (pkt1 kem cipher macS streamS geom
          (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem ks).1 s).1)) (k, iv, km, ke)
          cs.1.2.1 (honestHop kem cs.1.1 (keygenOf kem ks).1) cs.1.2.2))
      return tagFinal kem cipher macS streamS geom
        (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem ks).1 s).1)) (k, iv, km, ke)
        cs.1.2.1 (honestHop kem cs.1.1 (keygenOf kem ks).1) cs.1.2.2 r) := by
    unfold hopIdeal hopGame
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    simp only [tagSetup, SampleableType.uniformSample_prod_eq_bind, bind_assoc, pure_bind]
    exact EvalDistEq.rfl
  rw [e.prEvent_eq (fun x => x = true)]
  unfold tagForgeExp tagForgeAdv
  simp only [bind_assoc, pure_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun k => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun iv => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun km => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun ke => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun ks => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun cs => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun s => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
  refine prEvent_pure_bool_mono _ _ fun h => ?_
  unfold tagFinal at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hh, hne⟩, htag⟩ := h
  refine ⟨fun hc => hne ?_, htag⟩
  have h3 := extract_zero_append_extract r (hdr1 kem macS streamS geom
    (ofVector (kem.encodeCiphertext (encapOf kem (keygenOf kem ks).1 s).1)) iv km ke cs.1.2.1
    (honestHop kem cs.1.1 (keygenOf kem ks).1)).size
  rw [hh, hc] at h3
  exact h3.symm

/-- The game with the final hop's keys derived from the encapsulated secret is won at least as
often as the real game, off the bad draws. -/
theorem tagGame_le_hopReal (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength) :
    Pr{let x ← tagGame kdfS A}[x = true]
      ≤ Pr{let x ← hopReal cipher macS kdfS streamS geom A}[x = true]
        + Pr{let d ← tagDraw kdfS A}[tagBad kem d.1 d.2.2] := by
  have hr : tagGame kdfS A = tagDraw kdfS A >>= fun d => tagPost kdfS A d.1 d.2.1 d.2.2 := by
    unfold tagGame tagDraw
    simp only [bind_assoc, pure_bind]
  have e : hopReal cipher macS kdfS streamS geom A
      =ᵈ tagDraw kdfS A >>= fun d => tagKeyPost kdfS A d.1 d.2.1 d.2.2 := by
    unfold hopReal hopGame tagDraw tagKeyPost
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    simp only [tagSetup, bind_assoc, pure_bind]
    exact EvalDistEq.rfl
  rw [hr, e.prEvent_eq (fun x => x = true)]
  refine prEvent_bind_le_add_of_bad_le (tagDraw kdfS A) (fun d => tagPost kdfS A d.1 d.2.1 d.2.2)
    (fun d => tagKeyPost kdfS A d.1 d.2.1 d.2.2) (fun d => tagBad kem d.1 d.2.2)
    (fun x => x = true) fun d hd => ?_
  obtain ⟨ks, cs, s⟩ := d
  unfold tagBad at hd
  rw [not_not] at hd
  obtain ⟨hself, hrel⟩ := hd
  dsimp only at hself hrel ⊢
  unfold tagPost tagKeyPost
  cases hnk : newKEMPacket kem cipher macS kdfS streamS geom #[s] cs.1.2.1
      #[honestHop kem cs.1.1 (keygenOf kem ks).1] cs.1.2.2 with
  | error e =>
    dsimp only
    rw [prEvent_pure]
    simp
  | ok pkt =>
    dsimp only
    obtain ⟨ct, ss, sprp, henc, hhdr, hpkt⟩ :=
      newKEMPacket_one kem cipher macS kdfS streamS geom _ _ _ _ _ hnk
    obtain ⟨hct, hss⟩ := kemEncap_encapOf kem _ _ _ _ henc
    have hgen : (hopKeysPRG kem kdfS).gen (encapOf kem (keygenOf kem ks).1 s).2
        = keyTuple (deriveHopKeys kdfS ss) := by rw [hss]; rfl
    rw [hgen, ← hct]
    obtain ⟨hdr, hhd⟩ : ∃ hdr, hdr = hdr1 kem macS streamS geom ct
        (deriveHopKeys kdfS ss).headerEncryptionIV (deriveHopKeys kdfS ss).headerMAC
        (deriveHopKeys kdfS ss).headerEncryption cs.1.2.1
        (honestHop kem cs.1.1 (keygenOf kem ks).1) := ⟨_, rfl⟩
    rw [← hhd] at hhdr
    have hadL : adLength = 2 := rfl
    have hv0 : v0AD.size = 2 := rfl
    have hmacL : macLength = 32 := rfl
    obtain ⟨-, -, -, hheader, -, -⟩ := id hvalid
    have hH : hdr.size = payloadOffset kem geom := by
      rw [createKEMHeader_hdr_size kem macS kdfS streamS geom _ _ _ _ _ hvalid hmactag hhdr,
        hheader, hadL]
    have hctsize : ct.size = kem.ciphertextSize := kemEncap_size kem _ _ ct ss henc
    have hpk : pkt = hdr ++ cipher.encrypt (deriveHopKeys kdfS ss).payloadEncryption.toArray
        (ofVector (deriveHopKeys kdfS ss).headerEncryptionIV)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ cs.1.2.2) := by
      rw [hpkt, hhd]; rfl
    have hdec : kemDecap kem (skBytes kem ks) ct = .ok ss :=
      kemEncap_kemDecap_of_honest kem (skBytes kem ks) s ct ss hrel (by rw [hself]; exact henc)
    have hslice : pkt.extract 2 (2 + kem.ciphertextSize) = ct := by
      rw [hpk, Cryptlib.Util.Bytes.extract_append_of_le _ _ (by rw [hH]; unfold payloadOffset; omega),
        hhd]
      unfold hdr1
      dsimp only
      rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
          simp only [ByteArray.size_append, hv0, hctsize]; omega),
        Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
          simp only [ByteArray.size_append, hv0, hctsize]; omega),
        Cryptlib.Util.Bytes.extract_append_of_ge _ _ (by rw [hv0])]
      rw [hv0, ← hctsize]
      simp
    subst hpkt
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
    refine prEvent_pure_bool_mono _ _ fun h => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hh, hne⟩, hacc⟩ := h
    have hT : tagFinal kem cipher macS streamS geom ct (keyTuple (deriveHopKeys kdfS ss)) cs.1.2.1
        (honestHop kem cs.1.1 (keygenOf kem ks).1) cs.1.2.2 r
        = (decide (r.extract 0 hdr.size = hdr)
          && decide (r ≠ pkt1 kem cipher macS streamS geom ct (keyTuple (deriveHopKeys kdfS ss))
              cs.1.2.1 (honestHop kem cs.1.1 (keygenOf kem ks).1) cs.1.2.2)
          && tagOK geom (cipher.decrypt (deriveHopKeys kdfS ss).payloadEncryption.toArray
              (ofVector (deriveHopKeys kdfS ss).headerEncryptionIV)
              (r.extract hdr.size r.size))) := by rw [hhd]; rfl
    rw [hT]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨?_, hne⟩, ?_⟩
    · rw [hH, hh, hpk, Cryptlib.Util.Bytes.extract_append_of_le _ _ (le_of_eq hH.symm), ← hH]
      exact ByteArray.extract_zero_size
    · have hrs : r.extract 2 (2 + kem.ciphertextSize) = ct := by
        rw [extract_of_prefix_eq hh 2 (2 + kem.ciphertextSize) (by unfold payloadOffset; omega)]
        exact hslice
      unfold accepts at hacc
      cases hp : procWith kem cipher macS kdfS streamS geom (kemDecap kem (skBytes kem ks)) r with
      | none => rw [hp] at hacc; cases hacc
      | some x =>
        obtain ⟨p, t, cmds, f⟩ := x
        rw [hp] at hacc
        cases p with
        | none => cases hacc
        | some p =>
          have hs : hasSurbReply cmds = false := by simpa using hacc
          rw [hH]
          exact procWith_final_tag kem cipher macS kdfS streamS geom _ r ss p t cmds f
            (by rw [hrs]; exact hdec) hp hs

/-- **The final hop rejects a changed payload.** The adversary's chance of having the honest
final hop accept a packet with the challenge's header and a different payload is at most the sum
of:

- the advantage of `hopKEMAdv` against the KEM, with a decapsulation oracle that refuses the
  challenge ciphertext;
- the advantage of `hopKeyAdv` in telling the four keys the KDF derives from a uniform shared
  secret from uniform keys;
- the chance that `tagForgeAdv` wins the tag game of the payload cipher;
- the probability of the bad draws.

Nothing is assumed of the MAC: the adversary keeps the header. -/
theorem tagGame_le (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength) :
    (Pr{let x ← tagGame kdfS A}[x = true]).toReal
    ≤ |(Pr{let x ← kemCCAExp (hopKEMAdv cipher macS kdfS streamS geom A) true}[x = true]).toReal
        - (Pr{let x ← kemCCAExp (hopKEMAdv cipher macS kdfS streamS geom A) false}[x = true]).toReal|
      + |(Pr{let x ← prgRealExperiment (hopKeysPRG kem kdfS)
                        (hopKeyAdv cipher macS kdfS streamS geom A)}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment
                        (hopKeyAdv cipher macS kdfS streamS geom A)}[x = true]).toReal|
      + (Pr{let x ← tagForgeExp cipher geom (tagForgeAdv kdfS A)}[x = true]).toReal
      + (Pr{let d ← tagDraw kdfS A}[tagBad kem d.1 d.2.2]).toReal := by
  have h1 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩)
    (tagGame_le_hopReal kdfS A hvalid hmactag)
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at h1
  have h2 := hopChain_le cipher macS kdfS streamS geom A
  have h3 := ENNReal.toReal_mono (prEvent_ne_top _) (hopIdeal_le_tagForge kdfS A)
  have h4 := le_abs_self
    ((Pr{let x ← hopReal cipher macS kdfS streamS geom A}[x = true]).toReal
      - (Pr{let x ← hopIdeal cipher macS kdfS streamS geom A}[x = true]).toReal)
  linarith

end TagGame

end Cryptlib.Protocols.Sphinx.KEMSphinx
