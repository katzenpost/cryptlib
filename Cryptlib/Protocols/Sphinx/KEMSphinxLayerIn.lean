/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxLayer
import Cryptlib.Protocols.Sphinx.KEMSphinxTail

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

/-! # The packet entering a mix, from its keys and the packet leaving

`newKEMPacket_layer`: a packet built for a path of two or more hops is one layer around the
packet its first hop forwards. The layer uses the first hop's KEM ciphertext, its payload key
and IV, its MAC key, and the first `routingInfoLength` bytes of its header keystream. Everything
else in it is read off the forwarded packet. -/

section LayerIn

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- One layer: the header is the KEM ciphertext, the routing info `X` masked by the keystream
`ksA`, and the MAC over both. The payload is `inner` under the payload key. -/
def layerIn (ct : ByteArray) (kp : Vector UInt8 48) (iv : Vector UInt8 16) (km : Vector UInt8 32)
    (ksA X inner : ByteArray) : ByteArray :=
  v0AD ++ ct ++ xorBytes X ksA
    ++ ofVector (macS.mac (ofVector km) (v0AD ++ ct ++ xorBytes X ksA ++ ByteArray.empty))
    ++ cipher.encrypt kp.toArray (ofVector iv) inner

/-- The first hop's routing fragment reads only the second hop's ciphertext. -/
theorem kemRiFragment_zero_congr (path : Array PathHop) (ke : Array ByteArray) (mac : ByteArray)
    (n : Nat) :
    kemRiFragment kem geom path ke mac n 0
      = kemRiFragment kem geom path #[ByteArray.empty, ke[1]!] mac n 0 := by
  unfold kemRiFragment
  rfl

set_option maxHeartbeats 1000000 in
theorem newKEMPacket_layer (hvalid : geom.ValidForKEM kem)
    (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (path : Array PathHop)
    (payload pkt privKey : ByteArray) (h2 : 2 ≤ path.size)
    (hpp : kemSelfPublicKeyBytes kem privKey = (path[0]!).publicKey)
    (hrel : ∀ j, j < path.size → kem.Reliable (kem.stateFromSeed seeds[j]!))
    (hcmdnn : ∀ c ∈ (path[0]!).commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ (path[0]!).commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (hnk : newKEMPacket kem cipher macS kdfS streamS geom seeds filler path payload
      = Except.ok pkt) :
    ∃ (replayTag : Vector UInt8 32) (cmds : List RoutingCommand) (fwd : Vector UInt8 pkt.size)
      (ct ss frag : ByteArray),
      kemEncap kem (path[0]!).publicKey seeds[0]! = Except.ok (ct, ss) ∧
      unwrapKEM kem cipher macS kdfS streamS geom privKey pkt
        = Except.ok (none, replayTag, cmds, some fwd) ∧
      kemRiFragment kem geom path
          #[ByteArray.empty, (ofVector fwd).extract 2 (2 + kem.ciphertextSize)]
          ((ofVector fwd).extract (2 + kem.ciphertextSize + geom.routingInfoLength)
            (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)) path.size 0
        = Except.ok frag ∧
      pkt = layerIn cipher macS ct (deriveHopKeys kdfS ss).payloadEncryption
        (deriveHopKeys kdfS ss).headerEncryptionIV (deriveHopKeys kdfS ss).headerMAC
        ((streamS.keystream (ofVector (deriveHopKeys kdfS ss).headerEncryption)
          (ofVector (deriveHopKeys kdfS ss).headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0
          geom.routingInfoLength)
        (frag ++ (ofVector fwd).extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength))
        ((ofVector fwd).extract (payloadOffset kem geom) pkt.size) := by
  obtain ⟨hpaysize, hdr, sprpKeys, t, hcreate, ht0content, htstep, hpkteq⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom seeds filler path payload pkt hnk
  obtain ⟨hpne, hple, hesize, hfsize, kemElements, keys, riKeyStream, riPadding, s, hknsize,
    hkeysArrSize, hriKSarrSize, hriPadArrSize, hkeyscontent0, hriContent, hs0eq, hstep, hhdreq,
    hsprpeq⟩ :=
    createKEMHeader_unfold kem macS kdfS streamS geom seeds filler path hdr sprpKeys hcreate
  obtain ⟨hnnh, hperhopEq, hrouting, hheader, hpacket, -⟩ := id hvalid
  have hperhop : geom.nextNodeHopLength + kem.ciphertextSize ≤ geom.perHopRoutingInfoLength := by
    omega
  have hsprp : sprpKeys.size = path.size := by rw [hsprpeq]; simp
  have hkeyscontent : ∀ i (_hi : i < path.size), ∃ seed ss,
      kem.Reliable (kem.stateFromSeed seed) ∧
      kemEncap kem (path[i]!).publicKey seed = Except.ok (kemElements[i]!, ss) ∧
      keys[i]! = deriveHopKeys kdfS ss := by
    intro i hi
    obtain ⟨ct, ss, hkc, hcteq, hkeq⟩ := hkeyscontent0 i hi
    exact ⟨seeds[i]!, ss, hrel i hi, hcteq ▸ hkc, hkeq⟩
  have hksize : ∀ j (hj : j < kemElements.size), (kemElements[j]'hj).size = kem.ciphertextSize := by
    intro j hj
    obtain ⟨seed, ss, -, hkc, -⟩ := hkeyscontent j (by rwa [hknsize] at hj)
    have := kemEncap_size kem _ seed kemElements[j]! ss hkc
    rwa [getElem!_pos kemElements j hj] at this
  have hriKScontent : ∀ i (_hi : i < path.size), riKeyStream[i]! =
      (streamS.keystream (ofVector (keys[i]!).headerEncryption) (ofVector (keys[i]!).headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0
        ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) * geom.perHopRoutingInfoLength) :=
    fun i hi => (hriContent i hi).1
  have hriPadcontent : ∀ i (_hi : i < path.size), riPadding[i]! =
      (let totalRiLen := geom.routingInfoLength + geom.perHopRoutingInfoLength
       let ks := streamS.keystream (ofVector (keys[i]!).headerEncryption)
         (ofVector (keys[i]!).headerEncryptionIV) totalRiLen
       let ksLen := totalRiLen - (i + 1) * geom.perHopRoutingInfoLength
       let thisPad0 := ks.extract ksLen totalRiLen
       if i > 0 then
         xorBytes (thisPad0.extract 0 riPadding[i - 1]!.size) riPadding[i - 1]!
           ++ thisPad0.extract riPadding[i - 1]!.size thisPad0.size
       else thisPad0) :=
    fun i hi => (hriContent i hi).2
  have hle : ∀ j (_hj : j < path.size), (j + 1) * geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength + geom.perHopRoutingInfoLength := by
    intro j hj
    rw [hrouting]
    have h1 : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.perHopRoutingInfoLength * geom.nrHops := by
      rw [Nat.mul_comm geom.perHopRoutingInfoLength geom.nrHops]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  have hpadsize : ∀ i (_hi : i < path.size),
      riPadding[i]!.size = (i + 1) * geom.perHopRoutingInfoLength := by
    intro i
    induction i with
    | zero =>
      intro hi
      have hc := hriPadcontent 0 hi
      dsimp only at hc
      rw [if_neg (by omega)] at hc
      rw [hc, ByteArray.size_extract, streamS.keystream_size]
      have := hle 0 hi
      omega
    | succ i ih =>
      intro hi
      have hc := hriPadcontent (i + 1) hi
      dsimp only at hc
      rw [if_pos (by omega : i + 1 > 0)] at hc
      have hihsize := ih (by omega)
      have hthis0size : ((streamS.keystream (ofVector keys[i + 1]!.headerEncryption)
          (ofVector keys[i + 1]!.headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract
          (geom.routingInfoLength + geom.perHopRoutingInfoLength
            - (i + 1 + 1) * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size
          = (i + 1 + 1) * geom.perHopRoutingInfoLength := by
        rw [ByteArray.size_extract, streamS.keystream_size]
        have := hle (i + 1) hi
        omega
      rw [hc]
      simp only [ByteArray.size_append, size_xorBytes, ByteArray.size_extract, Nat.add_sub_cancel]
        at *
      omega
  have hs0size : (s 0).1.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength := by
    rw [hs0eq]
    split
    · next hc => rw [hfsize hc]
    · next hc =>
      have heq : geom.nrHops - path.size = 0 := by omega
      rw [heq, Nat.zero_mul]
      rfl
  have ht0size : (t 0).size = geom.payloadTagLength + geom.forwardPayloadLength := by
    rw [ht0content, ByteArray.size_append, hpaysize]
    simp [ByteArray.size]
  have hsprpkey : ∀ i (hi : i < sprpKeys.size), (sprpKeys[i]'hi).key = keys[i]!.payloadEncryption ∧
      (sprpKeys[i]'hi).iv = keys[i]!.headerEncryptionIV := by
    intro i hi
    simp only [hsprpeq, Array.getElem_ofFn]
    trivial
  have htsize := newKEMPacket_payload_size_trace cipher sprpKeys t htstep
  obtain ⟨replayTag, cmds, hnewsize, hunwrap, -⟩ := unwrapKEM_hopPacket_nonterminal kem cipher
    macS kdfS streamS geom path keys kemElements riKeyStream riPadding sprpKeys path.size s t
    hvalid hmactag hs0size hstep hknsize hksize hpadsize hriKScontent hriPadcontent
    htsize ht0size htstep hsprpkey hsprp hple h16 0 (by omega) hcmdnn hcmdnh privKey hpp
    (hkeyscontent 0 (by omega))
  have hsl := hopPacket_slices kem macS geom path keys kemElements riKeyStream riPadding cipher
    sprpKeys path.size s t hvalid hmactag hs0size hstep hknsize hksize hpadsize htsize ht0size
    hsprp hple 1 (by omega)
  obtain ⟨-, hsl1, hsl2, hsl3, hsl4⟩ := hsl
  obtain ⟨ct, ss, hkc, hcteq, hkeq⟩ := hkeyscontent0 0 (by omega)
  obtain ⟨frag, hfrag, hsn1, hsn2⟩ := hstep (path.size - 1) (by omega)
  have e0 : path.size - 1 - (path.size - 1) = 0 := by omega
  have e1 : path.size - 1 + 1 = path.size := by omega
  rw [e0] at hfrag hsn1 hsn2
  rw [e1] at hsn1 hsn2
  rw [if_neg (lt_irrefl 0)] at hsn2
  rw [if_pos Nat.one_pos] at hsl2
  have hssize := createKEMHeader_s_size kem macS geom path keys kemElements riKeyStream riPadding
    path.size s hperhop hnnh hknsize hksize hstep
  have hs1size : (s (path.size - 1)).1.size
      = geom.routingInfoLength - geom.perHopRoutingInfoLength := by
    have h1 := hs0size ▸ (hssize (path.size - 1) (by omega)).1
    rw [h1, ← Nat.add_mul, hrouting,
      show geom.nrHops - path.size + (path.size - 1) = geom.nrHops - 1 from by omega,
      Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
  have hinner : (s (path.size - 1)).1
      = (hopPacket kemElements riPadding s t path.size 1).extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength) := by
    have h1 := congrArg (fun x => x.extract 0 (s (path.size - 1)).1.size) hsl2
    simp only [ByteArray.extract_extract] at h1
    rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (le_refl _), ByteArray.extract_zero_size] at h1
    have hpRI : geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
      rw [hrouting]; exact Nat.le_mul_of_pos_right _ (by omega)
    rw [← h1, hs1size]
    congr 1
    all_goals omega
  have ht1 := htstep (path.size - 1) (by omega)
  rw [e1] at ht1
  unfold payloadEncryptStep at ht1
  dsimp only at ht1
  rw [show sprpKeys.size - 1 - (path.size - 1) = 0 from by omega,
    getElem!_pos sprpKeys 0 (by omega), (hsprpkey 0 (by omega)).1, (hsprpkey 0 (by omega)).2, hkeq]
    at ht1
  have hrik0 := hriKScontent 0 (by omega)
  rw [show geom.routingInfoLength + geom.perHopRoutingInfoLength
      - (0 + 1) * geom.perHopRoutingInfoLength = geom.routingInfoLength from by omega, hkeq]
    at hrik0
  have hpkteq2 : pkt = hopPacket kemElements riPadding s t path.size 0 := by
    rw [hpkteq, hhdreq]
    unfold hopPacket
    rw [Nat.sub_zero, if_neg (lt_irrefl 0), ByteArray.append_empty, hsprp]
  subst hpkteq2
  refine ⟨replayTag, cmds,
    ⟨(hopPacket kemElements riPadding s t path.size (0 + 1)).data, hnewsize⟩, ct, ss, frag, hkc,
    hunwrap, ?_, ?_⟩
  · show kemRiFragment kem geom path
        #[ByteArray.empty, (hopPacket kemElements riPadding s t path.size 1).extract 2
          (2 + kem.ciphertextSize)]
        ((hopPacket kemElements riPadding s t path.size 1).extract
          (2 + kem.ciphertextSize + geom.routingInfoLength)
          (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)) path.size 0 = Except.ok frag
    rw [hsl1, hsl3, ← kemRiFragment_zero_congr]
    exact hfrag
  · show hopPacket kemElements riPadding s t path.size 0 = layerIn cipher macS ct _ _ _ _
      (frag ++ (hopPacket kemElements riPadding s t path.size 1).extract (2 + kem.ciphertextSize)
        (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength))
      ((hopPacket kemElements riPadding s t path.size 1).extract (payloadOffset kem geom)
        (hopPacket kemElements riPadding s t path.size 0).size)
    rw [← hinner, ← hnewsize]
    have hsl4' : (hopPacket kemElements riPadding s t path.size (0 + 1)).extract
        (payloadOffset kem geom) (hopPacket kemElements riPadding s t path.size (0 + 1)).size
        = t (path.size - 1) := hsl4
    rw [hsl4']
    unfold layerIn
    rw [← hrik0, ← hsn1, ← ht1, ← hcteq, ← hkeq, ← hsn2]
    unfold hopPacket
    rw [Nat.sub_zero, if_neg (lt_irrefl 0), ByteArray.append_empty]

end LayerIn

end Cryptlib.Protocols.Sphinx.KEMSphinx
