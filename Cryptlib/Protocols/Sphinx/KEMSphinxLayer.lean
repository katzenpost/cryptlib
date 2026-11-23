/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTailOracle

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

/-! # Payload tagging

A mix checks the MAC over the header only. The payload is checked once, at the final hop, by the
zero tag inside the decrypted payload. This file states what follows for a packet whose payload
was changed in flight.

`procWith_payload_congr`: a mix forwards such a packet exactly as it forwards the original. The
replay tag, the commands and the forwarded header are the same. So a mix without a replay cache
links the two packets, which is the attack of Kuhn, Beck and Strufe (Section V) on layer
unlinkability. With a replay cache the second packet is refused, since the replay tag is the
same. -/

section Tagging

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- The length of everything before the payload. -/
abbrev payloadOffset : Nat := 2 + kem.ciphertextSize + geom.routingInfoLength + macLength

theorem extract_of_prefix_eq {a b : ByteArray} {n : Nat} (h : a.extract 0 n = b.extract 0 n)
    (i j : Nat) (hj : j ≤ n) : a.extract i j = b.extract i j := by
  have h' := congrArg (fun x => x.extract i j) h
  simp only [ByteArray.extract_extract] at h'
  rwa [Nat.zero_add, Nat.zero_add, Nat.min_eq_left hj] at h'

/-- A mix forwards a packet with a changed payload as it forwards the original: same replay tag,
same commands, same forwarded header. -/
theorem procWith_payload_congr (dec : ByteArray → Except String ByteArray) (pkt pkt' : ByteArray)
    (hsz : pkt'.size = pkt.size)
    (hhdr : pkt'.extract 0 (payloadOffset kem geom) = pkt.extract 0 (payloadOffset kem geom))
    (tag : Vector UInt8 32) (cmds : List RoutingCommand) (fwd : ByteArray)
    (h : procWith kem cipher macS kdfS streamS geom dec pkt = some (none, tag, cmds, some fwd)) :
    ∃ fwd', procWith kem cipher macS kdfS streamS geom dec pkt' = some (none, tag, cmds, some fwd')
      ∧ fwd'.extract 0 (payloadOffset kem geom) = fwd.extract 0 (payloadOffset kem geom) := by
  have hmacL : macLength = 32 := rfl
  have e0 := extract_of_prefix_eq hhdr 0 2 (by unfold payloadOffset; omega)
  have e1 := extract_of_prefix_eq hhdr 2 (2 + kem.ciphertextSize) (by unfold payloadOffset; omega)
  have e2 := extract_of_prefix_eq hhdr 0 (2 + kem.ciphertextSize + geom.routingInfoLength)
    (by unfold payloadOffset; omega)
  have e3 := extract_of_prefix_eq hhdr (2 + kem.ciphertextSize + geom.routingInfoLength)
    (2 + kem.ciphertextSize + geom.routingInfoLength + macLength) (by unfold payloadOffset; omega)
  have e4 := extract_of_prefix_eq hhdr (2 + kem.ciphertextSize)
    (2 + kem.ciphertextSize + geom.routingInfoLength) (by unfold payloadOffset; omega)
  unfold procWith unwrapKEMWith at h ⊢
  dsimp only at h ⊢
  simp only [e0, e1, e2, e3, e4]
  by_cases h1 : pkt.size < 2 + kem.ciphertextSize + geom.routingInfoLength + macLength
  · rw [dif_pos h1] at h; cases h
  rw [dif_neg h1] at h; rw [dif_neg (hsz ▸ h1)]
  by_cases h2 : (pkt.extract 0 2).data ≠ v0AD.data
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h ⊢
  cases hd : dec (pkt.extract 2 (2 + kem.ciphertextSize)) with
  | error e => rw [hd] at h; cases h
  | ok ss =>
    rw [hd] at h
    dsimp only [Bind.bind, Except.bind] at h ⊢
    by_cases h3 : (ofVector (macS.mac (ofVector (deriveHopKeys kdfS ss).headerMAC)
        (pkt.extract 0 (2 + kem.ciphertextSize + geom.routingInfoLength)))).data
        ≠ (pkt.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
          (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)).data
    · rw [if_pos h3] at h; cases h
    rw [if_neg h3] at h ⊢
    generalize parseAll _ = r at h ⊢
    cases r with
    | error e => cases h
    | ok cmds0 =>
      dsimp only at h ⊢
      generalize List.findSome? _ cmds0 = o at h ⊢
      cases o with
      | none =>
        dsimp only at h
        split_ifs at h <;> cases h
      | some nm =>
        dsimp only [pure, Except.pure] at h ⊢
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨_, rfl, ?_⟩
        have hv0 : v0AD.size = 2 := rfl
        show ((_ : ByteArray) ++ _).extract 0 _ = ((_ : ByteArray) ++ _).extract 0 _
        refine (Cryptlib.Util.Bytes.extract_append_of_le _ _ ?_).trans
          (Cryptlib.Util.Bytes.extract_append_of_le _ _ ?_).symm
        all_goals
          have hpad : (⟨Array.replicate geom.perHopRoutingInfoLength (0 : UInt8)⟩ : ByteArray).size
              = geom.perHopRoutingInfoLength := Array.size_replicate
          simp only [ByteArray.size_append, size_xorBytes, Util.Bytes.size_ofVector,
            ByteArray.size_extract, hpad, hv0, payloadOffset, hmacL, Nat.min_self] at h1 ⊢
          omega

/-- Whether the commands carry a SURB reply. A reply packet's payload is not checked by the
final hop, so the theorems below are about forward packets. -/
def hasSurbReply (cmds : List RoutingCommand) : Bool :=
  cmds.any fun
    | .surbReply _ => true
    | _ => false

/-- The final hop's check on a decrypted payload: long enough, and the tag bytes are zero. -/
def tagOK (d : ByteArray) : Bool :=
  !decide (d.size < geom.payloadTagLength) && (d.extract 0 geom.payloadTagLength).data.all (· == 0)

set_option maxHeartbeats 1000000 in
/-- The final hop accepts a forward packet only if its payload decrypts to a zero tag. -/
theorem procWith_final_tag (dec : ByteArray → Except String ByteArray) (pkt ss : ByteArray)
    (p : ByteArray) (tag : Vector UInt8 32) (cmds : List RoutingCommand) (f : Option ByteArray)
    (hd : dec (pkt.extract 2 (2 + kem.ciphertextSize)) = .ok ss)
    (h : procWith kem cipher macS kdfS streamS geom dec pkt = some (some p, tag, cmds, f))
    (hs : hasSurbReply cmds = false) :
    tagOK geom (cipher.decrypt (deriveHopKeys kdfS ss).payloadEncryption.toArray
      (ofVector (deriveHopKeys kdfS ss).headerEncryptionIV)
      (pkt.extract (payloadOffset kem geom) pkt.size)) = true := by
  unfold procWith unwrapKEMWith at h
  dsimp only at h
  by_cases h1 : pkt.size < 2 + kem.ciphertextSize + geom.routingInfoLength + macLength
  · rw [dif_pos h1] at h; cases h
  rw [dif_neg h1] at h
  by_cases h2 : (pkt.extract 0 2).data ≠ v0AD.data
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2, hd] at h
  dsimp only [Bind.bind, Except.bind] at h
  by_cases h3 : (ofVector (macS.mac (ofVector (deriveHopKeys kdfS ss).headerMAC)
      (pkt.extract 0 (2 + kem.ciphertextSize + geom.routingInfoLength)))).data
      ≠ (pkt.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
        (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)).data
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  generalize parseAll _ = r at h
  cases r with
  | error e => cases h
  | ok cmds0 =>
    dsimp only at h
    generalize List.findSome? _ cmds0 = o at h
    cases o with
    | some nm => cases h
    | none =>
      dsimp only at h
      have hraw : (pkt.extract (2 + kem.ciphertextSize + geom.routingInfoLength + macLength)
          pkt.size) = pkt.extract (payloadOffset kem geom) pkt.size := rfl
      rw [hraw] at h
      generalize hdd : (if (pkt.extract (payloadOffset kem geom) pkt.size).size > 0
        then cipher.decrypt (deriveHopKeys kdfS ss).payloadEncryption.toArray
          (ofVector (deriveHopKeys kdfS ss).headerEncryptionIV)
          (pkt.extract (payloadOffset kem geom) pkt.size)
        else pkt.extract (payloadOffset kem geom) pkt.size) = d at h
      by_cases hlt : d.size < geom.payloadTagLength
      · rw [if_pos hlt] at h; cases h
      rw [if_neg hlt] at h
      generalize hany : List.any cmds0 _ = bsr at h
      have hb : hasSurbReply cmds0 = bsr := by
        rw [← hany]; unfold hasSurbReply
        congr 1
      cases bsr with
      | true =>
        rw [if_pos rfl] at h
        simp only [pure, Except.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl, -⟩ := h
        rw [hs] at hb; cases hb
      | false =>
      rw [if_neg Bool.false_ne_true] at h
      by_cases htag : (!(d.extract 0 geom.payloadTagLength).data.all fun x => x == 0) = true
      · rw [if_pos htag] at h; cases h
      have hd' : tagOK geom d = true := by
        unfold tagOK
        simp only [Bool.not_eq_true, Bool.not_eq_false'] at htag
        rw [htag, decide_eq_false hlt]; rfl
      by_cases hpos : (pkt.extract (payloadOffset kem geom) pkt.size).size > 0
      · rw [if_pos hpos] at hdd; rw [hdd]; exact hd'
      · rw [if_neg hpos] at hdd
        have hz : d.size = 0 := by rw [← hdd]; omega
        unfold tagOK
        rw [cipher.decrypt_size, hdd, hz]
        have ht0 : geom.payloadTagLength = 0 := by omega
        simp [ht0]

/-- The four keys of a hop that KEM Sphinx uses: payload key, IV, header MAC key, header
encryption key. -/
abbrev KeyTuple := Vector UInt8 48 × Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32

def keyTuple (k : HopKeys) : KeyTuple :=
  (k.payloadEncryption, k.headerEncryptionIV, k.headerMAC, k.headerEncryption)

/-- The header of a one-hop packet in closed form. It does not use the payload key. -/
def hdr1 (ct : ByteArray) (iv : Vector UInt8 16) (km ke : Vector UInt8 32) (filler : ByteArray)
    (hop : PathHop) : ByteArray :=
  let ri0 := match kemRiFragment kem geom #[hop] #[ct] ByteArray.empty 1 0 with
    | .ok f => f
    | .error _ => ByteArray.empty
  let ri := xorBytes (ri0 ++ (if geom.nrHops > 1 then filler else ByteArray.empty))
    ((streamS.keystream (ofVector ke) (ofVector iv)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract 0
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength)
        - (0 + 1) * geom.perHopRoutingInfoLength))
  v0AD ++ ct ++ ri ++ ofVector (macS.mac (ofVector km) (v0AD ++ ct ++ ri ++ ByteArray.empty))

/-- A one-hop packet in closed form, from the hop's KEM ciphertext and keys. -/
def pkt1 (ct : ByteArray) (t : KeyTuple) (filler : ByteArray) (hop : PathHop)
    (payload : ByteArray) : ByteArray :=
  hdr1 kem macS streamS geom ct t.2.1 t.2.2.1 t.2.2.2 filler hop
    ++ cipher.encrypt t.1.toArray (ofVector t.2.1)
      ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)

/-- A packet built for one hop is `pkt1` on that hop's ciphertext and keys. -/
theorem newKEMPacket_one (seed : Vector UInt8 32) (filler : ByteArray) (hop : PathHop)
    (payload pkt : ByteArray)
    (h : newKEMPacket kem cipher macS kdfS streamS geom #[seed] filler #[hop] payload = .ok pkt) :
    ∃ ct ss sprp, kemEncap kem hop.publicKey seed = .ok (ct, ss) ∧
      createKEMHeader kem macS kdfS streamS geom #[seed] filler #[hop]
        = .ok (hdr1 kem macS streamS geom ct (deriveHopKeys kdfS ss).headerEncryptionIV
            (deriveHopKeys kdfS ss).headerMAC (deriveHopKeys kdfS ss).headerEncryption filler hop,
          sprp) ∧
      pkt = pkt1 kem cipher macS streamS geom ct (keyTuple (deriveHopKeys kdfS ss)) filler hop
        payload := by
  obtain ⟨-, hdr, sprpKeys, t, hhdr, ht0, htstep, rfl⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ h
  obtain ⟨-, -, -, -, kemElements, keys, riKS, riPad, s, hke, hks, -, -, hcontent, hrik, hs0,
    hsstep, rfl, rfl⟩ := createKEMHeader_unfold kem macS kdfS streamS geom _ _ _ _ _ hhdr
  have hsz : (#[hop] : Array PathHop).size = 1 := rfl
  rw [hsz] at hke hks hs0
  obtain ⟨ct, ss, henc, hct, hkey⟩ := hcontent 0 Nat.zero_lt_one
  have h0p : (#[hop] : Array PathHop)[0]! = hop := rfl
  have h0s : (#[seed] : Array (Vector UInt8 32))[0]! = seed := rfl
  rw [h0p, h0s] at henc
  have hkeArr : kemElements = #[ct] := by
    apply Array.ext
    · simpa using hke
    · intro i h1 h2
      have hi : i = 0 := by simp at h2; omega
      subst hi
      rw [← getElem!_pos kemElements 0 h1]; exact hct
  obtain ⟨hrik0, -⟩ := hrik 0 Nat.zero_lt_one
  obtain ⟨frag, hfrag, hs1, hs2⟩ := hsstep 0 Nat.zero_lt_one
  subst hkeArr
  have e10 : (#[hop] : Array PathHop).size - 1 - 0 = 0 := rfl
  rw [e10] at hfrag hs1 hs2
  rw [hsz] at hfrag
  rw [if_neg (by decide : ¬ (0 > 0))] at hs2
  have hs0b : (s 0).2 = ByteArray.empty := by rw [hs0]
  have hs0a : (s 0).1 = if geom.nrHops > 1 then filler else ByteArray.empty := by rw [hs0]
  rw [hs0b] at hfrag
  have ht1 := htstep 0 (by simp)
  unfold payloadEncryptStep at ht1
  have hk0 : (Array.ofFn (fun i : Fin (#[hop] : Array PathHop).size =>
      ({ key := keys[i.val]!.payloadEncryption, iv := keys[i.val]!.headerEncryptionIV } : SPRPKey)))[
        (Array.ofFn (fun i : Fin (#[hop] : Array PathHop).size =>
      ({ key := keys[i.val]!.payloadEncryption, iv := keys[i.val]!.headerEncryptionIV } : SPRPKey))).size
        - 1 - 0]!
      = ⟨keys[0]!.payloadEncryption, keys[0]!.headerEncryptionIV⟩ := rfl
  rw [hk0] at ht1
  have hsize1 : (Array.ofFn (fun i : Fin (#[hop] : Array PathHop).size =>
      ({ key := keys[i.val]!.payloadEncryption, iv := keys[i.val]!.headerEncryptionIV } : SPRPKey))).size
      = 0 + 1 := rfl
  have hH : v0AD ++ (#[ct] : Array ByteArray)[0]! ++ (s (0 + 1)).1 ++ (s (0 + 1)).2
      = hdr1 kem macS streamS geom ct (deriveHopKeys kdfS ss).headerEncryptionIV
          (deriveHopKeys kdfS ss).headerMAC (deriveHopKeys kdfS ss).headerEncryption filler hop := by
    rw [hs2, hs1, hrik0, hkey, hs0a]
    unfold hdr1
    rw [hfrag]
    rfl
  refine ⟨ct, ss, Array.ofFn (fun i : Fin (#[hop] : Array PathHop).size =>
    ({ key := keys[i.val]!.payloadEncryption, iv := keys[i.val]!.headerEncryptionIV } : SPRPKey)),
    henc, ?_, ?_⟩
  · rw [← hH]; exact hhdr
  · rw [hsize1, show (#[hop] : Array PathHop).size = 0 + 1 from rfl, ht1, ht0, hH, hkey]
    rfl

end Tagging

end Cryptlib.Protocols.Sphinx.KEMSphinx
