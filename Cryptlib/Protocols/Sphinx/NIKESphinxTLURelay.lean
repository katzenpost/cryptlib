/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUFn

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Common (commandsToBytes zeroPadTo toVec32 xorBytes)
open Cryptlib.Protocols.Sphinx.KEMSphinx (procSpec ProcResult relayImpl keysKs keysTag keysEnc)
open Cryptlib.Protocols.Sphinx.Common (v0AD)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion split join stepOf replyOf)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Protocols.RSOR (Role)

/-! # The last comparison of TLU→ for NIKE Sphinx: the relays in closed form

Both worlds as games against a relay that answers one header, and world 0 before the end of the
path as a game on the hops' functions. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- The honest relays, the relay answering the header `Hv` from the tag `T`, the keystream `U`
and the keys `t`, with its block decrypted by `D`. Other headers, and the other relays, are
answered by `procO` and `replyO`. -/
def hdrRelay (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom)) {n : ℕ}
    (T : Vector UInt8 n) (U : ByteArray) (t : HopKeys) (Hv : Vector UInt8 geom.headerLength)
    (D : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
      → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (patch : Protocols.RSOR.Patch 𝒮) :
    QueryImpl (Protocols.RSOR.oracleSpec 𝒮) (StateT (Protocols.RSOR.Log 𝒮) ProbComp) :=
  Protocols.RSOR.withDec (S := 𝒮) Role.relay Hv (fun o => o.2)
    (fun o y => stepOf geom (procD nike (Primitives.MAC.MAC.const T) (constStream U) geom
      (fun _ => .ok t) (fun _ _ => y) (join o)))
    (fun msg o y => replyOf cipher geom msg (procD nike (Primitives.MAC.MAC.const T)
      (constStream U) geom (fun _ => .ok t) (fun _ _ => y) (join o)))
    procO replyO D patch

/-- The honest relays, the relay answering the header `Hv` by forwarding to `name` the header
`Lh` with the block decrypted by `D`, and not replying. -/
def fwdRelay (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom))
    (Hv : Protocols.RSOR.Scheme.Header 𝒮) (name : Name) (Lh : ByteArray)
    (D : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
      → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) :
    QueryImpl (Protocols.RSOR.oracleSpec 𝒮) (StateT (Protocols.RSOR.Log 𝒮) ProbComp) :=
  Protocols.RSOR.oracle (S := 𝒮) (m := ProbComp)
    (fun h o => pure (if h = Role.relay ∧ o.1 = Hv then
        some (.forward name (split geom (Lh ++ Util.Bytes.ofVector (D o.2))))
      else procO h o))
    (fun h m o => pure (if h = Role.relay ∧ o.1 = Hv then none else replyO h m o)) {}

/-- **World 0's relay before the end of the path, in closed form.** A relay that answers the
header of layer `i` of a header function, from that layer's tag and keystream, forwards the
header of layer `i + 1` with the block it decrypts, and does not reply. -/
theorem hdrRelay_eq_fwdRelay (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom)) {n : ℕ}
    (T : Vector UInt8 n) (U : ByteArray) (t : HopKeys) (Hv : Vector UInt8 geom.headerLength)
    (D : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
      → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) (i : ℕ)
    (hi : i + 1 < path.size) (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hge : (ge i).size = nike.publicKeySize)
    (hcmd : path[i]!.commands = [])
    (hT : (nikeHdrTrace geom ks tag ge filler path (path.size - i)).isSome)
    (hksi : ks i = U) (htagi : tag i (hdrMsg geom ks tag ge filler path i) = Util.Bytes.ofVector T)
    (hblind : nikeBlind nike (ge i) t.blindingFactor = ge (i + 1))
    (hHv : Util.Bytes.ofVector Hv = layerHdr geom ks tag ge filler path i) :
    hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T U t Hv D {}
      = fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO Hv
        path[i + 1]!.id (layerHdr geom ks tag ge filler path (i + 1)) D := by
  obtain ⟨hnnh, hper, hrouting, -⟩ := id hvalid
  refine congrArg₂ (fun p r => Protocols.RSOR.oracle (S := 𝒮) (m := ProbComp) p r {})
    (funext fun h => funext fun o => congrArg pure ?_)
    (funext fun h => funext fun m => funext fun o => congrArg pure ?_)
  · by_cases hc : h = Role.relay ∧ o.1 = Hv
    · exact Eq.trans (ite_eq_left hc) (Eq.trans (stepOf_layerHdr nike geom T U t (D o.2) ks tag ge
        filler path i o hi hnnh (by omega) hrouting hn hfill hks htag hge hcmd hT hksi htagi hblind
        (by rw [hc.2]; exact hHv) (by omega)) (Eq.symm (ite_eq_left hc)))
    · exact Eq.trans (ite_eq_right hc) (Eq.symm (ite_eq_right hc))
  · by_cases hc : h = Role.relay ∧ o.1 = Hv
    · exact Eq.trans (ite_eq_left hc) (Eq.trans (replyOf_layerHdr nike geom cipher m T U t (D o.2)
        ks tag ge filler path i o hi hnnh (by omega) hrouting hn hfill hks htag hge hcmd hT hksi
        htagi hblind (by rw [hc.2]; exact hHv) (by omega)) (Eq.symm (ite_eq_left hc)))
    · exact Eq.trans (ite_eq_right hc) (Eq.symm (ite_eq_right hc))

/-- **World 1's patched relay before the end of the path, in the same form.** Whatever the
relay would answer under the replacement's header, the patch forwards the original's next
layer: with its own payload for the unchanged block, with the random block `g` otherwise. -/
theorem hdrRelay_patchDrawn_eq {pk : RSOR.Key nike} {keys : Role → RSOR.Key nike × nike.PrivateKey}
    (names : Role → Name)
    (c : Protocols.RSOR.ForwardChallenge (S := 𝒮)
      (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay names pk keys))
    (hn : c.pos + 1 < c.req.fwd.hops.length) (r : RSOR.Randomness nike geom) (mine : Onion geom)
    (g pl : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom)) {n : ℕ}
    (T : Vector UInt8 n) (U : ByteArray) (t : HopKeys)
    (D : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
      → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (Lh : ByteArray) (hLh : Lh.size = geom.headerLength)
    (hrep : ∀ (m : Msg geom) (o : Onion geom), o.1 = mine.1 →
      replyOf cipher geom m (procD nike (Primitives.MAC.MAC.const T) (constStream U) geom
        (fun _ => .ok t) (fun _ _ => D o.2) (join o)) = none) :
    hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T U t mine.1 D
        (c.patchDrawn (split geom (Lh ++ Util.Bytes.ofVector pl)) r mine g)
      = fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO mine.1
        c.req.fwd.hops[c.pos.val + 1].name Lh (fun y => if y = mine.2 then pl else g) := by
  refine Protocols.RSOR.oracle_pure_patch (S := 𝒮) _ _ _ _ _ (fun h o => ?_) (fun h m o => ?_)
  · unfold Protocols.RSOR.ForwardChallenge.patchDrawn
    dsimp only
    by_cases hc : h = Role.relay ∧ o.1 = mine.1
    · refine congrArg pure (Eq.trans (ite_eq_left hc) (Eq.trans (dite_eq_left hn)
        (Eq.trans (congrArg (fun z => some (Protocols.RSOR.Step.forward _ z)) ?_)
          (Eq.symm (ite_eq_left hc)))))
      rw [KEMSphinx.split_append geom _ _ hLh, KEMSphinx.split_append geom _ _ hLh]
      by_cases ho : o.2 = mine.2
      · exact (ite_eq_left ho).trans (Prod.ext rfl (ite_eq_left ho).symm)
      · exact (ite_eq_right ho).trans (Prod.ext rfl (ite_eq_right ho).symm)
    · exact congrArg pure (Eq.trans (ite_eq_right hc) (Eq.trans (ite_eq_right hc)
        (Eq.symm (ite_eq_right hc))))
  · unfold Protocols.RSOR.ForwardChallenge.patchDrawn Protocols.RSOR.ForwardChallenge.patchWith
    refine Eq.trans (ite_eq_right fun hx => absurd hx.2.2 (by omega)) ?_
    by_cases hc : h = Role.relay ∧ o.1 = mine.1
    · exact Eq.trans (ite_eq_left hc) (Eq.trans (hrep m o hc.2) (Eq.symm (ite_eq_left hc)))
    · exact Eq.trans (ite_eq_right hc) (Eq.symm (ite_eq_right hc))

/-- **World 0's relay on an onion's layer, before the end of the path.** The relay at hop `j`
holds the tag `T` and the keystream `U` of its layer of `q`'s onion. Under that layer's header
it forwards the header of layer `j + 1` with the block it decrypts, and does not reply. -/
theorem hdrRelay_onion (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom))
    (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (K : List HopKeys) (j : ℕ) (U : ByteArray) (T : Vector UInt8 macS.tagSize)
    (D : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
      → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hj : j + 1 < q.fwd.hops.length)
    (hU : U.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (ha : a.size = nike.publicKeySize)
    (hT : pathBuilds geom (RSOR.path nike q.fwd [.recipient q.receiver])
      ((RSOR.path nike q.fwd [.recipient q.receiver]).size - j)) :
    hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T U
        (K.toArray[j]!) (Util.Bytes.toVecN _ (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
            nike.publicKeySize + geom.routingInfoLength) (onionMsgStream nike macS streamS geom q r
            a K j U)) ++ Util.Bytes.ofVector T)) D {}
      = fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO
          (Util.Bytes.toVecN _ (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
              geom.routingInfoLength) (onionMsgStream nike macS streamS geom q r a K j U)) ++
              Util.Bytes.ofVector T))
        (RSOR.path nike q.fwd [.recipient q.receiver])[j + 1]!.id (layerHdr geom (Function.update
            (keysKs geom streamS K.toArray) j U) (Function.update (keysTag macS K.toArray) j fun _
            => Util.Bytes.ofVector T) (blindElem nike a K.toArray) (RSOR.filler nike geom
            (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient
            q.receiver]) (j + 1)) D := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hsz := RSOR.path_size nike q.fwd [.recipient q.receiver]
  have hlen := q.fwd.length_le
  have hmul : (geom.nrHops - (RSOR.path nike q.fwd [.recipient q.receiver]).size) *
      geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hfill : (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1).size =
      (geom.nrHops - (RSOR.path nike q.fwd [.recipient q.receiver]).size) *
      geom.perHopRoutingInfoLength := by
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hT' := fun (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) =>
    (nikeHdrTrace_isSome geom ks _ tag _ (blindElem nike a K.toArray) _
      (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) _
      (RSOR.path nike q.fwd [.recipient q.receiver])
      ((RSOR.path nike q.fwd [.recipient q.receiver]).size - j)).trans hT
  have hks : ∀ k, ((Function.update (keysKs geom streamS K.toArray) j U) k).size
      = geom.routingInfoLength + geom.perHopRoutingInfoLength := fun k => by
    by_cases hk : k = j
    · rw [hk, Function.update_self]
      exact hU
    · rw [Function.update_of_ne hk]
      exact streamS.keystream_size _ _ _
  have hcmd : (RSOR.path nike q.fwd [.recipient q.receiver])[j]!.commands = [] := by
    rw [RSOR.path_getElem! nike _ _ j (by omega)]
    exact ite_eq_right (by omega)
  have hM : (onionMsgStream nike macS streamS geom q r a K j U).size
      = 2 + nike.publicKeySize + geom.routingInfoLength :=
    hdrMsg_size nike geom _ _ _ _ _ j (by omega) hnnh (by omega) hrouting (by omega) hfill hks
      (fun m x => (Util.Bytes.size_ofVector _).trans hmactag) hcmd (hT' _ _)
      ((blindElem_size nike _ _ _).trans ha)
  rw [Util.Bytes.ofVector_toVecN _ hM]
  refine hdrRelay_eq_fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T
    U _ _ D _ _ _ _ _ j (by omega) (by omega) hfill hks (fun m x => ?_)
    ((blindElem_size nike _ _ _).trans ha) hcmd (hT' _ _) (Function.update_self _ _ _)
    (by rw [Function.update_self]) rfl ?_
  · by_cases hm : m = j
    · rw [hm, Function.update_self]
      exact (Util.Bytes.size_ofVector _).trans hmactag
    · rw [Function.update_of_ne hm]
      exact (Util.Bytes.size_ofVector _).trans hmactag
  · rw [Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, hM, Util.Bytes.size_ofVector, hhdr, had, hmactag])]
    unfold layerHdr onionMsgStream
    rw [hdrMsg_update_tag geom _ _ _ _ _ j (by omega), Function.update_self]

/-- **World 1's patched relay before the end of the path, its random payload drawn first.**
The game against the relay that answers the replacement's header and is patched with the
original's next layer `next` is the game that draws a block `g` and plays against the relay
forwarding `next`'s header: with `next`'s payload for the unchanged block, with `g` otherwise. -/
theorem hdrRelay_patchWith_run {pk : RSOR.Key nike}
    {keys : Role → RSOR.Key nike × nike.PrivateKey} (names : Role → Name)
    (c : Protocols.RSOR.ForwardChallenge (S := 𝒮) (honAt nike cipher macS kdfS streamS geom hvalid
        hmactag h16 .relay names pk keys))
    (hn : c.pos + 1 < c.req.fwd.hops.length) (r : RSOR.Randomness nike geom)
    (mine next : Onion geom)
    (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom)) {n : ℕ}
    (T : Vector UInt8 n) (U : ByteArray) (t : HopKeys) (D : Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength) → Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))
    (hrep : ∀ (m : Msg geom) (o : Onion geom), o.1 = mine.1 →
      replyOf cipher geom m (procD nike (Primitives.MAC.MAC.const T) (constStream U) geom (fun _ =>
          .ok t) (fun _ _ => D o.2) (join o)) = none)
    {α : Type} (oa : OracleComp (Protocols.RSOR.oracleSpec 𝒮) α) (log : Protocols.RSOR.Log 𝒮) :
    (simulateQ (hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T U t
        mine.1 D (c.patchWith next r mine)) oa).run' log
      =ᵈ $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) >>= fun g =>
        (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO
            mine.1 c.req.fwd.hops[c.pos.val + 1].name
          (Util.Bytes.ofVector next.1) (fun y => if y = mine.2 then next.2 else g)) oa).run' log :=
              by
  have hnext : split geom (Util.Bytes.ofVector next.1 ++ Util.Bytes.ofVector next.2) = next :=
    (KEMSphinx.split_append geom _ _ (Util.Bytes.size_ofVector _)).trans
      (Prod.ext (Cryptlib.Protocols.Sphinx.Common.toVecN_ofVector _) rfl)
  have he := fun g => hdrRelay_patchDrawn_eq nike cipher macS kdfS streamS geom hvalid hmactag h16
      names c hn r mine g next.2 procO replyO T U t D
    (Util.Bytes.ofVector next.1) (Util.Bytes.size_ofVector _) hrep
  simp only [hnext] at he
  have h := c.patchWith_draw next r mine
    (fun (h : Role) (o : Onion geom) => pure (if h = Role.relay ∧ o.1 = mine.1 then
        stepOf geom (procD nike (Primitives.MAC.MAC.const T) (constStream U) geom (fun _ => .ok t)
            (fun _ _ => D o.2) (join o))
      else procO h o))
    (fun (h : Role) (msg : Msg geom) (o : Onion geom) =>
      pure (if h = Role.relay ∧ o.1 = mine.1 then replyOf cipher geom msg (procD nike
          (Primitives.MAC.MAC.const T) (constStream U) geom (fun _ => .ok t) (fun _ _ => D o.2)
          (join o))
      else replyO h msg o))
    oa log
  have h2 := h.map Prod.fst
  rw [map_bind] at h2
  simp only [← he]
  exact h2

omit cipher hvalid hmactag h16 in
/-- The message is at the end of the sender's payload. -/
theorem msgOf_body (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) :
    KEMSphinx.RSOR.msgOf geom (RSOR.body nike macS kdfS streamS geom q r) = q.msg := by
  unfold KEMSphinx.RSOR.msgOf RSOR.body
  rw [ByteArray.size_append, Util.Bytes.size_ofVector, Nat.add_sub_cancel]
  have h := Util.Bytes.extract_append_right
    ((⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ : ByteArray)
      ++ (RSOR.surb nike macS kdfS streamS geom q r).1) (Util.Bytes.ofVector q.msg)
  rw [Util.Bytes.size_ofVector] at h
  rw [h]
  exact Util.Bytes.toVecN_ofVector _

omit cipher hvalid hmactag h16 in
/-- A request with no backward path has a payload that starts with the flag for no reply
block. -/
theorem body_get_zero (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (hq : q.back.hops = []) : (RSOR.body nike macS kdfS streamS geom q r).get! 0 = 0 := by
  have h2 : (⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ : ByteArray).size = 2 := rfl
  unfold RSOR.body
  rw [KEMSphinx.get!_eq_getElem _ 0 (by
      rw [ByteArray.size_append, ByteArray.size_append, h2]
      omega),
    ByteArray.getElem_append_left (by rw [ByteArray.size_append, h2]; omega),
    ByteArray.getElem_append_left (by rw [h2]; omega)]
  simp only [hq, List.isEmpty_nil, ↓reduceIte]
  rfl

/-- The adversary's second phase on a draw: its guess on the first layer of the onion shown. -/
def strGuess (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid hmactag
    h16 names)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A) (U :
        KEMSphinx.Keystream geom)
    (u : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) :
    OracleComp (Protocols.RSOR.oracleSpec 𝒮) Bool :=
  if drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
      (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) x.2.2
      < (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
        (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names W) x.2.2).size
            then
    A.guess x.2.2.st (strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x U u
        0)
  else pure false

/-- **A world after its payload step is a game against a relay that answers one header.** -/
theorem strRunP_eq (names : Role → Name) (W : FwdWorld nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A) (U :
        KEMSphinx.Keystream geom)
    (u v : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (pt : Onion geom → Protocols.RSOR.Patch 𝒮) :
    strRunP nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A x U u v pt
      = (simulateQ (hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16
          ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).proc
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x))
          ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A).reply
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x))
          (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x U)
              (Util.Bytes.ofVector U)
          (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names W (strPay
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x) default).1 default)
          (Util.Bytes.toVecN _ (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names
              W x U
            ++ Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16
                names W x U)))
          (fun y => if y = u then (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16
              names W A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
              W x) else v)
          (pt (strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16 names W x U u
              x.2.2.c.pos)))
        (strGuess nike cipher macS kdfS streamS geom hvalid hmactag h16 names W A x U u)).run'
            x.2.2.log :=
  rfl

/-- **World 0 on a draw, before the end of the path, against the relay in closed form.** Under
the challenge header the relay forwards the header of the next layer of the adversary's onion,
with the block it decrypts. This holds when the header builds up to the relay's layer and the
bytes under the relay's tag have their length. -/
theorem strRun_fwd0_eq (names : Role → Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A) (U : KEMSphinx.Keystream geom)
    (u v : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hj : (x.2.2.c.pos : ℕ) + 1 < x.2.2.c.req.fwd.hops.length)
    (hT : pathBuilds geom (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver])
      ((RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]).size - x.2.2.c.pos)) :
    strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names) A x U u v
      = (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 ((forwardPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) x)) ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) x))
          (Util.Bytes.toVecN _ (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names
              (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x U ++
              Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x U)))
          (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver])[(x.2.2.c.pos : ℕ) +
              1]!.id
          (layerHdr geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names) x) default)).toArray) x.2.2.c.pos
              (Util.Bytes.ofVector U)) (Function.update (keysTag macS (forwardKeys0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) x) default)).toArray) x.2.2.c.pos
              fun _ => Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              x U)) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2.2)
              (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x)
              default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names) x) default)).toArray) (RSOR.filler nike geom (RSOR.path nike
              x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]) x.2.2.o.1) (RSOR.path nike
              x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]) (x.2.2.c.pos + 1)) (fun y => if y
              = u then (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
              (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).plain (strPay
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names) x) else v))
        (strGuess nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) A x U u)).run' x.2.2.log := by
  have hk : (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) x) default)).toArray[(x.2.2.c.pos :
      ℕ)]! = restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) x) default).1 default :=
    (payKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        x) default).2
  have h := hdrRelay_onion nike cipher macS kdfS streamS geom hvalid hmactag h16 ((forwardPay nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x))
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) x)) x.2.2.c.req x.2.2.o (groupElem nike (drawKey nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2.2)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) x) default)).toArray 0) (forwardKeys0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) x) default)) x.2.2.c.pos (Util.Bytes.ofVector U) (strTag nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) x U) (fun y => if y = u then (forwardPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x) else v) hj
      (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) hT
  rw [hk] at h
  unfold strRun
  rw [strRunP_eq]
  exact congrArg (fun impl => (simulateQ impl (strGuess nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A x U
      u)).run' x.2.2.log) h

/-! ## World 1's relay answers the original's element again -/

/-- A draw of world 1's last game as a draw of the replacement's run. -/
def next4X {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (z : Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) : StrX nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names) A :=
  (z.km, z.seed, ⟨z.p.k, z.p.keys, z.p.c, z.p.st, z.p.log, z.o, z.d'⟩)

/-- The original's next layer in world 1's last game, from the keystream `W`: past the end of
the path it is the replacement's own layer. -/
def next4Nxt {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (z : Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) (W : ByteArray) (mine
        : Onion geom) : Onion geom :=
  if (z.p.c.pos : ℕ) + 1 < z.p.c.req.fwd.hops.length then
    nextOfStream nike cipher macS kdfS streamS geom z.p.c.req z.o.1
      (groupElem nike ((nike.decodePrivateKey z.p.d0).getD default)
        (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default z.y,
            z.p)).toArray 0)
      (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default z.y, z.p))
          z.p.c.pos W
  else mine

/-- The draws of world 1's last game: the keystream of the original's next layer, then the
rest. -/
def finDraw (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    ProbComp (KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names A) := do
  let W ← $ᵗ (KEMSphinx.Keystream geom)
  let y ← $ᵗ (Vector UInt8 48 × Vector UInt8 32 × Vector UInt8 32)
  let z ← next4Rest nike cipher macS kdfS streamS geom hvalid hmactag h16 names A default y
  return (W, z)

/-- The packets that carry the original's element at the relay. -/
def finChal {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) (pkt : ByteArray) : Bool :=
  decide (pkt.extract 2 (2 + nike.publicKeySize) = nextElemI nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (keys4 default x.2.y, x.2.p))

/-- The relay's own answers. -/
def finOwn {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) : ByteArray → ProcResult :=
  procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.p.k.2)

/-- The adversary's second phase in world 1's last game, on a draw. -/
def finRun (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) : OracleComp procSpec Bool :=
  nextPostN nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (⟨x.2.p.keys, x.2.p.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names x.2.p.k.1) x.2.p.st
      x.2.p.log
    x.2.U x.2.km x.2.seed x.2.o x.2.d' x.2.u x.2.v
    (next4Nxt nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2 (Util.Bytes.ofVector x.1))

/-- **World 1's last game is a relay game**: the relay refuses the original's element. -/
theorem prgIdeal_nextStreamAdv (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    PRGScheme.prgIdealExperiment (nextStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names A)
      = Relay.gameHand (finDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)
          (finChal nike cipher macS kdfS streamS geom hvalid hmactag h16) (finOwn nike cipher macS
          kdfS streamS geom hvalid hmactag h16) (finRun nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names A)
        fun _ _ => none := by
  unfold PRGScheme.prgIdealExperiment nextStreamAdv Relay.gameHand finDraw
  simp only [bind_assoc, pure_bind]
  rfl

/-- The draws of world 1's last game on which the bytes under the relay's tag carry the
replacement's element. -/
def finCar {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) : Prop :=
  (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2) x.2.U).extract 2 (2 + nike.publicKeySize)
    = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
      (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names)) (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2

/-- World 1 with the relay answering the original's element itself: the replacement's run,
the relay patched around the replacement's layer with the original's next layer. -/
def finOwnRun (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) : ProbComp Bool :=
  strRunP nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) A (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2) x.2.U x.2.u x.2.v
    fun mine => x.2.p.c.patchWith (next4Nxt nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2 (Util.Bytes.ofVector x.1) mine) x.2.o.1 mine

/-- **The relay may answer the original's element again.** World 1's last game differs from
the replacement's run with the patched relay by at most the chance that the adversary sends a
packet carrying the original's element, and the chance of a draw on which the bytes under the
relay's tag do not carry the replacement's element. -/
theorem prgIdeal_nextStreamAdv_sub_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable
    (S := 𝒮)).Adversary) :
    |(Pr{let b ← (PRGScheme.prgIdealExperiment (nextStreamAdv nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names A))}[b = true]).toReal
      - (Pr{let b ← (finDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A >>=
          finOwnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[b =
          true]).toReal|
    ≤ (Pr{let b ← (Relay.gameChal (finDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) (finChal nike cipher macS kdfS streamS geom hvalid hmactag h16) (finOwn nike
        cipher macS kdfS streamS geom hvalid hmactag h16)
          (finRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) fun _ _ =>
              none)}[b = true]).toReal
      + (Pr{let x ← (finDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[¬
          finCar nike cipher macS kdfS streamS geom hvalid hmactag h16 x]).toReal := by
  rw [prgIdeal_nextStreamAdv]
  have h1 := Relay.gameHand_sub_le (finDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
      names A) (finChal nike cipher macS kdfS streamS geom hvalid hmactag h16) (finOwn nike cipher
      macS kdfS streamS geom hvalid hmactag h16)
    (finRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) (finOwn nike cipher macS
        kdfS streamS geom hvalid hmactag h16) fun _ _ => none
  rw [abs_sub_comm] at h1
  have h2 := KEMSphinx.abs_prEvent_bind_sub_le_bad (finDraw nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names A)
    (fun x => simulateQ (relayImpl (Relay.ansOf (finChal nike cipher macS kdfS streamS geom hvalid
        hmactag h16) (finOwn nike cipher macS kdfS streamS geom hvalid hmactag h16) x (finOwn nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x)))
      (finRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A x))
    (finOwnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) (fun x => ¬ finCar
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x) fun x hx => by
      have hans : Relay.ansOf (finChal nike cipher macS kdfS streamS geom hvalid hmactag h16)
          (finOwn nike cipher macS kdfS streamS geom hvalid hmactag h16) x (finOwn nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x) = finOwn nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x :=
        funext fun pkt => ite_self _
      rw [hans]
      exact nextPostN_real nike cipher macS kdfS streamS geom hvalid hmactag h16 names A x.2.p.k
          (⟨x.2.p.keys, x.2.p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names
        x.2.p.k.1) x.2.p.st x.2.p.log x.2.U x.2.km x.2.seed x.2.o x.2.d' x.2.u x.2.v
        (next4Nxt nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2 (Util.Bytes.ofVector
            x.1)) (not_not.mp hx)
  exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)

/-- The replacement's layer at the relay, on a draw of world 1's last game. -/
def finMine {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) : Onion geom :=
  strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2) x.2.U x.2.u x.2.p.c.pos

/-- The original's next layer, on a draw of world 1's last game. -/
def finNext {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) : Onion geom :=
  next4Nxt nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2 (Util.Bytes.ofVector x.1)
      (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x)

/-- **World 1 on a draw, before the end of the path, against the relay in closed form.** With
the random payload `g` drawn first, the relay under the replacement's header forwards the
header of the original's next layer: with that layer's payload for the unchanged block, with
`g` otherwise. This holds when the replacement's layer at the relay has the header the relay
answers, and the relay would not reply to it. -/
theorem finOwnRun_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary)
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A)
    (hn : (x.2.p.c.pos : ℕ) + 1 < x.2.p.c.req.fwd.hops.length)
    (hmine : (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x).1 =
        Util.Bytes.toVecN _ (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2) x.2.U
      ++ Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2) x.2.U)))
    (hrep : ∀ (m : Msg geom) (o : Onion geom), o.1 = (finMine nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x).1 →
      replyOf cipher geom m (procD nike (Primitives.MAC.MAC.const (strTag nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)
          x.2.U))
        (constStream (Util.Bytes.ofVector x.2.U)) geom (fun _ => .ok (restKeys (payRest nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default).1 default))
        (fun _ _ => (fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2)) else x.2.v) o.2) (join o)) = none) :
    finOwnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A x
      =ᵈ $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) >>= fun g =>
        (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 ((forwardPay
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)))
            ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2))) (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x).1
          x.2.p.c.req.fwd.hops[(x.2.p.c.pos : ℕ) + 1].name (Util.Bytes.ofVector (finNext nike
              cipher macS kdfS streamS geom hvalid hmactag h16 x).1)
          (fun y => if y = (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x).2 then
              (finNext nike cipher macS kdfS streamS geom hvalid hmactag h16 x).2 else g))
          (strGuess nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) A (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2) x.2.U x.2.u)).run' x.2.p.log := by
  unfold finOwnRun
  rw [strRunP_eq, ← hmine]
  exact hdrRelay_patchWith_run nike cipher macS kdfS streamS geom hvalid hmactag h16 names x.2.p.c
      hn x.2.o.1 (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x) (finNext nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x) ((forwardPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) A).proc (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2))) ((forwardPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).reply
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2))) (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2) x.2.U)
    (Util.Bytes.ofVector x.2.U) (restKeys (payRest nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2)) default).1 default) (fun y => if y = x.2.u then (forwardPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) A).plain (strPay nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) else x.2.v) hrep _ _

/-! ## A world before the end of the path, from the hops' functions -/

/-- **The game before the end of the path, from each hop's keystream, tagging function,
encryption and element.** The adversary is shown the first layer of `q`'s onion, the relay at
hop `j` tagging its layer with the key `km` and showing the block `u` for its encryption. Under
that layer's header the relay forwards the next layer's header: with the payload the later
hops left for the block `u`, with `v` for another. -/
def fnRun (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom))
    (st : A.State) (log : Protocols.RSOR.Log 𝒮)
    (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (j : ℕ) (km : Vector UInt8 32)
    (u v : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) (ks : ℕ → ByteArray)
        (tag enc : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) : ProbComp Bool :=
  (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO
      (Util.Bytes.toVecN _ ((Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
          geom.routingInfoLength) (hdrMsg geom ks tag ge (RSOR.filler nike geom (RSOR.path nike
          q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j)))
          ++ Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (Util.Bytes.ofVector
          (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom ks tag
          ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path
          nike q.fwd [.recipient q.receiver]) j))))))
      (RSOR.path nike q.fwd [.recipient q.receiver])[j + 1]!.id (layerHdr geom ks (Function.update
          tag j fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
          (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
          (hdrMsg geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
          q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j))))) ge (RSOR.filler
          nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd
          [.recipient q.receiver]) (j + 1))
      (fun y => if y = u then Util.Bytes.toVecN _ (encTrace enc (RSOR.path nike q.fwd [.recipient
          q.receiver]).size
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)
          ++ RSOR.body nike macS kdfS streamS geom q r) ((RSOR.path nike q.fwd [.recipient
              q.receiver]).size - 1 - j)) else v))
    (A.guess st (layerFn nike macS kdfS streamS geom q r ks (Function.update tag j fun _ =>
        Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (Util.Bytes.ofVector
        (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom ks tag ge
        (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike
        q.fwd [.recipient q.receiver]) j)))))
      (Function.update enc j fun _ => Util.Bytes.ofVector u) ge 0))).run' log

/-- **The game reads the hops after the relay through `tailOf`.** On the keys of a path with
the relay's replaced, the game from the hops' functions is the game on those functions spliced
with the functions of the path's tail. -/
theorem fnRun_tailOf (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom))
    (st : A.State) (log : Protocols.RSOR.Log 𝒮)
    (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (j : ℕ) (km : Vector UInt8 32)
    (u v : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) (c : nike.PrivateKey)
        (hops : Array PathHop) (seed : Vector UInt8 32)
    (t : HopKeys) (U : ByteArray) (hj : j < hops.size)
    (ht : t.blindingFactor = blindingFactorPrivKey seed) :
    fnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 A procO replyO st log q r j km u v
        (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c hops j t hops.size).toArray)
            j U) (keysTag macS (hopKeysWith nike kdfS c hops j t hops.size).toArray)
        (keysEnc cipher (hopKeysWith nike kdfS c hops j t hops.size).toArray) (blindElem nike
            (groupElem nike c (hopKeysWith nike kdfS c hops j t hops.size).toArray 0) (hopKeysWith
            nike kdfS c hops j t hops.size).toArray)
      = fnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 A procO replyO st log q r j km
          u v
        (spliceAt j (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c hops j t
            hops.size).toArray) j U)
          (keysKs geom streamS (tailOf nike kdfS c hops j seed).2.toArray))
        (spliceAt j (keysTag macS (hopKeysWith nike kdfS c hops j t hops.size).toArray) (keysTag
            macS (tailOf nike kdfS c hops j seed).2.toArray))
        (spliceAt j (keysEnc cipher (hopKeysWith nike kdfS c hops j t hops.size).toArray) (keysEnc
            cipher (tailOf nike kdfS c hops j seed).2.toArray))
        (spliceAt j (blindElem nike (groupElem nike c (hopKeysWith nike kdfS c hops j t
            hops.size).toArray 0) (hopKeysWith nike kdfS c hops j t hops.size).toArray)
          (blindElem nike (tailOf nike kdfS c hops j seed).1 (tailOf nike kdfS c hops j
              seed).2.toArray)) := by
  have hg := groupElem_eq_blindElem nike c (hopKeysWith nike kdfS c hops j t hops.size).toArray
    (j + 1)
  rw [tailOf_hopKeysWith nike kdfS c hops j seed t hj ht]
  dsimp only
  rw [hg,
    spliceAt_drop (keysKs geom streamS) (fun K K' i i' h => by unfold keysKs; rw [h]) _ j _
      (fun i hi => Function.update_of_ne (by omega) _ _),
    spliceAt_drop (keysTag macS) (fun K K' i i' h => by unfold keysTag; rw [h]) _ j _
      (fun i hi => rfl),
    spliceAt_drop (keysEnc cipher) (fun K K' i i' h => by unfold keysEnc; rw [h]) _ j _
      (fun i hi => rfl),
    spliceAt_blindElem]

include hvalid in
/-- **The layer at the last hop of a path**, the hop's tag `tg` and its encrypted block `u`
given: the bytes under the tag, the tag, and the block. -/
theorem layerFn_last (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (ks : ℕ → ByteArray) (tag enc : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) (j : ℕ)
    (tg : ByteArray) (u : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) (hj : j
        + 1 = (RSOR.path nike q.fwd [.recipient q.receiver]).size)
    (hb : (RSOR.body nike macS kdfS streamS geom q r).size = geom.forwardPayloadLength) (hT :
        pathBuilds geom (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
        [.recipient q.receiver]).size)
    (hMsz : (hdrMsg geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
        q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j).size = 2 +
        nike.publicKeySize + geom.routingInfoLength)
    (htg : tg.size = macLength) :
    layerFn nike macS kdfS streamS geom q r ks (Function.update tag j fun _ => tg)
        (Function.update enc j fun _ => Util.Bytes.ofVector u) ge j
      = (Util.Bytes.toVecN _ ((hdrMsg geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd
          [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j) ++ tg),
          u) := by
  obtain ⟨-, -, -, hhdr, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hL : layerHdr geom ks (Function.update tag j fun _ => tg) ge (RSOR.filler nike geom
      (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient
      q.receiver]) j = (hdrMsg geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd
      [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j) ++ tg := by
    unfold layerHdr
    rw [hdrMsg_update_tag geom _ _ _ _ _ j (by omega), Function.update_self]
  have hE : encTrace (Function.update enc j fun _ => Util.Bytes.ofVector u) (RSOR.path nike q.fwd
      [.recipient q.receiver]).size
      ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS streamS
          geom q r)) ((RSOR.path nike q.fwd [.recipient q.receiver]).size - j)
      = Util.Bytes.ofVector u := by
    rw [show (RSOR.path nike q.fwd [.recipient q.receiver]).size - j = 0 + 1 by omega,
        encTrace_succ,
      show (RSOR.path nike q.fwd [.recipient q.receiver]).size - 1 - 0 = j by omega,
          Function.update_self]
  rw [layerFn_eq nike macS kdfS streamS geom q r _ _ _ _ j hb
      ((nikeHdrTrace_isSome geom _ _ _ _ _ _ _ _ (RSOR.path nike q.fwd [.recipient q.receiver])
          _).trans hT), hL, hE,
    split_append_bytes geom _ _ (by rw [ByteArray.size_append, hMsz, htg, hhdr, had]),
    Util.Bytes.toVecN_ofVector]

set_option maxHeartbeats 4000000 in
/-- **The game from the hops' functions is the game of a replacement cut after the relay.**
Take an onion `q` given by its hops' functions, a replacement `q'` whose path ends at the relay
at hop `j`, and functions for `q`'s next layer. When the hops in front agree, the bytes under
the relay's tag agree, and the next layer's functions are `q`'s after the relay with the same
padding, the game on `q` shows the replacement's first layer and forwards that next layer:
with its payload for the block `u`, with `v` for another. -/
theorem fnRun_eq_short (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom))
    (st : A.State) (log : Protocols.RSOR.Log 𝒮)
    (q q' : RSOR.Request nike geom) (r r' : RSOR.Randomness nike geom) (j : ℕ)
    (km : Vector UInt8 32) (u v : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (ks ks' ksI : ℕ → ByteArray) (tag tag' tagI enc enc' encI : ℕ → ByteArray → ByteArray)
    (ge ge' geI : ℕ → ByteArray)
    (hj : j + 1 < (RSOR.path nike q.fwd [.recipient q.receiver]).size) (hj' : j + 1 = (RSOR.path
        nike q'.fwd [.recipient q'.receiver]).size) (hn : (RSOR.path nike q.fwd [.recipient
        q.receiver]).size ≤ geom.nrHops)
    (hT : pathBuilds geom (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
        [.recipient q.receiver]).size) (hT' : pathBuilds geom (RSOR.path nike q'.fwd [.recipient
        q'.receiver]) (RSOR.path nike q'.fwd [.recipient q'.receiver]).size)
    (hb : (RSOR.body nike macS kdfS streamS geom q r).size = geom.forwardPayloadLength)
    (hb' : (RSOR.body nike macS kdfS streamS geom q' r').size = geom.forwardPayloadLength)
    (hks : ∀ k, (ks k).size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (htag : ∀ i m, (tag i m).size = macLength) (htag' : ∀ i m, (tag' i m).size = macLength)
    (hge : ∀ i, (ge i).size = nike.publicKeySize) (hge' : (ge' j).size = nike.publicKeySize)
    (hfront : ∀ i < j, ks i = ks' i ∧ tag i = tag' i ∧ ge i = ge' i ∧ enc i = enc' i
      ∧ (RSOR.path nike q.fwd [.recipient q.receiver])[i]!.commands = (RSOR.path nike q'.fwd
          [.recipient q'.receiver])[i]!.commands ∧ (RSOR.path nike q.fwd [.recipient q.receiver])[i
          + 1]!.id = (RSOR.path nike q'.fwd [.recipient q'.receiver])[i + 1]!.id)
    (hge0 : ge 0 = ge' 0)
    (hM : hdrMsg geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
        q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j = (hdrMsg geom ks' tag'
        ge' (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1)
        (RSOR.path nike q'.fwd [.recipient q'.receiver]) j))
    (htail : ∀ i, j < i → ksI i = ks i ∧ tagI i = tag i ∧ geI i = ge i ∧ encI i = enc i)
    (hpad : KEMSphinx.padAt geom ksI j = KEMSphinx.padAt geom ks j)
    (hcmd : (RSOR.path nike q.fwd [.recipient q.receiver])[j]!.commands = []) :
    fnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 A procO replyO st log q r j km u v
        ks tag enc ge
      = (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO
          (layerFn nike macS kdfS streamS geom q' r' ks' (Function.update tag' j fun _ =>
          Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (Util.Bytes.ofVector
          (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom ks'
          tag' ge' (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1)
          (RSOR.path nike q'.fwd [.recipient q'.receiver]) j))))) (Function.update enc' j fun _ =>
          Util.Bytes.ofVector u) ge' j).1 (RSOR.path nike q.fwd [.recipient q.receiver])[j + 1]!.id
          (Util.Bytes.ofVector (layerFn nike macS kdfS streamS geom q r ksI tagI encI geI (j +
              1)).1) (fun y => if y = (layerFn nike macS kdfS streamS geom q' r' ks'
              (Function.update tag' j fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector
              km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
              geom.routingInfoLength) (hdrMsg geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path
              nike q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q'.fwd [.recipient
              q'.receiver]) j))))) (Function.update enc' j fun _ => Util.Bytes.ofVector u) ge' j).2
              then (layerFn nike macS kdfS streamS geom q r ksI tagI encI geI (j + 1)).2 else v))
        (A.guess st (layerFn nike macS kdfS streamS geom q' r' ks' (Function.update tag' j fun _ =>
            Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (Util.Bytes.ofVector
            (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom ks'
            tag' ge' (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1)
            (RSOR.path nike q'.fwd [.recipient q'.receiver]) j))))) (Function.update enc' j fun _
            => Util.Bytes.ofVector u) ge' 0))).run' log := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hfillOf : ∀ (pth : Array PathHop) (rr : RSOR.Randomness nike geom),
      (RSOR.filler nike geom pth rr.1).size
        = (geom.nrHops - pth.size) * geom.perHopRoutingInfoLength := fun pth rr => by
    have hmul : (geom.nrHops - pth.size) * geom.perHopRoutingInfoLength
        ≤ geom.routingInfoLength := by
      rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have iso : ∀ (k : ℕ → ByteArray) (tg : ℕ → ByteArray → ByteArray) (g : ℕ → ByteArray),
      (nikeHdrTrace geom k tg g (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
          q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
          [.recipient q.receiver]).size).isSome := fun k tg g =>
    (nikeHdrTrace_isSome geom k _ tg _ g _ (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
        q.receiver]) r.1) _ (RSOR.path nike q.fwd [.recipient q.receiver]) _).trans hT
  have iso' : ∀ (k : ℕ → ByteArray) (tg : ℕ → ByteArray → ByteArray) (g : ℕ → ByteArray),
      (nikeHdrTrace geom k tg g (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient
          q'.receiver]) r'.1) (RSOR.path nike q'.fwd [.recipient q'.receiver]) (RSOR.path nike
          q'.fwd [.recipient q'.receiver]).size).isSome := fun k tg g =>
    (nikeHdrTrace_isSome geom k _ tg _ g _ (RSOR.filler nike geom (RSOR.path nike q'.fwd
        [.recipient q'.receiver]) r'.1) _ (RSOR.path nike q'.fwd [.recipient q'.receiver]) _).trans
        hT'
  have isoj : ∀ (k : ℕ → ByteArray) (tg : ℕ → ByteArray → ByteArray) (g : ℕ → ByteArray),
      (nikeHdrTrace geom k tg g (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
          q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) ((RSOR.path nike q.fwd
          [.recipient q.receiver]).size - j)).isSome := fun k tg g =>
    nikeHdrTrace_isSome_of_le geom k tg g _ _ ((RSOR.path nike q.fwd [.recipient q.receiver]).size
        - j) j (by
      rw [Nat.sub_add_cancel (by omega)]
      exact iso k tg g)
  have isoj' : ∀ (k : ℕ → ByteArray) (tg : ℕ → ByteArray → ByteArray) (g : ℕ → ByteArray),
      (nikeHdrTrace geom k tg g (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient
          q'.receiver]) r'.1) (RSOR.path nike q'.fwd [.recipient q'.receiver]) ((RSOR.path nike
          q'.fwd [.recipient q'.receiver]).size - j)).isSome := fun k tg g =>
    nikeHdrTrace_isSome_of_le geom k tg g _ _ ((RSOR.path nike q'.fwd [.recipient
        q'.receiver]).size - j) j (by
      rw [Nat.sub_add_cancel (by omega)]
      exact iso' k tg g)
  have hMsz : (hdrMsg geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient
      q'.receiver]) r'.1) (RSOR.path nike q'.fwd [.recipient q'.receiver]) j).size = 2 +
      nike.publicKeySize + geom.routingInfoLength := by
    rw [← hM]
    exact hdrMsg_size nike geom ks tag ge _ _ j hj hnnh (by omega) hrouting hn (hfillOf _ _) hks
      htag hcmd (isoj _ _ _) (hge j)
  have htag0 : ∀ i m, ((Function.update tag j fun _ => Util.Bytes.ofVector (macS.mac
      (Util.Bytes.ofVector km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
      geom.routingInfoLength) (hdrMsg geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path nike
      q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q'.fwd [.recipient q'.receiver])
      j))))) i m).size = macLength := fun i m => by
    by_cases hi : i = j
    · rw [hi, Function.update_self]
      exact (Util.Bytes.size_ofVector _).trans hmactag
    · rw [Function.update_of_ne hi]
      exact htag i m
  have htag1 : ∀ i m, ((Function.update tag' j fun _ => Util.Bytes.ofVector (macS.mac
      (Util.Bytes.ofVector km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
      geom.routingInfoLength) (hdrMsg geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path nike
      q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q'.fwd [.recipient q'.receiver])
      j))))) i m).size = macLength := fun i m => by
    by_cases hi : i = j
    · rw [hi, Function.update_self]
      exact (Util.Bytes.size_ofVector _).trans hmactag
    · rw [Function.update_of_ne hi]
      exact htag' i m
  have hmine : (layerFn nike macS kdfS streamS geom q' r' ks' (Function.update tag' j fun _ =>
      Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (Util.Bytes.ofVector
      (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom ks' tag'
      ge' (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path
      nike q'.fwd [.recipient q'.receiver]) j))))) (Function.update enc' j fun _ =>
      Util.Bytes.ofVector u) ge' j) = (Util.Bytes.toVecN _ ((hdrMsg geom ks' tag' ge' (RSOR.filler
      nike geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q'.fwd
      [.recipient q'.receiver]) j) ++ Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
      (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
      (hdrMsg geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient
      q'.receiver]) r'.1) (RSOR.path nike q'.fwd [.recipient q'.receiver]) j))))), u) := by
    exact layerFn_last nike macS kdfS streamS geom hvalid q' r' ks' tag' enc' ge' j _ u hj' hb' hT'
        hMsz ((Util.Bytes.size_ofVector _).trans hmactag)
  have hLsz : (layerHdr geom ks (Function.update tag j fun _ => Util.Bytes.ofVector (macS.mac
      (Util.Bytes.ofVector km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
      geom.routingInfoLength) (hdrMsg geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path nike
      q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q'.fwd [.recipient q'.receiver])
      j))))) ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1)
      (RSOR.path nike q.fwd [.recipient q.receiver]) (j + 1)).size = geom.headerLength := by
    rw [hhdr, had]
    exact layerHdr_succ_size nike geom ks _ ge _ _ j hj hnnh (by omega) hrouting hn
      (hfillOf _ _) hks htag0 hcmd (isoj _ _ _) (hge (j + 1))
  have hnext : (layerFn nike macS kdfS streamS geom q r ksI tagI encI geI (j + 1)) =
      (Util.Bytes.toVecN _ (layerHdr geom ks (Function.update tag j fun _ => Util.Bytes.ofVector
      (macS.mac (Util.Bytes.ofVector km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
      nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom ks' tag' ge' (RSOR.filler nike geom
      (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q'.fwd [.recipient
      q'.receiver]) j))))) ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver])
      r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (j + 1)),
      Util.Bytes.toVecN _ (encTrace enc (RSOR.path nike q.fwd [.recipient q.receiver]).size
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS
          streamS geom q r)) ((RSOR.path nike q.fwd [.recipient q.receiver]).size - 1 - j))) := by
    rw [layerFn_eq nike macS kdfS streamS geom q r _ _ _ _ (j + 1) hb (iso _ _ _),
      layerHdr_congr_tail geom ksI ks tagI (Function.update tag j fun _ => Util.Bytes.ofVector
          (macS.mac (Util.Bytes.ofVector km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
          nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom ks' tag' ge' (RSOR.filler nike
          geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q'.fwd
          [.recipient q'.receiver]) j))))) geI ge (RSOR.filler nike geom (RSOR.path nike q.fwd
          [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j hj (fun i
          hi =>
        ⟨(htail i hi).1, (htail i hi).2.1.trans (Function.update_of_ne (by omega) _ _).symm,
          (htail i hi).2.2.1⟩) hpad,
      encTrace_congr encI enc (RSOR.path nike q.fwd [.recipient q.receiver]).size
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS
          streamS geom q r)) ((RSOR.path nike q.fwd [.recipient q.receiver]).size - (j + 1)) (by
          omega)
        (fun i h1 h2 => (htail i (by omega)).2.2.2),
      show (RSOR.path nike q.fwd [.recipient q.receiver]).size - (j + 1) = (RSOR.path nike q.fwd
          [.recipient q.receiver]).size - 1 - j by omega]
    exact split_append_bytes geom _ _ hLsz
  have hshown : layerFn nike macS kdfS streamS geom q r ks (Function.update tag j fun _ =>
      Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (Util.Bytes.ofVector
      (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom ks' tag'
      ge' (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path
      nike q'.fwd [.recipient q'.receiver]) j))))) (Function.update enc j fun _ =>
      Util.Bytes.ofVector u) ge 0 = (layerFn nike macS kdfS streamS geom q' r' ks' (Function.update
      tag' j fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (Util.Bytes.ofVector
      (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom ks' tag'
      ge' (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path
      nike q'.fwd [.recipient q'.receiver]) j))))) (Function.update enc' j fun _ =>
      Util.Bytes.ofVector u) ge' 0) := by
    rw [layerFn_zero nike macS kdfS streamS geom q r _ _ _ _ (by omega),
      layerFn_zero nike macS kdfS streamS geom q' r' _ _ _ _ (by omega),
      nikePktFn_shift nike geom ks ks' (Function.update tag j fun _ => Util.Bytes.ofVector
          (macS.mac (Util.Bytes.ofVector km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
          nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom ks' tag' ge' (RSOR.filler nike
          geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q'.fwd
          [.recipient q'.receiver]) j))))) (Function.update tag' j fun _ => Util.Bytes.ofVector
          (macS.mac (Util.Bytes.ofVector km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
          nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom ks' tag' ge' (RSOR.filler nike
          geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q'.fwd
          [.recipient q'.receiver]) j))))) (Function.update enc j fun _ => Util.Bytes.ofVector u)
          (Function.update enc' j fun _ => Util.Bytes.ofVector u) ge ge' (RSOR.filler nike geom
          (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.filler nike geom (RSOR.path
          nike q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q.fwd [.recipient
          q.receiver]) (RSOR.path nike q'.fwd [.recipient q'.receiver]) (RSOR.body nike macS kdfS
          streamS geom q r)
        (RSOR.body nike macS kdfS streamS geom q' r') j (by omega) (by omega) (fun i hi => ⟨(hfront
            i hi).1, by
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (hfront i hi).2.1, (hfront i hi).2.2.1, by
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (hfront i hi).2.2.2.1, (hfront i hi).2.2.2.2⟩) hge0 (by
          rw [hdrMsg_update_tag geom _ _ _ _ _ j (by omega),
            hdrMsg_update_tag geom _ _ _ _ _ j (by omega)]
          exact hM) (by rw [Function.update_self, Function.update_self]) (isoj _ _ _)
        (isoj' _ _ _) hnnh (by omega) hn (by omega) (hfillOf _ _) (hfillOf _ _) htag0 htag1
        (hge j) hge' (Util.Bytes.ofVector u) (fun b => by rw [Function.update_self])
        (fun b => by rw [Function.update_self]) hb hb']
  unfold fnRun
  rw [hM, hshown, hmine, hnext]
  dsimp only
  rw [Util.Bytes.ofVector_toVecN _ hLsz, Util.Bytes.ofVector_toVecN _ hMsz]

/-- **World 0 on a draw, before the end of the path, is that game on its hops' keys.** -/
theorem strRun_fwd0_fn (names : Role → Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A) (U : KEMSphinx.Keystream geom) (u v : Vector
        UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hj : (x.2.2.c.pos : ℕ) + 1 < x.2.2.c.req.fwd.hops.length)
    (hT : pathBuilds geom (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver])
      ((RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]).size - x.2.2.c.pos)) :
    strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names) A x U u v
      = fnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 A ((forwardPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x))
          ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) x)) x.2.2.st x.2.2.log x.2.2.c.req x.2.2.o x.2.2.c.pos x.1 u v
          (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) x) default)).toArray) x.2.2.c.pos (Util.Bytes.ofVector U))
        (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x)
            default)).toArray) (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) x) default)).toArray) (blindElem nike (groupElem nike (drawKey nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S
            := 𝒮)) .relay names x.2.2) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) x) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) x) default)).toArray) := by
  have hlt := fwd_hops_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) x.2.2
  have hon : strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) x U u 0
      = layerFn nike macS kdfS streamS geom x.2.2.c.req x.2.2.o (Function.update (keysKs geom
          streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x)
          default)).toArray) x.2.2.c.pos (Util.Bytes.ofVector U)) (Function.update (keysTag macS
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x) default)).toArray)
          x.2.2.c.pos fun _ => Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) x U))
        (Function.update (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) x) default)).toArray) x.2.2.c.pos fun _ => Util.Bytes.ofVector u)
        (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2.2) (forwardKeys0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) x) default)).toArray 0)
            (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x)
            default)).toArray) 0 :=
    onionOfStream_eq_layerFn nike cipher macS kdfS streamS geom 0 x.2.2.c.req x.2.2.o (groupElem
        nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2.2) (forwardKeys0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) x) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) x) default))
      x.2.2.c.pos (Util.Bytes.ofVector U) (Util.Bytes.ofVector (strTag nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) x U))
      (Util.Bytes.ofVector u) hvalid hmactag (Nat.zero_le _)
      (by rw [RSOR.path_size]; exact x.2.2.c.pos.isLt)
      (le_of_lt (lt_of_lt_of_eq hlt (hopKeysWith_length nike kdfS _ _ _ _ _).symm))
      (Util.Bytes.size_ofVector _) ((Util.Bytes.size_ofVector _).trans hmactag)
      (by rw [Util.Bytes.size_ofVector]; exact h16) (Util.Bytes.size_ofVector _)
  rw [strRun_fwd0_eq nike cipher macS kdfS streamS geom hvalid hmactag h16 names A x U u v hj hT]
  unfold fnRun strGuess
  rw [ite_eq_left hlt, hon]
  rfl

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
