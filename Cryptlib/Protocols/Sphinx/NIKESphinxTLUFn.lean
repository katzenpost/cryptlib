/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUNext
import Cryptlib.Protocols.Sphinx.KEMSphinxTLUFinal
import Cryptlib.Protocols.Sphinx.KEMSphinxSLURelay

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

/-! # The last comparison of the two worlds of TLU→, for NIKE Sphinx: the hops' functions

Lemmas on headers, paddings and keystreams that do not mention the games: a layer from each
hop's keystream, tagging function, encryption and element, the blinding game, the padding after
a hop from the tail of its keystream, the keystream that joins the two worlds, and the relay as
the last hop. -/

section NextFn

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

/-- Layer `i` of `q`'s onion, from each hop's keystream, tag, encryption and element: the
header of layer `i` and the block the hops from `i` on left. -/
def layerFn (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (ks : ℕ → ByteArray)
    (tag enc : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) (i : ℕ) : Onion geom :=
  if (RSOR.body nike macS kdfS streamS geom q r).size = geom.forwardPayloadLength then
    match nikeHdrTrace geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
        q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
        [.recipient q.receiver]).size with
    | some _ => split geom (layerHdr geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd
        [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) i
      ++ encTrace enc (RSOR.path nike q.fwd [.recipient q.receiver]).size ((⟨Array.replicate
          geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS streamS geom q r))
          ((RSOR.path nike q.fwd [.recipient q.receiver]).size - i))
    | none => default
  else default

omit nike in
/-- Whether a hop's fragment builds does not depend on the tag it names. -/
theorem nikeFragment_isOk (path : Array PathHop) (mac mac' : ByteArray) (i : ℕ) :
    (nikeFragment geom path mac i).isOk = (nikeFragment geom path mac' i).isOk := by
  unfold nikeFragment
  generalize commandsToBytes _ _ = e
  cases e <;> simp only [bind, Except.bind, pure, Except.pure, Except.isOk, Except.toBool]

omit nike in
/-- Whether a header builds depends on the path alone. -/
theorem nikeHdrTrace_isSome (ks ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler filler' : ByteArray) (path : Array PathHop) (t : ℕ) :
    (nikeHdrTrace geom ks tag ge filler path t).isSome
      = (nikeHdrTrace geom ks' tag' ge' filler' path t).isSome := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [nikeHdrTrace, nikeHdrTrace]
    cases h : nikeHdrTrace geom ks tag ge filler path t with
    | none =>
      rw [h] at ih
      cases h' : nikeHdrTrace geom ks' tag' ge' filler' path t with
      | none => rfl
      | some s' => rw [h'] at ih; cases ih
    | some s =>
      rw [h] at ih
      cases h' : nikeHdrTrace geom ks' tag' ge' filler' path t with
      | none => rw [h'] at ih; cases ih
      | some s' =>
        dsimp only
        have hf := nikeFragment_isOk geom path s.2 s'.2 (path.size - 1 - t)
        cases hf1 : nikeFragment geom path s.2 (path.size - 1 - t) with
        | error e =>
          rw [hf1] at hf
          cases hf2 : nikeFragment geom path s'.2 (path.size - 1 - t) with
          | error e' => rfl
          | ok F' => rw [hf2] at hf; cases hf
        | ok F =>
          rw [hf1] at hf
          cases hf2 : nikeFragment geom path s'.2 (path.size - 1 - t) with
          | error e' => rw [hf2] at hf; cases hf
          | ok F' => rfl

omit nike cipher macS kdfS streamS in
/-- A header's bytes followed by any bytes split into the two. -/
theorem split_append_bytes (L X : ByteArray) (hL : L.size = geom.headerLength) :
    split geom (L ++ X) = (Util.Bytes.toVecN _ L, Util.Bytes.toVecN _ X) := by
  have e1 : (L ++ X).extract 0 geom.headerLength = L := by
    rw [← hL]
    exact Util.Bytes.extract_append_left L _
  have e2 : (L ++ X).extract geom.headerLength (L ++ X).size = X := by
    rw [← hL, ByteArray.size_append]
    exact Util.Bytes.extract_append_right L _
  unfold split
  rw [e1, e2]
  rfl

/-- **A layer of an onion that builds**: its header, then the block the hops from it on left. -/
theorem layerFn_eq (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (ks : ℕ → ByteArray) (tag enc : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) (i : ℕ)
    (hb : (RSOR.body nike macS kdfS streamS geom q r).size = geom.forwardPayloadLength)
    (hT : (nikeHdrTrace geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
        q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
        [.recipient q.receiver]).size).isSome) :
    layerFn nike macS kdfS streamS geom q r ks tag enc ge i
      = split geom (layerHdr geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd
          [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) i
        ++ encTrace enc (RSOR.path nike q.fwd [.recipient q.receiver]).size ((⟨Array.replicate
            geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS streamS geom q r))
            ((RSOR.path nike q.fwd [.recipient q.receiver]).size - i)) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hT
  unfold layerFn
  rw [ite_eq_left hb, hs]

/-- **The first layer is the packet.** -/
theorem layerFn_zero (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (ks : ℕ → ByteArray) (tag enc : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (hpos : 0 < (RSOR.path nike q.fwd [.recipient q.receiver]).size) :
    layerFn nike macS kdfS streamS geom q r ks tag enc ge 0
      = match nikePktFn geom ks tag enc ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
          q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver])
          (RSOR.body nike macS kdfS streamS geom q r) with
        | some pkt => split geom pkt
        | none => default := by
  unfold layerFn nikePktFn
  by_cases hb : (RSOR.body nike macS kdfS streamS geom q r).size = geom.forwardPayloadLength
  · rw [ite_eq_left hb, ite_eq_left hb]
    cases hs : nikeHdrTrace geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
        q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
        [.recipient q.receiver]).size with
    | none => rfl
    | some s =>
      show split geom (layerHdr geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd
          [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) 0 ++ _) =
          split geom (v0AD ++ ge 0 ++ s.1
        ++ s.2 ++ _)
      rw [← layerHdr_zero geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
          q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) s hpos hs]
      rfl
  · rw [ite_eq_right hb, ite_eq_right hb]

/-- The layer after hop `j` from the hops' keys and hop `j`'s keystream is `layerFn` on their
keystreams, tags, encryptions and elements. -/
theorem nextOfStream_eq_layerFn (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (a : ByteArray) (K : List HopKeys) (j : ℕ) (U : ByteArray)
    (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (hj : j + 1 < (RSOR.path nike q.fwd [.recipient q.receiver]).size) (hjk : j < K.length) (hU :
        U.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (ha : a.size = nike.publicKeySize) :
    nextOfStream nike cipher macS kdfS streamS geom q r a K j U
      = layerFn nike macS kdfS streamS geom q r
        (Function.update (keysKs geom streamS K.toArray) j U) (keysTag macS K.toArray)
        (keysEnc cipher K.toArray) (blindElem nike a K.toArray) (j + 1) :=
  nextOfStream_layerHdr nike cipher macS kdfS streamS geom q r a K j U hvalid hmactag hj hjk hU ha

set_option maxHeartbeats 1000000 in
/-- **The onion with hop `j`'s keystream, tag and encrypted block given, at a layer up to
`j`, in closed form**: the header of that layer of the header function, and the payload the
hops from that layer on left. -/
theorem onionOfStream_eq_layerFn (i : ℕ) (q : RSOR.Request nike geom)
    (r : RSOR.Randomness nike geom) (a : ByteArray) (K : List HopKeys) (j : ℕ)
    (U tg e : ByteArray) (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (hi : i ≤ j) (hj : j < (RSOR.path nike q.fwd [.recipient q.receiver]).size) (hjk : j ≤
        K.length) (hU : U.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htg : tg.size = macLength) (he : 16 ≤ e.size) (ha : a.size = nike.publicKeySize) :
    onionOfStream nike cipher macS kdfS streamS geom i q r a K j U tg e
      = layerFn nike macS kdfS streamS geom q r (Function.update (keysKs geom streamS K.toArray) j
          U) (Function.update (keysTag macS K.toArray) j fun _ => tg) (Function.update (keysEnc
          cipher K.toArray) j fun _ => e) (blindElem nike a K.toArray) i := by
  obtain ⟨hnnh, hper, hrouting, -⟩ := id hvalid
  have hsz := RSOR.path_size nike q.fwd [.recipient q.receiver]
  have hn : (RSOR.path nike q.fwd [.recipient q.receiver]).size ≤ geom.nrHops := by
    rw [hsz]
    exact q.fwd.length_le
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
  have hks : ∀ k, ((Function.update (keysKs geom streamS K.toArray) j U) k).size =
      (geom.routingInfoLength + geom.perHopRoutingInfoLength) := fun k => by
    by_cases hk : k = j
    · rw [hk, Function.update_self]
      exact hU
    · rw [Function.update_of_ne hk]
      exact streamS.keystream_size _ _ _
  have htag : ∀ (m : ℕ) (x : ByteArray), ((Function.update (keysTag macS K.toArray) j fun _ => tg)
      m x).size = macLength := fun m x => by
    by_cases hm : m = j
    · rw [hm, Function.update_self]
      exact htg
    · rw [Function.update_of_ne hm]
      exact (Util.Bytes.size_ofVector _).trans hmactag
  have hcmd : ∀ i, i + 1 < (RSOR.path nike q.fwd [.recipient q.receiver]).size → (RSOR.path nike
      q.fwd [.recipient q.receiver])[i]!.commands = [] := fun i hi => by
    rw [RSOR.path_getElem! nike _ _ i (by omega)]
    exact ite_eq_right (by omega)
  unfold onionOfStream nikePktFn layerFn
  by_cases hb : (RSOR.body nike macS kdfS streamS geom q r).size = geom.forwardPayloadLength
  · rw [ite_eq_left hb, ite_eq_left hb]
    cases hs : nikeHdrTrace geom (Function.update (keysKs geom streamS K.toArray) j U)
        (Function.update (keysTag macS K.toArray) j fun _ => tg) (blindElem nike a K.toArray)
        (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike
        q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd [.recipient q.receiver]).size with
    | none => rfl
    | some s =>
      dsimp only
      have hH := hdr_size geom nike.publicKeySize (Function.update (keysKs geom streamS K.toArray)
          j U) (Function.update (keysTag macS K.toArray) j fun _ => tg) (blindElem nike a
          K.toArray) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1)
          (RSOR.path nike q.fwd [.recipient q.receiver]) hnnh (by omega)
        hrouting hn (by omega) hfill htag ha s hs
      have hpe := peels_enc nike cipher streamS geom K (Function.update (keysEnc cipher K.toArray)
          j fun _ => e) (RSOR.path nike q.fwd [.recipient q.receiver]).size ((⟨Array.replicate
          geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS streamS geom q r)) _
          hH i (by omega)
        (by omega) (fun m hm => Function.update_of_ne (by omega) _ _) (fun m hm => by
          rw [encTrace_size_const (Function.update (keysEnc cipher K.toArray) j fun _ => e)
              (RSOR.path nike q.fwd [.recipient q.receiver]).size ((⟨Array.replicate
              geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS streamS geom q r))
              e j hj
            (fun b => by rw [Function.update_self])
            (fun m' hm' b => by
              rw [Function.update_of_ne (by omega)]
              exact cipher.encrypt_size _ _ _) _ (by omega) (by omega)]
          exact he)
      have hlh := (hdrPeels_layerHdr nike geom streamS K (Function.update (keysKs geom streamS
          K.toArray) j U) (Function.update (keysTag macS K.toArray) j fun _ => tg) (blindElem nike
          a K.toArray) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1)
          (RSOR.path nike q.fwd [.recipient q.receiver]) hnnh
        (by omega) hrouting hn hfill hks htag ha hcmd (by rw [hs]; rfl) i (by omega) (by omega)
        (fun m hm => (Function.update_of_ne (by omega) _ _).symm) (fun m hm => rfl)).1
      rw [← layerHdr_zero geom _ _ _ _ _ s (by omega) hs] at hlh
      exact congrArg (split geom) (hpe.2.trans (congrArg (· ++ _) hlh))
  · rw [ite_eq_right hb, ite_eq_right hb]

end NextFn

/-! ## The relay's step under a layer's header -/

section Step

variable (nike : NIKE) (geom : Geometry)

/-- **The header of the layer after a hop has a header's length**: its tagged bytes are the
element, what is left of the routing information, and the padding of the hops up to that hop. -/
theorem layerHdr_succ_size (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (i : ℕ)
    (hi : i + 1 < path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hcmd : path[i]!.commands = [])
    (hT : (nikeHdrTrace geom ks tag ge filler path (path.size - i)).isSome)
    (hge : (ge (i + 1)).size = nike.publicKeySize) :
    (layerHdr geom ks tag ge filler path (i + 1)).size
      = 2 + nike.publicKeySize + geom.routingInfoLength + macLength := by
  obtain ⟨F, B, -, h2, hF, hFB, -⟩ := hdrMsg_struct geom ks tag ge filler path i hi hnnh hle
    hrouting hn hfill hks htag hcmd hT
  have hmulle : (i + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting]
    exact (Nat.mul_comm _ _).le.trans (Nat.mul_le_mul_left _ (by omega))
  have hv : v0AD.size = 2 := rfl
  have hp := padAt_size geom ks hks i (by omega)
  unfold layerHdr
  rw [ByteArray.size_append, htag, h2, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_append, hv, hge, hp]
  omega

/-- **The bytes under the tag of a layer before the last have their length.** -/
theorem hdrMsg_size (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (filler : ByteArray) (path : Array PathHop) (i : ℕ)
    (hi : i + 1 < path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hcmd : path[i]!.commands = [])
    (hT : (nikeHdrTrace geom ks tag ge filler path (path.size - i)).isSome)
    (hge : (ge i).size = nike.publicKeySize) :
    (hdrMsg geom ks tag ge filler path i).size
      = 2 + nike.publicKeySize + geom.routingInfoLength := by
  obtain ⟨F, B, h1, -, hF, hFB, -, h6, -⟩ := hdrMsg_struct geom ks tag ge filler path i hi hnnh
    hle hrouting hn hfill hks htag hcmd hT
  have hv : v0AD.size = 2 := rfl
  rw [h1]
  simp only [ByteArray.size_append, Cryptlib.Protocols.Sphinx.Common.size_xorBytes, hv, hge]
  omega

omit nike in
/-- A path's header builds through its last `n` hops. This depends on the path alone
(`nikeHdrTrace_isSome`). -/
def pathBuilds (path : Array PathHop) (n : ℕ) : Prop :=
  (nikeHdrTrace geom (fun _ => ByteArray.empty) (fun _ _ => ByteArray.empty)
    (fun _ => ByteArray.empty) ByteArray.empty path n).isSome = true

omit nike in
instance (path : Array PathHop) (n : ℕ) : Decidable (pathBuilds geom path n) := by
  unfold pathBuilds
  infer_instance

omit nike in
/-- The fragment of hop `i` of a path that names no tag, empty when it does not build. -/
def lastFrag (path : Array PathHop) (i : ℕ) : ByteArray :=
  match nikeFragment geom path ByteArray.empty i with
  | .ok F => F
  | .error _ => ByteArray.empty

omit nike in
/-- A path whose header builds through its last hop has a fragment for that hop. -/
theorem pathBuilds_fragment (path : Array PathHop) (h : pathBuilds geom path 1) :
    ∃ F, nikeFragment geom path ByteArray.empty (path.size - 1) = .ok F := by
  unfold pathBuilds at h
  rw [nikeHdrTrace, nikeHdrTrace] at h
  dsimp only at h
  cases hf : nikeFragment geom path ByteArray.empty (path.size - 1) with
  | ok F => exact ⟨F, rfl⟩
  | error e =>
    have hf' : nikeFragment geom path ByteArray.empty (path.size - 1 - 0) = .error e := hf
    rw [hf'] at h
    cases h

set_option maxHeartbeats 2000000 in
/-- **What a relay answers for a layer before the last, in the games' form.** A relay that
holds the layer's tag and keystream, and is handed the payload's decryption `y`, forwards the
next layer's header with `y`. -/
theorem procD_join_layerHdr {n : ℕ} (T : Vector UInt8 n) (U : ByteArray) (t : HopKeys)
    (y : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) (i : ℕ) (o : Onion geom)
    (hi : i + 1 < path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength) (hrouting :
        geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength) (hks : ∀ k,
        (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hge : (ge i).size = nike.publicKeySize)
    (hcmd : path[i]!.commands = []) (hT : (nikeHdrTrace geom ks tag ge filler path (path.size -
        i)).isSome)
    (hksi : ks i = U) (htagi : tag i (hdrMsg geom ks tag ge filler path i) = Util.Bytes.ofVector T)
    (hblind : nikeBlind nike (ge i) t.blindingFactor = ge (i + 1))
    (ho : Util.Bytes.ofVector o.1 = layerHdr geom ks tag ge filler path i)
    (hL : 0 < geom.payloadTagLength + geom.forwardPayloadLength) :
    procD nike (Primitives.MAC.MAC.const T) (constStream U) geom (fun _ => .ok t)
        (fun _ _ => y) (join o)
      = some (none, Primitives.Hash.Sha512.sha512_256 (ge i),
        [RoutingCommand.nextNodeHop path[i + 1]!.id
          (toVec32 (tag (i + 1) (hdrMsg geom ks tag ge filler path (i + 1))))],
        some (layerHdr geom ks tag ge filler path (i + 1) ++ Util.Bytes.ofVector y)) := by
  have hz : (⟨Array.replicate (geom.routingInfoLength + geom.perHopRoutingInfoLength) (0 : UInt8)⟩
      : ByteArray).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) :=
      Array.size_replicate
  have hksi' : (constStream U).keystream (Util.Bytes.ofVector t.headerEncryption)
      (Util.Bytes.ofVector t.headerEncryptionIV) (geom.routingInfoLength +
          geom.perHopRoutingInfoLength) = ks i := by
    have h := Util.Bytes.extract_append_left (ks i) (⟨Array.replicate (geom.routingInfoLength +
        geom.perHopRoutingInfoLength) 0⟩ : ByteArray)
    rw [hks i] at h
    rw [← hksi]
    exact h
  unfold join
  rw [ho, procD_layerHdr nike (Primitives.MAC.MAC.const T) (constStream U) geom t (fun _ _ => y)
    ks tag ge filler path i (Util.Bytes.ofVector o.2) hi hnnh hle hrouting hn hfill hks htag hge
    hcmd hT hksi' htagi.symm hblind (Util.Bytes.size_ofVector _) hL]

/-- So its step is to forward that layer to the next hop. -/
theorem stepOf_layerHdr {n : ℕ} (T : Vector UInt8 n) (U : ByteArray) (t : HopKeys)
    (y : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) (i : ℕ) (o : Onion geom)
    (hi : i + 1 < path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength) (hrouting :
        geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength) (hks : ∀ k,
        (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hge : (ge i).size = nike.publicKeySize)
    (hcmd : path[i]!.commands = []) (hT : (nikeHdrTrace geom ks tag ge filler path (path.size -
        i)).isSome)
    (hksi : ks i = U) (htagi : tag i (hdrMsg geom ks tag ge filler path i) = Util.Bytes.ofVector T)
    (hblind : nikeBlind nike (ge i) t.blindingFactor = ge (i + 1))
    (ho : Util.Bytes.ofVector o.1 = layerHdr geom ks tag ge filler path i)
    (hL : 0 < geom.payloadTagLength + geom.forwardPayloadLength) :
    stepOf geom (procD nike (Primitives.MAC.MAC.const T) (constStream U) geom (fun _ => .ok t)
        (fun _ _ => y) (join o))
      = some (.forward path[i + 1]!.id
        (split geom (layerHdr geom ks tag ge filler path (i + 1) ++ Util.Bytes.ofVector y))) := by
  rw [procD_join_layerHdr nike geom T U t y ks tag ge filler path i o hi hnnh hle hrouting hn hfill
      hks htag hge hcmd hT hksi htagi
    hblind ho hL]
  rfl

/-- And it does not reply. -/
theorem replyOf_layerHdr (cipher : WideBlockCipher) (m : Msg geom) {n : ℕ} (T : Vector UInt8 n) (U
    : ByteArray) (t : HopKeys)
    (y : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) (i : ℕ) (o : Onion geom)
    (hi : i + 1 < path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength) (hrouting :
        geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength) (hks : ∀ k,
        (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hge : (ge i).size = nike.publicKeySize)
    (hcmd : path[i]!.commands = []) (hT : (nikeHdrTrace geom ks tag ge filler path (path.size -
        i)).isSome)
    (hksi : ks i = U) (htagi : tag i (hdrMsg geom ks tag ge filler path i) = Util.Bytes.ofVector T)
    (hblind : nikeBlind nike (ge i) t.blindingFactor = ge (i + 1))
    (ho : Util.Bytes.ofVector o.1 = layerHdr geom ks tag ge filler path i)
    (hL : 0 < geom.payloadTagLength + geom.forwardPayloadLength) :
    replyOf cipher geom m (procD nike (Primitives.MAC.MAC.const T) (constStream U) geom (fun _ =>
        .ok t)
        (fun _ _ => y) (join o)) = none := by
  rw [procD_join_layerHdr nike geom T U t y ks tag ge filler path i o hi hnnh hle hrouting hn hfill
      hks htag hge hcmd hT hksi htagi
    hblind ho hL]
  rfl

end Step

/-! ## The keys of a path cut at a hop -/

section Cut

variable (nike : NIKE) (kdfS : KDF)

/-- The first keys of a longer list of hops' keys are the keys of the first hops. -/
theorem hopKeysWith_take_le (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (t : HopKeys)
    (m n : ℕ) (h : m ≤ n) :
    (hopKeysWith nike kdfS c hops j t n).take m = hopKeysWith nike kdfS c hops j t m := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    rfl
  | succ n ih =>
    by_cases hm : m ≤ n
    · rw [hopKeysWith, List.take_append_of_le_length (by rw [hopKeysWith_length]; exact hm)]
      exact ih hm
    · obtain rfl : m = n + 1 := by omega
      exact List.take_of_length_le (by rw [hopKeysWith_length])

/-- The keys of the first `n` hops read those hops' public keys only. -/
theorem hopKeysWith_congr_hops (c : nike.PrivateKey) (hops hops' : Array PathHop) (j : ℕ)
    (t : HopKeys) (n : ℕ) (h : ∀ i < n, hops[i]!.publicKey = hops'[i]!.publicKey) :
    hopKeysWith nike kdfS c hops j t n = hopKeysWith nike kdfS c hops' j t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hopKeysWith, hopKeysWith, ih fun i hi => h i (by omega), h n (Nat.lt_succ_self n)]

/-- **The keys of a path cut after hop `n - 1` are the first `n` keys of the whole path's**,
entry by entry. -/
theorem hopKeysWith_cut (c : nike.PrivateKey) (hops hops' : Array PathHop) (j : ℕ) (t : HopKeys)
    (n n' : ℕ) (hn : n ≤ n') (h : ∀ i < n, hops[i]!.publicKey = hops'[i]!.publicKey) (i : ℕ)
    (hi : i < n) :
    (hopKeysWith nike kdfS c hops j t n).toArray[i]!
      = (hopKeysWith nike kdfS c hops' j t n').toArray[i]! := by
  refine toArray_getElem!_congr _ _ i ?_
  rw [hopKeysWith_congr_hops nike kdfS c hops hops' j t n h,
    ← hopKeysWith_take_le nike kdfS c hops' j t n n' hn, List.getElem?_take, ite_eq_left hi]

end Cut

section Front

variable (nike : NIKE) (kdfS : KDF)

/-- The keys of the hops before hop `j` do not read the keys put at hop `j`. -/
theorem hopKeysWith_front (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (t t' : HopKeys)
    (m : ℕ) (hm : m ≤ j) :
    hopKeysWith nike kdfS c hops j t m = hopKeysWith nike kdfS c hops j t' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hne : ¬ m = j := by omega
    rw [hopKeysWith, hopKeysWith, ih (by omega)]
    simp only [hne, ↓reduceIte]

/-- So a hop before hop `j` has the same keys whatever is put at hop `j`. -/
theorem hopKeysWith_getElem!_lt (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ)
    (t t' : HopKeys) (n i : ℕ) (hi : i < j) (hn : j ≤ n) :
    (hopKeysWith nike kdfS c hops j t n).toArray[i]!
      = (hopKeysWith nike kdfS c hops j t' n).toArray[i]! := by
  have h : ∀ s, (hopKeysWith nike kdfS c hops j s n)[i]?
      = (hopKeysWith nike kdfS c hops j s j)[i]? := fun s => by
    rw [← hopKeysWith_take_le nike kdfS c hops j s j n hn]
    simp [hi]
  exact toArray_getElem!_congr _ _ i ((h t).trans ((congrArg (·[i]?)
    (hopKeysWith_front nike kdfS c hops j t t' j le_rfl)).trans (h t').symm))

end Front

/-! ## The blinding game

The hops after the honest relay get their keys from the sender's secret and the relay's
blinding factor, and the element that reaches them is the sender's, blinded. When the relay's
blinding factor is uniform, a prime-order group makes all of this independent of the sender's
secret. The NIKE type does not say so, and with clamped scalars it need not hold exactly, so
it is a game: its advantage is a term of the bound. -/

section Blind

variable (nike : NIKE) (kdfS : KDF)

/-- What lies after hop `j` of a path: the element that reaches hop `j + 1` and the keys of the
hops after `j`, from the sender's secret `c` and the seed of hop `j`'s blinding factor. -/
def tailOf (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (seed : Vector UInt8 32) :
    ByteArray × List HopKeys :=
  (groupElem nike c
      (hopKeysWith nike kdfS c hops j (keysOfDraw (default, seed)) hops.size).toArray (j + 1),
    (hopKeysWith nike kdfS c hops j (keysOfDraw (default, seed)) hops.size).drop (j + 1))

/-- **The tail of a path with a hop's keys replaced is `tailOf`**, whatever the other keys of
the replacement. -/
theorem tailOf_hopKeysWith (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ)
    (seed : Vector UInt8 32) (t : HopKeys) (hj : j < hops.size)
    (ht : t.blindingFactor = blindingFactorPrivKey seed) :
    tailOf nike kdfS c hops j seed
      = (groupElem nike c (hopKeysWith nike kdfS c hops j t hops.size).toArray (j + 1),
        (hopKeysWith nike kdfS c hops j t hops.size).drop (j + 1)) := by
  have hf : RSOR.factor nike (keysOfDraw (default, seed)) = RSOR.factor nike t := by
    unfold RSOR.factor
    rw [ht]
    rfl
  have hk : ∀ t' : HopKeys, (hopKeysWith nike kdfS c hops j t' hops.size).toArray[j]! = t' :=
    fun t' => toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS c hops j t' _ hj)
  have hg : ∀ t' : HopKeys, groupElem nike c (hopKeysWith nike kdfS c hops j t'
      hops.size).toArray (j + 1)
      = nikeBlind nike (groupElem nike c (RSOR.hopKeys nike kdfS c hops j).toArray j)
        t'.blindingFactor := fun t' => by
    show nikeBlind nike _ _ = _
    rw [groupElem_hopKeysWith nike kdfS c hops j t' hops.size (le_of_lt hj), hk]
  unfold tailOf
  rw [hg, hg, ht]
  refine congrArg (Prod.mk _) (List.ext_getElem? fun m => ?_)
  rw [List.getElem?_drop, List.getElem?_drop]
  exact (hopKeysWith_congr nike kdfS c hops j _ _ hf hops.size).2 (j + 1 + m) (by omega)

/-- A hop's keys in the list cut before hop `m` are the keys `m` places on in the whole list. -/
theorem toArray_drop_getElem! (L : List HopKeys) (m i : ℕ) :
    (L.drop m).toArray[i]! = L.toArray[m + i]! := by
  simp [getElem!_def, List.getElem?_drop]

/-- **The elements after hop `m` are the element that reaches it, blinded by the later hops'
factors.** -/
theorem blindElem_drop (a : ByteArray) (L : List HopKeys) (m i : ℕ) :
    blindElem nike (blindElem nike a L.toArray m) (L.drop m).toArray i
      = blindElem nike a L.toArray (m + i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show nikeBlind nike _ _ = nikeBlind nike _ _
    rw [ih, toArray_drop_getElem!]
    rfl

/-- The functions of a path's hops, those up to hop `j` from `f` and the later ones from `g`,
which counts from the hop after `j`. -/
def spliceAt {α : Type} (j : ℕ) (f g : ℕ → α) (i : ℕ) : α :=
  if i ≤ j then f i else g (i - (j + 1))

theorem spliceAt_le {α : Type} (j : ℕ) (f g : ℕ → α) (i : ℕ) (hi : i ≤ j) :
    spliceAt j f g i = f i :=
  ite_eq_left hi

theorem spliceAt_gt {α : Type} (j : ℕ) (f g : ℕ → α) (i : ℕ) (hi : j < i) :
    spliceAt j f g i = g (i - (j + 1)) :=
  ite_eq_right (by omega)

theorem spliceAt_congr_le {α : Type} (j : ℕ) (f f' g : ℕ → α) (h : ∀ i, i ≤ j → f i = f' i) :
    spliceAt j f g = spliceAt j f' g := by
  funext i
  by_cases hi : i ≤ j
  · rw [spliceAt_le j _ _ i hi, spliceAt_le j _ _ i hi, h i hi]
  · rw [spliceAt_gt j _ _ i (by omega), spliceAt_gt j _ _ i (by omega)]

theorem spliceAt_update {α : Type} (j : ℕ) (f g : ℕ → α) (x : α) :
    spliceAt j (Function.update f j x) g = Function.update (spliceAt j f g) j x := by
  funext i
  by_cases hi : i = j
  · rw [hi, Function.update_self, spliceAt_le j _ _ j le_rfl, Function.update_self]
  · rw [Function.update_of_ne hi]
    by_cases hl : i ≤ j
    · rw [spliceAt_le j _ _ i hl, spliceAt_le j _ _ i hl, Function.update_of_ne hi]
    · rw [spliceAt_gt j _ _ i (by omega), spliceAt_gt j _ _ i (by omega)]

/-- **Functions that are the hops' keys' after hop `j`, spliced with the keys' after hop `j`,
are themselves.** -/
theorem spliceAt_drop {α : Type} (F : Array HopKeys → ℕ → α)
    (hF : ∀ (K K' : Array HopKeys) (i i' : ℕ), K[i]! = K'[i']! → F K i = F K' i')
    (L : List HopKeys) (j : ℕ) (f : ℕ → α) (hf : ∀ i, j < i → f i = F L.toArray i) :
    spliceAt j f (F (L.drop (j + 1)).toArray) = f := by
  funext i
  by_cases hi : i ≤ j
  · exact spliceAt_le j _ _ i hi
  · rw [spliceAt_gt j _ _ i (by omega), hf i (by omega)]
    exact hF _ _ _ _ (by rw [toArray_drop_getElem!, show j + 1 + (i - (j + 1)) = i by omega])

/-- **The elements, spliced with those after hop `j` counted from the element that reaches the
next hop, are the elements.** -/
theorem spliceAt_blindElem (a : ByteArray) (L : List HopKeys) (j : ℕ) :
    spliceAt j (blindElem nike a L.toArray)
        (blindElem nike (blindElem nike a L.toArray (j + 1)) (L.drop (j + 1)).toArray)
      = blindElem nike a L.toArray := by
  funext i
  by_cases hi : i ≤ j
  · exact spliceAt_le j _ _ i hi
  · rw [spliceAt_gt j _ _ i (by omega), blindElem_drop,
      show j + 1 + (i - (j + 1)) = i by omega]

/-- An adversary on the blinding game: it names a secret, a path and a hop, and is given what
lies after the hop. -/
structure BlindAdversary where
  St : Type
  pre : ProbComp ((nike.PrivateKey × Array PathHop × ℕ) × St)
  post : St → ByteArray × List HopKeys → ProbComp Bool

variable {nike} in
/-- **The blinding game.** What lies after the hop comes from the adversary's secret, or from
an independent uniform one. The hop's blinding factor is uniform. -/
def blindGame (B : BlindAdversary nike) (b : Bool) : ProbComp Bool := do
  let x ← B.pre
  let seed ← $ᵗ (Vector UInt8 32)
  let d ← $ᵗ (Vector UInt8 nike.privateKeySize)
  B.post x.2 (tailOf nike kdfS (if b then (nike.decodePrivateKey d).getD default else x.1.1)
    x.1.2.1 x.1.2.2 seed)

variable {nike} in
/-- The adversary's advantage in the blinding game. -/
noncomputable def blindAdvantage (B : BlindAdversary nike) : ℝ :=
  |(Pr{let x ← blindGame kdfS B true}[x = true]).toReal
    - (Pr{let x ← blindGame kdfS B false}[x = true]).toReal|

end Blind

/-! ## The padding after the relay, from the tail of its keystream -/

section Pad

/-- XOR with a mask followed by zero bytes changes the bytes under the mask only. -/
theorem xorBytes_pad (X p : ByteArray) (z : ℕ) (hs : p.size ≤ X.size)
    (hz : X.size - p.size ≤ z) :
    xorBytes X (p ++ KEMSphinx.zeroBytes z)
      = xorBytes (X.extract 0 p.size) p ++ X.extract p.size X.size := by
  have h1 : (X.extract 0 p.size).size = p.size := by
    rw [ByteArray.size_extract]
    omega
  have h2 : (X.extract p.size X.size).size ≤ (KEMSphinx.zeroBytes z).size := by
    rw [ByteArray.size_extract, KEMSphinx.zeroBytes_size]
    omega
  conv_lhs => rw [← Util.Bytes.append_extract X p.size hs]
  rw [Cryptlib.Protocols.Sphinx.Common.xorBytes_append _ _ _ _ h1 h2,
    KEMSphinx.xorBytes_zeroBytes]

variable (geom : Geometry)

/-- The padding in front of hop `j` has `j` hops' length. -/
theorem padFront_size (ks : ℕ → ByteArray) (hks : ∀ k, (ks k).size = (geom.routingInfoLength +
    geom.perHopRoutingInfoLength)) (j : ℕ)
    (hj : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength) :
    (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty).size = j *
        geom.perHopRoutingInfoLength := by
  by_cases hp : j > 0
  · rw [ite_eq_left hp, padAt_size geom ks hks (j - 1) (by
        rw [show j - 1 + 1 = j by omega]
        have : j * geom.perHopRoutingInfoLength ≤ (j + 1) * geom.perHopRoutingInfoLength :=
          Nat.mul_le_mul_right _ (Nat.le_succ j)
        omega), show j - 1 + 1 = j by omega]
  · rw [ite_eq_right hp, show j = 0 by omega, Nat.zero_mul]
    rfl

/-- **The padding after a hop, from the tail of its keystream.** If the tail of hop `j`'s
keystream is the padding another header has after hop `j`, with this header's padding in front
masked in, then the two paddings after hop `j` are the same. -/
theorem padAt_of_tail (ks ksI : ℕ → ByteArray)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hksI : ∀ k,
        (ksI k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j : ℕ)
    (hj : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength)
    (htail : (ks j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength) (ks j).size
      = xorBytes (KEMSphinx.padAt geom ksI j)
        ((if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty) ++
            KEMSphinx.zeroBytes geom.perHopRoutingInfoLength)) :
    KEMSphinx.padAt geom ks j = KEMSphinx.padAt geom ksI j := by
  have hI := padAt_size geom ksI hksI j (by omega)
  have h0 : (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty).size = j *
      geom.perHopRoutingInfoLength :=
    padFront_size geom ks hks j hj
  have hsucc : (j + 1) * geom.perHopRoutingInfoLength
      = j * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
  rw [padAt_step geom ks hks j, htail,
    xorBytes_pad _ _ _ (by rw [hI, h0]; omega) (by rw [hI, h0]; omega)]
  have hQ : (xorBytes ((KEMSphinx.padAt geom ksI j).extract 0 (if j > 0 then KEMSphinx.padAt geom
      ks (j - 1) else ByteArray.empty).size) (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else
      ByteArray.empty)).size
      = (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty).size := by
    rw [Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract, hI, h0]
    omega
  have e1 := Util.Bytes.extract_append_left
    (xorBytes ((KEMSphinx.padAt geom ksI j).extract 0 (if j > 0 then KEMSphinx.padAt geom ks (j -
        1) else ByteArray.empty).size) (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else
        ByteArray.empty))
    ((KEMSphinx.padAt geom ksI j).extract (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else
        ByteArray.empty).size (KEMSphinx.padAt geom ksI j).size)
  have e2 := Util.Bytes.extract_append_right
    (xorBytes ((KEMSphinx.padAt geom ksI j).extract 0 (if j > 0 then KEMSphinx.padAt geom ks (j -
        1) else ByteArray.empty).size) (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else
        ByteArray.empty))
    ((KEMSphinx.padAt geom ksI j).extract (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else
        ByteArray.empty).size (KEMSphinx.padAt geom ksI j).size)
  rw [hQ] at e1 e2
  rw [ByteArray.size_append, hQ, e1, e2, Cryptlib.Protocols.Sphinx.Common.xorBytes_xorBytes,
    Util.Bytes.append_extract _ _ (by rw [hI, h0]; omega)]

/-- **The same, from the tail of the other header's keystream**: the tail of hop `j`'s
keystream is the other's, with the two paddings in front masked in. -/
theorem padAt_of_tails (ks ksI : ℕ → ByteArray)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hksI : ∀ k,
        (ksI k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j : ℕ)
    (hj : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength)
    (htail : (ks j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength) (ks j).size
      = xorBytes ((ksI j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j +
          1) * geom.perHopRoutingInfoLength) (ksI j).size)
        (xorBytes ((if j > 0 then KEMSphinx.padAt geom ksI (j - 1) else ByteArray.empty) ++
            KEMSphinx.zeroBytes geom.perHopRoutingInfoLength) ((if j > 0 then KEMSphinx.padAt geom
            ks (j - 1) else ByteArray.empty) ++ KEMSphinx.zeroBytes geom.perHopRoutingInfoLength)))
            :
    KEMSphinx.padAt geom ks j = KEMSphinx.padAt geom ksI j := by
  have h0 := padFront_size geom ks hks j hj
  have hI := padFront_size geom ksI hksI j hj
  have hsucc : (j + 1) * geom.perHopRoutingInfoLength
      = j * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
  have ht : ((ksI j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength) (ksI j).size).size
      = j * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := by
    rw [ByteArray.size_extract, hksI]
    omega
  refine padAt_of_tail geom ks ksI hks hksI j hj ?_
  rw [htail, ← KEMSphinx.xorBytes_assoc _ _ _
    (by rw [ht, ByteArray.size_append, hI, KEMSphinx.zeroBytes_size])
    (by rw [ByteArray.size_append, ByteArray.size_append, hI, h0])]
  refine congrArg (fun X => xorBytes X _) ?_
  rw [padAt_step geom ksI hksI j, xorBytes_pad _ _ _ (by rw [ht, hI]; omega)
    (by rw [ht, hI]; omega)]

/-- The mask between the tails of two keystreams of hop `j` that makes the paddings after hop
`j` agree: the two paddings in front, each followed by a hop's length of zero bytes. -/
def padMask (ks ksI : ℕ → ByteArray) (j : ℕ) : ByteArray :=
  xorBytes ((if j > 0 then KEMSphinx.padAt geom ksI (j - 1) else ByteArray.empty) ++
      KEMSphinx.zeroBytes geom.perHopRoutingInfoLength)
    ((if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty) ++ KEMSphinx.zeroBytes
        geom.perHopRoutingInfoLength)

/-- **A keystream for hop `j` whose tail is another header's, masked, gives that header's
padding after hop `j`**, whatever its head `X`. -/
theorem padAt_comb (ks ksI : ℕ → ByteArray)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hksI : ∀ k,
        (ksI k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j : ℕ)
    (hj : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength) (X : ByteArray)
    (hX : X.size = ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength)) :
    KEMSphinx.padAt geom (Function.update ks j
        (X ++ xorBytes ((ksI j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) -
            (j + 1) * geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j))) j
      = KEMSphinx.padAt geom ksI j := by
  have ht : (xorBytes ((ksI j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) -
      (j + 1) * geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j)).size
      = (j + 1) * geom.perHopRoutingInfoLength := by
    rw [Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract, hksI]
    omega
  have hks' : ∀ k, ((Function.update ks j
      (X ++ xorBytes ((ksI j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j
          + 1) * geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j))) k).size
      = (geom.routingInfoLength + geom.perHopRoutingInfoLength) := fun k => by
    by_cases hk : k = j
    · rw [hk, Function.update_self, ByteArray.size_append, hX, ht]
      omega
    · rw [Function.update_of_ne hk]
      exact hks k
  have hfront : (if j > 0 then KEMSphinx.padAt geom (Function.update ks j
      (X ++ xorBytes ((ksI j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j
          + 1) * geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j))) (j - 1)
      else ByteArray.empty)
      = (if j > 0 then KEMSphinx.padAt geom ks (j - 1) else ByteArray.empty) := by
    by_cases hp : j > 0
    · rw [ite_eq_left hp, ite_eq_left hp]
      exact padAt_congr_rest geom _ _ hks' hks (j - 1)
        (fun i hi => Function.update_of_ne (by omega) _ _)
        (by rw [Function.update_of_ne (by omega)])
    · rw [ite_eq_right hp, ite_eq_right hp]
  refine padAt_of_tails geom _ ksI hks' hksI j hj ?_
  rw [hfront, Function.update_self]
  have e := Util.Bytes.extract_append_right X
    (xorBytes ((ksI j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j))
  rw [hX] at e
  rw [ByteArray.size_append, hX, e]
  rfl

/-- The mask reads the other header's keystreams in front of hop `j` only. -/
theorem padMask_congr (ks ksI ksI' : ℕ → ByteArray)
    (hksI : ∀ k, (ksI k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (hksI' : ∀ k, (ksI' k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (j : ℕ) (h : ∀ i < j, ksI i = ksI' i) :
    padMask geom ks ksI j = padMask geom ks ksI' j := by
  unfold padMask
  by_cases hp : j > 0
  · rw [padAt_congr_rest geom ksI ksI' hksI hksI' (j - 1) (fun i hi => h i (by omega))
      (by rw [h (j - 1) (by omega)])]
  · obtain rfl : j = 0 := by omega
    rfl

end Pad

/-! ## The relay's keystream that joins the two worlds -/

section Comb

variable (nike : NIKE) (geom : Geometry)

/-- **The keystream of the relay in world 0 that matches world 1.** Its tail is the tail of
the keystream `ksI j`, masked so that the padding after the relay is that of `ksI`. Its head
is the head of `U`, shifted by the difference between the content `X` and what the relay's
keystream masks in the header of `ks`. -/
def combStream (ks ksI : ℕ → ByteArray) (j : ℕ) (U X : ByteArray)
    (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) (filler : ByteArray)
    (path : Array PathHop) : ByteArray :=
  (xorBytes (U.extract 0 ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength)) (xorBytes X (hopContent nike geom (Function.update ks j
      (KEMSphinx.zeroBytes ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength) ++ (xorBytes ((ksI j).extract ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) (ksI j).size)
      (padMask geom ks ksI j)))) tag ge filler path j))) ++ (xorBytes ((ksI j).extract
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j))

/-- **With the joining keystream, the bytes under the relay's tag are those of a header that
ends at the relay**, and the hops in front are the same. -/
theorem hdrMsg_comb (ks ksI ks' : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (filler filler' : ByteArray) (path path' : Array PathHop) (j : ℕ)
    (hi : j + 1 < path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hksI : ∀ k,
        (ksI k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (hks' : ∀ k, (ks' k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (htag : ∀
        m x, (tag m x).size = macLength)
    (hcmd : path[j]!.commands = []) (hT : pathBuilds geom path (path.size - j))
    (hge1 : (ge (j + 1)).size = nike.publicKeySize) (hi' : j + 1 = path'.size) (F' : ByteArray)
    (hF' : nikeFragment geom path' ByteArray.empty j = .ok F')
    (hX' : (F' ++ (if geom.nrHops > path'.size then filler' else ByteArray.empty)).size =
        ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength))
    (hge : ge j = ge' j) (hfront : ∀ m < j, ks m = ks' m) :
    hdrMsg geom (Function.update ks j
        (combStream nike geom ks ksI j (ks' j) (F' ++ (if geom.nrHops > path'.size then filler'
            else ByteArray.empty)) tag ge filler path)) tag ge filler path j
      = hdrMsg geom ks' tag' ge' filler' path' j := by
  have hjp : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting]
    exact (Nat.mul_comm _ _).le.trans (Nat.mul_le_mul_left _ (by omega))
  have hHD : (xorBytes ((ks' j).extract 0 ((geom.routingInfoLength + geom.perHopRoutingInfoLength)
      - (j + 1) * geom.perHopRoutingInfoLength)) (xorBytes (F' ++ (if geom.nrHops > path'.size then
      filler' else ByteArray.empty)) (hopContent nike geom (Function.update ks j
      (KEMSphinx.zeroBytes ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength) ++ (xorBytes ((ksI j).extract ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) (ksI j).size)
      (padMask geom ks ksI j)))) tag ge filler path j))).size = ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) := by
    rw [Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract, hks']
    omega
  have hTL : (xorBytes ((ksI j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) -
      (j + 1) * geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j)).size = (j + 1)
      * geom.perHopRoutingInfoLength := by
    rw [Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract, hksI]
    omega
  have hksU : ∀ k, ((Function.update ks j ((xorBytes ((ks' j).extract 0 ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength)) (xorBytes (F' ++ (if
      geom.nrHops > path'.size then filler' else ByteArray.empty)) (hopContent nike geom
      (Function.update ks j (KEMSphinx.zeroBytes ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) ++ (xorBytes ((ksI
      j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j)))) tag ge filler path
      j))) ++ (xorBytes ((ksI j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) -
      (j + 1) * geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j)))) k).size =
      (geom.routingInfoLength + geom.perHopRoutingInfoLength) := fun k => by
    by_cases hk : k = j
    · rw [hk, Function.update_self, ByteArray.size_append, hHD, hTL]
      omega
    · rw [Function.update_of_ne hk]
      exact hks k
  have hpadU := padAt_comb geom ks ksI hks hksI j hjp (xorBytes ((ks' j).extract 0
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength)) (xorBytes (F' ++ (if geom.nrHops > path'.size then filler'
      else ByteArray.empty)) (hopContent nike geom (Function.update ks j (KEMSphinx.zeroBytes
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength) ++ (xorBytes ((ksI j).extract ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) (ksI j).size)
      (padMask geom ks ksI j)))) tag ge filler path j))) hHD
  have hpadZ := padAt_comb geom ks ksI hks hksI j hjp (KEMSphinx.zeroBytes ((geom.routingInfoLength
      + geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength))
    (KEMSphinx.zeroBytes_size _)
  have hcont := hopContent_congr nike geom
    (Function.update ks j (KEMSphinx.zeroBytes ((geom.routingInfoLength +
        geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) ++ (xorBytes ((ksI
        j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j))))
    (Function.update ks j ((xorBytes ((ks' j).extract 0 ((geom.routingInfoLength +
        geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength)) (xorBytes (F' ++
        (if geom.nrHops > path'.size then filler' else ByteArray.empty)) (hopContent nike geom
        (Function.update ks j (KEMSphinx.zeroBytes ((geom.routingInfoLength +
        geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) ++ (xorBytes ((ksI
        j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j)))) tag ge filler path
        j))) ++ (xorBytes ((ksI j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength)
        - (j + 1) * geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j)))) tag tag
        ge ge filler path j hi
    (fun i hij => ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
      rfl, rfl⟩) (hpadZ.trans hpadU.symm)
  unfold combStream
  refine hdrMsg_shift nike geom _ tag ge filler path j hi hnnh hle hrouting hn hfill hksU htag
    hcmd ((nikeHdrTrace_isSome geom _ _ _ _ _ _ _ _ path _).trans hT) hge1 ks' tag' ge' filler'
    path' hi' F' hF' hX' hks' hge
    (fun m hm => (Function.update_of_ne (by omega) _ _).trans (hfront m hm)) ?_
  rw [Function.update_self]
  have e := Util.Bytes.extract_append_left (xorBytes ((ks' j).extract 0 ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength)) (xorBytes (F' ++ (if
      geom.nrHops > path'.size then filler' else ByteArray.empty)) (hopContent nike geom
      (Function.update ks j (KEMSphinx.zeroBytes ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength) ++ (xorBytes ((ksI
      j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
      geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j)))) tag ge filler path
      j))) (xorBytes ((ksI j).extract ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j
      + 1) * geom.perHopRoutingInfoLength) (ksI j).size) (padMask geom ks ksI j))
  rw [hHD] at e
  rw [e]
  exact congrArg (fun c => xorBytes ((ks' j).extract 0 ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength)) (xorBytes (F' ++ (if
      geom.nrHops > path'.size then filler' else ByteArray.empty)) c)) hcont

/-- The joining keystream has a keystream's length. -/
theorem combStream_size (ks ksI : ℕ → ByteArray) (hksI : ∀ k, (ksI k).size =
    (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j : ℕ)
    (hj : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength) (U X : ByteArray)
    (hU : U.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (tag : ℕ → ByteArray →
        ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) :
    (combStream nike geom ks ksI j U X tag ge filler path).size = (geom.routingInfoLength +
        geom.perHopRoutingInfoLength) := by
  unfold combStream
  rw [ByteArray.size_append, Cryptlib.Protocols.Sphinx.Common.size_xorBytes,
    Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract,
    ByteArray.size_extract, hksI, hU]
  omega

/-- With the joining keystream the padding after the relay is the other header's. -/
theorem padAt_combStream (ks ksI : ℕ → ByteArray) (hks : ∀ k, (ks k).size = (geom.routingInfoLength
    + geom.perHopRoutingInfoLength))
    (hksI : ∀ k, (ksI k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (j : ℕ)
    (hj : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength) (U X : ByteArray)
    (hU : U.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (tag : ℕ → ByteArray →
        ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) :
    KEMSphinx.padAt geom (Function.update ks j
        (combStream nike geom ks ksI j U X tag ge filler path)) j
      = KEMSphinx.padAt geom ksI j := by
  unfold combStream
  exact padAt_comb geom ks ksI hks hksI j hj _ (by
    rw [Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract, hU]
    omega)

end Comb

/-! ## The relay as the last hop -/

section Last

variable (nike : NIKE) (macS : MAC) (streamS : StreamCipher) (geom : Geometry)

set_option maxHeartbeats 2000000 in
/-- **What a relay does as the last hop, for a header and a payload.** With its tag right and
commands that name no next hop and no reply block, it hands over what follows the zero tag of
the decrypted payload, when that tag is zero, and refuses the packet otherwise. -/
theorem procD_last_append {L : ℕ} (t : HopKeys)
    (D : HopKeys → Vector UInt8 L → Vector UInt8 L) (H P : ByteArray)
    (cmds : List RoutingCommand) (hH : H.size = (2 + nike.publicKeySize + geom.routingInfoLength) +
        macLength) (hP : P.size = L) (hL : 0 < L)
    (hLt : geom.payloadTagLength ≤ L) (hver : H.extract 0 2 = v0AD)
    (hmac : Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector t.headerMAC) (H.extract 0 (2 +
        nike.publicKeySize + geom.routingInfoLength)))
      = H.extract (2 + nike.publicKeySize + geom.routingInfoLength) ((2 + nike.publicKeySize +
          geom.routingInfoLength) + macLength))
    (hparse : parseAll ((xorBytes (H.extract (2 + nike.publicKeySize) (2 + nike.publicKeySize +
        geom.routingInfoLength)
        ++ ⟨Array.replicate geom.perHopRoutingInfoLength 0⟩)
        (streamS.keystream (Util.Bytes.ofVector t.headerEncryption)
          (Util.Bytes.ofVector t.headerEncryptionIV)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength))).extract 0
        geom.perHopRoutingInfoLength) = .ok cmds)
    (hnext : cmds.findSome? RSOR.nextHop = none)
    (hsr : (cmds.any fun c => match c with
      | RoutingCommand.surbReply _ => true
      | _ => false) = false) :
    procD nike macS streamS geom (fun _ => .ok t) D (H ++ P)
      = if ((Util.Bytes.ofVector (D t (Util.Bytes.toVecN L P))).extract 0
          geom.payloadTagLength).data.all (· == 0) = true then
          some (some ((Util.Bytes.ofVector (D t (Util.Bytes.toVecN L P))).extract
              geom.payloadTagLength L),
            Primitives.Hash.Sha512.sha512_256 (H.extract 2 (2 + nike.publicKeySize)), cmds, none)
        else none := by
  have hz : (⟨Array.replicate geom.perHopRoutingInfoLength (0 : UInt8)⟩ : ByteArray).size
      = geom.perHopRoutingInfoLength := Array.size_replicate
  have ex : ∀ a b, b ≤ H.size → (H ++ P).extract a b = H.extract a b := fun a b hb =>
    Util.Bytes.extract_append_of_le H P hb
  have e3 : (H ++ P).extract ((2 + nike.publicKeySize + geom.routingInfoLength) + macLength) (H ++
      P).size = P := by
    rw [ByteArray.size_append, ← hH]
    exact Util.Bytes.extract_append_right H P
  have e4 : (H.extract (2 + nike.publicKeySize) (2 + nike.publicKeySize + geom.routingInfoLength)
      ++ (⟨Array.replicate geom.perHopRoutingInfoLength 0⟩ : ByteArray)).size
      = geom.routingInfoLength + geom.perHopRoutingInfoLength := by
    rw [ByteArray.size_append, ByteArray.size_extract, hz]
    omega
  have hPpos : P.size > 0 := by omega
  have hbd : blockDec D t P = (Util.Bytes.ofVector (D t (Util.Bytes.toVecN L P))) := by
    unfold blockDec
    exact ite_eq_left hP
  have E := procD_last nike macS streamS geom t D (H ++ P) cmds
    (by rw [ByteArray.size_append]; omega) (by rw [ex _ _ (by omega), hver])
    (by rw [ex _ _ (by omega), ex _ _ (by omega), hmac])
    (by rw [ex _ _ (by omega), e4]; exact hparse) hnext hsr
    (by rw [e3, ite_eq_left hPpos, hbd, Util.Bytes.size_ofVector]; omega)
  rw [E, e3, ite_eq_left hPpos, hbd, Util.Bytes.size_ofVector, ex _ _ (by omega)]

omit nike macS streamS in
/-- The last hop's fragment parses to its commands. -/
theorem nikeFragment_parse_last (path : Array PathHop) (mac : ByteArray) (i : ℕ)
    (hi : i + 1 = path.size) (hnull : ∀ c ∈ path[i]!.commands, c ≠ .null) (F : ByteArray)
    (h : nikeFragment geom path mac i = .ok F) : parseAll F = .ok path[i]!.commands := by
  unfold nikeFragment at h
  have hb : (i == path.size - 1) = true := beq_iff_eq.mpr (by omega)
  rw [hb] at h
  simp only [↓reduceIte] at h
  obtain ⟨f0, hf0, h⟩ := Cryptlib.Protocols.Sphinx.Common.Except.eq_ok_of_bind_eq_ok h
  obtain rfl := Except.ok.inj h
  exact Cryptlib.Protocols.Sphinx.Common.parseAll_commandsToBytes geom.perHopRoutingInfoLength
      geom.perHopRoutingInfoLength _ hnull
    _ hf0 (Cryptlib.Protocols.Sphinx.Common.commandsToBytes_size_le hf0)

set_option maxHeartbeats 2000000 in
/-- **A relay given the last layer of a path** hands over what follows the zero tag of the
decrypted payload, with the hop's commands, when that tag is zero, and refuses otherwise. The
relay's keys give the layer's keystream and tag. -/
theorem procD_lastHdr {L : ℕ} (t : HopKeys) (D : HopKeys → Vector UInt8 L → Vector UInt8 L)
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) (i : ℕ) (P : ByteArray)
    (hi : i + 1 = path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hge : (ge i).size = nike.publicKeySize)
    (F : ByteArray) (hF : nikeFragment geom path ByteArray.empty i = .ok F)
    (hnull : ∀ c ∈ path[i]!.commands, c ≠ .null)
    (hnext : path[i]!.commands.findSome? RSOR.nextHop = none)
    (hsr : (path[i]!.commands.any fun c => match c with
      | RoutingCommand.surbReply _ => true
      | _ => false) = false)
    (hksi : streamS.keystream (Util.Bytes.ofVector t.headerEncryption)
      (Util.Bytes.ofVector t.headerEncryptionIV)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength) = ks i)
    (htagi : Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector t.headerMAC) (hdrMsg geom ks tag ge
        filler path i)) = tag i (hdrMsg geom ks tag ge filler path i))
    (hP : P.size = L) (hL : 0 < L) (hLt : geom.payloadTagLength ≤ L) :
    procD nike macS streamS geom (fun _ => .ok t) D (layerHdr geom ks tag ge filler path i ++ P)
      = if ((Util.Bytes.ofVector (D t (Util.Bytes.toVecN L P))).extract 0
          geom.payloadTagLength).data.all (· == 0) = true then
          some (some ((Util.Bytes.ofVector (D t (Util.Bytes.toVecN L P))).extract
              geom.payloadTagLength L),
            Primitives.Hash.Sha512.sha512_256 (ge i), path[i]!.commands, none)
        else none := by
  obtain ⟨k, hk⟩ : ∃ k, geom.nrHops = i + 1 + k := ⟨geom.nrHops - (i + 1), by omega⟩
  have e1 : geom.routingInfoLength = (i + 1) * geom.perHopRoutingInfoLength
      + k * geom.perHopRoutingInfoLength := by
    rw [hrouting, hk, Nat.mul_comm, Nat.add_mul]
  have e2 : (i + 1) * geom.perHopRoutingInfoLength
      = i * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
  have hjp : (i + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by omega
  have hFs : F.size = geom.perHopRoutingInfoLength :=
    nikeFragment_size geom path _ i hnnh hle F hF
  have hB : (if geom.nrHops > path.size then filler else ByteArray.empty).size = k *
      geom.perHopRoutingInfoLength := by
    by_cases hg : geom.nrHops > path.size
    · rw [ite_eq_left hg, hfill, show geom.nrHops - path.size = k by omega]
    · rw [ite_eq_right hg, show k = 0 by omega, Nat.zero_mul]
      rfl
  have hPd : (if i > 0 then KEMSphinx.padAt geom ks (i - 1) else ByteArray.empty).size = i *
      geom.perHopRoutingInfoLength := padFront_size geom ks hks i hjp
  have hFB : F.size + (if geom.nrHops > path.size then filler else ByteArray.empty).size =
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
      geom.perHopRoutingInfoLength) := by
    rw [hFs, hB]
    omega
  have hR : ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
      geom.perHopRoutingInfoLength) + (if i > 0 then KEMSphinx.padAt geom ks (i - 1) else
      ByteArray.empty).size = geom.routingInfoLength := by
    rw [hPd]
    omega
  have hU : (ks i).size = ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
      geom.perHopRoutingInfoLength) + (if i > 0 then KEMSphinx.padAt geom ks (i - 1) else
      ByteArray.empty).size + geom.perHopRoutingInfoLength := by
    rw [hks, hPd]
    omega
  have hm0 : (hdrMsg geom ks tag ge filler path i) = v0AD ++ ge i ++ (xorBytes (F ++ (if
      geom.nrHops > path.size then filler else ByteArray.empty)) ((ks i).extract 0
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
      geom.perHopRoutingInfoLength)) ++ (if i > 0 then KEMSphinx.padAt geom ks (i - 1) else
      ByteArray.empty)) :=
    (hdrMsg_last geom ks tag ge filler path i hi F hF).trans ByteArray.append_assoc
  obtain ⟨b0, b1, -, -, b4, b5, b6⟩ := peel_bytes nike geom (ks i) (ge i) F (if geom.nrHops >
      path.size then filler else ByteArray.empty) (if i > 0 then KEMSphinx.padAt geom ks (i - 1)
      else ByteArray.empty) (tag i (hdrMsg geom ks tag ge filler path i))
    ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
        geom.perHopRoutingInfoLength) hU hFB hR hge
  have hL0 : layerHdr geom ks tag ge filler path i
      = v0AD ++ ge i ++ (xorBytes (F ++ (if geom.nrHops > path.size then filler else
          ByteArray.empty)) ((ks i).extract 0 ((geom.routingInfoLength +
          geom.perHopRoutingInfoLength) - (i + 1) * geom.perHopRoutingInfoLength)) ++ (if i > 0
          then KEMSphinx.padAt geom ks (i - 1) else ByteArray.empty)) ++ tag i (hdrMsg geom ks tag
          ge filler path i) :=
    congrArg (· ++ tag i (hdrMsg geom ks tag ge filler path i)) hm0
  rw [htag i (hdrMsg geom ks tag ge filler path i)] at b5
  rw [hL0, procD_last_append nike macS streamS geom t D _ P path[i]!.commands
      (by rw [ByteArray.size_append, b6, htag]) hP hL hLt b0
      (by rw [b4, b5, ← hm0]; exact htagi)
      (by
        rw [hksi, peel_cmdBuf nike geom (ks i) (ge i) F (if geom.nrHops > path.size then filler
            else ByteArray.empty) _ _ _ hU hFB hFs hR hge]
        exact nikeFragment_parse_last geom path _ i hi hnull F hF) hnext hsr, b1]

omit macS streamS in
set_option maxHeartbeats 2000000 in
/-- **What a relay answers for the last layer of a path, in the games' form.** A relay that
holds the layer's tag and keystream, and is handed the payload's decryption `y`, hands over what
follows the zero tag of `y`, with the hop's commands, when that tag is zero. -/
theorem procD_join_last {n : ℕ} (T : Vector UInt8 n) (U : ByteArray) (t : HopKeys)
    (y : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) (ks : ℕ → ByteArray)
        (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray)
    (filler : ByteArray) (path : Array PathHop) (i : ℕ) (o : Onion geom)
    (hi : i + 1 = path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hks : ∀ k, (ks k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htag : ∀ m x, (tag m x).size = macLength) (hge : (ge i).size = nike.publicKeySize)
    (F : ByteArray) (hF : nikeFragment geom path ByteArray.empty i = .ok F)
    (hnull : ∀ c ∈ path[i]!.commands, c ≠ .null)
    (hnext : path[i]!.commands.findSome? RSOR.nextHop = none)
    (hsr : (path[i]!.commands.any fun c => match c with
      | RoutingCommand.surbReply _ => true
      | _ => false) = false)
    (hksi : ks i = U) (htagi : tag i (hdrMsg geom ks tag ge filler path i) = Util.Bytes.ofVector T)
    (ho : Util.Bytes.ofVector o.1 = layerHdr geom ks tag ge filler path i)
    (hL : 0 < geom.payloadTagLength + geom.forwardPayloadLength) :
    procD nike (Primitives.MAC.MAC.const T) (constStream U) geom (fun _ => .ok t)
        (fun _ _ => y) (join o)
      = if ((Util.Bytes.ofVector y).extract 0 geom.payloadTagLength).data.all (· == 0) = true then
          some (some ((Util.Bytes.ofVector y).extract geom.payloadTagLength
            (geom.payloadTagLength + geom.forwardPayloadLength)),
            Primitives.Hash.Sha512.sha512_256 (ge i), path[i]!.commands, none)
        else none := by
  have hksi' : (constStream U).keystream (Util.Bytes.ofVector t.headerEncryption)
      (Util.Bytes.ofVector t.headerEncryptionIV) (geom.routingInfoLength +
          geom.perHopRoutingInfoLength) = ks i := by
    have h := Util.Bytes.extract_append_left (ks i) (⟨Array.replicate (geom.routingInfoLength +
        geom.perHopRoutingInfoLength) 0⟩ : ByteArray)
    rw [hks i] at h
    rw [← hksi]
    exact h
  unfold join
  rw [ho, procD_lastHdr nike (Primitives.MAC.MAC.const T) (constStream U) geom t (fun _ _ => y)
    ks tag ge filler path i (Util.Bytes.ofVector o.2) hi hnnh hle hrouting hn hfill hks htag hge F
    hF hnull hnext hsr hksi' htagi.symm (Util.Bytes.size_ofVector _) hL (Nat.le_add_right _ _)]

end Last

/-! ## The original and the replacement at the relay's hop -/

section Shift

variable (nike : NIKE) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)

omit macS kdfS streamS geom in
omit macS kdfS streamS in
/-- **Two packets are one when the bytes under the relay's tag agree**, the hops in front are
the same, and the relay's tagging function and encrypted block are the same. Their paths may
differ after the relay. -/
theorem nikePktFn_shift (geom : Geometry) (ks ks' : ℕ → ByteArray)
    (tag tag' enc enc' : ℕ → ByteArray → ByteArray) (ge ge' : ℕ → ByteArray)
    (filler filler' : ByteArray) (path path' : Array PathHop) (payload payload' : ByteArray)
    (j : ℕ) (hj : j < path.size) (hj' : j < path'.size)
    (h : ∀ i < j, ks i = ks' i ∧ tag i = tag' i ∧ ge i = ge' i ∧ enc i = enc' i
      ∧ path[i]!.commands = path'[i]!.commands ∧ path[i + 1]!.id = path'[i + 1]!.id)
    (hge0 : ge 0 = ge' 0)
    (hM : hdrMsg geom ks tag ge filler path j = hdrMsg geom ks' tag' ge' filler' path' j)
    (htj : tag j = tag' j)
    (hT : (nikeHdrTrace geom ks tag ge filler path (path.size - j)).isSome)
    (hT' : (nikeHdrTrace geom ks' tag' ge' filler' path' (path'.size - j)).isSome)
    (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hn : path.size ≤ geom.nrHops) (hn' : path'.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hfill' : filler'.size = (geom.nrHops - path'.size) * geom.perHopRoutingInfoLength)
    (htag : ∀ i m, (tag i m).size = macLength) (htag' : ∀ i m, (tag' i m).size = macLength)
    (hgej : (ge j).size = nike.publicKeySize) (hgej' : (ge' j).size = nike.publicKeySize)
    (e : ByteArray) (he : ∀ b, enc j b = e) (he' : ∀ b, enc' j b = e)
    (hp : payload.size = geom.forwardPayloadLength)
    (hp' : payload'.size = geom.forwardPayloadLength) :
    nikePktFn geom ks tag enc ge filler path payload
      = nikePktFn geom ks' tag' enc' ge' filler' path' payload' := by
  obtain ⟨s, hs0⟩ := Option.isSome_iff_exists.mp hT
  obtain ⟨s', hs1⟩ := Option.isSome_iff_exists.mp hT'
  obtain ⟨a1, a2⟩ := nikeHdrTrace_at_msg nike geom ks tag ge filler path j hj hgej s hs0
  obtain ⟨b1, b2⟩ := nikeHdrTrace_at_msg nike geom ks' tag' ge' filler' path' j hj' hgej' s' hs1
  have hsize : s.1.size = s'.1.size := by
    rw [(nikeHdrTrace_size geom ks tag ge filler path hnnh hle hfill htag _ s hs0).1,
      (nikeHdrTrace_size geom ks' tag' ge' filler' path' hnnh hle hfill' htag' _ s' hs1).1]
    congr 1
    omega
  refine nikePktFn_front geom ks ks' tag tag' enc enc' ge ge' filler filler' path path' payload
    payload' j hj hj' h hge0 ?_ e he he' hp hp'
  rw [hs0, hs1]
  exact congrArg some (Prod.ext (by rw [a1, b1, hM, hsize]) (by rw [a2, b2, hM, htj]))

/-- The element that reaches hop `i` reads the blinding factors of the hops in front. -/
theorem blindElem_congr_lt (a : ByteArray) (K K' : Array HopKeys) (i : ℕ)
    (h : ∀ n < i, (K[n]!).blindingFactor = (K'[n]!).blindingFactor) :
    blindElem nike a K i = blindElem nike a K' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show nikeBlind nike (blindElem nike a K i) _ = nikeBlind nike (blindElem nike a K' i) _
    rw [ih fun n hn => h n (by omega), h i (Nat.lt_succ_self i)]

omit macS kdfS streamS geom in
/-- A blinded element has the length of the element. -/
theorem blindElem_size (a : ByteArray) (K : Array HopKeys) (i : ℕ) :
    (blindElem nike a K i).size = a.size := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show (nikeBlind nike (blindElem nike a K i) _).size = _
    rw [size_nikeBlind, ih]

end Shift

end Cryptlib.Protocols.Sphinx.NIKESphinx
