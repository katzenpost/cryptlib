/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUNext
import Cryptlib.Protocols.Sphinx.KEMSphinxTLUFinal

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

/-! # The last comparison of the two worlds of TLU→, for NIKE Sphinx

After the steps of `NIKESphinxTLU.lean` and `NIKESphinxTLUNext.lean` each world is played from
uniform keystreams. Here the two are compared. -/

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

/-- **The layer after hop `j` reads the hops up to `j` through the padding after hop `j`
only.** -/
theorem layerFn_congr (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (ks ks' : ℕ → ByteArray) (tag tag' enc enc' : ℕ → ByteArray → ByteArray)
    (ge ge' : ℕ → ByteArray) (j : ℕ) (hj : j + 1 < (RSOR.path nike q.fwd [.recipient
        q.receiver]).size)
    (h : ∀ i, j < i → ks i = ks' i ∧ tag i = tag' i ∧ ge i = ge' i ∧ enc i = enc' i)
    (hp : KEMSphinx.padAt geom ks j = KEMSphinx.padAt geom ks' j) :
    layerFn nike macS kdfS streamS geom q r ks tag enc ge (j + 1)
      = layerFn nike macS kdfS streamS geom q r ks' tag' enc' ge' (j + 1) := by
  have hL := layerHdr_congr_tail geom ks ks' tag tag' ge ge' (RSOR.filler nike geom (RSOR.path nike
      q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) j hj
    (fun i hi => ⟨(h i hi).1, (h i hi).2.1, (h i hi).2.2.1⟩) hp
  have hE := encTrace_congr enc enc' (RSOR.path nike q.fwd [.recipient q.receiver]).size
      ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS streamS
      geom q r)) ((RSOR.path nike q.fwd [.recipient q.receiver]).size - (j + 1)) (by omega)
    fun i hi _ => (h i (by omega)).2.2.2
  have hS := nikeHdrTrace_isSome geom ks ks' tag tag' ge ge' (RSOR.filler nike geom (RSOR.path nike
      q.fwd [.recipient q.receiver]) r.1) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
      q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
      [.recipient q.receiver]).size
  unfold layerFn
  rw [hL, hE]
  cases h1 : nikeHdrTrace geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
      q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path nike q.fwd
      [.recipient q.receiver]).size with
  | none =>
    rw [h1] at hS
    cases h2 : nikeHdrTrace geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path nike q.fwd
        [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path
        nike q.fwd [.recipient q.receiver]).size with
    | none => rfl
    | some s' => rw [h2] at hS; cases hS
  | some s =>
    rw [h1] at hS
    cases h2 : nikeHdrTrace geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path nike q.fwd
        [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver]) (RSOR.path
        nike q.fwd [.recipient q.receiver]).size with
    | none => rw [h2] at hS; cases hS
    | some s' => rfl

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

end Comb

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

private theorem last_arith (N j p R : ℕ) (hR : R = p * N) (hj : j + 1 ≤ N) :
    R + p - (j + 1) * p = p + (N - (j + 1)) * p := by
  obtain ⟨k, rfl⟩ : ∃ k, N = j + 1 + k := ⟨N - (j + 1), by omega⟩
  have e : j + 1 + k - (j + 1) = k := by omega
  subst hR
  rw [e]
  have h1 : p * (j + 1 + k) = j * p + p + k * p := by ring
  have h2 : (j + 1) * p = j * p + p := by ring
  omega

set_option maxHeartbeats 2000000 in
/-- **The bytes under the relay's tag: the original's are the replacement's, under the
shift.** The replacement's path is the original's cut after hop `j`. With the keystream of hop
`j` shifted at its head by the difference of what the two mask, the bytes under hop `j`'s tag
agree. -/
theorem onionMsgStream_shift (q : RSOR.Request nike geom) (r r' : RSOR.Randomness nike geom)
    (c : nike.PrivateKey) (t : HopKeys) (j : ℕ) (rc : Name) (U U' F' : ByteArray)
    (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (hj : j + 1 < q.fwd.hops.length) (hU : U.size = (geom.routingInfoLength +
        geom.perHopRoutingInfoLength)) (hU' : U'.size = (geom.routingInfoLength +
        geom.perHopRoutingInfoLength))
    (hT : (nikeHdrTrace geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c
        (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) j U) (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike
        q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey
        (nike.derivePublicKey c))) (hopKeysWith nike kdfS c (RSOR.path nike q.fwd [.recipient
        q.receiver]) j t (RSOR.path nike q.fwd [.recipient q.receiver]).size).toArray)
      (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike
          q.fwd [.recipient q.receiver]) ((RSOR.path nike q.fwd [.recipient q.receiver]).size -
          j)).isSome)
    (hF' : nikeFragment geom (RSOR.path nike (q.fwd.take (j + 1)) [.recipient rc]) ByteArray.empty
        j = .ok F')
    (hshift : U.extract 0 ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
        geom.perHopRoutingInfoLength) = xorBytes (U'.extract 0 ((geom.routingInfoLength +
        geom.perHopRoutingInfoLength) - (j + 1) * geom.perHopRoutingInfoLength))
      (xorBytes (F' ++ (if geom.nrHops > (RSOR.path nike (q.fwd.take (j + 1)) [.recipient rc]).size
          then (RSOR.filler nike geom (RSOR.path nike (q.fwd.take (j + 1)) [.recipient rc]) r'.1)
          else ByteArray.empty))
        (hopContent nike geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c
            (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
            q.receiver]).size).toArray) j U) (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike
            q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
            q.receiver]).size).toArray)
          (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey c)))
              (hopKeysWith nike kdfS c (RSOR.path nike q.fwd [.recipient q.receiver]) j t
              (RSOR.path nike q.fwd [.recipient q.receiver]).size).toArray) (RSOR.filler nike geom
              (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient
              q.receiver]) j))) :
    hdrMsg geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c (RSOR.path nike
        q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) j U) (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike
        q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey
        (nike.derivePublicKey c))) (hopKeysWith nike kdfS c (RSOR.path nike q.fwd [.recipient
        q.receiver]) j t (RSOR.path nike q.fwd [.recipient q.receiver]).size).toArray) (RSOR.filler
        nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1)
        (RSOR.path nike q.fwd [.recipient q.receiver]) j
      = hdrMsg geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c (RSOR.path nike
          (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray) j U')
        (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t
            (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray) (blindElem nike
            (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey c))) (hopKeysWith nike
            kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j +
            1)) []).size).toArray) (RSOR.filler nike geom (RSOR.path nike (q.fwd.take (j + 1))
            [.recipient rc]) r'.1) (RSOR.path nike (q.fwd.take (j + 1)) [.recipient rc]) j := by
  obtain ⟨hnnh, hper, hrouting, -⟩ := id hvalid
  have hsz := RSOR.path_size nike q.fwd [.recipient q.receiver]
  have hlen : (q.fwd.take (j + 1)).hops.length = j + 1 := by
    show (List.take (j + 1) q.fwd.hops).length = j + 1
    rw [List.length_take]
    omega
  have hszS := RSOR.path_size nike (q.fwd.take (j + 1)) [.recipient rc]
  have hsz1 := RSOR.path_size nike (q.fwd.take (j + 1)) []
  have hn : (RSOR.path nike q.fwd [.recipient q.receiver]).size ≤ geom.nrHops := by
    rw [hsz]
    exact q.fwd.length_le
  have hmul : ∀ k : ℕ, (geom.nrHops - k) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength :=
      fun k => by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hfill : (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1).size =
      (geom.nrHops - (RSOR.path nike q.fwd [.recipient q.receiver]).size) *
      geom.perHopRoutingInfoLength := by
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    have := hmul (RSOR.path nike q.fwd [.recipient q.receiver]).size
    omega
  have hfillS : (RSOR.filler nike geom (RSOR.path nike (q.fwd.take (j + 1)) [.recipient rc])
      r'.1).size = (geom.nrHops - (RSOR.path nike (q.fwd.take (j + 1)) [.recipient rc]).size) *
      geom.perHopRoutingInfoLength := by
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    have := hmul (RSOR.path nike (q.fwd.take (j + 1)) [.recipient rc]).size
    omega
  have hks : ∀ k, ((Function.update (keysKs geom streamS (hopKeysWith nike kdfS c (RSOR.path nike
      q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
      q.receiver]).size).toArray) j U) k).size = (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) := fun k => by
    by_cases hk : k = j
    · rw [hk, Function.update_self]
      exact hU
    · rw [Function.update_of_ne hk]
      exact streamS.keystream_size _ _ _
  have hks' : ∀ k, (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c (RSOR.path nike
      (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray) j U'
      k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) :=
    fun k => by
      by_cases hk : k = j
      · rw [hk, Function.update_self]
        exact hU'
      · rw [Function.update_of_ne hk]
        exact streamS.keystream_size _ _ _
  have htag : ∀ (m : ℕ) (x : ByteArray), (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike
      q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
      q.receiver]).size).toArray m x).size = macLength :=
    fun m x => (Util.Bytes.size_ofVector _).trans hmactag
  have hcmd : (RSOR.path nike q.fwd [.recipient q.receiver])[j]!.commands = [] := by
    rw [RSOR.path_getElem! nike _ _ j (by omega)]
    exact ite_eq_right (by omega)
  have hpub : ∀ i < j + 1, (RSOR.path nike (q.fwd.take (j + 1)) [])[i]!.publicKey = (RSOR.path nike
      q.fwd [.recipient q.receiver])[i]!.publicKey := fun i hi => by
    rw [RSOR.path_getElem! nike _ _ i (by omega), RSOR.path_getElem! nike _ _ i (by omega)]
    exact congrArg (fun h : Protocols.RSOR.Hop Name (RSOR.Key nike) =>
      Util.Bytes.ofVector (nike.encodePublicKey h.key.1)) List.getElem_take
  have hcut : ∀ i < j + 1, (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t
      (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray[i]! = (hopKeysWith nike kdfS c
      (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
      q.receiver]).size).toArray[i]! := fun i hi => by
    rw [hsz1, hlen]
    exact hopKeysWith_cut nike kdfS c _ _ j t (j + 1) _ (by omega) hpub i hi
  have hXs : (F' ++ (if geom.nrHops > (RSOR.path nike (q.fwd.take (j + 1)) [.recipient rc]).size
      then (RSOR.filler nike geom (RSOR.path nike (q.fwd.take (j + 1)) [.recipient rc]) r'.1) else
      ByteArray.empty)).size
      = ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (j + 1) *
          geom.perHopRoutingInfoLength) := by
    have hF := nikeFragment_size geom _ _ j hnnh (by omega) F' hF'
    have ha := last_arith geom.nrHops j geom.perHopRoutingInfoLength geom.routingInfoLength
        hrouting (by omega)
    rw [ByteArray.size_append, hF, ha]
    by_cases hg : geom.nrHops > (RSOR.path nike (q.fwd.take (j + 1)) [.recipient rc]).size
    · rw [ite_eq_left hg, hfillS, hszS, hlen]
    · rw [ite_eq_right hg, show geom.nrHops - (j + 1) = 0 by omega, Nat.zero_mul]
      rfl
  refine hdrMsg_shift nike geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c
      (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
      q.receiver]).size).toArray) j U) _ _ _ _ j (by omega) hnnh (by omega) hrouting hn hfill hks
    htag hcmd hT ((blindElem_size nike _ _ _).trans (Util.Bytes.size_ofVector _)) _ _ _ _ _
    (by rw [hszS, hlen]) F' hF' hXs hks'
    (blindElem_congr_lt nike _ _ _ j fun n hn => by rw [hcut n (by omega)])
    (fun m hm => ?_) ?_
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    unfold keysKs
    rw [hcut m (by omega)]
  · rw [Function.update_self, Function.update_self]
    exact hshift

set_option maxHeartbeats 4000000 in
/-- **The onion shown: the original's is the replacement's, when the bytes under the relay's
tag agree.** The hops in front are the same, and the relay's tag and encrypted block are given,
so the two first layers are one packet. -/
theorem onionOfStream_shift (cipher : WideBlockCipher) (q q' : RSOR.Request nike geom)
    (r r' : RSOR.Randomness nike geom) (c : nike.PrivateKey) (t : HopKeys) (j : ℕ)
    (U U' tg e : ByteArray) (hq' : q'.fwd = q.fwd.take (j + 1))
    (hj : j + 1 < q.fwd.hops.length)
    (hT : (nikeHdrTrace geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c
        (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) j U) (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike
        q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey
        (nike.derivePublicKey c))) (hopKeysWith nike kdfS c (RSOR.path nike q.fwd [.recipient
        q.receiver]) j t (RSOR.path nike q.fwd [.recipient q.receiver]).size).toArray)
      (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike
          q.fwd [.recipient q.receiver]) ((RSOR.path nike q.fwd [.recipient q.receiver]).size -
          j)).isSome)
    (hT' : (nikeHdrTrace geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c
        (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1))
        []).size).toArray) j U') (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take
        (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray)
      (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey c)))
          (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike
          (q.fwd.take (j + 1)) []).size).toArray) (RSOR.filler nike geom (RSOR.path nike
          (q.fwd.take (j + 1)) [.recipient q'.receiver]) r'.1) (RSOR.path nike (q.fwd.take (j + 1))
          [.recipient q'.receiver]) ((RSOR.path nike (q.fwd.take (j + 1)) [.recipient
          q'.receiver]).size - j)).isSome)
    (hM : hdrMsg geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c (RSOR.path
        nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) j U) (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike
        q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey
        (nike.derivePublicKey c))) (hopKeysWith nike kdfS c (RSOR.path nike q.fwd [.recipient
        q.receiver]) j t (RSOR.path nike q.fwd [.recipient q.receiver]).size).toArray) (RSOR.filler
        nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1)
        (RSOR.path nike q.fwd [.recipient q.receiver]) j
      = hdrMsg geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c (RSOR.path nike
          (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray) j
          U') (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t
          (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray) (blindElem nike
          (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey c))) (hopKeysWith nike
          kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1))
          []).size).toArray) (RSOR.filler nike geom (RSOR.path nike (q.fwd.take (j + 1))
          [.recipient q'.receiver]) r'.1)
        (RSOR.path nike (q.fwd.take (j + 1)) [.recipient q'.receiver]) j)
    (hsz : geom.nextNodeHopLength = nextNodeHopLength
      ∧ geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength ∧ macS.tagSize = macLength ∧ tg.size
          = macLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hb : (RSOR.body nike macS kdfS streamS geom q r).size = geom.forwardPayloadLength)
    (hb' : (RSOR.body nike macS kdfS streamS geom q' r').size = geom.forwardPayloadLength) :
    onionOfStream nike cipher macS kdfS streamS geom 0 q r (Util.Bytes.ofVector
        (nike.encodePublicKey (nike.derivePublicKey c))) (hopKeysWith nike kdfS c (RSOR.path nike
        q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient q.receiver]).size) j U
        tg e
      = onionOfStream nike cipher macS kdfS streamS geom 0 q' r' (Util.Bytes.ofVector
          (nike.encodePublicKey (nike.derivePublicKey c))) (hopKeysWith nike kdfS c (RSOR.path nike
          (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size) j U' tg e :=
          by
  obtain ⟨hnnh, hle, hmactag, htg⟩ := hsz
  have hsz0 := RSOR.path_size nike q.fwd [.recipient q.receiver]
  have hlen : (q.fwd.take (j + 1)).hops.length = j + 1 := by
    show (List.take (j + 1) q.fwd.hops).length = j + 1
    rw [List.length_take]
    omega
  have hszS := RSOR.path_size nike (q.fwd.take (j + 1)) [.recipient q'.receiver]
  have hsz1 := RSOR.path_size nike (q.fwd.take (j + 1)) []
  have hP : (RSOR.path nike q'.fwd [.recipient q'.receiver]) = (RSOR.path nike (q.fwd.take (j + 1))
      [.recipient q'.receiver]) := by rw [hq']
  have hpub : ∀ i < j + 1, (RSOR.path nike (q.fwd.take (j + 1)) [])[i]!.publicKey = (RSOR.path nike
      q.fwd [.recipient q.receiver])[i]!.publicKey := fun i hi => by
    rw [RSOR.path_getElem! nike _ _ i (by omega), RSOR.path_getElem! nike _ _ i (by omega)]
    exact congrArg (fun h : Protocols.RSOR.Hop Name (RSOR.Key nike) =>
      Util.Bytes.ofVector (nike.encodePublicKey h.key.1)) List.getElem_take
  have hcut : ∀ i < j + 1, (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t
      (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray[i]! = (hopKeysWith nike kdfS c
      (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
      q.receiver]).size).toArray[i]! := fun i hi => by
    rw [hsz1, hlen]
    exact hopKeysWith_cut nike kdfS c _ _ j t (j + 1) _ (by omega) hpub i hi
  have hgj : (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey c)))
      (hopKeysWith nike kdfS c (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike
      q.fwd [.recipient q.receiver]).size).toArray j).size = nike.publicKeySize :=
    (blindElem_size nike _ _ _).trans (Util.Bytes.size_ofVector _)
  have hgj' : (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey c)))
      (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike
      (q.fwd.take (j + 1)) []).size).toArray j).size = nike.publicKeySize :=
    (blindElem_size nike _ _ _).trans (Util.Bytes.size_ofVector _)
  have hs : nikeHdrTrace geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c
      (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
      q.receiver]).size).toArray) j U) (Function.update (keysTag macS (hopKeysWith nike kdfS c
      (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
      q.receiver]).size).toArray) j fun _ => tg) (blindElem nike (Util.Bytes.ofVector
      (nike.encodePublicKey (nike.derivePublicKey c))) (hopKeysWith nike kdfS c (RSOR.path nike
      q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
      q.receiver]).size).toArray) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
      q.receiver]) r.1) (RSOR.path nike q.fwd [.recipient q.receiver])
        ((RSOR.path nike q.fwd [.recipient q.receiver]).size - j)
      = nikeHdrTrace geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c (RSOR.path
          nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray)
          j U') (Function.update (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take
          (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray) j fun _ => tg)
          (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey c)))
          (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike
          (q.fwd.take (j + 1)) []).size).toArray) (RSOR.filler nike geom (RSOR.path nike
          (q.fwd.take (j + 1)) [.recipient q'.receiver]) r'.1) (RSOR.path nike (q.fwd.take (j + 1))
          [.recipient q'.receiver])
        ((RSOR.path nike (q.fwd.take (j + 1)) [.recipient q'.receiver]).size - j) := by
    have h0 := nikeHdrTrace_isSome geom (Function.update (keysKs geom streamS (hopKeysWith nike
        kdfS c (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) j U) (Function.update (keysKs geom streamS (hopKeysWith nike
        kdfS c (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) j U) (Function.update (keysTag macS (hopKeysWith nike kdfS c
        (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) j fun _ => tg) (keysTag macS (hopKeysWith nike kdfS c
        (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray)
      (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey c)))
          (hopKeysWith nike kdfS c (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path
          nike q.fwd [.recipient q.receiver]).size).toArray) (blindElem nike (Util.Bytes.ofVector
          (nike.encodePublicKey (nike.derivePublicKey c))) (hopKeysWith nike kdfS c (RSOR.path nike
          q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
          q.receiver]).size).toArray) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient
          q.receiver]) r.1) (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver])
          r.1) (RSOR.path nike q.fwd [.recipient q.receiver])
      ((RSOR.path nike q.fwd [.recipient q.receiver]).size - j)
    have h1 := nikeHdrTrace_isSome geom (Function.update (keysKs geom streamS (hopKeysWith nike
        kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1))
        []).size).toArray) j U') (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c
        (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1))
        []).size).toArray) j U') (Function.update (keysTag macS (hopKeysWith nike kdfS c (RSOR.path
        nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray) j
        fun _ => tg) (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take (j + 1))
        []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray)
      (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey c)))
          (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike
          (q.fwd.take (j + 1)) []).size).toArray) (blindElem nike (Util.Bytes.ofVector
          (nike.encodePublicKey (nike.derivePublicKey c))) (hopKeysWith nike kdfS c (RSOR.path nike
          (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray)
          (RSOR.filler nike geom (RSOR.path nike (q.fwd.take (j + 1)) [.recipient q'.receiver])
          r'.1) (RSOR.filler nike geom (RSOR.path nike (q.fwd.take (j + 1)) [.recipient
          q'.receiver]) r'.1)
      (RSOR.path nike (q.fwd.take (j + 1)) [.recipient q'.receiver]) ((RSOR.path nike (q.fwd.take
          (j + 1)) [.recipient q'.receiver]).size - j)
    rw [hT] at h0
    rw [hT'] at h1
    obtain ⟨s, hs0⟩ := Option.isSome_iff_exists.mp h0
    obtain ⟨s', hs1⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨a1, a2⟩ := nikeHdrTrace_at_msg nike geom _ _ _ _ _ j (by omega) hgj s hs0
    obtain ⟨b1, b2⟩ := nikeHdrTrace_at_msg nike geom _ _ _ _ _ j (by rw [hszS, hlen]; omega)
      hgj' s' hs1
    have htag0 : ∀ (m : ℕ) (x : ByteArray), ((Function.update (keysTag macS (hopKeysWith nike kdfS
        c (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
        q.receiver]).size).toArray) j fun _ => tg) m x).size = macLength := fun m x => by
      by_cases hm : m = j
      · rw [hm, Function.update_self]
        exact htg
      · rw [Function.update_of_ne hm]
        exact (Util.Bytes.size_ofVector _).trans hmactag
    have htag1 : ∀ (m : ℕ) (x : ByteArray), ((Function.update (keysTag macS (hopKeysWith nike kdfS
        c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1))
        []).size).toArray) j fun _ => tg) m x).size = macLength := fun m x => by
      by_cases hm : m = j
      · rw [hm, Function.update_self]
        exact htg
      · rw [Function.update_of_ne hm]
        exact (Util.Bytes.size_ofVector _).trans hmactag
    have hfill : ∀ (pth : Array PathHop) (rr : RSOR.Randomness nike geom),
        (RSOR.filler nike geom pth rr.1).size = (geom.nrHops - pth.size) *
            geom.perHopRoutingInfoLength := fun pth rr => by
      have hmul : (geom.nrHops - pth.size) * geom.perHopRoutingInfoLength
          ≤ geom.routingInfoLength := by
        rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
        exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      unfold RSOR.filler
      rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
      omega
    have hsize : s.1.size = s'.1.size := by
      rw [(nikeHdrTrace_size geom _ _ _ _ _ hnnh hle (hfill _ r) htag0 _ s hs0).1,
        (nikeHdrTrace_size geom _ _ _ _ _ hnnh hle (hfill _ r') htag1 _ s' hs1).1, hsz0, hszS, hlen]
      have := q.fwd.length_le
      congr 1
      omega
    rw [hs0, hs1]
    refine congrArg some (Prod.ext ?_ ?_)
    · rw [a1, b1, hdrMsg_update_tag geom _ _ _ _ _ j (by omega),
        hdrMsg_update_tag geom _ _ _ _ _ j (by rw [hszS, hlen]; omega), hM,
        hsize]
    · rw [a2, b2, Function.update_self, Function.update_self]
  have hpkt := nikePktFn_front geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c
      (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
      q.receiver]).size).toArray) j U) (Function.update (keysKs geom streamS (hopKeysWith nike kdfS
      c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1))
      []).size).toArray) j U') (Function.update (keysTag macS (hopKeysWith nike kdfS c (RSOR.path
      nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
      q.receiver]).size).toArray) j fun _ => tg) (Function.update (keysTag macS (hopKeysWith nike
      kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1))
      []).size).toArray) j fun _ => tg) (Function.update (keysEnc cipher (hopKeysWith nike kdfS c
      (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike q.fwd [.recipient
      q.receiver]).size).toArray) j fun _ => e) (Function.update (keysEnc cipher (hopKeysWith nike
      kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1))
      []).size).toArray) j fun _ => e)
    (blindElem nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey c)))
        (hopKeysWith nike kdfS c (RSOR.path nike q.fwd [.recipient q.receiver]) j t (RSOR.path nike
        q.fwd [.recipient q.receiver]).size).toArray) (blindElem nike (Util.Bytes.ofVector
        (nike.encodePublicKey (nike.derivePublicKey c))) (hopKeysWith nike kdfS c (RSOR.path nike
        (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray)
        (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.filler
        nike geom (RSOR.path nike (q.fwd.take (j + 1)) [.recipient q'.receiver]) r'.1) (RSOR.path
        nike q.fwd [.recipient q.receiver])
    (RSOR.path nike (q.fwd.take (j + 1)) [.recipient q'.receiver]) (RSOR.body nike macS kdfS
        streamS geom q r) (RSOR.body nike macS kdfS streamS geom q' r')
    j (by omega) (by rw [hszS, hlen]; omega)
    (fun i hi => ⟨by
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        unfold keysKs
        rw [hcut i (by omega)], by
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        funext x
        unfold keysTag
        rw [hcut i (by omega)],
      blindElem_congr_lt nike _ _ _ i fun n hn => by rw [hcut n (by omega)], by
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        funext x
        unfold keysEnc
        rw [hcut i (by omega)], by
        rw [RSOR.path_getElem! nike _ _ i (by omega),
          RSOR.path_getElem! nike _ _ i (by rw [hlen]; omega)]
        exact (ite_eq_right (by omega)).trans (ite_eq_right (by rw [hlen]; omega)).symm, by
        rw [RSOR.path_getElem! nike _ _ (i + 1) (by omega),
          RSOR.path_getElem! nike _ _ (i + 1) (by rw [hlen]; omega)]
        exact congrArg (fun h : Protocols.RSOR.Hop Name (RSOR.Key nike) => h.name)
          List.getElem_take.symm⟩)
    rfl hs e (fun b => by rw [Function.update_self]) (fun b => by rw [Function.update_self]) hb hb'
  unfold onionOfStream
  rw [hP, hpkt]
  cases nikePktFn geom (Function.update (keysKs geom streamS (hopKeysWith nike kdfS c (RSOR.path
      nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray) j
      U') (Function.update (keysTag macS (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take (j +
      1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray) j fun _ => tg)
      (Function.update (keysEnc cipher (hopKeysWith nike kdfS c (RSOR.path nike (q.fwd.take (j +
      1)) []) j t (RSOR.path nike (q.fwd.take (j + 1)) []).size).toArray) j fun _ => e) (blindElem
      nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey c))) (hopKeysWith nike
      kdfS c (RSOR.path nike (q.fwd.take (j + 1)) []) j t (RSOR.path nike (q.fwd.take (j + 1))
      []).size).toArray) (RSOR.filler nike geom (RSOR.path nike (q.fwd.take (j + 1)) [.recipient
      q'.receiver]) r'.1) (RSOR.path nike (q.fwd.take (j + 1)) [.recipient q'.receiver])
    (RSOR.body nike macS kdfS streamS geom q' r') <;> rfl

end Shift

/-! ## The two final games -/

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
    have hL : layerHdr geom ks' (Function.update tag' j fun _ => Util.Bytes.ofVector (macS.mac
        (Util.Bytes.ofVector km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
        geom.routingInfoLength) (hdrMsg geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path nike
        q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q'.fwd [.recipient q'.receiver])
        j))))) ge' (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1)
        (RSOR.path nike q'.fwd [.recipient q'.receiver]) j = (hdrMsg geom ks' tag' ge' (RSOR.filler
        nike geom (RSOR.path nike q'.fwd [.recipient q'.receiver]) r'.1) (RSOR.path nike q'.fwd
        [.recipient q'.receiver]) j) ++ Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
        (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
        (hdrMsg geom ks' tag' ge' (RSOR.filler nike geom (RSOR.path nike q'.fwd [.recipient
        q'.receiver]) r'.1) (RSOR.path nike q'.fwd [.recipient q'.receiver]) j)))) := by
      unfold layerHdr
      rw [hdrMsg_update_tag geom _ _ _ _ _ j (by omega), Function.update_self]
    have hE : encTrace (Function.update enc' j fun _ => Util.Bytes.ofVector u) (RSOR.path nike
        q'.fwd [.recipient q'.receiver]).size
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ (RSOR.body nike macS kdfS
            streamS geom q' r')) ((RSOR.path nike q'.fwd [.recipient q'.receiver]).size - j)
        = Util.Bytes.ofVector u := by
      rw [show (RSOR.path nike q'.fwd [.recipient q'.receiver]).size - j = 0 + 1 by omega,
          encTrace_succ,
        show (RSOR.path nike q'.fwd [.recipient q'.receiver]).size - 1 - 0 = j by omega,
            Function.update_self]
    rw [layerFn_eq nike macS kdfS streamS geom q' r' _ _ _ _ j hb' (iso' _ _ _), hL, hE,
      split_append_bytes geom _ _ (by
        rw [ByteArray.size_append, hMsz, Util.Bytes.size_ofVector, hhdr, had, hmactag]),
      Util.Bytes.toVecN_ofVector]
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

/-! ## The blinding adversary of world 0 -/

/-- **What world 0 does with the hops after the relay.** On the draws of world 0 besides the
relay's blinding seed (the relay's keystream and MAC key, the game's draws, the two blocks) and
on what lies after the relay, `tail`: before the end of a path whose header builds, the game
from the hops' functions, those after the relay from `tail`; at the end of the path, `E`. -/
def blindPost (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength
        + geom.forwardPayloadLength)) → ProbComp Bool) (s : KEMSphinx.Keystream geom × Vector UInt8
        32 × (PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) (tail : ByteArray × List HopKeys) : ProbComp Bool :=
  if (s.2.2.1.c.pos : ℕ) + 1 < s.2.2.1.c.req.fwd.hops.length then
    if pathBuilds geom (RSOR.path nike s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver])
        ((RSOR.path nike s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver]).size -
        s.2.2.1.c.pos) then
      fnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 A ((forwardPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A
          := A) (s.2.1, default, s.2.2.1)))
        ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (A := A) (s.2.1, default, s.2.2.1)))
        s.2.2.1.st s.2.2.1.log s.2.2.1.c.req s.2.2.1.o s.2.2.1.c.pos s.2.1 s.2.2.2.1 s.2.2.2.2
        (spliceAt s.2.2.1.c.pos (Function.update (keysKs geom streamS (hopKeysWith nike kdfS
            ((nike.decodePrivateKey s.2.2.1.d).getD default) (RSOR.path nike s.2.2.1.c.req.fwd
            [.recipient s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys ((default, default,
            default), default) default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]).size).toArray)
          s.2.2.1.c.pos (Util.Bytes.ofVector s.1)) (keysKs geom streamS tail.2.toArray))
        (spliceAt s.2.2.1.c.pos (keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey
            s.2.2.1.d).getD default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys ((default, default, default), default)
            default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]).size).toArray) (keysTag macS tail.2.toArray))
        (spliceAt s.2.2.1.c.pos (keysEnc cipher (hopKeysWith nike kdfS ((nike.decodePrivateKey
            s.2.2.1.d).getD default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys ((default, default, default), default)
            default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]).size).toArray) (keysEnc cipher tail.2.toArray))
        (spliceAt s.2.2.1.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey
            s.2.2.1.d).getD default) (hopKeysWith nike kdfS ((nike.decodePrivateKey s.2.2.1.d).getD
            default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver])
            s.2.2.1.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
            s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver]).size).toArray 0) (hopKeysWith
            nike kdfS ((nike.decodePrivateKey s.2.2.1.d).getD default) (RSOR.path nike
            s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys
            ((default, default, default), default) default) (RSOR.path nike s.2.2.1.c.req.fwd
            [.recipient s.2.2.1.c.req.receiver]).size).toArray)
          (blindElem nike tail.1 tail.2.toArray))
    else pure false
  else E s

/-- **The adversary on the blinding game that world 0 gives.** It draws what world 0 draws
besides the relay's blinding seed, names the sender's secret, the path and the relay's place,
and plays `blindPost` on what it is given. -/
def blindAdv (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength
        + geom.forwardPayloadLength)) → ProbComp Bool) : BlindAdversary nike where
  St := KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
      (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
      geom.forwardPayloadLength))
  pre := do
    let U ← $ᵗ (KEMSphinx.Keystream geom)
    let km ← $ᵗ (Vector UInt8 32)
    let D ← forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) A
    let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    return (((nike.decodePrivateKey D.d).getD default,
      RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver], D.c.pos), (U, km, D, u, v))
  post := blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E

/-- The hops' keys of world 0 after its steps: the sender's, the honest relay's replaced by
its blinding seed alone. -/
theorem fwd0_keys (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A) :
    forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) x) default)
      = hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.2.d).getD default)
        (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]) x.2.2.c.pos
        (restKeys ((default, default, default), x.2.1) default)
        (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]).size := by
  have hpos : (x.2.2.c.pos : ℕ) < x.2.2.c.req.fwd.hops.length := x.2.2.c.pos.isLt
  have hsz := RSOR.path_size nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]
  have hkey : (x.2.2.c.req.fwd.hops[(x.2.2.c.pos : ℕ)]'hpos).key = x.2.2.k.1 :=
    congrArg (·.key) x.2.2.c.relay
  have hpk : ((RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver])[
        (x.2.2.c.pos : ℕ)]!).publicKey
      = Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1) := by
    rw [RSOR.path_getElem! nike _ _ _ hpos]
    exact congrArg (fun k : RSOR.Key nike => Util.Bytes.ofVector (nike.encodePublicKey k.1)) hkey
  have hmod := modify_publicKey_self
    (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]) x.2.2.c.pos
    (Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1)) (by rw [hsz]; exact hpos) hpk
  show hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.2.d).getD default)
    ((RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]).modify x.2.2.c.pos
      fun h => { h with publicKey := Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1) })
    x.2.2.c.pos (restKeys ((default, default, default), x.2.1) default) _ = _
  rw [hmod]
  exact congrArg (hopKeysWith nike kdfS _ _ _ _) (congrArg Array.size hmod)

/-- The hops' keys of world 1 after its first steps: the sender's for the replacement's path,
which is the original's cut after the honest relay, the relay's replaced likewise. -/
theorem fwd1_keys (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (x : StrX nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A) :
    forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) x) default)
      = hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.2.d).getD default)
        (RSOR.path nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) []) x.2.2.c.pos
        (restKeys ((default, default, default), x.2.1) default)
        (RSOR.path nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) []).size := by
  have hpos : (x.2.2.c.pos : ℕ) < x.2.2.c.req.fwd.hops.length := x.2.2.c.pos.isLt
  have hpos1 : (x.2.2.c.pos : ℕ) < (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)).hops.length := by
    show (x.2.2.c.pos : ℕ) < (List.take ((x.2.2.c.pos : ℕ) + 1) x.2.2.c.req.fwd.hops).length
    rw [List.length_take]
    exact lt_min (Nat.lt_succ_self _) hpos
  have hsz := RSOR.path_size nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) []
  have hkey : ((x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)).hops[(x.2.2.c.pos : ℕ)]'hpos1).key
      = x.2.2.k.1 := by
    show ((List.take ((x.2.2.c.pos : ℕ) + 1) x.2.2.c.req.fwd.hops)[(x.2.2.c.pos : ℕ)]'hpos1).key
      = _
    have h0 : (x.2.2.c.req.fwd.hops[(x.2.2.c.pos : ℕ)]'hpos).key = x.2.2.k.1 :=
      congrArg (·.key) x.2.2.c.relay
    have h1 : (List.take ((x.2.2.c.pos : ℕ) + 1) x.2.2.c.req.fwd.hops)[(x.2.2.c.pos : ℕ)]'hpos1
        = x.2.2.c.req.fwd.hops[(x.2.2.c.pos : ℕ)]'hpos := List.getElem_take
    exact (congrArg Protocols.RSOR.Hop.key h1).trans h0
  have hpk : ((RSOR.path nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) [])[
        (x.2.2.c.pos : ℕ)]!).publicKey
      = Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1) := by
    rw [RSOR.path_getElem! nike _ _ _ hpos1]
    exact congrArg (fun k : RSOR.Key nike => Util.Bytes.ofVector (nike.encodePublicKey k.1)) hkey
  have hmod := modify_publicKey_self
    (RSOR.path nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) []) x.2.2.c.pos
    (Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1)) (by rw [hsz]; exact hpos1) hpk
  show hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.2.d).getD default)
    ((RSOR.path nike (x.2.2.c.req.fwd.take (x.2.2.c.pos + 1)) []).modify x.2.2.c.pos
      fun h => { h with publicKey := Util.Bytes.ofVector (nike.encodePublicKey x.2.2.k.1.1) })
    x.2.2.c.pos (restKeys ((default, default, default), x.2.1) default) _ = _
  rw [hmod]
  exact congrArg (hopKeysWith nike kdfS _ _ _ _) (congrArg Array.size hmod)

set_option maxHeartbeats 4000000 in
/-- **Handed the path's own tail, the blinding adversary plays world 0**, on a draw before the
end of a path whose header builds. -/
theorem blindPost_real (names : Role → Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (E : KEMSphinx.Keystream geom ×
        Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) → ProbComp Bool)
    (U : KEMSphinx.Keystream geom) (km seed : Vector UInt8 32) (D : PropDraw nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
        (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) (u v : Vector
        UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hj : (D.c.pos : ℕ) + 1 < D.c.req.fwd.hops.length)
    (hT : pathBuilds geom (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) ((RSOR.path
        nike D.c.req.fwd [.recipient D.c.req.receiver]).size - D.c.pos)) :
    blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U, km, D, u, v)
        (tailOf nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd
        [.recipient D.c.req.receiver]) D.c.pos seed)
      = strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) A (km, seed, D) U u v := by
  have hpos : (D.c.pos : ℕ) < (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size :=
    lt_of_lt_of_eq D.c.pos.isLt (RSOR.path_size nike D.c.req.fwd _).symm
  have hlt : ∀ i, i < (D.c.pos : ℕ) → (hopKeysWith nike kdfS ((nike.decodePrivateKey D.d).getD
      default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos (restKeys
      ((default, default, default), seed) default) (RSOR.path nike D.c.req.fwd [.recipient
      D.c.req.receiver]).size).toArray[i]! = (hopKeysWith nike kdfS ((nike.decodePrivateKey
      D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos
      (restKeys ((default, default, default), default) default) (RSOR.path nike D.c.req.fwd
      [.recipient D.c.req.receiver]).size).toArray[i]! := fun i hi =>
    hopKeysWith_getElem!_lt nike kdfS _ _ _ _ _ _ i hi hpos.le
  have hat : ∀ s : HopKeys, (hopKeysWith nike kdfS ((nike.decodePrivateKey D.d).getD default)
      (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos s (RSOR.path nike
      D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray[
      (D.c.pos : ℕ)]! = s := fun s =>
    toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS _ _ _ _ _ hpos)
  have e1 : ∀ i, i ≤ (D.c.pos : ℕ) →
      Function.update (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey D.d).getD
          default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos (restKeys
          ((default, default, default), seed) default) (RSOR.path nike D.c.req.fwd [.recipient
          D.c.req.receiver]).size).toArray) D.c.pos (Util.Bytes.ofVector U) i
        = Function.update (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey
            D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos
            (restKeys ((default, default, default), default) default) (RSOR.path nike D.c.req.fwd
            [.recipient D.c.req.receiver]).size).toArray) D.c.pos (Util.Bytes.ofVector U) i :=
    fun i hi => by
      by_cases he : i = (D.c.pos : ℕ)
      · rw [he, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne he, Function.update_of_ne he]
        unfold keysKs
        rw [hlt i (by omega)]
  have e2 : ∀ i, i ≤ (D.c.pos : ℕ) → keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey
      D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos
      (restKeys ((default, default, default), seed) default) (RSOR.path nike D.c.req.fwd
      [.recipient D.c.req.receiver]).size).toArray i = keysTag macS (hopKeysWith nike kdfS
      ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient
      D.c.req.receiver]) D.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray i :=
    fun i hi => by
      funext m
      unfold keysTag
      by_cases he : i = (D.c.pos : ℕ)
      · rw [he, hat, hat]
        rfl
      · rw [hlt i (by omega)]
  have e3 : ∀ i, i ≤ (D.c.pos : ℕ) →
      keysEnc cipher (hopKeysWith nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path
          nike D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos (restKeys ((default, default,
          default), seed) default) (RSOR.path nike D.c.req.fwd [.recipient
          D.c.req.receiver]).size).toArray i = keysEnc cipher (hopKeysWith nike kdfS
          ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient
          D.c.req.receiver]) D.c.pos (restKeys ((default, default, default), default) default)
          (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray i := fun i hi =>
          by
    funext m
    unfold keysEnc
    by_cases he : i = (D.c.pos : ℕ)
    · rw [he, hat, hat]
      rfl
    · rw [hlt i (by omega)]
  have e4 : ∀ i, i ≤ (D.c.pos : ℕ) →
      blindElem nike (groupElem nike ((nike.decodePrivateKey D.d).getD default) (hopKeysWith nike
          kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd [.recipient
          D.c.req.receiver]) D.c.pos (restKeys ((default, default, default), seed) default)
          (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray 0) (hopKeysWith
          nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd
          [.recipient D.c.req.receiver]) D.c.pos (restKeys ((default, default, default), seed)
          default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray i
        = blindElem nike (groupElem nike ((nike.decodePrivateKey D.d).getD default) (hopKeysWith
            nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike D.c.req.fwd
            [.recipient D.c.req.receiver]) D.c.pos (restKeys ((default, default, default), default)
            default) (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size).toArray 0)
            (hopKeysWith nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
            D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos (restKeys ((default, default,
            default), default) default) (RSOR.path nike D.c.req.fwd [.recipient
            D.c.req.receiver]).size).toArray i := fun i hi =>
    blindElem_congr_lt nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey
      ((nike.decodePrivateKey D.d).getD default)))) _ _ i fun n hn =>
      congrArg HopKeys.blindingFactor (hlt n (by omega))
  have hrun := strRun_fwd0_fn nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (km,
      seed, D) U u v hj hT
  rw [fwd0_keys nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (km, seed, D)] at hrun
  have htail := fnRun_tailOf nike cipher macS kdfS streamS geom hvalid hmactag h16 A
    ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (A := A) (km, seed, D)))
    ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (A := A) (km, seed, D)))
    D.st D.log D.c.req D.o D.c.pos km u v ((nike.decodePrivateKey D.d).getD default) (RSOR.path
        nike D.c.req.fwd [.recipient D.c.req.receiver]) seed (restKeys ((default, default,
        default), seed) default) (Util.Bytes.ofVector U)
    hpos rfl
  rw [spliceAt_congr_le _ _ _ _ e1, spliceAt_congr_le _ _ _ _ e2, spliceAt_congr_le _ _ _ _ e3,
    spliceAt_congr_le _ _ _ _ e4] at htail
  unfold blindPost
  rw [ite_eq_left hj, ite_eq_left hT]
  exact (hrun.trans htail).symm

/-- At the end of the path the blinding adversary plays `E`. -/
theorem blindPost_exit (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) (s : KEMSphinx.Keystream geom × Vector UInt8 32 ×
    (PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
    (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS kdfS streamS
    geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)))
    (tail : ByteArray × List HopKeys)
    (hj : ¬ (s.2.2.1.c.pos : ℕ) + 1 < s.2.2.1.c.req.fwd.hops.length) :
    blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E s tail = E s := by
  unfold blindPost
  exact ite_eq_right hj

/-- **World 0 over its draws, with `E` at the end of the path**: the game's draws, the relay's
keystream and MAC key, the two blocks, and the relay's blinding seed last. -/
def world0E (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (E :
    KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom
    hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher
    macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength
    + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) : ProbComp Bool :=
  forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) A >>= fun D => do
    let U ← $ᵗ (KEMSphinx.Keystream geom)
    let km ← $ᵗ (Vector UInt8 32)
    let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let seed ← $ᵗ (Vector UInt8 32)
    if (D.c.pos : ℕ) + 1 < D.c.req.fwd.hops.length then
      strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) A (km, seed, D) U u v
    else E (U, km, D, u, v)

/-- The draws of world 0 on which the relay is before the end of a path whose header does not
build. -/
def fwdBad0 {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).Oth A) : Prop :=
  (D.c.pos : ℕ) + 1 < D.c.req.fwd.hops.length ∧ ¬ pathBuilds geom (RSOR.path nike D.c.req.fwd
      [.recipient D.c.req.receiver]) ((RSOR.path nike D.c.req.fwd [.recipient
      D.c.req.receiver]).size - D.c.pos)

set_option maxHeartbeats 2000000 in
/-- **The blinding game's side with the sender's own secret is world 0**, off the draws on
which the path's header does not build. -/
theorem blindGame_false_sub_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) :
    |(Pr{let b ← (blindGame kdfS (blindAdv nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A E) false)}[b = true]).toReal
      - (Pr{let b ← (world0E nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E)}[b =
          true]).toReal|
    ≤ (Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)}[fwdBad0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 D]).toReal := by
  have hB : blindGame kdfS (blindAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
      E) false
      =ᵈ (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) A >>= fun D => do
        let U ← $ᵗ (KEMSphinx.Keystream geom)
        let km ← $ᵗ (Vector UInt8 32)
        let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        let seed ← $ᵗ (Vector UInt8 32)
        blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U, km, D, u, v)
            (tailOf nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
            D.c.req.fwd [.recipient D.c.req.receiver]) D.c.pos seed)) := by
    unfold blindGame blindAdv
    simp only [bind_assoc, pure_bind, Bool.false_eq_true, ↓reduceIte]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    exact EvalDistEq.bind_right _ fun D => EvalDistEq.bind_right _ fun U =>
      EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun u =>
      EvalDistEq.bind_right _ fun v => EvalDistEq.bind_right _ fun seed =>
      OracleComp.EvalDistEq.bind_const _ _
  rw [hB (fun b => b = true)]
  unfold world0E
  exact KEMSphinx.abs_prEvent_bind_sub_le_bad _ _ _ (fun D => fwdBad0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 D) fun D hD => by
    by_cases hj : (D.c.pos : ℕ) + 1 < D.c.req.fwd.hops.length
    · have hT : pathBuilds geom (RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver])
        ((RSOR.path nike D.c.req.fwd [.recipient D.c.req.receiver]).size - D.c.pos) := not_not.mp
        fun h => hD ⟨hj, h⟩
      simp only [blindPost_real nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E _ _
          _ D _ _ hj hT, hj, ↓reduceIte]
    · have hx := fun (U : KEMSphinx.Keystream geom) (km : Vector UInt8 32)
          (u v : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
          (tail : ByteArray × List HopKeys) =>
        blindPost_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E
          (U, km, D, u, v) tail hj
      simp only [hx, hj, ↓reduceIte]

/-- **World 0 with the hops after the relay from an independent secret**: the draws of
`world0E`, then a secret `d0`, and the blinding adversary's game on the tail of the path from
`d0`. -/
def world0B (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (E :
    KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom
    hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher
    macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength
    + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) : ProbComp Bool :=
  forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) A >>= fun D => do
    let U ← $ᵗ (KEMSphinx.Keystream geom)
    let km ← $ᵗ (Vector UInt8 32)
    let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let seed ← $ᵗ (Vector UInt8 32)
    let d0 ← $ᵗ (Vector UInt8 nike.privateKeySize)
    blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U, km, D, u, v)
      (tailOf nike kdfS ((nike.decodePrivateKey d0).getD default) (RSOR.path nike D.c.req.fwd
          [.recipient D.c.req.receiver]) D.c.pos seed)

/-- The blinding game's side with an independent secret is `world0B`. -/
theorem blindGame_true_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S
    := 𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) :
    blindGame kdfS (blindAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E) true
        =ᵈ world0B nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E := by
  unfold blindGame blindAdv world0B
  simp only [bind_assoc, pure_bind, ↓reduceIte]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- **Replacing the secret behind the hops after the relay** costs the blinding advantage of
`blindAdv` and the chance of a draw on which the path's header does not build. -/
theorem world0E_sub_world0B_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) :
    |(Pr{let b ← (world0E nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E)}[b =
        true]).toReal
      - (Pr{let b ← (world0B nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E)}[b =
          true]).toReal|
    ≤ (Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)}[fwdBad0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 D]).toReal
      + blindAdvantage kdfS (blindAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
          E) := by
  have h1 := blindGame_false_sub_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E
  rw [abs_sub_comm] at h1
  rw [← (blindGame_true_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E)
      (fun b => b = true)]
  refine (abs_sub_le _ (Pr{let b ← (blindGame kdfS (blindAdv nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names A E)
    false)}[b = true]).toReal _).trans (add_le_add h1 (le_of_eq ?_))
  exact abs_sub_comm _ _

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
