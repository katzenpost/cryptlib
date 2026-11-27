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

/-! ## The original and the replacement at the relay's hop -/

section Shift

variable (nike : NIKE) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)

omit macS kdfS streamS geom in
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

/-- **A relay behind two filters is one relay that answers by cases.** The packets `chal` picks
are answered by `f`, the rest by `g`, and the game is the honest relays' with the relay answering
so. -/
theorem first_viaOracle_run (chal : ByteArray → Bool) (f g : ByteArray → ProcResult)
    (sk : Role → nike.PrivateKey) (patch : Protocols.RSOR.Patch 𝒮) {α : Type}
    (oa : OracleComp (Protocols.RSOR.oracleSpec 𝒮) α) (log : Protocols.RSOR.Log 𝒮) :
    simulateQ (relayImpl g) (simulateQ (Relay.first chal f)
        ((simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay sk
          patch) oa).run' log))
      = (simulateQ (Protocols.RSOR.oracle (m := ProbComp)
          (fun h o => pure (if h = Role.relay then
              stepOf geom (if chal (join o) = true then f (join o) else g (join o))
            else RSOR.proc nike cipher macS kdfS streamS geom (sk h) o))
          (fun h msg o => pure (if h = Role.relay then
              replyOf cipher geom msg (if chal (join o) = true then f (join o) else g (join o))
            else RSOR.reply nike cipher macS kdfS streamS geom (sk h) msg o))
          patch) oa).run' log := by
  rw [← QueryImpl.simulateQ_compose, Relay.relayImpl_comp_first]
  simp only [StateT.run', simulateQ_map]
  exact congrArg (fun x => (·.1) <$> x)
    (viaOracle_relayImpl nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay
      (fun pkt => if chal pkt = true then f pkt else g pkt) sk patch oa log)

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
    (hT : (nikeHdrTrace geom (Function.update (keysKs geom streamS K.toArray) j U) (Function.update
        (keysTag macS K.toArray) j fun _ => Util.Bytes.ofVector T) (blindElem nike a K.toArray)
        (RSOR.filler nike geom (RSOR.path nike q.fwd [.recipient q.receiver]) r.1) (RSOR.path nike
        q.fwd [.recipient q.receiver]) ((RSOR.path nike q.fwd [.recipient q.receiver]).size -
        j)).isSome)
    (hM : (onionMsgStream nike macS streamS geom q r a K j U).size
      = 2 + nike.publicKeySize + geom.routingInfoLength) :
    hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T U
        (K.toArray[j]!) (Util.Bytes.toVecN _ (onionMsgStream nike macS streamS geom q r a K j U ++
            Util.Bytes.ofVector T)) D {}
      = fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO
          (Util.Bytes.toVecN _ (onionMsgStream nike macS streamS geom q r a K j U ++
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
  refine hdrRelay_eq_fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T
    U _ _ D _ _ _ _ _ j (by omega) (by omega) hfill (fun k => ?_) (fun m x => ?_)
    ((blindElem_size nike _ _ _).trans ha) ?_ hT (Function.update_self _ _ _)
    (by rw [Function.update_self]) rfl ?_
  · by_cases hk : k = j
    · rw [hk, Function.update_self]
      exact hU
    · rw [Function.update_of_ne hk]
      exact streamS.keystream_size _ _ _
  · by_cases hm : m = j
    · rw [hm, Function.update_self]
      exact (Util.Bytes.size_ofVector _).trans hmactag
    · rw [Function.update_of_ne hm]
      exact (Util.Bytes.size_ofVector _).trans hmactag
  · rw [RSOR.path_getElem! nike _ _ j (by omega)]
    exact ite_eq_right (by omega)
  · rw [Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, hM, Util.Bytes.size_ofVector, hhdr, had, hmactag])]
    unfold layerHdr onionMsgStream
    rw [hdrMsg_update_tag geom _ _ _ _ _ j (by omega), Function.update_self]

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
    (hT : (nikeHdrTrace geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) x) default)).toArray) x.2.2.c.pos (Util.Bytes.ofVector U))
        (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        x) default)).toArray) x.2.2.c.pos fun _ => Util.Bytes.ofVector (strTag nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) x U)) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
        x.2.2) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) x) default)).toArray) (RSOR.filler
        nike geom (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]) x.2.2.o.1)
        (RSOR.path nike x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]) ((RSOR.path nike
        x.2.2.c.req.fwd [.recipient x.2.2.c.req.receiver]).size - x.2.2.c.pos)).isSome)
    (hM : (onionMsgStream nike macS streamS geom x.2.2.c.req x.2.2.o (groupElem nike (drawKey nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S :=
        𝒮)) .relay names x.2.2) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x)
        default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x) default))
        x.2.2.c.pos (Util.Bytes.ofVector U)).size = 2 + nike.publicKeySize +
        geom.routingInfoLength) :
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
  have hmsg : strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) x U = (onionMsgStream nike macS streamS geom
      x.2.2.c.req x.2.2.o (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names x.2.2) (forwardKeys0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) x) default)).toArray 0) (forwardKeys0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) x) default)) x.2.2.c.pos (Util.Bytes.ofVector U)) :=
    Util.Bytes.ofVector_toVecN _ hM
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
      (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) hT hM
  rw [hk, ← hmsg] at h
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

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
