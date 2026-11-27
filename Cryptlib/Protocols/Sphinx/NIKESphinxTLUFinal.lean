/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUNext

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Common (commandsToBytes zeroPadTo toVec32)
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

end Cryptlib.Protocols.Sphinx.NIKESphinx
