/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.RSOR
import Cryptlib.Protocols.Sphinx.KEMSphinxLayer
import Cryptlib.Protocols.Sphinx.SURB

/-! # KEM Sphinx as a repliable service onion routing scheme

`scheme` is KEM Sphinx as a `Protocols.RSOR.Scheme`: the algorithms, and the four correctness laws
proved of `newKEMPacket`, `unwrapKEM`, `newKEMSURB`, `newPacketFromSURB` and `decryptSURBPayload`.
A relay is named by its node ID. The exit relay's commands name the receiver, and
the forward payload carries the SURB in front of the message, as Katzenpost lays it out. -/

namespace Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR

open OracleComp OracleSpec
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

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

abbrev Name := Vector UInt8 32

abbrev Msg := Vector UInt8 geom.userForwardPayloadLength

abbrev Onion := Vector UInt8 geom.headerLength ×
  Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)

/-- What a sender draws for one path: a seed for each hop, and the filler. A path shorter than
`geom.nrHops` uses a prefix of each. -/
abbrev Draw := Vector (Vector UInt8 32) geom.nrHops × Vector UInt8 geom.routingInfoLength

/-- The draws for the forward path and for the backward path, the SURB's payload key, and its
ID. -/
abbrev Randomness := Draw geom × Draw geom × Vector UInt8 64 × Vector UInt8 16

/-- A relay's public key: one that some private key gives. The paper's challenger checks that
the adversary's keys are valid; here a key that is not valid is not a `Key`. -/
abbrev Key := {k : kem.PublicKey // ∃ sk, k = kem.derivePublicKey sk}

abbrev Request := Protocols.RSOR.Request geom.nrHops Name (Key kem) (Msg geom) Name

variable {geom} in
/-- A route as `newKEMPacket` takes it. Only its last hop has commands. -/
def path (R : Protocols.RSOR.Route geom.nrHops Name (Key kem)) (last : List RoutingCommand) :
    Array PathHop :=
  (R.hops.mapIdx fun i h =>
    ⟨h.name, ofVector (kem.encodePublicKey h.key.1),
      if i + 1 = R.hops.length then last else []⟩).toArray

/-- The key pair of a relay. The public key is the one derived from the private key. -/
def keygen : ProbComp (Key kem × kem.PrivateKey) := do
  let s ← $ᵗ Vector UInt8 32
  return (⟨kem.derivePublicKey (keygenOf kem s).2, _, rfl⟩, (keygenOf kem s).2)

theorem key_of_keygen (k : Key kem) (sk : kem.PrivateKey) (h : (k, sk) ∈ support (keygen kem)) :
    k.1 = kem.derivePublicKey sk := by
  simp only [keygen, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    Prod.mk.injEq] at h
  obtain ⟨s, -, h1, h2⟩ := h
  rw [h1, h2]

/-- The filler of the layer for position `i`. -/
def fillerAt (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (filler : ByteArray) :
    ℕ → ByteArray
  | 0 => filler
  | i + 1 => tailFiller kem kdfS streamS geom (hops.extract i hops.size)
      (seeds.extract i seeds.size) (fillerAt hops seeds filler i)

/-- The layer of a packet that the hop at position `i` receives: a packet on the path from that
hop on. -/
def layer (hops : Array PathHop) (d : Draw geom) (payload : ByteArray) (i : ℕ) :
    Except String ByteArray :=
  let seeds := d.1.toArray.extract 0 hops.size
  newKEMPacket kem cipher macS kdfS streamS geom (seeds.extract i seeds.size)
    (fillerAt kem kdfS streamS geom hops seeds
      ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)) i)
    (hops.extract i hops.size) payload

/-- The SURB for the backward path and the keys that open its reply. An empty backward path has
none. -/
def surb (q : Request kem geom) (r : Randomness geom) : ByteArray × ByteArray :=
  let hops := path kem q.back [.surbReply r.2.2.2]
  match newKEMSURB kem macS kdfS streamS geom (r.2.1.1.toArray.extract 0 hops.size) r.2.2.1
      ((ofVector r.2.1.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
      hops with
  | .ok x => x
  | .error _ => (⟨Array.replicate geom.surbLength 0⟩, .empty)

/-- The forward payload: a flag for the SURB, a reserved byte, the SURB, and the message. -/
def body (q : Request kem geom) (r : Randomness geom) : ByteArray :=
  ⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ ++ (surb kem macS kdfS streamS geom q r).1
    ++ ofVector q.msg

/-- The message at the end of a forward payload. -/
def msgOf (p : ByteArray) : Msg geom :=
  toVecN _ (p.extract (p.size - geom.userForwardPayloadLength) p.size)

def split (pkt : ByteArray) : Onion geom :=
  (toVecN _ (pkt.extract 0 geom.headerLength), toVecN _ (pkt.extract geom.headerLength pkt.size))

variable {geom} in
def join (o : Onion geom) : ByteArray := ofVector o.1 ++ ofVector o.2

def form (q : Request kem geom) (r : Randomness geom) (i : Fin q.fwd.hops.length) : Onion geom :=
  match layer kem cipher macS kdfS streamS geom (path kem q.fwd [.recipient q.receiver]) r.1
      (body kem macS kdfS streamS geom q r) i with
  | .ok pkt => split geom pkt
  | .error _ => default

/-- A relay unwraps the packet and reads its commands. A relay does not use its own name. -/
def proc (sk : kem.PrivateKey) (o : Onion geom) :
    Option (Protocols.RSOR.Step Name (Onion geom) (Msg geom) Name
      (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) :=
  match procWith kem cipher macS kdfS streamS geom
      (kemDecap kem (ofVector (kem.encodePrivateKey sk))) (join o) with
  | some (none, _, cmds, some fwd) => cmds.findSome? fun
    | .nextNodeHop next _ => some (.forward next (split geom fwd))
    | _ => none
  | some (some p, _, cmds, none) => cmds.findSome? fun
    | .recipient receiver => some (.deliver (msgOf geom p) receiver)
    | .surbReply _ => some (.reply (toVecN _ p))
    | _ => none
  | _ => none

/-- The draws from which the first layer on a path can be built and no KEM round trip fails.
Every later layer can then be built too (`Builds.layer`). -/
def Builds (R : Protocols.RSOR.Route geom.nrHops Name (Key kem)) (last : List RoutingCommand)
    (d : Draw geom) (payload : ByteArray) : Prop :=
  (∀ i < R.hops.length, kem.Reliable (kem.stateFromSeed d.1.toArray[i]!)) ∧
    (0 < R.hops.length →
      ∃ pkt, layer kem cipher macS kdfS streamS geom (path kem R last) d payload 0 = .ok pkt)

/-- A reply's plaintext: the message, then zeros up to the forward payload length. -/
def pad (m : Msg geom) : ByteArray :=
  ofVector m ++ ⟨Array.replicate (geom.forwardPayloadLength - geom.userForwardPayloadLength) 0⟩

/-- The reply packet the exit relay builds from the SURB, and the relay it sends it to. -/
def replyPacket (q : Request kem geom) (r : Randomness geom) (m : Msg geom) : ByteArray × Name :=
  match SURB.newPacketFromSURB cipher geom (surb kem macS kdfS streamS geom q r).1 (pad geom m) with
  | .ok x => x
  | .error _ => (.empty, default)

/-- A payload after `j` relays have each decrypted it under their hop key. -/
def peeled (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (p : ByteArray) : ℕ → ByteArray
  | 0 => p
  | j + 1 =>
    cipher.decrypt (kemHopKeys kem kdfS hops seeds j).payloadEncryption.toArray
      (ofVector (kemHopKeys kem kdfS hops seeds j).headerEncryptionIV) (peeled hops seeds p j)

/-- The layer of a reply that the relay at backward position `j` receives: the header of a
packet on the rest of the backward path, and the payload as the relays before left it. -/
def formBack (q : Request kem geom) (r : Randomness geom) (m : Msg geom)
    (j : Fin q.back.hops.length) : Onion geom :=
  let hops := path kem q.back [.surbReply r.2.2.2]
  match layer kem cipher macS kdfS streamS geom hops r.2.1
      ⟨Array.replicate geom.forwardPayloadLength 0⟩ j with
  | .ok pkt =>
    let first := (replyPacket kem cipher macS kdfS streamS geom q r m).1
    split geom (pkt.extract 0 geom.headerLength ++ peeled kem cipher kdfS hops
      (r.2.1.1.toArray.extract 0 hops.size) (first.extract geom.headerLength first.size) j)
  | .error _ => default

/-- The exit relay answers with the SURB it finds in the payload. -/
def reply (sk : kem.PrivateKey) (m : Msg geom) (o : Onion geom) : Option (Name × Onion geom) :=
  match procWith kem cipher macS kdfS streamS geom
      (kemDecap kem (ofVector (kem.encodePrivateKey sk))) (join o) with
  | some (some p, _, _, none) =>
    if p.get! 0 = 1 then
      match SURB.newPacketFromSURB cipher geom (p.extract 2 (2 + geom.surbLength)) (pad geom m) with
      | .ok (pkt, next) => some (next, split geom pkt)
      | .error _ => none
    else none
  | _ => none

/-- The sender opens a reply with the keys it kept from the SURB. -/
def recover (q : Request kem geom) (r : Randomness geom)
    (p : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) : Option (Msg geom) :=
  match SURB.decryptSURBPayload cipher geom (surb kem macS kdfS streamS geom q r).2
      (ofVector p) with
  | .ok b => some (toVecN _ (b.extract 0 geom.userForwardPayloadLength))
  | .error _ => none

/-- The draws for which no relay on either path fails to process its layer. -/
def Reliable (q : Request kem geom) (r : Randomness geom) : Prop :=
  Builds kem cipher macS kdfS streamS geom q.fwd [.recipient q.receiver] r.1
    (body kem macS kdfS streamS geom q r) ∧
  Builds kem cipher macS kdfS streamS geom q.back [.surbReply r.2.2.2] r.2.1
    ⟨Array.replicate geom.forwardPayloadLength 0⟩

variable {geom} in
theorem path_size (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last : List RoutingCommand) : (path kem R last).size = R.hops.length := by
  simp [path]

variable {geom} in
theorem path_getElem! (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last : List RoutingCommand) (j : ℕ) (h : j < R.hops.length) :
    (path kem R last)[j]! = ⟨R.hops[j].name, ofVector (kem.encodePublicKey R.hops[j].key.1),
      if j + 1 = R.hops.length then last else []⟩ := by
  simp [path, h]

theorem extract_extract_one {α : Type} (a : Array α) (i : ℕ) :
    (a.extract i a.size).extract 1 (a.extract i a.size).size = a.extract (i + 1) a.size := by
  apply Array.ext
  · simp; omega
  · intro j h1 h2
    simp only [Array.getElem_extract]
    congr 1
    omega

theorem join_split (pkt : ByteArray) (h : geom.headerLength ≤ pkt.size)
    (hp : pkt.size = geom.headerLength + (geom.payloadTagLength + geom.forwardPayloadLength)) :
    join (split geom pkt) = pkt := by
  unfold join split
  rw [ofVector_toVecN _ (by rw [ByteArray.size_extract]; omega),
    ofVector_toVecN _ (by rw [ByteArray.size_extract]; omega)]
  exact Cryptlib.Util.Bytes.append_extract pkt _ h

theorem join_split_layer (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (hops : Array PathHop) (d : Draw geom) (payload pkt : ByteArray) (i : ℕ)
    (hpkt : layer kem cipher macS kdfS streamS geom hops d payload i = .ok pkt) :
    pkt.size = geom.headerLength + (geom.payloadTagLength + geom.forwardPayloadLength) ∧
      join (split geom pkt) = pkt := by
  have hpay := (newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hpkt).1
  have hsz := newKEMPacket_size kem cipher macS kdfS streamS geom _ _ _ _ _ hvalid hmactag hpkt hpay
  obtain ⟨-, -, -, -, hpacket, -⟩ := id hvalid
  exact ⟨by omega, join_split geom pkt (by omega) (by omega)⟩

set_option maxHeartbeats 1000000 in
/-- **What a relay does with a layer.** It decapsulates the shared secret the sender derived its
hop keys from. Before the end of the path it gets the next relay's name and the next layer. At
the end it gets the last hop's commands and the payload, with its tag still in front if the
commands carry a SURB reply. -/
theorem procWith_layer (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (R : Protocols.RSOR.Route geom.nrHops Name (Key kem)) (last : List RoutingCommand)
    (hnn : ∀ c ∈ last, c ≠ .null) (hnh : ∀ c ∈ last, ∀ id m, c ≠ .nextNodeHop id m)
    (d : Draw geom) (payload : ByteArray) (i : ℕ) (hi : i < R.hops.length) (sk : kem.PrivateKey)
    (hkey : R.hops[i].key.1 = kem.derivePublicKey sk)
    (hrel : ∀ j < R.hops.length, kem.Reliable (kem.stateFromSeed d.1.toArray[j]!))
    (pkt : ByteArray)
    (hpkt : layer kem cipher macS kdfS streamS geom (path kem R last) d payload i = .ok pkt) :
    let dec := kemDecap kem (ofVector (kem.encodePrivateKey sk))
    (∃ ss, dec (pkt.extract 2 (2 + kem.ciphertextSize)) = .ok ss ∧
      kemHopKeys kem kdfS (path kem R last) (d.1.toArray.extract 0 (path kem R last).size) i
        = deriveHopKeys kdfS ss) ∧
    (∀ h : i + 1 < R.hops.length, ∃ tag mac fwd,
      procWith kem cipher macS kdfS streamS geom dec pkt
        = some (none, tag, [.nextNodeHop R.hops[i + 1].name mac], some fwd) ∧
      layer kem cipher macS kdfS streamS geom (path kem R last) d payload (i + 1) = .ok fwd) ∧
    (i + 1 = R.hops.length → ∃ tag, procWith kem cipher macS kdfS streamS geom dec pkt
      = some (some (if hasSurbReply last
          then (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload else payload),
        tag, last, none)) := by
  intro dec
  have hn := path_size kem R last
  have hle := R.length_le
  unfold layer at hpkt
  dsimp only at hpkt
  have h0 : ((path kem R last).extract i (path kem R last).size)[0]!
      = ⟨R.hops[i].name, ofVector (kem.encodePublicKey R.hops[i].key.1),
        if i + 1 = R.hops.length then last else []⟩ := by
    rw [getElem!_extract_from _ _ _ (by omega), Nat.add_zero, path_getElem! kem _ _ _ hi]
  have hself : kemSelfPublicKeyBytes kem (ofVector (kem.encodePrivateKey sk))
      = (((path kem R last).extract i (path kem R last).size)[0]!).publicKey := by
    rw [h0, hkey]
    unfold kemSelfPublicKeyBytes
    rw [toVecN_ofVector, kem.decode_encode_priv]
  have hs : ∀ j, i + j < R.hops.length →
      ((d.1.toArray.extract 0 (path kem R last).size).extract i
        (d.1.toArray.extract 0 (path kem R last).size).size)[j]! = d.1.toArray[i + j]! := by
    intro j hj
    rw [getElem!_extract_from _ _ _ (by simp; omega),
      getElem!_extract_zero _ _ _ (by omega) (by simpa [hn] using hle)]
  have hseed : ∀ j, j < ((path kem R last).extract i (path kem R last).size).size →
      kem.Reliable (kem.stateFromSeed
        ((d.1.toArray.extract 0 (path kem R last).size).extract i
          (d.1.toArray.extract 0 (path kem R last).size).size)[j]!) := by
    intro j hj
    have hj' : i + j < R.hops.length := by simp at hj; omega
    rw [hs j hj']
    exact hrel _ hj'
  obtain ⟨hmid, hlast⟩ := newKEMPacket_unwrapKEM kem cipher macS kdfS streamS geom hvalid hmactag
    h16 _ _ _ _ pkt (ofVector (kem.encodePrivateKey sk)) hself hseed
    (by rw [h0]; intro c hc; split at hc <;> simp at hc; exact hnn c hc)
    (by rw [h0]; intro c hc; split at hc <;> simp at hc; exact hnh c hc) hpkt
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨-, hdr, sprpKeys, t, hcreate, -, -, hpkteq⟩ :=
      newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hpkt
    obtain ⟨-, -, -, -, ke, keys, -, -, s, -, -, -, -, hkc, -, -, -, hhdreq, -⟩ :=
      createKEMHeader_unfold kem macS kdfS streamS geom _ _ _ _ _ hcreate
    obtain ⟨ct, ss, henc, hct, -⟩ := hkc 0 (by simp; omega)
    have hctsize : ct.size = kem.ciphertextSize := kemEncap_size kem _ _ ct ss henc
    have hv0 : v0AD.size = 2 := rfl
    refine ⟨ss, ?_, ?_⟩
    · have hslice : pkt.extract 2 (2 + kem.ciphertextSize) = ct := by
        rw [hpkteq, hhdreq, hct,
          Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
            simp only [ByteArray.size_append, hv0, hctsize]; omega),
          Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
            simp only [ByteArray.size_append, hv0, hctsize]; omega),
          Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
            simp only [ByteArray.size_append, hv0, hctsize]; omega)]
        exact extract_append_tail v0AD ct 2 _ rfl (by rw [hctsize])
      show kemDecap kem _ _ = _
      rw [hslice]
      exact kemEncap_kemDecap_of_honest kem _ _ ct ss (hseed 0 (by simp; omega))
        (by rw [hself]; exact henc)
    · rw [getElem!_extract_from _ _ _ (by omega), hs 0 (by omega), Nat.add_zero] at henc
      unfold kemHopKeys
      rw [getElem!_extract_zero d.1.toArray i _ (by omega) (by simpa [hn] using hle), henc]
  · intro h
    obtain ⟨tag, mac, fwd, hun, hnext⟩ := hmid (by simp; omega)
    rw [extract_extract_one, extract_extract_one] at hnext
    have h1 : ((path kem R last).extract i (path kem R last).size)[1]!.id
        = R.hops[i + 1].name := by
      rw [getElem!_extract_from _ _ _ (by omega), path_getElem! kem _ _ _ h]
    refine ⟨tag, mac, ofVector fwd, ?_, ?_⟩
    · unfold procWith
      rw [show unwrapKEMWith kem cipher macS kdfS streamS geom _ pkt = _ from hun, h0, h1]
      simp [show ¬ (i + 1 = R.hops.length) by omega]
    · unfold layer
      simp only [fillerAt]
      exact hnext
  · intro h
    obtain ⟨tag, hun⟩ := hlast (by simp; omega)
    rw [h0] at hun
    simp only [if_pos h] at hun
    exact ⟨tag, by
      unfold procWith
      rw [show unwrapKEMWith kem cipher macS kdfS streamS geom _ pkt = _ from hun]
      rfl⟩

/-- Every layer on a path can be built when the first can: each relay's key has a private key,
and what that relay would forward is the next layer. -/
theorem Builds.layer (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (R : Protocols.RSOR.Route geom.nrHops Name (Key kem)) (last : List RoutingCommand)
    (hnn : ∀ c ∈ last, c ≠ .null) (hnh : ∀ c ∈ last, ∀ id m, c ≠ .nextNodeHop id m)
    (d : Draw geom) (payload : ByteArray)
    (hb : Builds kem cipher macS kdfS streamS geom R last d payload) (i : ℕ)
    (hi : i < R.hops.length) :
    ∃ pkt, layer kem cipher macS kdfS streamS geom (path kem R last) d payload i = .ok pkt := by
  induction i with
  | zero => exact hb.2 hi
  | succ i ih =>
    obtain ⟨pkt, hpkt⟩ := ih (by omega)
    obtain ⟨sk, hsk⟩ := (R.hops[i]'(by omega)).key.2
    obtain ⟨-, hmid, -⟩ := procWith_layer kem cipher macS kdfS streamS geom hvalid hmactag h16
      R last hnn hnh d payload i (by omega) sk hsk hb.1 pkt hpkt
    obtain ⟨-, -, fwd, -, h⟩ := hmid hi
    exact ⟨fwd, h⟩

/-- A relay on the forward path gets the next layer, and the exit relay the message. -/
theorem proc_form (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (q : Request kem geom) (r : Randomness geom) (i : Fin q.fwd.hops.length)
    (sk : kem.PrivateKey)
    (hr : Builds kem cipher macS kdfS streamS geom q.fwd [.recipient q.receiver] r.1
      (body kem macS kdfS streamS geom q r))
    (hk : (q.fwd.hops[i].key, sk) ∈ support (keygen kem)) :
    proc kem cipher macS kdfS streamS geom sk (form kem cipher macS kdfS streamS geom q r i)
      = some (if h : i + 1 < q.fwd.hops.length
        then .forward q.fwd.hops[i.val + 1].name
          (form kem cipher macS kdfS streamS geom q r ⟨i + 1, h⟩)
        else .deliver q.msg q.receiver) := by
  obtain ⟨pkt, hpkt⟩ := Builds.layer kem cipher macS kdfS streamS geom hvalid hmactag h16 _ _
    (by simp) (by simp) _ _ hr i i.isLt
  obtain ⟨-, hmid, hlast⟩ := procWith_layer kem cipher macS kdfS streamS geom hvalid hmactag h16
    q.fwd [.recipient q.receiver] (by simp) (by simp) r.1 _ i i.isLt sk
    (key_of_keygen kem _ _ hk) hr.1 pkt hpkt
  unfold proc form
  rw [hpkt]
  dsimp only
  rw [(join_split_layer kem cipher macS kdfS streamS geom hvalid hmactag _ _ _ _ _ hpkt).2]
  by_cases h : i + 1 < q.fwd.hops.length
  · obtain ⟨tag, mac, fwd, hp, hnext⟩ := hmid h
    rw [hp, dif_pos h, hnext]
    simp
  · obtain ⟨tag, hp⟩ := hlast (by omega)
    have hmsg : msgOf geom (body kem macS kdfS streamS geom q r) = q.msg := by
      unfold msgOf body
      have := Cryptlib.Util.Bytes.extract_append_right
        (⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ ++ (surb kem macS kdfS streamS geom q r).1)
        (ofVector q.msg)
      rw [Cryptlib.Util.Bytes.size_ofVector] at this
      rw [ByteArray.size_append, Cryptlib.Util.Bytes.size_ofVector, Nat.add_sub_cancel, this,
        toVecN_ofVector]
    rw [hp, dif_neg h, hasSurbReply_eq_false (by simp), if_neg Bool.false_ne_true]
    simp [hmsg]

/-- The keys that open a reply, as `newKEMSURB` lays them out: the hops' payload keys, last hop
first, then the SURB's payload key. -/
def surbKeys (keys : Array SPRPKey) (kp : Vector UInt8 64) : ByteArray :=
  (List.range' 0 keys.size).foldl (fun k i =>
    k ++ ofVector keys[keys.size - 1 - i]!.key ++ ofVector keys[keys.size - 1 - i]!.iv) .empty
    ++ ofVector kp

theorem newKEMSURB_eq (seeds : Array (Vector UInt8 32)) (kp : Vector UInt8 64)
    (filler : ByteArray) (hops : Array PathHop) (hdr : ByteArray) (keys : Array SPRPKey)
    (h : createKEMHeader kem macS kdfS streamS geom seeds filler hops = .ok (hdr, keys)) :
    newKEMSURB kem macS kdfS streamS geom seeds kp filler hops
      = .ok (hdr ++ ofVector (hops[0]!).id ++ ofVector kp, surbKeys keys kp) := by
  unfold newKEMSURB
  dsimp only
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, pure_bind]
  rw [h]
  rfl

theorem surbKeys_chunks (keys : Array SPRPKey) (kp : Vector UInt8 64) :
    (surbKeys keys kp).size = (keys.size + 1) * 64 ∧
    (∀ j < keys.size,
      (surbKeys keys kp).extract (j * 64) (j * 64 + 48) = ofVector keys[keys.size - 1 - j]!.key ∧
      (surbKeys keys kp).extract (j * 64 + 48) (j * 64 + 64)
        = ofVector keys[keys.size - 1 - j]!.iv) ∧
    (surbKeys keys kp).extract (keys.size * 64) (keys.size * 64 + 48) = (ofVector kp).extract 0 48 ∧
    (surbKeys keys kp).extract (keys.size * 64 + 48) (keys.size * 64 + 64)
      = (ofVector kp).extract 48 64 := by
  have key : ∀ m, ((List.range' 0 m).foldl (fun k i =>
        k ++ ofVector keys[keys.size - 1 - i]!.key ++ ofVector keys[keys.size - 1 - i]!.iv)
        ByteArray.empty).size = m * 64 ∧
      ∀ j < m, ((List.range' 0 m).foldl (fun k i =>
        k ++ ofVector keys[keys.size - 1 - i]!.key ++ ofVector keys[keys.size - 1 - i]!.iv)
        ByteArray.empty).extract (j * 64) (j * 64 + 48) = ofVector keys[keys.size - 1 - j]!.key ∧
        ((List.range' 0 m).foldl (fun k i =>
        k ++ ofVector keys[keys.size - 1 - i]!.key ++ ofVector keys[keys.size - 1 - i]!.iv)
        ByteArray.empty).extract (j * 64 + 48) (j * 64 + 64)
          = ofVector keys[keys.size - 1 - j]!.iv := by
    intro m
    induction m with
    | zero => exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ m ih =>
      obtain ⟨hsz, hch⟩ := ih
      rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
      refine ⟨by simp only [ByteArray.size_append, hsz, Cryptlib.Util.Bytes.size_ofVector]; omega,
        fun j hj => ?_⟩
      by_cases hjm : j < m
      · rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
            simp only [ByteArray.size_append, hsz, Cryptlib.Util.Bytes.size_ofVector]; omega),
          Cryptlib.Util.Bytes.extract_append_of_le _ _ (by rw [hsz]; omega),
          Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
            simp only [ByteArray.size_append, hsz, Cryptlib.Util.Bytes.size_ofVector]; omega),
          Cryptlib.Util.Bytes.extract_append_of_le _ _ (by rw [hsz]; omega)]
        exact hch j hjm
      · obtain rfl : j = m := by omega
        refine ⟨?_, ?_⟩
        · rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
            simp only [ByteArray.size_append, hsz, Cryptlib.Util.Bytes.size_ofVector]; omega)]
          exact extract_append_tail _ _ _ _ hsz (by rw [Cryptlib.Util.Bytes.size_ofVector])
        · exact extract_append_tail _ _ _ _ (by
            simp only [ByteArray.size_append, hsz, Cryptlib.Util.Bytes.size_ofVector])
            (by rw [Cryptlib.Util.Bytes.size_ofVector])
  obtain ⟨hsz, hch⟩ := key keys.size
  unfold surbKeys
  refine ⟨by simp only [ByteArray.size_append, hsz, Cryptlib.Util.Bytes.size_ofVector]; omega,
    fun j hj => ?_, ?_, ?_⟩
  · rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by rw [hsz]; omega),
      Cryptlib.Util.Bytes.extract_append_of_le _ _ (by rw [hsz]; omega)]
    exact hch j hj
  · rw [Cryptlib.Util.Bytes.extract_append_of_ge _ _ (by rw [hsz]), hsz, Nat.sub_self,
      Nat.add_sub_cancel_left]
  · rw [Cryptlib.Util.Bytes.extract_append_of_ge _ _ (by rw [hsz]; omega), hsz,
      Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]

/-- **The sender opens a reply.** Each relay of the backward path decrypted the payload once
under its hop key. `decryptSURBPayload` encrypts under those keys in reverse and then decrypts
under the SURB's payload key. -/
theorem decryptSURBPayload_surbKeys (keys : Array SPRPKey) (kp : Vector UInt8 64)
    (pl : ByteArray) (y : ℕ → ByteArray) (h16 : 16 ≤ geom.payloadTagLength + pl.size)
    (hy0 : y 0 = cipher.encrypt ((ofVector kp).extract 0 48).data ((ofVector kp).extract 48 64)
      ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pl))
    (hy : ∀ j < keys.size,
      y (j + 1) = cipher.decrypt keys[j]!.key.toArray (ofVector keys[j]!.iv) (y j)) :
    SURB.decryptSURBPayload cipher geom (surbKeys keys kp) (y keys.size) = .ok pl := by
  obtain ⟨hsz, hch, hk1, hk2⟩ := surbKeys_chunks keys kp
  have hz : (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray).size
      = geom.payloadTagLength := by simp [ByteArray.size]
  have hys : ∀ j ≤ keys.size, (y j).size = geom.payloadTagLength + pl.size := by
    intro j hj
    induction j with
    | zero => rw [hy0, cipher.encrypt_size, ByteArray.size_append, hz]
    | succ j ih => rw [hy j (by omega), cipher.decrypt_size]; exact ih (by omega)
  have hmod : (surbKeys keys kp).size % 64 = 0 := by rw [hsz]; exact Nat.mul_mod_left _ _
  have hdiv : (surbKeys keys kp).size / 64 = keys.size + 1 := by
    rw [hsz]; exact Nat.mul_div_cancel _ (by norm_num)
  have hfold : List.foldl (fun b a =>
        if (a == keys.size) = true then
          cipher.decrypt ((surbKeys keys kp).extract (a * 64) (a * 64 + 48)).data
            ((surbKeys keys kp).extract (a * 64 + 48) (a * 64 + 64)) b
        else
          cipher.encrypt ((surbKeys keys kp).extract (a * 64) (a * 64 + 48)).data
            ((surbKeys keys kp).extract (a * 64 + 48) (a * 64 + 64)) b)
      (y keys.size) (List.range' 0 (keys.size + 1))
      = (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pl := by
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add]
    have hin := foldl_range'_trace (fun b a =>
        if (a == keys.size) = true then
          cipher.decrypt ((surbKeys keys kp).extract (a * 64) (a * 64 + 48)).data
            ((surbKeys keys kp).extract (a * 64 + 48) (a * 64 + 64)) b
        else
          cipher.encrypt ((surbKeys keys kp).extract (a * 64) (a * 64 + 48)).data
            ((surbKeys keys kp).extract (a * 64 + 48) (a * 64 + 64)) b)
      (fun j => y (keys.size - j)) keys.size 0 (fun j hj => by
        simp only [Nat.zero_add]
        rw [if_neg (by simp; omega), (hch j hj).1, (hch j hj).2]
        show _ = cipher.encrypt keys[keys.size - 1 - j]!.key.toArray _ _
        rw [show keys.size - j = keys.size - 1 - j + 1 by omega, hy _ (by omega),
          encrypt_decrypt cipher _ _ _ (by rw [hys _ (by omega)]; exact h16)]
        congr 1
        omega)
    simp only [Nat.sub_zero, Nat.sub_self] at hin
    rw [hin, if_pos (by simp), hk1, hk2, hy0,
      cipher.roundTrip _ _ _ (by rw [ByteArray.size_append, hz]; exact h16)]
  have htag : ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pl).extract 0
      geom.payloadTagLength = ⟨Array.replicate geom.payloadTagLength 0⟩ := by
    have := Cryptlib.Util.Bytes.extract_append_left
      (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) pl
    rwa [hz] at this
  unfold SURB.decryptSURBPayload
  simp only [sprpKeyMaterialLength, sprpKeyLength, sprpIVLength, streamIVLength, Nat.reduceAdd,
    hmod, hdiv, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl]
  rw [if_neg (by simp), if_neg (by rw [hys _ le_rfl]; omega)]
  simp only [pure_bind, hfold, htag]
  have hall : ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray).data.all fun x => x == 0)
      = true := by
    exact Array.all_eq_true_iff_forall_mem.2 (by simp)
  rw [if_neg (by rw [hall]; simp),
    extract_append_tail _ _ _ _ hz (by rw [ByteArray.size_append, hz])]
  rfl

/-- A hop's payload key in `createKEMHeader`'s result is the one derived from its seed. -/
theorem createKEMHeader_sprpKeys (seeds : Array (Vector UInt8 32)) (filler : ByteArray)
    (hops : Array PathHop) (hdr : ByteArray) (keys : Array SPRPKey)
    (h : createKEMHeader kem macS kdfS streamS geom seeds filler hops = .ok (hdr, keys)) :
    keys.size = hops.size ∧ ∀ i < hops.size, keys[i]!
      = ⟨(kemHopKeys kem kdfS hops seeds i).payloadEncryption,
        (kemHopKeys kem kdfS hops seeds i).headerEncryptionIV⟩ := by
  obtain ⟨-, -, -, -, ke, hk, -, -, s, -, -, -, -, hkc, -, -, -, -, hsprp⟩ :=
    createKEMHeader_unfold kem macS kdfS streamS geom _ _ _ _ _ h
  subst hsprp
  refine ⟨by simp, fun i hi => ?_⟩
  obtain ⟨ct, ss, henc, -, hki⟩ := hkc i hi
  rw [getElem!_pos _ i (by simpa using hi)]
  simp only [Array.getElem_ofFn]
  rw [hki]
  unfold kemHopKeys
  rw [henc]

theorem newPacketFromSURB_eq (hdr : ByteArray) (id : Vector UInt8 32) (kp : Vector UInt8 64)
    (pl : ByteArray) (hh : hdr.size = geom.headerLength)
    (hs : geom.surbLength = geom.headerLength + 32 + 64) :
    SURB.newPacketFromSURB cipher geom (hdr ++ ofVector id ++ ofVector kp) pl
      = .ok (hdr ++ cipher.encrypt ((ofVector kp).extract 0 48).data ((ofVector kp).extract 48 64)
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pl), id) := by
  have hsize : (hdr ++ ofVector id ++ ofVector kp).size = geom.surbLength := by
    simp only [ByteArray.size_append, Cryptlib.Util.Bytes.size_ofVector, hh, hs]
  have h1 : (hdr ++ ofVector id ++ ofVector kp).extract 0 geom.headerLength = hdr := by
    rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
        simp only [ByteArray.size_append, hh]; omega),
      Cryptlib.Util.Bytes.extract_append_of_le _ _ (by omega), ← hh]
    exact ByteArray.extract_zero_size
  have h2 : (hdr ++ ofVector id ++ ofVector kp).extract geom.headerLength
      (geom.headerLength + 32) = ofVector id := by
    rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
        simp only [ByteArray.size_append, hh, Cryptlib.Util.Bytes.size_ofVector]; omega)]
    exact extract_append_tail _ _ _ _ hh (by rw [Cryptlib.Util.Bytes.size_ofVector])
  have h3 : (hdr ++ ofVector id ++ ofVector kp).extract (geom.headerLength + 32)
      (geom.headerLength + 32 + 48) = (ofVector kp).extract 0 48 := by
    rw [Cryptlib.Util.Bytes.extract_append_of_ge _ _ (by
        simp only [ByteArray.size_append, hh, Cryptlib.Util.Bytes.size_ofVector]; omega)]
    simp only [ByteArray.size_append, hh, Cryptlib.Util.Bytes.size_ofVector, Nat.sub_self,
      Nat.add_sub_cancel_left]
  have h4 : (hdr ++ ofVector id ++ ofVector kp).extract (geom.headerLength + 32 + 48)
      (hdr ++ ofVector id ++ ofVector kp).size = (ofVector kp).extract 48 64 := by
    rw [Cryptlib.Util.Bytes.extract_append_of_ge _ _ (by
        simp only [ByteArray.size_append, hh, Cryptlib.Util.Bytes.size_ofVector]; omega)]
    simp only [ByteArray.size_append, hh, Cryptlib.Util.Bytes.size_ofVector,
      Nat.add_sub_cancel_left]
  unfold SURB.newPacketFromSURB
  simp only [nodeIDLength, sprpKeyLength]
  rw [if_neg (by rw [hsize]; simp)]
  simp only [h1, h2, h3, h4, toVec32_eq_toVecN, toVecN_ofVector]
  rfl

theorem peeled_size (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (p : ByteArray)
    (j : ℕ) : (peeled kem cipher kdfS hops seeds p j).size = p.size := by
  induction j with
  | zero => rfl
  | succ j ih => rw [peeled, cipher.decrypt_size, ih]

set_option maxHeartbeats 1000000 in
/-- What a relay does with a layer whose payload was replaced: what it does with the layer,
except that the payload it passes on is the new one, decrypted under its hop key. -/
theorem procWith_layer_payload (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (R : Protocols.RSOR.Route geom.nrHops Name (Key kem)) (last : List RoutingCommand)
    (hnn : ∀ c ∈ last, c ≠ .null) (hnh : ∀ c ∈ last, ∀ id m, c ≠ .nextNodeHop id m)
    (d : Draw geom) (payload : ByteArray) (i : ℕ) (hi : i < R.hops.length) (sk : kem.PrivateKey)
    (hkey : R.hops[i].key.1 = kem.derivePublicKey sk)
    (hrel : ∀ j < R.hops.length, kem.Reliable (kem.stateFromSeed d.1.toArray[j]!))
    (pkt : ByteArray)
    (hpkt : layer kem cipher macS kdfS streamS geom (path kem R last) d payload i = .ok pkt)
    (P : ByteArray) (hP : P.size = geom.payloadTagLength + geom.forwardPayloadLength) :
    let dec := kemDecap kem (ofVector (kem.encodePrivateKey sk))
    let k := kemHopKeys kem kdfS (path kem R last)
      (d.1.toArray.extract 0 (path kem R last).size) i
    let D := cipher.decrypt k.payloadEncryption.toArray (ofVector k.headerEncryptionIV) P
    (∀ h : i + 1 < R.hops.length, ∃ tag mac fwd,
      procWith kem cipher macS kdfS streamS geom dec (pkt.extract 0 geom.headerLength ++ P)
        = some (none, tag, [.nextNodeHop R.hops[i + 1].name mac],
          some (fwd.extract 0 geom.headerLength ++ D)) ∧
      layer kem cipher macS kdfS streamS geom (path kem R last) d payload (i + 1) = .ok fwd) ∧
    (i + 1 = R.hops.length → hasSurbReply last = true → ∃ tag,
      procWith kem cipher macS kdfS streamS geom dec (pkt.extract 0 geom.headerLength ++ P)
        = some (some D, tag, last, none)) := by
  intro dec k D
  obtain ⟨⟨ss, hd, hkeys⟩, hmid, hlast⟩ := procWith_layer kem cipher macS kdfS streamS geom hvalid
    hmactag h16 R last hnn hnh d payload i hi sk hkey hrel pkt hpkt
  obtain ⟨hsz, -⟩ :=
    join_split_layer kem cipher macS kdfS streamS geom hvalid hmactag _ _ _ _ _ hpkt
  obtain ⟨-, -, -, hheader, -, -⟩ := id hvalid
  have hoff : payloadOffset kem geom = geom.headerLength := by rw [hheader]; rfl
  have hx : (pkt.extract 0 geom.headerLength).size = geom.headerLength := by
    rw [ByteArray.size_extract]; omega
  have hY : (pkt.extract 0 geom.headerLength ++ P).extract geom.headerLength
      (pkt.extract 0 geom.headerLength ++ P).size = P :=
    extract_append_tail _ _ _ _ hx (by rw [ByteArray.size_append, hx])
  have hH : (pkt.extract 0 geom.headerLength ++ P).extract 0 (payloadOffset kem geom)
      = pkt.extract 0 (payloadOffset kem geom) := by
    rw [hoff]
    have := Cryptlib.Util.Bytes.extract_append_left (pkt.extract 0 geom.headerLength) P
    rwa [hx] at this
  have hpp := fun p tag cmds f h => procWith_payload kem cipher macS kdfS streamS geom dec pkt
    (pkt.extract 0 geom.headerLength ++ P) ss (by rw [ByteArray.size_append, hx, hP, hsz]) hH
    (by rw [hoff]; omega) hd p tag cmds f h
  simp only [hoff, hY, ← hkeys] at hpp
  refine ⟨fun h => ?_, fun h hs => ?_⟩
  · obtain ⟨tag, mac, fwd, hp, hnext⟩ := hmid h
    exact ⟨tag, mac, fwd, (hpp _ _ _ _ hp).1 fwd rfl, hnext⟩
  · obtain ⟨tag, hp⟩ := hlast h
    exact ⟨tag, (hpp _ _ _ _ hp).2 rfl hs⟩

/-- The SURB of a request with a backward path: its keys are the hops' payload keys, and a reply
packet built from it has the header of the first layer on that path. -/
theorem surb_spec (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (q : Request kem geom) (r : Randomness geom) (payload x0 : ByteArray)
    (hb : 0 < q.back.hops.length)
    (hx0 : layer kem cipher macS kdfS streamS geom (path kem q.back [.surbReply r.2.2.2]) r.2.1
      payload 0 = .ok x0) :
    ∃ keys : Array SPRPKey, keys.size = q.back.hops.length ∧
      (∀ j < q.back.hops.length, keys[j]!
        = ⟨(kemHopKeys kem kdfS (path kem q.back [.surbReply r.2.2.2])
            (r.2.1.1.toArray.extract 0 (path kem q.back [.surbReply r.2.2.2]).size)
            j).payloadEncryption,
          (kemHopKeys kem kdfS (path kem q.back [.surbReply r.2.2.2])
            (r.2.1.1.toArray.extract 0 (path kem q.back [.surbReply r.2.2.2]).size)
            j).headerEncryptionIV⟩) ∧
      (surb kem macS kdfS streamS geom q r).2 = surbKeys keys r.2.2.1 ∧
      ∀ pl, SURB.newPacketFromSURB cipher geom (surb kem macS kdfS streamS geom q r).1 pl
        = .ok (x0.extract 0 geom.headerLength
            ++ cipher.encrypt ((ofVector r.2.2.1).extract 0 48).data
              ((ofVector r.2.2.1).extract 48 64)
              ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pl),
          q.back.hops[0].name) := by
  unfold layer at hx0
  dsimp only at hx0
  simp only [fillerAt, Array.extract_size] at hx0
  obtain ⟨-, hdr, keys, t, hcreate, -, -, hx⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hx0
  have hh := createKEMHeader_hdr_size kem macS kdfS streamS geom _ _ _ hdr keys hvalid hmactag
    hcreate
  obtain ⟨hks, hkk⟩ := createKEMHeader_sprpKeys kem macS kdfS streamS geom _ _ _ _ _ hcreate
  obtain ⟨-, -, -, -, -, hsl⟩ := id hvalid
  have hxh : x0.extract 0 geom.headerLength = hdr := by
    rw [hx, ← hh]
    exact Cryptlib.Util.Bytes.extract_append_left hdr _
  have hsurb : surb kem macS kdfS streamS geom q r
      = (hdr ++ ofVector q.back.hops[0].name ++ ofVector r.2.2.1, surbKeys keys r.2.2.1) := by
    unfold surb
    dsimp only
    rw [newKEMSURB_eq kem macS kdfS streamS geom _ _ _ _ _ _ hcreate, path_getElem! kem _ _ 0 hb]
  refine ⟨keys, by rw [hks, path_size], fun j hj => hkk j (by rw [path_size]; exact hj),
    by rw [hsurb], fun pl => ?_⟩
  rw [hsurb, hxh]
  exact newPacketFromSURB_eq cipher geom hdr _ _ pl hh (by rw [hsl]; rfl)

theorem size_tagged (pl : ByteArray) :
    ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pl).size
      = geom.payloadTagLength + pl.size := by
  rw [ByteArray.size_append]
  show (Array.replicate _ (0 : UInt8)).size + _ = _
  rw [Array.size_replicate]

/-- The first reply packet: the header of the first layer on the backward path, and the padded
message under the SURB's payload key. -/
theorem replyPacket_eq (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (q : Request kem geom) (r : Randomness geom) (m : Msg geom)
    (hr : Reliable kem cipher macS kdfS streamS geom q r) (hb : 0 < q.back.hops.length) :
    (pad geom m).size = geom.forwardPayloadLength ∧
    ∃ (x0 : ByteArray) (keys : Array SPRPKey),
      layer kem cipher macS kdfS streamS geom (path kem q.back [.surbReply r.2.2.2]) r.2.1
        ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0 = .ok x0 ∧
      keys.size = q.back.hops.length ∧
      (∀ j < q.back.hops.length, keys[j]!
        = ⟨(kemHopKeys kem kdfS (path kem q.back [.surbReply r.2.2.2])
            (r.2.1.1.toArray.extract 0 (path kem q.back [.surbReply r.2.2.2]).size)
            j).payloadEncryption,
          (kemHopKeys kem kdfS (path kem q.back [.surbReply r.2.2.2])
            (r.2.1.1.toArray.extract 0 (path kem q.back [.surbReply r.2.2.2]).size)
            j).headerEncryptionIV⟩) ∧
      (surb kem macS kdfS streamS geom q r).2 = surbKeys keys r.2.2.1 ∧
      SURB.newPacketFromSURB cipher geom (surb kem macS kdfS streamS geom q r).1 (pad geom m)
        = .ok (x0.extract 0 geom.headerLength
            ++ cipher.encrypt ((ofVector r.2.2.1).extract 0 48).data
              ((ofVector r.2.2.1).extract 48 64)
              ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pad geom m),
          q.back.hops[0].name) ∧
      (replyPacket kem cipher macS kdfS streamS geom q r m).1.extract geom.headerLength
          (replyPacket kem cipher macS kdfS streamS geom q r m).1.size
        = cipher.encrypt ((ofVector r.2.2.1).extract 0 48).data ((ofVector r.2.2.1).extract 48 64)
            ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pad geom m) := by
  have hpad : (pad geom m).size = geom.forwardPayloadLength := by
    obtain ⟨pk, hpk⟩ := hr.1.2 (List.length_pos_iff.2 q.fwd_ne)
    have h := (newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hpk).1
    rw [body, ByteArray.size_append, Cryptlib.Util.Bytes.size_ofVector] at h
    rw [pad, ByteArray.size_append, Cryptlib.Util.Bytes.size_ofVector]
    show _ + (Array.replicate _ (0 : UInt8)).size = _
    rw [Array.size_replicate]
    omega
  obtain ⟨x0, hx0⟩ := hr.2.2 hb
  obtain ⟨keys, hks, hkk, hsk, hnp⟩ :=
    surb_spec kem cipher macS kdfS streamS geom hvalid hmactag q r _ x0 hb hx0
  obtain ⟨hsz, -⟩ :=
    join_split_layer kem cipher macS kdfS streamS geom hvalid hmactag _ _ _ _ _ hx0
  refine ⟨hpad, x0, keys, hx0, hks, hkk, hsk, hnp (pad geom m), ?_⟩
  have hx : (x0.extract 0 geom.headerLength).size = geom.headerLength := by
    rw [ByteArray.size_extract]; omega
  unfold replyPacket
  rw [hnp (pad geom m)]
  exact extract_append_tail _ _ _ _ hx (by rw [ByteArray.size_append, hx])

/-- The exit relay's reply is the first layer of the reply onion. -/
theorem reply_form (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (q : Request kem geom) (r : Randomness geom) (m : Msg geom) (i : Fin q.fwd.hops.length)
    (j : Fin q.back.hops.length) (sk : kem.PrivateKey)
    (hr : Reliable kem cipher macS kdfS streamS geom q r) (hi : i + 1 = q.fwd.hops.length)
    (hj : j.val = 0) (hk : (q.fwd.hops[i].key, sk) ∈ support (keygen kem)) :
    reply kem cipher macS kdfS streamS geom sk m (form kem cipher macS kdfS streamS geom q r i)
      = some (q.back.hops[j].name, formBack kem cipher macS kdfS streamS geom q r m j) := by
  have hjlt : 0 < q.back.hops.length := j.pos
  obtain rfl : j = ⟨0, hjlt⟩ := Fin.ext hj
  obtain ⟨pkt, hpkt⟩ := Builds.layer kem cipher macS kdfS streamS geom hvalid hmactag h16 _ _
    (by simp) (by simp) _ _ hr.1 i i.isLt
  obtain ⟨-, -, hlast⟩ := procWith_layer kem cipher macS kdfS streamS geom hvalid hmactag h16
    q.fwd [.recipient q.receiver] (by simp) (by simp) r.1 _ i i.isLt sk
    (key_of_keygen kem _ _ hk) hr.1.1 pkt hpkt
  obtain ⟨tag, hp⟩ := hlast hi
  rw [hasSurbReply_eq_false (by simp), if_neg Bool.false_ne_true] at hp
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
  unfold reply form formBack
  dsimp only
  rw [hpkt]
  dsimp only
  rw [(join_split_layer kem cipher macS kdfS streamS geom hvalid hmactag _ _ _ _ _ hpkt).2, hp]
  dsimp only
  rw [if_pos hfl, hsb, hnp, hx0]
  dsimp only
  rw [hP0]
  rfl

/-- A relay on the backward path gets the next layer. -/
theorem proc_formBack (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (q : Request kem geom) (r : Randomness geom) (m : Msg geom) (i : Fin q.back.hops.length)
    (h : i.val + 1 < q.back.hops.length) (sk : kem.PrivateKey)
    (hr : Reliable kem cipher macS kdfS streamS geom q r)
    (hk : (q.back.hops[i].key, sk) ∈ support (keygen kem)) :
    proc kem cipher macS kdfS streamS geom sk (formBack kem cipher macS kdfS streamS geom q r m i)
      = some (.forward q.back.hops[i.val + 1].name
          (formBack kem cipher macS kdfS streamS geom q r m ⟨i.val + 1, h⟩)) := by
  obtain ⟨pkt, hpkt⟩ := Builds.layer kem cipher macS kdfS streamS geom hvalid hmactag h16 _ _
    (by simp) (by simp) _ _ hr.2 i i.isLt
  obtain ⟨hpad, x0, keys, hx0, -, -, -, -, hP0⟩ :=
    replyPacket_eq kem cipher macS kdfS streamS geom hvalid hmactag q r m hr (by omega)
  have hE : (cipher.encrypt ((ofVector r.2.2.1).extract 0 48).data
      ((ofVector r.2.2.1).extract 48 64)
      ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pad geom m)).size
      = geom.payloadTagLength + geom.forwardPayloadLength := by
    rw [cipher.encrypt_size, size_tagged, hpad]
  obtain ⟨hsz, -⟩ :=
    join_split_layer kem cipher macS kdfS streamS geom hvalid hmactag _ _ _ _ _ hpkt
  obtain ⟨hmid, -⟩ := procWith_layer_payload kem cipher macS kdfS streamS geom hvalid hmactag h16
    q.back [.surbReply r.2.2.2] (by simp) (by simp) r.2.1 _ i i.isLt sk
    (key_of_keygen kem _ _ hk) hr.2.1 pkt hpkt
    (peeled kem cipher kdfS (path kem q.back [.surbReply r.2.2.2])
      (r.2.1.1.toArray.extract 0 (path kem q.back [.surbReply r.2.2.2]).size) _ i)
    (by rw [peeled_size, hE])
  obtain ⟨tag, mac, fwd, hp, hnext⟩ := hmid h
  unfold proc formBack
  dsimp only
  rw [hpkt, hnext]
  dsimp only
  rw [hP0, join_split geom _ (by rw [ByteArray.size_append, ByteArray.size_extract]; omega)
    (by rw [ByteArray.size_append, ByteArray.size_extract, peeled_size, hE]; omega), hp]
  simp [peeled]

/-- The last relay of the backward path gets a payload that the sender opens to the reply. -/
theorem recover_formBack (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (q : Request kem geom) (r : Randomness geom) (m : Msg geom) (i : Fin q.back.hops.length)
    (sk : kem.PrivateKey) (hr : Reliable kem cipher macS kdfS streamS geom q r)
    (hi : i.val + 1 = q.back.hops.length)
    (hk : (q.back.hops[i].key, sk) ∈ support (keygen kem)) :
    ∃ p, proc kem cipher macS kdfS streamS geom sk
        (formBack kem cipher macS kdfS streamS geom q r m i) = some (.reply p) ∧
      recover kem cipher macS kdfS streamS geom q r p = some m := by
  obtain ⟨pkt, hpkt⟩ := Builds.layer kem cipher macS kdfS streamS geom hvalid hmactag h16 _ _
    (by simp) (by simp) _ _ hr.2 i i.isLt
  obtain ⟨hpad, x0, keys, hx0, hks, hkk, hsk, -, hP0⟩ :=
    replyPacket_eq kem cipher macS kdfS streamS geom hvalid hmactag q r m hr (by omega)
  have hE : (cipher.encrypt ((ofVector r.2.2.1).extract 0 48).data
      ((ofVector r.2.2.1).extract 48 64)
      ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pad geom m)).size
      = geom.payloadTagLength + geom.forwardPayloadLength := by
    rw [cipher.encrypt_size, size_tagged, hpad]
  obtain ⟨hsz, -⟩ :=
    join_split_layer kem cipher macS kdfS streamS geom hvalid hmactag _ _ _ _ _ hpkt
  obtain ⟨-, hlast⟩ := procWith_layer_payload kem cipher macS kdfS streamS geom hvalid hmactag h16
    q.back [.surbReply r.2.2.2] (by simp) (by simp) r.2.1 _ i i.isLt sk
    (key_of_keygen kem _ _ hk) hr.2.1 pkt hpkt
    (peeled kem cipher kdfS (path kem q.back [.surbReply r.2.2.2])
      (r.2.1.1.toArray.extract 0 (path kem q.back [.surbReply r.2.2.2]).size) _ i)
    (by rw [peeled_size, hE])
  obtain ⟨tag, hp⟩ := hlast hi (by simp [hasSurbReply])
  refine ⟨toVecN _ (peeled kem cipher kdfS (path kem q.back [.surbReply r.2.2.2])
    (r.2.1.1.toArray.extract 0 (path kem q.back [.surbReply r.2.2.2]).size)
    (cipher.encrypt ((ofVector r.2.2.1).extract 0 48).data ((ofVector r.2.2.1).extract 48 64)
      ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pad geom m)) (i + 1)), ?_, ?_⟩
  · unfold proc formBack
    dsimp only
    rw [hpkt]
    dsimp only
    rw [hP0, join_split geom _ (by rw [ByteArray.size_append, ByteArray.size_extract]; omega)
      (by rw [ByteArray.size_append, ByteArray.size_extract, peeled_size, hE]; omega), hp]
    simp [peeled]
  · have hd := decryptSURBPayload_surbKeys cipher geom keys r.2.2.1 (pad geom m)
      (peeled kem cipher kdfS (path kem q.back [.surbReply r.2.2.2])
        (r.2.1.1.toArray.extract 0 (path kem q.back [.surbReply r.2.2.2]).size)
        (cipher.encrypt ((ofVector r.2.2.1).extract 0 48).data ((ofVector r.2.2.1).extract 48 64)
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ pad geom m)))
      (by rw [hpad]; exact h16) rfl
      (fun j hj => by rw [peeled, hkk j (by omega)])
    rw [hks, ← hi] at hd
    unfold recover
    rw [hsk, ofVector_toVecN _ (by rw [peeled_size, hE]), hd]
    dsimp only
    have := Cryptlib.Util.Bytes.extract_append_left (ofVector m)
      ⟨Array.replicate (geom.forwardPayloadLength - geom.userForwardPayloadLength) 0⟩
    rw [Cryptlib.Util.Bytes.size_ofVector] at this
    rw [pad, this, toVecN_ofVector]

/-- KEM Sphinx is a repliable service onion routing scheme. A relay does not use its own name. -/
def scheme (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) : Protocols.RSOR.Scheme where
  Name := Name
  Key := Key kem
  Secret := kem.PrivateKey
  Randomness := Randomness geom
  Msg := Msg geom
  Receiver := Name
  Header := Vector UInt8 geom.headerLength
  Payload := Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
  maxHops := geom.nrHops
  keygen _ := keygen kem
  form := form kem cipher macS kdfS streamS geom
  formBack := formBack kem cipher macS kdfS streamS geom
  proc sk _ := proc kem cipher macS kdfS streamS geom sk
  reply sk _ := reply kem cipher macS kdfS streamS geom sk
  recover := recover kem cipher macS kdfS streamS geom
  reliable := Reliable kem cipher macS kdfS streamS geom
  proc_form q r i sk hr hk :=
    proc_form kem cipher macS kdfS streamS geom hvalid hmactag h16 q r i sk hr.1 hk
  reply_form q r m i j sk hr hi hj hk :=
    reply_form kem cipher macS kdfS streamS geom hvalid hmactag h16 q r m i j sk hr hi hj hk
  proc_formBack q r m i h sk hr hk :=
    proc_formBack kem cipher macS kdfS streamS geom hvalid hmactag h16 q r m i h sk hr hk
  recover_formBack q r m i sk hr hi hk :=
    recover_formBack kem cipher macS kdfS streamS geom hvalid hmactag h16 q r m i sk hr hi hk

end Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR
