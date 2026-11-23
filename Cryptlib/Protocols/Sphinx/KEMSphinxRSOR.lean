/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.RSOR
import Cryptlib.Protocols.Sphinx.KEMSphinxTailOracle

/-! # KEM Sphinx as a repliable service onion routing scheme

The algorithms of `Protocols.RSOR.Scheme` for KEM Sphinx, and its correctness on the forward path
(`proc_form`). A relay is named by its node ID. The exit relay's commands name the receiver, and
the forward payload carries the SURB in front of the message, as Katzenpost lays it out. -/

namespace Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR

open OracleComp OracleSpec
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
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

abbrev Request := Protocols.RSOR.Request geom.nrHops Name kem.PublicKey (Msg geom) Name

variable {geom} in
/-- A route as `newKEMPacket` takes it. Only its last hop has commands. -/
def path (R : Protocols.RSOR.Route geom.nrHops Name kem.PublicKey) (last : List RoutingCommand) :
    Array PathHop :=
  (R.hops.mapIdx fun i h =>
    ⟨h.name, ofVector (kem.encodePublicKey h.key), if i + 1 = R.hops.length then last else []⟩).toArray

/-- The key pair of a relay. The public key is the one derived from the private key. -/
def keygen : ProbComp (kem.PublicKey × kem.PrivateKey) := do
  let s ← $ᵗ Vector UInt8 32
  return (kem.derivePublicKey (keygenOf kem s).2, (keygenOf kem s).2)

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

/-- The draws from which every layer of the forward path can be built and no KEM round trip
fails. -/
def Reliable (q : Request kem geom) (r : Randomness geom) : Prop :=
  ∀ i < q.fwd.hops.length, kem.Reliable (kem.stateFromSeed r.1.1.toArray[i]!) ∧
    ∃ pkt, layer kem cipher macS kdfS streamS geom (path kem q.fwd [.recipient q.receiver]) r.1
      (body kem macS kdfS streamS geom q r) i = .ok pkt

variable {geom} in
theorem path_size (R : Protocols.RSOR.Route geom.nrHops Name kem.PublicKey)
    (last : List RoutingCommand) : (path kem R last).size = R.hops.length := by
  simp [path]

variable {geom} in
theorem path_getElem! (R : Protocols.RSOR.Route geom.nrHops Name kem.PublicKey)
    (last : List RoutingCommand) (j : ℕ) (h : j < R.hops.length) :
    (path kem R last)[j]! = ⟨R.hops[j].name, ofVector (kem.encodePublicKey R.hops[j].key),
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

set_option maxHeartbeats 1000000 in
/-- A relay on the forward path gets the next layer, and the exit relay the message. -/
theorem proc_form (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (q : Request kem geom) (r : Randomness geom) (i : Fin q.fwd.hops.length)
    (sk : kem.PrivateKey) (hr : Reliable kem cipher macS kdfS streamS geom q r)
    (hk : (q.fwd.hops[i].key, sk) ∈ support (keygen kem)) :
    proc kem cipher macS kdfS streamS geom sk (form kem cipher macS kdfS streamS geom q r i)
      = some (if h : i + 1 < q.fwd.hops.length
        then .forward q.fwd.hops[i.val + 1].name
          (form kem cipher macS kdfS streamS geom q r ⟨i + 1, h⟩)
        else .deliver q.msg q.receiver) := by
  obtain ⟨-, pkt, hpkt⟩ := hr i i.isLt
  have hkey : q.fwd.hops[i].key = kem.derivePublicKey sk := by
    simp only [keygen, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      Prod.mk.injEq] at hk
    obtain ⟨s, -, h1, h2⟩ := hk
    rw [h1, h2]
  have hn := path_size kem q.fwd [.recipient q.receiver]
  have hform : form kem cipher macS kdfS streamS geom q r i = split geom pkt := by
    unfold form; rw [hpkt]
  unfold layer at hpkt
  dsimp only at hpkt
  have hpay := (newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hpkt).1
  have hsz := newKEMPacket_size kem cipher macS kdfS streamS geom _ _ _ _ _ hvalid hmactag hpkt hpay
  obtain ⟨-, -, -, hheader, hpacket, -⟩ := id hvalid
  have hjs := join_split geom pkt (by omega) (by omega)
  have h0 : ((path kem q.fwd [.recipient q.receiver]).extract i
      (path kem q.fwd [.recipient q.receiver]).size)[0]!
      = ⟨q.fwd.hops[i].name, ofVector (kem.encodePublicKey q.fwd.hops[i].key),
        if i + 1 = q.fwd.hops.length then [.recipient q.receiver] else []⟩ := by
    rw [getElem!_extract_from _ _ _ (by omega), Nat.add_zero, path_getElem! kem _ _ _ i.isLt]
    rfl
  obtain ⟨hmid, hlast⟩ := newKEMPacket_unwrapKEM kem cipher macS kdfS streamS geom hvalid hmactag
    h16 _ _ _ _ pkt (ofVector (kem.encodePrivateKey sk))
    (by
      rw [h0, hkey]
      unfold kemSelfPublicKeyBytes
      rw [toVecN_ofVector, kem.decode_encode_priv])
    (fun j hj => by
      have hj' : i + j < q.fwd.hops.length := by simp at hj; omega
      have hle := q.fwd.length_le
      rw [getElem!_extract_from _ _ _ (by simp; omega),
        getElem!_extract_zero _ _ _ (by omega) (by simpa [hn] using q.fwd.length_le)]
      exact (hr _ hj').1)
    (by rw [h0]; intro c hc; split at hc <;> simp at hc; subst hc; simp)
    (by rw [h0]; intro c hc; split at hc <;> simp at hc; subst hc; simp) hpkt
  rw [hform]
  unfold proc procWith
  rw [hjs]
  by_cases h : i + 1 < q.fwd.hops.length
  · obtain ⟨tag, mac, fwd, hun, hnext⟩ := hmid (by simp; omega)
    rw [extract_extract_one, extract_extract_one] at hnext
    have h1 : ((path kem q.fwd [.recipient q.receiver]).extract i
        (path kem q.fwd [.recipient q.receiver]).size)[1]!.id = q.fwd.hops[i.val + 1].name := by
      rw [getElem!_extract_from _ _ _ (by omega), path_getElem! kem _ _ _ h]
    have hform' : form kem cipher macS kdfS streamS geom q r ⟨i + 1, h⟩
        = split geom (ofVector fwd) := by
      unfold form layer
      simp only [fillerAt]
      rw [hnext]
    rw [show unwrapKEMWith kem cipher macS kdfS streamS geom _ pkt = _ from hun, dif_pos h, h0,
      h1, hform']
    simp [show ¬ (i.val + 1 = q.fwd.hops.length) by omega]
  · obtain ⟨tag, hun⟩ := hlast (by simp; omega)
      (by rw [h0]; intro c hc; split at hc <;> simp at hc; subst hc; simp)
    have hmsg : msgOf geom (body kem macS kdfS streamS geom q r) = q.msg := by
      unfold msgOf body
      have := Cryptlib.Util.Bytes.extract_append_right
        (⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ ++ (surb kem macS kdfS streamS geom q r).1)
        (ofVector q.msg)
      rw [Cryptlib.Util.Bytes.size_ofVector] at this
      rw [ByteArray.size_append, Cryptlib.Util.Bytes.size_ofVector, Nat.add_sub_cancel, this,
        toVecN_ofVector]
    rw [show unwrapKEMWith kem cipher macS kdfS streamS geom _ pkt = _ from hun, dif_neg h, h0]
    simp [show i.val + 1 = q.fwd.hops.length by omega, hmsg]

end Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR
