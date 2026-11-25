/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxKeyed

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
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Key keygen)
open Cryptlib.Util.Bytes (ofVector)

/-! # A packet with one hop's ciphertext and keys given

`packetK` is the packet `newKEMPacket` builds, except that hop `j`'s KEM ciphertext and four keys
are arguments. With the ciphertext and keys the hop's seed gives, it is `newKEMPacket`'s packet
(`packetK_real`). The games that replace an honest relay's keys show the adversary `packetK`. -/

section PacketK

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- A hop's KEM ciphertext, as `createKEMHeader` makes it from the hop's seed. -/
def kemHopCt (path : Array PathHop) (seeds : Array (Vector UInt8 32)) (i : Nat) : ByteArray :=
  match kemEncap kem (path[i]!).publicKey (seeds[i]!) with
  | .ok (ct, _) => ct
  | .error _ => .empty

/-- Hop keys from the four KEM Sphinx uses. -/
def hopKeysOf (t : KeyTuple) : HopKeys := ⟨t.2.2.1, t.2.2.2, t.2.1, t.1, .empty⟩

theorem keyTuple_hopKeysOf (t : KeyTuple) : keyTuple (hopKeysOf t) = t := rfl

/-- `newKEMPacket`'s packet, with hop `j`'s ciphertext `c` and keys `t` given. -/
def packetK (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (path : Array PathHop)
    (payload : ByteArray) (j : Nat) (c : ByteArray) (t : KeyTuple) : Except String ByteArray :=
  newKEMPacketFrom kem cipher macS streamS geom
    (Array.ofFn fun i : Fin path.size => if i.val = j then c else kemHopCt kem path seeds i)
    (Array.ofFn fun i : Fin path.size =>
      if i.val = j then hopKeysOf t else kemHopKeys kem kdfS path seeds i)
    filler path payload

/-- With the ciphertext and the keys hop `j`'s seed gives, `packetK` is `newKEMPacket`'s
packet. -/
theorem packetK_real (seeds : Array (Vector UInt8 32)) (filler : ByteArray)
    (path : Array PathHop) (payload pkt : ByteArray) (j : Nat) (c ss : ByteArray)
    (hj : kemEncap kem (path[j]!).publicKey (seeds[j]!) = .ok (c, ss))
    (h : newKEMPacket kem cipher macS kdfS streamS geom seeds filler path payload = .ok pkt) :
    packetK kem cipher macS kdfS streamS geom seeds filler path payload j c
      (keyTuple (deriveHopKeys kdfS ss)) = .ok pkt := by
  obtain ⟨-, hdr, sprpKeys, t, hcreate, -, -, -⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom seeds filler path payload pkt h
  obtain ⟨hpos, hgen, hseeds, hfsize, ke, keys, -, -, s, -, -, -, -, hkc, -⟩ :=
    createKEMHeader_unfold kem macS kdfS streamS geom seeds filler path hdr sprpKeys hcreate
  have key := newKEMPacket_eq_newKEMPacketFrom kem cipher macS kdfS streamS geom seeds filler
    path payload
    (Array.ofFn fun i : Fin path.size => kemHopCt kem path seeds i)
    (Array.ofFn fun i : Fin path.size => kemHopKeys kem kdfS path seeds i)
    hpos hgen hseeds hfsize (by simp) (by simp) (fun i hi => by
      obtain ⟨ct, ss', henc, -, -⟩ := hkc i hi
      refine ⟨ct, ss', henc, ?_, ?_⟩
      · rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
        unfold kemHopCt
        rw [henc]
      · rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
        unfold kemHopKeys
        rw [henc])
  rw [h] at key
  have hke : (Array.ofFn fun i : Fin path.size =>
      if i.val = j then c else kemHopCt kem path seeds i)
      = Array.ofFn fun i : Fin path.size => kemHopCt kem path seeds i := by
    congr 1
    funext i
    split_ifs with hi
    · subst hi
      unfold kemHopCt
      rw [hj]
    · rfl
  have hk : ∀ i : Nat,
      keyTuple ((Array.ofFn fun i : Fin path.size => if i.val = j
        then hopKeysOf (keyTuple (deriveHopKeys kdfS ss))
        else kemHopKeys kem kdfS path seeds i)[i]!)
      = keyTuple ((Array.ofFn fun i : Fin path.size => kemHopKeys kem kdfS path seeds i)[i]!) := by
    intro i
    by_cases hi : i < path.size
    · rw [getElem!_pos _ i (by simpa using hi), getElem!_pos _ i (by simpa using hi)]
      simp only [Array.getElem_ofFn]
      split_ifs with hij
      · subst hij
        rw [keyTuple_hopKeysOf]
        unfold kemHopKeys
        rw [hj]
      · rfl
    · simp [hi]
  unfold packetK
  rw [key, hke]
  exact newKEMPacketFrom_congr kem cipher macS streamS geom _ _ _ filler path payload
    (fun i => congrArg (·.2.2.1) (hk i)) (fun i => congrArg (·.2.2.2) (hk i))
    (fun i => congrArg (·.2.1) (hk i)) (fun i => congrArg (·.1) (hk i))

/-- `packetK` does not use hop `j`'s seed. -/
theorem packetK_congr (seeds seeds' : Array (Vector UInt8 32)) (filler : ByteArray)
    (path : Array PathHop) (payload : ByteArray) (j : Nat) (c : ByteArray) (t : KeyTuple)
    (h : ∀ i, i ≠ j → seeds[i]! = seeds'[i]!) :
    packetK kem cipher macS kdfS streamS geom seeds filler path payload j c t
      = packetK kem cipher macS kdfS streamS geom seeds' filler path payload j c t := by
  unfold packetK
  congr 2 <;>
    · funext i
      split_ifs with hi
      · rfl
      · simp only [kemHopCt, kemHopKeys, h i hi]

end PacketK

/-! # Tagging-forward layer unlinkability: the worlds as keyed games -/

section Forward

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry) (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

/-- The honest relays of a game, from their names and keys. -/
def honOf (names : Role → RSOR.Name) (pk kb ks : Key kem) : Protocols.RSOR.Honest 𝒮 := fun
  | .relay => ⟨names .relay, pk⟩
  | .back => ⟨names .back, kb⟩
  | .sender => ⟨names .sender, ks⟩

/-- What the adversary's first phase leaves the challenger: the key pairs of the two honest
relays that are not behind the oracle, and the challenge. -/
structure ForwardCh (names : Role → RSOR.Name) (pk : Key kem) where
  kb : Key kem × kem.PrivateKey
  ks : Key kem × kem.PrivateKey
  c : Protocols.RSOR.ForwardChallenge (S := 𝒮)
    (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk kb.1 ks.1)

/-- The first layer of the challenge's onion, with the honest relay's KEM ciphertext and keys
given. -/
def forwardOnionK (names : Role → RSOR.Name) {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (t : KeyTuple) : RSOR.Onion geom :=
  let hops := RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]
  match packetK kem cipher macS kdfS streamS geom (r.1.1.toArray.extract 0 hops.size)
      ((ofVector r.1.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
      hops (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos
      (ofVector (kem.encodeCiphertext c)) t with
  | .ok pkt => RSOR.split geom pkt
  | .error _ => default

theorem extract_setIfInBounds_getElem? {α : Type} (a : Array α) (j m i : ℕ) (s : α)
    (h : i ≠ j) : ((a.setIfInBounds j s).extract 0 m)[i]? = (a.extract 0 m)[i]? := by
  simp [Array.getElem?_extract, Ne.symm h]

/-- The challenger's randomness with the seed for forward position `j` replaced. -/
def setSeed (r : RSOR.Randomness geom) (j : Nat) (s : Vector UInt8 32) : RSOR.Randomness geom :=
  ((r.1.1.setIfInBounds j s, r.1.2), r.2)

/-- With the ciphertext and keys that the seed `s` gives at the honest relay's position, the
keyed first layer is the first layer of the challenge's onion, built from the randomness with
`s` at that position. -/
theorem forwardOnionK_real (names : Role → RSOR.Name) {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (r : RSOR.Randomness geom) (s : Vector UInt8 32) (c : kem.Ciphertext) (ss pkt : ByteArray)
    (henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s
      = .ok (ofVector (kem.encodeCiphertext c), ss))
    (hpkt : RSOR.layer kem cipher macS kdfS streamS geom
      (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
      (setSeed geom r ch.c.pos s).1
      (RSOR.body kem macS kdfS streamS geom ch.c.req (setSeed geom r ch.c.pos s)) 0 = .ok pkt) :
    forwardOnionK kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c
        (keyTuple (deriveHopKeys kdfS ss))
      = RSOR.form kem cipher macS kdfS streamS geom ch.c.req (setSeed geom r ch.c.pos s)
          ch.c.req.first := by
  have hn := RSOR.path_size kem ch.c.req.fwd [.recipient ch.c.req.receiver]
  have hpos : (ch.c.pos : ℕ) < ch.c.req.fwd.hops.length := ch.c.pos.isLt
  have hle : ch.c.req.fwd.hops.length ≤ geom.nrHops := ch.c.req.fwd.length_le
  have hkey : (ch.c.req.fwd.hops[(ch.c.pos : ℕ)]'hpos).key = pk := congrArg (·.key) ch.c.relay
  have hposn : (ch.c.pos : ℕ)
      < (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size := by
    rw [hn]; exact hpos
  have hlen : (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size ≤ geom.nrHops := by
    rw [hn]; exact hle
  have hpub :
      ((RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])[(ch.c.pos : ℕ)]!).publicKey
        = ofVector (kem.encodePublicKey pk.1) := by
    rw [RSOR.path_getElem! kem _ _ _ hpos]
    exact congrArg (fun k : Key kem => ofVector (kem.encodePublicKey k.1)) hkey
  have hform : RSOR.form kem cipher macS kdfS streamS geom ch.c.req (setSeed geom r ch.c.pos s)
      ch.c.req.first = RSOR.split geom pkt := by
    unfold RSOR.form
    rw [show RSOR.layer kem cipher macS kdfS streamS geom _ _ _ (ch.c.req.first : ℕ) = .ok pkt
      from hpkt]
  rw [hform]
  unfold RSOR.layer at hpkt
  dsimp only at hpkt
  simp only [RSOR.fillerAt, Array.extract_size] at hpkt
  have hs : ((setSeed geom r ch.c.pos s).1.1.toArray.extract 0
      (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)[(ch.c.pos : ℕ)]! = s := by
    rw [getElem!_extract_zero _ _ _ hposn (by rw [Vector.size_toArray]; exact hlen)]
    simp [setSeed, lt_of_lt_of_le hposn hlen]
  have h1 := packetK_real kem cipher macS kdfS streamS geom _ _ _ _ pkt ch.c.pos
    (ofVector (kem.encodeCiphertext c)) ss
    (by rw [hs, hpub]; exact henc) hpkt
  have h2 := packetK_congr kem cipher macS kdfS streamS geom
    (r.1.1.toArray.extract 0 (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
    ((setSeed geom r ch.c.pos s).1.1.toArray.extract 0
      (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
    ((ofVector r.1.2).extract 0
      ((geom.nrHops - (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
        * geom.perHopRoutingInfoLength))
    (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
    (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos
    (ofVector (kem.encodeCiphertext c)) (keyTuple (deriveHopKeys kdfS ss))
    (fun i hi => by
      simp only [setSeed, Vector.setIfInBounds, Array.getElem!_eq_getD,
        Array.getD_eq_getD_getElem?]
      rw [extract_setIfInBounds_getElem? _ _ _ _ _ hi])
  unfold forwardOnionK
  dsimp only
  rw [h2]
  have h1' : packetK kem cipher macS kdfS streamS geom
      ((setSeed geom r ch.c.pos s).1.1.toArray.extract 0
        (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
      ((ofVector r.1.2).extract 0
        ((geom.nrHops - (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
          * geom.perHopRoutingInfoLength))
      (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
      (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos
      (ofVector (kem.encodeCiphertext c)) (keyTuple (deriveHopKeys kdfS ss)) = .ok pkt := h1
  rw [h1']

end Forward

end Cryptlib.Protocols.Sphinx.KEMSphinx
