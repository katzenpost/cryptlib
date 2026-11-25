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

/-- The bytes `kemEncap` returns for an encoded public key are the encodings of what `encapOf`
returns. -/
theorem kemEncap_encapOf (pk : kem.PublicKey) (s : Vector UInt8 32) (ct ss : ByteArray)
    (h : kemEncap kem (ofVector (kem.encodePublicKey pk)) s = .ok (ct, ss)) :
    ct = ofVector (kem.encodeCiphertext (encapOf kem pk s).1) ∧
      ss = ofVector (kem.encodePlaintext (encapOf kem pk s).2) := by
  unfold kemEncap at h
  unfold encapOf
  rw [Cryptlib.Protocols.Sphinx.Common.toVecN_ofVector, kem.decode_encode_pub] at h
  dsimp only at h
  cases hE : kem.encap pk (kem.stateFromSeed s) with
  | ok r a =>
    rw [hE] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩
  | error a b =>
    rw [hE] at h
    cases h

/-- From a reliable seed, a relay's private key decapsulates what was encapsulated to its public
key. -/
theorem decapOf_encapOf (sk : kem.PrivateKey) (s : Vector UInt8 32)
    (hrel : kem.Reliable (kem.stateFromSeed s)) (ct ss : ByteArray)
    (h : kemEncap kem (ofVector (kem.encodePublicKey (kem.derivePublicKey sk))) s = .ok (ct, ss)) :
    decapOf kem sk (encapOf kem (kem.derivePublicKey sk) s).1
      = some (encapOf kem (kem.derivePublicKey sk) s).2 := by
  unfold kemEncap at h
  rw [Cryptlib.Protocols.Sphinx.Common.toVecN_ofVector, kem.decode_encode_pub] at h
  dsimp only at h
  unfold encapOf decapOf
  cases hE : kem.encap (kem.derivePublicKey sk) (kem.stateFromSeed s) with
  | ok r a =>
    obtain ⟨t', hd⟩ := kem.honestRoundTrip sk (kem.stateFromSeed s) hrel r.1 r.2 a hE
      (kem.stateFromSeed (Vector.replicate 32 0))
    dsimp only
    rw [hd]
  | error a b =>
    rw [hE] at h
    cases h

/-! ## The filler of a later layer, with one hop's keys given

The filler of the layer for a position past the first is the sender's filler followed by blocks
of every remaining hop's header keystream (`tailFiller`). So it depends on each hop's keys, and
the layer with one hop's keys given needs its filler computed from those keys. -/

/-- `tailPad`, with each hop's keys given by `keys`. -/
def tailPadOf (keys : ℕ → HopKeys) : ℕ → ByteArray
  | 0 => tailPadBlock streamS geom (keys 0) 0
  | i + 1 => xorBytes (tailPadBlock streamS geom (keys (i + 1)) (i + 1)) (tailPadOf keys i)

theorem tailPadOf_kemHopKeys (path : Array PathHop) (seeds : Array (Vector UInt8 32)) (i : ℕ) :
    tailPadOf streamS geom (kemHopKeys kem kdfS path seeds) i
      = tailPad kem kdfS streamS geom path seeds i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [tailPadOf, tailPad, ih]

/-- `tailPadOf` uses a hop's keys only through its header encryption key and IV. -/
theorem tailPadOf_congr (k₁ k₂ : ℕ → HopKeys) (i : ℕ)
    (h : ∀ m ≤ i, (k₁ m).headerEncryption = (k₂ m).headerEncryption
      ∧ (k₁ m).headerEncryptionIV = (k₂ m).headerEncryptionIV) :
    tailPadOf streamS geom k₁ i = tailPadOf streamS geom k₂ i := by
  induction i with
  | zero =>
    simp only [tailPadOf, tailPadBlock, headerKeystream, (h 0 le_rfl).1, (h 0 le_rfl).2]
  | succ i ih =>
    simp only [tailPadOf, tailPadBlock, headerKeystream, (h (i + 1) le_rfl).1,
      (h (i + 1) le_rfl).2, ih fun m hm => h m (Nat.le_succ_of_le hm)]

/-- `tailFiller` for a path of `size` hops, with each hop's keys given by `keys`. -/
def tailFillerOf (keys : ℕ → HopKeys) (size : ℕ) (filler : ByteArray) : ByteArray :=
  (if geom.nrHops > size then filler else ByteArray.empty)
    ++ tailPadOf streamS geom keys (size - 1)

/-- The filler of the layer for position `i`, with hop `j`'s keys `t` given. -/
def fillerAtK (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (filler : ByteArray)
    (j : ℕ) (t : KeyTuple) : ℕ → ByteArray
  | 0 => filler
  | i + 1 => tailFillerOf streamS geom
      (fun k => if i + k = j then hopKeysOf t else kemHopKeys kem kdfS hops seeds (i + k))
      (hops.size - i) (fillerAtK hops seeds filler j t i)

/-- With the keys that hop `j`'s seed gives, `fillerAtK` is the filler built from the seeds, for
a layer up to hop `j`'s. The seeds may differ at `j`, which `fillerAtK` does not read. -/
theorem fillerAtK_real (hops : Array PathHop) (seeds seeds' : Array (Vector UInt8 32))
    (filler : ByteArray) (j : ℕ) (c ss : ByteArray) (hj : j < hops.size)
    (hsz : seeds'.size = hops.size)
    (henc : kemEncap kem (hops[j]!).publicKey (seeds'[j]!) = .ok (c, ss))
    (hagree : ∀ k, k ≠ j → seeds[k]! = seeds'[k]!) (i : ℕ) (hi : i ≤ j) :
    fillerAtK kem kdfS streamS geom hops seeds filler j (keyTuple (deriveHopKeys kdfS ss)) i
      = RSOR.fillerAt kem kdfS streamS geom hops seeds' filler i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [fillerAtK, RSOR.fillerAt]
    rw [ih (by omega)]
    unfold tailFillerOf tailFiller
    rw [show (hops.extract i hops.size).size = hops.size - i by simp]
    congr 1
    rw [← tailPadOf_kemHopKeys]
    apply tailPadOf_congr
    intro m hm
    have hlt : i + m < hops.size := by omega
    have hk : kemHopKeys kem kdfS (hops.extract i hops.size) (seeds'.extract i seeds'.size) m
        = kemHopKeys kem kdfS hops seeds' (i + m) := by
      unfold kemHopKeys
      rw [getElem!_extract_from _ _ _ hlt, getElem!_extract_from _ _ _ (by omega)]
    rw [hk]
    split_ifs with hij
    · have : kemHopKeys kem kdfS hops seeds' (i + m) = deriveHopKeys kdfS ss := by
        rw [hij]
        unfold kemHopKeys
        rw [henc]
      rw [this]
      exact ⟨rfl, rfl⟩
    · have : kemHopKeys kem kdfS hops seeds (i + m) = kemHopKeys kem kdfS hops seeds' (i + m) := by
        unfold kemHopKeys
        rw [hagree _ hij]
      rw [this]
      exact ⟨rfl, rfl⟩

theorem extract_getElem!_congr {α : Type} [Inhabited α] (a b : Array α) (i m : ℕ)
    (hsz : a.size = b.size) (h : a[i + m]? = b[i + m]?) :
    (a.extract i a.size)[m]! = (b.extract i b.size)[m]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getD_eq_getD_getElem?, Array.getElem?_extract, Array.getElem?_extract, hsz, h]

/-- `RSOR.layer` with hop `j`'s ciphertext `c` and keys `t` given: the layer for position
`i`. -/
def layerK (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (c : ByteArray) (t : KeyTuple) (i : ℕ) : Except String ByteArray :=
  let seeds := d.1.toArray.extract 0 hops.size
  packetK kem cipher macS kdfS streamS geom (seeds.extract i seeds.size)
    (fillerAtK kem kdfS streamS geom hops seeds
      ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)) j t i)
    (hops.extract i hops.size) payload (j - i) c t

/-- With the ciphertext and keys that the seed `s` gives at hop `j`, `layerK` is the layer built
from the draw with `s` at position `j`, for a layer up to hop `j`'s. -/
theorem layerK_real (hops : Array PathHop) (d : RSOR.Draw geom) (payload pkt : ByteArray)
    (j i : ℕ) (s : Vector UInt8 32) (c ss : ByteArray) (hi : i ≤ j) (hj : j < hops.size)
    (hlen : hops.size ≤ geom.nrHops)
    (henc : kemEncap kem (hops[j]!).publicKey s = .ok (c, ss))
    (hpkt : RSOR.layer kem cipher macS kdfS streamS geom hops (d.1.setIfInBounds j s, d.2)
      payload i = .ok pkt) :
    layerK kem cipher macS kdfS streamS geom hops d payload j c
      (keyTuple (deriveHopKeys kdfS ss)) i = .ok pkt := by
  have hsz : ((d.1.setIfInBounds j s).toArray.extract 0 hops.size).size = hops.size := by
    simp; omega
  have hSS : (d.1.toArray.extract 0 hops.size).size
      = ((d.1.setIfInBounds j s).toArray.extract 0 hops.size).size := by simp
  have hget : ∀ k, k ≠ j → (d.1.toArray.extract 0 hops.size)[k]?
      = ((d.1.setIfInBounds j s).toArray.extract 0 hops.size)[k]? := fun k hk => by
    simp [Array.getElem?_extract, Ne.symm hk]
  have hs : ((d.1.setIfInBounds j s).toArray.extract 0 hops.size)[j]! = s := by
    rw [getElem!_extract_zero _ _ _ hj (by rw [Vector.size_toArray]; exact hlen)]
    simp [lt_of_lt_of_le hj hlen]
  unfold RSOR.layer at hpkt
  dsimp only at hpkt
  have h1 := packetK_real kem cipher macS kdfS streamS geom _ _ _ _ pkt (j - i) c ss
    (by
      rw [getElem!_extract_from _ _ _ (by omega), getElem!_extract_from _ _ _ (by omega),
        Nat.add_sub_cancel' hi, hs]
      exact henc) hpkt
  unfold layerK
  dsimp only
  rw [fillerAtK_real kem kdfS streamS geom hops _ _ _ j c ss hj hsz (by rw [hs]; exact henc)
    (fun k hk => by
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hget k hk]) i hi]
  exact (packetK_congr kem cipher macS kdfS streamS geom _ _ _ _ _ _ _ _ fun m hm =>
    extract_getElem!_congr _ _ i m hSS (hget (i + m) (by omega))).trans h1

end PacketK

/-! # Tagging-forward layer unlinkability: the worlds as keyed games -/

section Forward

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry) (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

/-- The honest relays of a game, from their names and keys. -/
def honOf (names : Role → RSOR.Name) (pk kb ks : Key kem) : Protocols.RSOR.Honest 𝒮 :=
  Protocols.RSOR.Property.honestOf (S := 𝒮) names (pk, kem.privI.default)
    (kb, kem.privI.default) (ks, kem.privI.default)

/-- What the adversary's first phase leaves the challenger: the key pairs of the two honest
relays that are not behind the oracle, and the challenge. -/
structure ForwardCh (names : Role → RSOR.Name) (pk : Key kem) where
  kb : Key kem × kem.PrivateKey
  ks : Key kem × kem.PrivateKey
  c : Protocols.RSOR.ForwardChallenge (S := 𝒮)
    (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk kb.1 ks.1)

/-- The challenger's randomness with the seed for forward position `j` replaced. -/
def setSeed (r : RSOR.Randomness geom) (j : Nat) (s : Vector UInt8 32) : RSOR.Randomness geom :=
  ((r.1.1.setIfInBounds j s, r.1.2), r.2)

theorem setIfInBounds_getElem_self {α : Type} {n : ℕ} (v : Vector α n) (j : ℕ) (h : j < n) :
    v.setIfInBounds j v[j] = v := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_setIfInBounds]
  split_ifs with hji
  · subst hji; rfl
  · rfl

/-- Drawing the challenger's randomness and a seed, and putting the seed at forward position
`j`, is drawing the randomness. -/
theorem evalDistEq_setSeed {δ : Type} (j : ℕ) (hj : j < geom.nrHops)
    (K : RSOR.Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let s ← $ᵗ (Vector UInt8 32)
      K (setSeed geom r j s)) =ᵈ ($ᵗ (RSOR.Randomness geom) >>= K) := by
  have hg : Function.Bijective (Function.uncurry
      fun (r : RSOR.Randomness geom) (s : Vector UInt8 32) => (setSeed geom r j s, r.1.1[j])) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun p => (setSeed geom p.1 j p.2, p.1.1.1[j]), ?_, ?_⟩ <;>
    · rintro ⟨r, s⟩
      simp [setSeed, Function.uncurry, setIfInBounds_getElem_self _ _ hj]
  have hp := evalDistEq_pair_of_bijective
    (g := fun (r : RSOR.Randomness geom) (s : Vector UInt8 32) => (r, s))
    ⟨fun ⟨_, _⟩ ⟨_, _⟩ h => h, fun p => ⟨p, rfl⟩⟩ (fun p => K p.1)
  exact ((evalDistEq_pair_of_bijective hg
    (fun p : RSOR.Randomness geom × Vector UInt8 32 => K p.1)).trans hp.symm).trans
    (EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 32)) (K r))

/-- The layer of `q`'s onion for forward position `i`, with the KEM ciphertext and keys of the
hop at position `j` given. -/
def onionK (q : RSOR.Request kem geom) (r : RSOR.Randomness geom) (j : ℕ) (c : kem.Ciphertext)
    (t : KeyTuple) (i : ℕ) : RSOR.Onion geom :=
  match layerK kem cipher macS kdfS streamS geom (RSOR.path kem q.fwd [.recipient q.receiver]) r.1
      (RSOR.body kem macS kdfS streamS geom q r) j (ofVector (kem.encodeCiphertext c)) t i with
  | .ok pkt => RSOR.split geom pkt
  | .error _ => default

/-- With the ciphertext and keys that the seed `s` gives at position `j`, the keyed layer is the
layer of `q`'s onion built from the randomness with `s` at that position, for a layer up to
`j`'s. -/
theorem onionK_real (q : RSOR.Request kem geom) (r : RSOR.Randomness geom)
    (j i : Fin q.fwd.hops.length) (hi : i ≤ j) (pk : Key kem)
    (hkey : (q.fwd.hops[(j : ℕ)]'j.isLt).key = pk) (s : Vector UInt8 32) (c : kem.Ciphertext)
    (ss pkt : ByteArray)
    (henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s
      = .ok (ofVector (kem.encodeCiphertext c), ss))
    (hpkt : RSOR.layer kem cipher macS kdfS streamS geom
      (RSOR.path kem q.fwd [.recipient q.receiver]) (setSeed geom r j s).1
      (RSOR.body kem macS kdfS streamS geom q (setSeed geom r j s)) i = .ok pkt) :
    onionK kem cipher macS kdfS streamS geom q r j c (keyTuple (deriveHopKeys kdfS ss)) i
      = RSOR.form kem cipher macS kdfS streamS geom q (setSeed geom r j s) i := by
  have hn := RSOR.path_size kem q.fwd [.recipient q.receiver]
  have hpub : ((RSOR.path kem q.fwd [.recipient q.receiver])[(j : ℕ)]!).publicKey
      = ofVector (kem.encodePublicKey pk.1) := by
    rw [RSOR.path_getElem! kem _ _ _ j.isLt]
    exact congrArg (fun k : Key kem => ofVector (kem.encodePublicKey k.1)) hkey
  have h : layerK kem cipher macS kdfS streamS geom
      (RSOR.path kem q.fwd [.recipient q.receiver]) r.1
      (RSOR.body kem macS kdfS streamS geom q r) j (ofVector (kem.encodeCiphertext c))
      (keyTuple (deriveHopKeys kdfS ss)) i = .ok pkt :=
    layerK_real kem cipher macS kdfS streamS geom _ r.1 _ pkt j i s _ ss hi
      (by rw [hn]; exact j.isLt)
      (by rw [hn]; exact q.fwd.length_le) (by rw [hpub]; exact henc) hpkt
  have hform : RSOR.form kem cipher macS kdfS streamS geom q (setSeed geom r j s) i
      = RSOR.split geom pkt := by
    unfold RSOR.form
    rw [hpkt]
  rw [hform]
  unfold onionK
  rw [h]

/-- A world of TLU→ around the honest relay's ciphertext and keys: what the challenger draws,
and the world it shows. The game's output is the adversary's guess. -/
def forwardSetupOf (names : Role → RSOR.Name) (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : Key kem} → ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
      → Oth → kem.Ciphertext → KeyTuple → Protocols.RSOR.World 𝒮) :
    KeyedSetup kem (Protocols.RSOR.World 𝒮) Bool where
  Ch := ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names
  Oth := Oth
  drawOth _ := draw
  view := view
  final _ _ _ _ out := out

/-- World 0: the challenger draws its randomness and shows the first layer of the adversary's
own onion. -/
abbrev forwardSetup (names : Role → RSOR.Name) :
    KeyedSetup kem (Protocols.RSOR.World 𝒮) Bool :=
  forwardSetupOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names (RSOR.Randomness geom)
    ($ᵗ RSOR.Randomness geom) fun ch r c t =>
      { onion := onionK kem cipher macS kdfS streamS geom ch.c.req r ch.c.pos c t 0 }

/-- The adversary of the keyed game that an adversary of TLU→ gives. It draws the keys of the
two honest relays that are not behind the oracle, and answers for all three. -/
def forwardAdvOf (names : Role → RSOR.Name) (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : Key kem} → ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
      → Oth → kem.Ciphertext → KeyTuple → Protocols.RSOR.World 𝒮)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    KeyedAdversary (forwardSetupOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth
      draw view) where
  St := A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey)
  pre pk := do
    let kb ← (liftM (keygen kem) : OracleComp procSpec _)
    let ks ← (liftM (keygen kem) : OracleComp procSpec _)
    let sk : Role → kem.PrivateKey := fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2
    let out ← (simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 sk {})
      (A.choose (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk kb.1
        ks.1))).run {}
    return (⟨kb, ks, out.1.1⟩, (out.1.2, out.2, sk))
  post st w :=
    (simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 st.2.2 w.patch)
      (A.guess st.1 w.onion)).run' st.2.1

/-- The adversary for world 0. -/
abbrev forwardAdv (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    KeyedAdversary (forwardSetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names) :=
  forwardAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names _ _ _ A

/-- The first phase of `forwardAdv`, answered by the honest relay: it is the first phase of the
adversary of TLU→ against the game's honest relays. -/
theorem forwardAdv_pre (names : Role → RSOR.Name) (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : Key kem} → ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
      → Oth → kem.Ciphertext → KeyTuple → Protocols.RSOR.World 𝒮)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (k : Key kem × kem.PrivateKey) :
    simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
        ((forwardAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth draw view
          A).pre k.1)
      = (do
        let kb ← keygen kem
        let ks ← keygen kem
        let out ← (simulateQ (Protocols.RSOR.honest
            (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1 ks.1)
            (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2) {})
          (A.choose (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1
            ks.1))).run {}
        return (⟨kb, ks, out.1.1⟩,
          (out.1.2, out.2, fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2))) := by
  have hv : ∀ (kb ks : Key kem × kem.PrivateKey) {α : Type}
      (oa : OracleComp (Protocols.RSOR.oracleSpec 𝒮) α),
      simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
          ((simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16
            (fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2) {}) oa).run {})
        = (simulateQ (Protocols.RSOR.honest
            (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1 ks.1)
            (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2) {}) oa).run {} :=
    fun kb ks _ oa => viaOracle_honest kem cipher macS kdfS streamS geom hvalid hmactag h16 _
      (fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2)
      (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2)
      (fun h hr => by cases h <;> first | rfl | exact absurd rfl hr) {} oa {}
  unfold forwardAdvOf
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_procImpl_liftM, hv]

/-- The second phase of `forwardAdv`, answered by the keyed relay with the keys of the
ciphertext's own secret: it is the second phase of the adversary of TLU→ against the game's
honest relays. -/
theorem forwardAdv_post (names : Role → RSOR.Name) (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : Key kem} → ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
      → Oth → kem.Ciphertext → KeyTuple → Protocols.RSOR.World 𝒮)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (k kb ks : Key kem × kem.PrivateKey)
    (c : kem.Ciphertext) (K : kem.Plaintext) (hdec : decapOf kem k.2 c = some K)
    (st : A.State) (log : Protocols.RSOR.Log 𝒮) (w : Protocols.RSOR.World 𝒮) :
    simulateQ (procImplK kem cipher macS kdfS streamS geom k.2 c ((hopKeysPRG kem kdfS).gen K))
        ((forwardAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth draw view
          A).post (st, log, fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2) w)
      = (simulateQ (Protocols.RSOR.honest
            (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1 ks.1)
            (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2) w.patch)
          (A.guess st w.onion)).run' log := by
  have hv := viaOracle_honest kem cipher macS kdfS streamS geom hvalid hmactag h16
    (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1 ks.1)
    (fun | .relay => kb.2 | .back => kb.2 | .sender => ks.2)
    (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2)
    (fun h hr => by cases h <;> first | rfl | exact absurd rfl hr) w.patch (A.guess st w.onion) log
  rw [procImplK_real kem cipher macS kdfS streamS geom k.2 c K hdec]
  unfold forwardAdvOf
  simp only [StateT.run', simulateQ_map]
  exact congrArg (fun x => (·.1) <$> x) hv

/-- The draws of a world of TLU→: the honest relays' key pairs, the adversary's first phase, the
challenger's draws, and the seed of the encapsulation to the honest relay. -/
structure ForwardDraw (names : Role → RSOR.Name) (Oth : Type)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) where
  k : Key kem × kem.PrivateKey
  ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1
  st : A.State
  log : Protocols.RSOR.Log 𝒮
  o : Oth
  s : Vector UInt8 32

/-- The secret keys of the honest relays in a draw. -/
def ForwardDraw.sk {names : Role → RSOR.Name} {Oth : Type}
    {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (d : ForwardDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth A) :
    Role → kem.PrivateKey :=
  fun | .relay => d.k.2 | .back => d.ch.kb.2 | .sender => d.ch.ks.2

def forwardDrawOf (names : Role → RSOR.Name) (Oth : Type) (draw : ProbComp Oth)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    ProbComp (ForwardDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth A) := do
  let k ← keygen kem
  let kb ← keygen kem
  let ks ← keygen kem
  let out ← (simulateQ (Protocols.RSOR.honest
      (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1 ks.1)
      (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2) {})
    (A.choose (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1 kb.1
      ks.1))).run {}
  let o ← draw
  let s ← $ᵗ (Vector UInt8 32)
  return ⟨k, ⟨kb, ks, out.1.1⟩, out.1.2, out.2, o, s⟩

/-- The draws of world 0: the challenger draws its randomness. -/
abbrev forwardDraw (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    ProbComp (ForwardDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      (RSOR.Randomness geom) A) :=
  forwardDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names _
    ($ᵗ RSOR.Randomness geom) A

/-- World 0 of TLU→ as its draws, then the adversary's guess on the first layer of its own
onion, built with the seed drawn apart at the honest relay's position. -/
theorem play_false_evalDistEq (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    Protocols.RSOR.Property.play names A false
      =ᵈ forwardDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A >>= fun d =>
        (simulateQ (Protocols.RSOR.honest
            (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names d.k.1 d.ch.kb.1
              d.ch.ks.1) d.sk {})
          (A.guess d.st (RSOR.form kem cipher macS kdfS streamS geom d.ch.c.req
            (setSeed geom d.o d.ch.c.pos d.s) d.ch.c.req.first))).run' d.log := by
  unfold Protocols.RSOR.Property.play Protocols.RSOR.Property.playFrom forwardDraw forwardDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun kb =>
    EvalDistEq.bind_right _ fun ks => EvalDistEq.bind_right _ fun out => ?_
  have hlt : (out.1.1.pos : ℕ) < geom.nrHops :=
    lt_of_lt_of_le out.1.1.pos.isLt out.1.1.req.fwd.length_le
  have h := evalDistEq_setSeed geom out.1.1.pos hlt fun r =>
    (simulateQ (Protocols.RSOR.honest (Protocols.RSOR.Property.honestOf names k kb ks)
        (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2) {})
      (A.guess out.1.2 (RSOR.form kem cipher macS kdfS streamS geom out.1.1.req r
        out.1.1.req.first))).run' out.2
  have hw : Protocols.RSOR.forwardUnlinkable.world out.1.1 false = (do
      let r ← $ᵗ (RSOR.Randomness geom)
      return { onion := (RSOR.form kem cipher macS kdfS streamS geom out.1.1.req r
        out.1.1.req.first) }) := by
    simp [Protocols.RSOR.forwardUnlinkable]
    rfl
  refine EvalDistEq.trans ?_ h.symm
  rw [hw]
  simp only [bind_assoc, pure_bind]
  exact EvalDistEq.rfl

variable [SampleableType kem.Plaintext]

/-- The keyed game of `forwardAdvOf` with the real keys, as the draws of its world and then the
second phase on the world it shows. -/
theorem keyedReal_forwardAdvOf_evalDistEq (names : Role → RSOR.Name) (Oth : Type)
    (draw : ProbComp Oth)
    (view : {pk : Key kem} → ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk
      → Oth → kem.Ciphertext → KeyTuple → Protocols.RSOR.World 𝒮)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    keyedReal cipher macS kdfS streamS geom
        (forwardAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth draw view A)
      =ᵈ forwardDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth draw
          A >>= fun d =>
        simulateQ (procImplK kem cipher macS kdfS streamS geom d.k.2 (encapOf kem d.k.1.1 d.s).1
            ((hopKeysPRG kem kdfS).gen (encapOf kem d.k.1.1 d.s).2))
          ((forwardAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names Oth draw
            view A).post
            (d.st, d.log, fun | .relay => d.ch.kb.2 | .back => d.ch.kb.2 | .sender => d.ch.ks.2)
            (view d.ch d.o (encapOf kem d.k.1.1 d.s).1
              ((hopKeysPRG kem kdfS).gen (encapOf kem d.k.1.1 d.s).2))) := by
  unfold keyedReal keyedGame forwardDrawOf
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
  simp only [forwardAdv_pre]
  simp only [forwardSetupOf, bind_assoc, pure_bind, bind_pure]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun kb =>
    EvalDistEq.bind_right _ fun ks => EvalDistEq.bind_right _ fun out => ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

omit [SampleableType kem.Plaintext] in
/-- If the first layer on a path builds, the encapsulation to each of its relays succeeded. -/
theorem layer_zero_encap (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last : List RoutingCommand) (d : RSOR.Draw geom) (payload pkt : ByteArray)
    (h : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem R last) d payload 0
      = .ok pkt) (j : ℕ) (hj : j < R.hops.length) :
    ∃ ct ss, kemEncap kem (ofVector (kem.encodePublicKey (R.hops[j]).key.1)) (d.1.toArray[j]!)
      = .ok (ct, ss) := by
  have hn := RSOR.path_size kem R last
  have hle : R.hops.length ≤ geom.nrHops := R.length_le
  unfold RSOR.layer at h
  dsimp only at h
  simp only [RSOR.fillerAt, Array.extract_size] at h
  obtain ⟨-, hdr, sprp, t, hcreate, -, -, -⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ h
  obtain ⟨-, -, -, -, ke, keys, -, -, st, -, -, -, -, hkc, -⟩ :=
    createKEMHeader_unfold kem macS kdfS streamS geom _ _ _ _ _ hcreate
  obtain ⟨ct, ss, henc, -, -⟩ := hkc j (by rw [hn]; exact hj)
  rw [RSOR.path_getElem! kem _ _ _ hj,
    getElem!_extract_zero _ _ _ (by rw [hn]; exact hj)
      (by rw [Vector.size_toArray, hn]; exact hle)] at henc
  exact ⟨ct, ss, henc⟩

/-- The draws that the exact steps do not cover: the honest relay's public key is not the one
its private key gives, its seed may make the KEM fail, or the first layer cannot be built. -/
def forwardBad {names : Role → RSOR.Name}
    {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (d : ForwardDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      (RSOR.Randomness geom) A) :
    Prop :=
  ¬ (d.k.1.1 = kem.derivePublicKey d.k.2 ∧ kem.Reliable (kem.stateFromSeed d.s) ∧
    ∃ pkt, RSOR.layer kem cipher macS kdfS streamS geom
      (RSOR.path kem d.ch.c.req.fwd [.recipient d.ch.c.req.receiver])
      (setSeed geom d.o d.ch.c.pos d.s).1
      (RSOR.body kem macS kdfS streamS geom d.ch.c.req (setSeed geom d.o d.ch.c.pos d.s)) 0
        = .ok pkt)

/-- **World 0 of TLU→ is the keyed game with the real keys, off the bad draws.** -/
theorem play_false_sub_keyedReal_le (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
      - (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
          (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal|
    ≤ (Pr{let d ← (forwardDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A)}[forwardBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal := by
  rw [(play_false_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).prEvent_eq (fun x => x = true),
    (keyedReal_forwardAdvOf_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      _ _ _ A).prEvent_eq (fun x => x = true)]
  refine prEvent_bind_toReal_sub_le_of_bad _ _ _
    (forwardBad kem cipher macS kdfS streamS geom hvalid hmactag h16) (fun d hd => ?_)
    (fun x => x = true)
  obtain ⟨hpk, hrel, pkt, hpkt⟩ := Classical.not_not.mp hd
  have hpos : (d.ch.c.pos : ℕ) < d.ch.c.req.fwd.hops.length := d.ch.c.pos.isLt
  have hle : d.ch.c.req.fwd.hops.length ≤ geom.nrHops := d.ch.c.req.fwd.length_le
  obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem cipher macS kdfS streamS geom d.ch.c.req.fwd
    _ _ _ pkt hpkt d.ch.c.pos hpos
  have hkey : (d.ch.c.req.fwd.hops[(d.ch.c.pos : ℕ)]'hpos).key = d.k.1 :=
    congrArg (·.key) d.ch.c.relay
  have hpub : ofVector (kem.encodePublicKey (d.ch.c.req.fwd.hops[(d.ch.c.pos : ℕ)]'hpos).key.1)
      = ofVector (kem.encodePublicKey d.k.1.1) :=
    congrArg (fun k : Key kem => ofVector (kem.encodePublicKey k.1)) hkey
  have hs : (setSeed geom d.o d.ch.c.pos d.s).1.1.toArray[(d.ch.c.pos : ℕ)]! = d.s := by
    simp [setSeed, lt_of_lt_of_le hpos hle]
  rw [hs] at henc
  replace henc : kemEncap kem (ofVector (kem.encodePublicKey d.k.1.1)) d.s = .ok (ct, ss) :=
    (congrArg (fun b => kemEncap kem b d.s) hpub).symm.trans henc
  obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem d.k.1.1 d.s ct ss henc
  have hdec : decapOf kem d.k.2 (encapOf kem d.k.1.1 d.s).1 = some (encapOf kem d.k.1.1 d.s).2 := by
    have h := decapOf_encapOf kem d.k.2 d.s hrel _ _ (hpk ▸ henc)
    rwa [← hpk] at h
  have honion : onionK kem cipher macS kdfS streamS geom d.ch.c.req d.o d.ch.c.pos
      (encapOf kem d.k.1.1 d.s).1 ((hopKeysPRG kem kdfS).gen (encapOf kem d.k.1.1 d.s).2) 0
      = RSOR.form kem cipher macS kdfS streamS geom d.ch.c.req (setSeed geom d.o d.ch.c.pos d.s)
          d.ch.c.req.first :=
    onionK_real kem cipher macS kdfS streamS geom d.ch.c.req d.o d.ch.c.pos
      d.ch.c.req.first (Nat.zero_le _) d.k.1 hkey d.s _ _
      pkt henc hpkt
  rw [forwardAdv_post kem cipher macS kdfS streamS geom hvalid hmactag h16 names _ _ _ A d.k
    d.ch.kb d.ch.ks _ _ hdec d.st d.log _]
  simp only [honion]
  rfl

/-! ## World 1

The challenger shows a replacement that ends at the honest relay, and the relay answers it as
it would answer the adversary's own onion. -/

/-- What the challenger draws in world 1: the randomness of the adversary's own onion, and the
replacement's message, receiver and randomness. -/
def shortDraw :
    ProbComp (RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom) := do
  let r ← $ᵗ (RSOR.Randomness geom)
  let m ← $ᵗ (RSOR.Msg geom)
  let n ← $ᵗ RSOR.Name
  let r' ← $ᵗ (RSOR.Randomness geom)
  return (r, m, n, r')

omit [SampleableType kem.Plaintext] in
/-- World 1 of TLU→ as its draws, then the adversary's guess on the first layer of the
replacement, built with the seed drawn apart at the honest relay's position, against the relay
patched around the replacement's layer there. -/
theorem play_true_evalDistEq (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    Protocols.RSOR.Property.play names A true
      =ᵈ forwardDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          _ (shortDraw geom) A >>= fun d =>
        (simulateQ (Protocols.RSOR.honest
            (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                d.k.1 d.ch.kb.1 d.ch.ks.1) d.sk
            (d.ch.c.patch d.o.1 (RSOR.form kem cipher macS kdfS streamS geom
                (d.ch.c.short d.o.2.1 d.o.2.2.1)
              (setSeed geom d.o.2.2.2 d.ch.c.pos d.s) d.ch.c.shortPos)))
          (A.guess d.st (RSOR.form kem cipher macS kdfS streamS geom
              (d.ch.c.short d.o.2.1 d.o.2.2.1)
            (setSeed geom d.o.2.2.2 d.ch.c.pos d.s)
            (d.ch.c.short d.o.2.1 d.o.2.2.1).first))).run' d.log := by
  unfold Protocols.RSOR.Property.play Protocols.RSOR.Property.playFrom forwardDrawOf shortDraw
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun kb =>
    EvalDistEq.bind_right _ fun ks => EvalDistEq.bind_right _ fun out => ?_
  have hlt : (out.1.1.pos : ℕ) < geom.nrHops :=
    lt_of_lt_of_le out.1.1.pos.isLt out.1.1.req.fwd.length_le
  have hw : Protocols.RSOR.forwardUnlinkable.world out.1.1 true = (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let m ← $ᵗ (RSOR.Msg geom)
      let n ← $ᵗ RSOR.Name
      let r' ← $ᵗ (RSOR.Randomness geom)
      return {
        onion := (RSOR.form kem cipher macS kdfS streamS geom
          (out.1.1.short m n) r' (out.1.1.short m n).first)
        patch := (out.1.1.patch r
          (RSOR.form kem cipher macS kdfS streamS geom
            (out.1.1.short m n) r' out.1.1.shortPos)) }) := by
    simp [Protocols.RSOR.forwardUnlinkable]
    rfl
  rw [hw]
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun r => EvalDistEq.bind_right _ fun m =>
    EvalDistEq.bind_right _ fun n => ?_
  have h := evalDistEq_setSeed geom out.1.1.pos hlt fun r' =>
    (simulateQ (Protocols.RSOR.honest (Protocols.RSOR.Property.honestOf names k kb ks)
        (fun | .relay => k.2 | .back => kb.2 | .sender => ks.2)
        (out.1.1.patch r (RSOR.form kem cipher macS kdfS streamS geom
            (out.1.1.short m n) r' out.1.1.shortPos)))
      (A.guess out.1.2 (RSOR.form kem cipher macS kdfS streamS geom (out.1.1.short m n) r'
        (out.1.1.short m n).first))).run' out.2
  exact h.symm

/-- The world the challenger shows in world 1, around the honest relay's ciphertext and keys:
the replacement's first layer, and the relay patched around the replacement's layer at its own
position. -/
def shortView (names : Role → RSOR.Name) {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (o : RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)
    (c : kem.Ciphertext) (t : KeyTuple) : Protocols.RSOR.World 𝒮 where
  onion := onionK kem cipher macS kdfS streamS geom
      (ch.c.short o.2.1 o.2.2.1) o.2.2.2 ch.c.pos c t 0
  patch := ch.c.patch o.1
    (onionK kem cipher macS kdfS streamS geom
        (ch.c.short o.2.1 o.2.2.1) o.2.2.2 ch.c.pos c t ch.c.pos)

/-- The adversary for world 1. -/
abbrev shortAdv (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :=
  forwardAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names _ (shortDraw geom)
    (shortView kem cipher macS kdfS streamS geom hvalid hmactag h16 names) A

/-- The draws of world 1 that the exact steps do not cover: the honest relay's public key is not
the one its private key gives, its seed may make the KEM fail, or the replacement's first layer
or its layer at the honest relay cannot be built. -/
def shortBad {names : Role → RSOR.Name}
    {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (d : ForwardDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      (RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom) A) :
    Prop :=
  ¬ (d.k.1.1 = kem.derivePublicKey d.k.2 ∧ kem.Reliable (kem.stateFromSeed d.s) ∧
    ∃ pkt₀ pkt,
      RSOR.layer kem cipher macS kdfS streamS geom
        (RSOR.path kem (d.ch.c.short d.o.2.1 d.o.2.2.1).fwd
          [.recipient (d.ch.c.short d.o.2.1 d.o.2.2.1).receiver])
        (setSeed geom d.o.2.2.2 d.ch.c.pos d.s).1
        (RSOR.body kem macS kdfS streamS geom (d.ch.c.short d.o.2.1 d.o.2.2.1)
          (setSeed geom d.o.2.2.2 d.ch.c.pos d.s)) 0 = .ok pkt₀ ∧
      RSOR.layer kem cipher macS kdfS streamS geom
        (RSOR.path kem (d.ch.c.short d.o.2.1 d.o.2.2.1).fwd
          [.recipient (d.ch.c.short d.o.2.1 d.o.2.2.1).receiver])
        (setSeed geom d.o.2.2.2 d.ch.c.pos d.s).1
        (RSOR.body kem macS kdfS streamS geom (d.ch.c.short d.o.2.1 d.o.2.2.1)
          (setSeed geom d.o.2.2.2 d.ch.c.pos d.s)) d.ch.c.pos = .ok pkt)

/-- **World 1 of TLU→ is the keyed game with the real keys, off the bad draws.** -/
theorem play_true_sub_keyedReal_le (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A true}[x = true]).toReal
      - (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
          (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal|
    ≤ (Pr{let d ← (forwardDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names _
        (shortDraw geom) A)}[shortBad kem cipher macS kdfS streamS geom hvalid hmactag h16
            d]).toReal := by
  rw [(play_true_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).prEvent_eq (fun x => x = true),
    (keyedReal_forwardAdvOf_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      _ _ _ A).prEvent_eq (fun x => x = true)]
  refine prEvent_bind_toReal_sub_le_of_bad _ _ _
    (shortBad kem cipher macS kdfS streamS geom hvalid hmactag h16) (fun d hd => ?_)
    (fun x => x = true)
  obtain ⟨hpk, hrel, pkt₀, pkt, hpkt₀, hpkt⟩ := Classical.not_not.mp hd
  have hpos : (d.ch.c.pos : ℕ) < d.ch.c.req.fwd.hops.length := d.ch.c.pos.isLt
  have hle : d.ch.c.req.fwd.hops.length ≤ geom.nrHops := d.ch.c.req.fwd.length_le
  have hposq : (d.ch.c.pos : ℕ) < (d.ch.c.short d.o.2.1 d.o.2.2.1).fwd.hops.length :=
    (d.ch.c.shortPos (msg := d.o.2.1) (receiver := d.o.2.2.1)).isLt
  have hhop : (d.ch.c.short d.o.2.1 d.o.2.2.1).fwd.hops[(d.ch.c.pos : ℕ)]'hposq
      = d.ch.c.req.fwd.hops[(d.ch.c.pos : ℕ)]'hpos := by
    simp [Protocols.RSOR.ForwardChallenge.short, Protocols.RSOR.Route.take]
  have hkey : ((d.ch.c.short d.o.2.1 d.o.2.2.1).fwd.hops[(d.ch.c.pos : ℕ)]'hposq).key = d.k.1 :=
    (congrArg (·.key) hhop).trans (congrArg (·.key) d.ch.c.relay)
  obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem cipher macS kdfS streamS geom
      (d.ch.c.short d.o.2.1 d.o.2.2.1).fwd
    _ _ _ pkt₀ hpkt₀ d.ch.c.pos hposq
  have hpub : ofVector (kem.encodePublicKey
        ((d.ch.c.short d.o.2.1 d.o.2.2.1).fwd.hops[(d.ch.c.pos : ℕ)]'hposq).key.1)
      = ofVector (kem.encodePublicKey d.k.1.1) :=
    congrArg (fun k : Key kem => ofVector (kem.encodePublicKey k.1)) hkey
  have hs : (setSeed geom d.o.2.2.2 d.ch.c.pos d.s).1.1.toArray[(d.ch.c.pos : ℕ)]! = d.s := by
    simp [setSeed, lt_of_lt_of_le hpos hle]
  rw [hs] at henc
  replace henc : kemEncap kem (ofVector (kem.encodePublicKey d.k.1.1)) d.s = .ok (ct, ss) :=
    (congrArg (fun b => kemEncap kem b d.s) hpub).symm.trans henc
  obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem d.k.1.1 d.s ct ss henc
  have hdec : decapOf kem d.k.2 (encapOf kem d.k.1.1 d.s).1 = some (encapOf kem d.k.1.1 d.s).2 := by
    have h := decapOf_encapOf kem d.k.2 d.s hrel _ _ (hpk ▸ henc)
    rwa [← hpk] at h
  have h0 : onionK kem cipher macS kdfS streamS geom
      (d.ch.c.short d.o.2.1 d.o.2.2.1) d.o.2.2.2 d.ch.c.pos
      (encapOf kem d.k.1.1 d.s).1 ((hopKeysPRG kem kdfS).gen (encapOf kem d.k.1.1 d.s).2) 0
      = RSOR.form kem cipher macS kdfS streamS geom
          (d.ch.c.short d.o.2.1 d.o.2.2.1) (setSeed geom d.o.2.2.2 d.ch.c.pos d.s)
          (d.ch.c.short d.o.2.1 d.o.2.2.1).first :=
    onionK_real kem cipher macS kdfS streamS geom
        (d.ch.c.short d.o.2.1 d.o.2.2.1) d.o.2.2.2 d.ch.c.shortPos
      (d.ch.c.short d.o.2.1 d.o.2.2.1).first (Nat.zero_le _) d.k.1 hkey d.s _ _ pkt₀ henc hpkt₀
  have hp : onionK kem cipher macS kdfS streamS geom
      (d.ch.c.short d.o.2.1 d.o.2.2.1) d.o.2.2.2 d.ch.c.pos
      (encapOf kem d.k.1.1 d.s).1 ((hopKeysPRG kem kdfS).gen (encapOf kem d.k.1.1 d.s).2)
        d.ch.c.pos
      = RSOR.form kem cipher macS kdfS streamS geom
          (d.ch.c.short d.o.2.1 d.o.2.2.1) (setSeed geom d.o.2.2.2 d.ch.c.pos d.s)
          d.ch.c.shortPos :=
    onionK_real kem cipher macS kdfS streamS geom
        (d.ch.c.short d.o.2.1 d.o.2.2.1) d.o.2.2.2 d.ch.c.shortPos
      d.ch.c.shortPos (le_refl _) d.k.1 hkey d.s _ _ pkt henc hpkt
  rw [forwardAdv_post kem cipher macS kdfS streamS geom hvalid hmactag h16 names _ _ _ A d.k
    d.ch.kb d.ch.ks _ _ hdec d.st d.log _]
  simp only [shortView, h0, hp]
  rfl

/-- **TLU→ for KEM Sphinx, down to uniform keys.** The advantage is at most the chance of a bad
draw in either world, the cost of replacing the honest relay's keys in either world, and the
distance between the two worlds once those keys are uniform. -/
theorem forwardUnlinkable_le_keyedIdeal (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    ((Protocols.RSOR.forwardUnlinkable (S := 𝒮)).advantage names A).toReal
      ≤ (Pr{let d ← (forwardDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A)}[forwardBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + (Pr{let d ← (forwardDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names _
          (shortDraw geom)
          A)}[shortBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + keyedCost cipher macS kdfS streamS geom
          (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        + keyedCost cipher macS kdfS streamS geom
          (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        + |(Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
            (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal
          - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
            (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal| := by
  refine (Protocols.RSOR.Property.advantage_toReal
    (P := Protocols.RSOR.forwardUnlinkable (S := 𝒮)) names A).le.trans ?_
  obtain ⟨h0, h0'⟩ := abs_le.1
    (play_false_sub_keyedReal_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
  obtain ⟨h1, h1'⟩ := abs_le.1
    (play_true_sub_keyedReal_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
  obtain ⟨c0, c0'⟩ := abs_le.1 (keyedChain_le cipher macS kdfS streamS geom
    (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))
  obtain ⟨c1, c1'⟩ := abs_le.1 (keyedChain_le cipher macS kdfS streamS geom
    (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))
  have hi := le_abs_self
    ((Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
        (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A))}[x = true]).toReal
      - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
        (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A))}[x = true]).toReal)
  have hi' := neg_abs_le
    ((Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
        (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A))}[x = true]).toReal
      - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
        (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A))}[x = true]).toReal)
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith

end Forward

end Cryptlib.Protocols.Sphinx.KEMSphinx
