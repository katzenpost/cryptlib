/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxKeyed
import Cryptlib.Protocols.Sphinx.KEMSphinxLayerIn
import Cryptlib.Protocols.Sphinx.KEMSphinxHeaderFn

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

/-- Whether the keyed packet can be built does not depend on the ciphertext and keys given, nor
on the seeds or the filler. -/
theorem packetK_ok_congr (seeds seeds' : Array (Vector UInt8 32)) (filler filler' : ByteArray)
    (path : Array PathHop) (payload pkt : ByteArray) (j : ℕ) (c c' : ByteArray) (t t' : KeyTuple)
    (h : packetK kem cipher macS kdfS streamS geom seeds filler path payload j c t = .ok pkt) :
    ∃ pkt', packetK kem cipher macS kdfS streamS geom seeds' filler' path payload j c' t'
      = .ok pkt' := by
  unfold packetK at h ⊢
  have h1 := newKEMPacketFrom_pktFn kem geom macS streamS cipher
    (Array.ofFn fun i : Fin path.size => if i.val = j then c else kemHopCt kem path seeds i)
    (Array.ofFn fun i : Fin path.size =>
      if i.val = j then hopKeysOf t else kemHopKeys kem kdfS path seeds i) filler path payload
  rw [h] at h1
  obtain ⟨p', hp'⟩ := pktFn_isSome_congr kem geom _ _ _ _ _ _ _ _ _ _ path payload pkt h1.symm
  have h2 := newKEMPacketFrom_pktFn kem geom macS streamS cipher
    (Array.ofFn fun i : Fin path.size => if i.val = j then c' else kemHopCt kem path seeds' i)
    (Array.ofFn fun i : Fin path.size =>
      if i.val = j then hopKeysOf t' else kemHopKeys kem kdfS path seeds' i) filler' path payload
  rw [hp'] at h2
  cases hr : newKEMPacketFrom kem cipher macS streamS geom
      (Array.ofFn fun i : Fin path.size => if i.val = j then c' else kemHopCt kem path seeds' i)
      (Array.ofFn fun i : Fin path.size =>
        if i.val = j then hopKeysOf t' else kemHopKeys kem kdfS path seeds' i) filler' path
      payload with
  | ok q => exact ⟨q, rfl⟩
  | error e =>
    rw [hr] at h2
    cases h2

theorem kemHopCt_extract (path : Array PathHop) (seeds : Array (Vector UInt8 32)) (i : ℕ)
    (hp : 1 + i < path.size) (hs : 1 + i < seeds.size) :
    kemHopCt kem (path.extract 1 path.size) (seeds.extract 1 seeds.size) i
      = kemHopCt kem path seeds (1 + i) := by
  unfold kemHopCt
  rw [getElem!_extract_from path 1 i hp, getElem!_extract_from seeds 1 i hs]

theorem kemHopKeys_extract (path : Array PathHop) (seeds : Array (Vector UInt8 32)) (i : ℕ)
    (hp : 1 + i < path.size) (hs : 1 + i < seeds.size) :
    kemHopKeys kem kdfS (path.extract 1 path.size) (seeds.extract 1 seeds.size) i
      = kemHopKeys kem kdfS path seeds (1 + i) := by
  unfold kemHopKeys
  rw [getElem!_extract_from path 1 i hp, getElem!_extract_from seeds 1 i hs]

/-- The header keystream of a hop's keys. -/
def ksOf (t : KeyTuple) : ByteArray :=
  streamS.keystream (ofVector t.2.2.2) (ofVector t.2.1)
    (geom.routingInfoLength + geom.perHopRoutingInfoLength)

/-- The tagging function of a hop's keys. -/
def tagOf (t : KeyTuple) (m : ByteArray) : ByteArray := ofVector (macS.mac (ofVector t.2.2.1) m)

/-- The payload encryption of a hop's keys. -/
def encOf (t : KeyTuple) (b : ByteArray) : ByteArray :=
  cipher.encrypt t.1.toArray (ofVector t.2.1) b

/-- `packetK`'s packet, with hop `j`'s header keystream `U`, tagging function `tagf` and payload
encryption `encf` given in place of its keys. -/
def packetF (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (path : Array PathHop)
    (payload : ByteArray) (j : Nat) (c U : ByteArray) (tagf encf : ByteArray → ByteArray) :
    Option ByteArray :=
  pktFn kem geom
    (Function.update (keysKs geom streamS
      (Array.ofFn fun i : Fin path.size => kemHopKeys kem kdfS path seeds i)) j U)
    (Function.update (keysTag macS
      (Array.ofFn fun i : Fin path.size => kemHopKeys kem kdfS path seeds i)) j tagf)
    (Function.update (keysEnc cipher
      (Array.ofFn fun i : Fin path.size => kemHopKeys kem kdfS path seeds i)) j encf)
    (Array.ofFn fun i : Fin path.size => if i.val = j then c else kemHopCt kem path seeds i)
    filler path payload

/-- **A packet uses the keys given for hop `j` in three ways only**: their header keystream,
their MAC, and one encryption of the payload. -/
theorem packetK_eq_packetF (seeds : Array (Vector UInt8 32)) (filler : ByteArray)
    (path : Array PathHop) (payload : ByteArray) (j : Nat) (c : ByteArray) (t : KeyTuple) :
    (packetK kem cipher macS kdfS streamS geom seeds filler path payload j c t).toOption
      = packetF kem cipher macS kdfS streamS geom seeds filler path payload j c
          (ksOf streamS geom t) (tagOf macS t) (encOf cipher t) := by
  unfold packetK packetF
  rw [newKEMPacketFrom_pktFn]
  refine pktFn_congr kem geom _ _ _ _ _ _ _ _ _ _ fun i hi => ?_
  have hget : ∀ f : Fin path.size → HopKeys, (Array.ofFn f)[i]! = f ⟨i, hi⟩ := fun f => by
    rw [getElem!_pos _ i (by simpa using hi)]
    simp only [Array.getElem_ofFn]
  by_cases hij : i = j
  · subst hij
    refine ⟨?_, funext fun m => ?_, funext fun b => ?_⟩
    · simp only [Function.update_self, keysKs, hget, ↓reduceIte, hopKeysOf, ksOf]
    · simp only [Function.update_self, keysTag, hget, ↓reduceIte, hopKeysOf, tagOf]
    · simp only [Function.update_self, keysEnc, hget, ↓reduceIte, hopKeysOf, encOf]
  · refine ⟨?_, funext fun m => ?_, funext fun b => ?_⟩
    · simp only [Function.update_of_ne hij, keysKs, hget, hij, ↓reduceIte]
    · simp only [Function.update_of_ne hij, keysTag, hget, hij, ↓reduceIte]
    · simp only [Function.update_of_ne hij, keysEnc, hget, hij, ↓reduceIte]

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

/-- **A hop in front of the keyed one forwards the keyed packet on the rest of the path.** The
keyed hop moves one place forward, and the filler gains one block, in which the keyed hop's part
comes from the keystream of the keys given. -/
theorem packetK_step (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (path : Array PathHop)
    (payload pkt privKey : ByteArray) (j : ℕ) (c : ByteArray) (t : KeyTuple)
    (hj : 1 ≤ j) (hjn : j < path.size) (hple : path.size ≤ geom.nrHops)
    (hseeds : path.size ≤ seeds.size)
    (hfsize : geom.nrHops > path.size →
      filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hc : c.size = kem.ciphertextSize)
    (henc : ∀ i, i < path.size → i ≠ j →
      ∃ ct ss, kemEncap kem (path[i]!).publicKey (seeds[i]!) = .ok (ct, ss))
    (hrel : kem.Reliable (kem.stateFromSeed seeds[0]!))
    (hpp : kemSelfPublicKeyBytes kem privKey = (path[0]!).publicKey)
    (hcmdnn : ∀ c ∈ (path[0]!).commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ (path[0]!).commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (hpk : packetK kem cipher macS kdfS streamS geom seeds filler path payload j c t = .ok pkt) :
    ∃ (replayTag mac : Vector UInt8 32) (fwd : Vector UInt8 pkt.size),
      unwrapKEM kem cipher macS kdfS streamS geom privKey pkt
        = .ok (none, replayTag,
            (path[0]!).commands ++ [RoutingCommand.nextNodeHop (path[1]!).id mac], some fwd) ∧
      packetK kem cipher macS kdfS streamS geom (seeds.extract 1 seeds.size)
          ((if geom.nrHops > path.size then filler else ByteArray.empty)
            ++ tailPadOf geom (fun k => if k = j then ksOf streamS geom t
              else headerKeystream streamS geom (kemHopKeys kem kdfS path seeds k))
              (path.size - 1))
          (path.extract 1 path.size) payload (j - 1) c t = .ok (ofVector fwd) ∧
      pkt = wrapHop kem cipher macS streamS geom path (kemHopCt kem path seeds 0)
        (kemHopKeys kem kdfS path seeds 0) (ofVector fwd) := by
  obtain ⟨ct0, ss0, henc0⟩ := henc 0 (by omega) (by omega)
  have hget : ∀ {α : Type} [Inhabited α] (f : Fin path.size → α) (i : ℕ) (hi : i < path.size),
      (Array.ofFn f)[i]! = f ⟨i, hi⟩ := fun f i hi => by
    rw [getElem!_pos _ i (by simpa using hi)]
    simp only [Array.getElem_ofFn]
  unfold packetK at hpk
  obtain ⟨replayTag, mac, fwd, hun, hfwd, hwrap⟩ := newKEMPacketFrom_step kem cipher macS kdfS
    streamS geom hvalid hmactag h16 _ _ filler path payload pkt privKey (by omega) hple hfsize
    (by simp) (by simp)
    (fun i hi => by
      have hi' : i < path.size := by simpa using hi
      simp only [Array.getElem_ofFn]
      split_ifs with hij
      · exact hc
      · obtain ⟨ct, ss, he⟩ := henc i hi' hij
        unfold kemHopCt
        rw [he]
        exact kemEncap_size kem _ _ ct ss he)
    hpp
    ⟨seeds[0]!, ss0, hrel, by
      rw [hget _ 0 (by omega)]
      simp only [show ¬ (0 = j) by omega, ↓reduceIte]
      unfold kemHopCt
      rw [henc0], by
      rw [hget _ 0 (by omega)]
      simp only [show ¬ (0 = j) by omega, ↓reduceIte]
      unfold kemHopKeys
      rw [henc0]⟩
    hcmdnn hcmdnh hpk
  rw [hget _ 0 (by omega), hget _ 0 (by omega)] at hwrap
  simp only [show ¬ (0 = j) by omega, ↓reduceIte] at hwrap
  refine ⟨replayTag, mac, fwd, hun, ?_, hwrap⟩
  have hps : (path.extract 1 path.size).size = path.size - 1 := by simp
  unfold packetK
  rw [← hfwd]
  congr 1
  · apply Array.ext
    · simp
    · intro i h1 h2
      have hi : 1 + i < path.size := by
        simp only [Array.size_ofFn, hps] at h1
        omega
      simp only [Array.getElem_ofFn, Array.getElem_extract]
      rw [kemHopCt_extract kem path seeds i hi (by omega)]
      split_ifs <;> first | rfl | omega
  · apply Array.ext
    · simp
    · intro i h1 h2
      have hi : 1 + i < path.size := by
        simp only [Array.size_ofFn, hps] at h1
        omega
      simp only [Array.getElem_ofFn, Array.getElem_extract]
      rw [kemHopKeys_extract kem kdfS path seeds i hi (by omega)]
      split_ifs <;> first | rfl | omega
  · congr 1
    refine tailPadOf_congr geom _ _ _ fun m hm => ?_
    show (if m = j then _ else _) = headerKeystream streamS geom _
    rw [hget _ m (by omega)]
    split_ifs <;> rfl

/-! ## The filler of a later layer, with one hop's keystream given

The filler of the layer for a position past the first is the sender's filler followed by blocks
of every remaining hop's header keystream (`tailFiller`). So the layer with one hop's keystream
given needs its filler computed from that keystream. -/

/-- `tailFiller` for a path of `size` hops, from each hop's header keystream. -/
def tailFillerOf (ks : ℕ → ByteArray) (size : ℕ) (filler : ByteArray) : ByteArray :=
  (if geom.nrHops > size then filler else ByteArray.empty) ++ tailPadOf geom ks (size - 1)

/-- The filler of the layer for position `i`, with hop `j`'s header keystream `U` given. -/
def fillerAtF (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (filler : ByteArray)
    (j : ℕ) (U : ByteArray) : ℕ → ByteArray
  | 0 => filler
  | i + 1 => tailFillerOf geom
      (fun k => if i + k = j then U
        else headerKeystream streamS geom (kemHopKeys kem kdfS hops seeds (i + k)))
      (hops.size - i) (fillerAtF hops seeds filler j U i)

/-- With the keystream of the keys that hop `j`'s seed gives, `fillerAtF` is the filler built
from the seeds, for a layer up to hop `j`'s. The seeds may differ at `j`, which `fillerAtF` does
not read. -/
theorem fillerAtF_real (hops : Array PathHop) (seeds seeds' : Array (Vector UInt8 32))
    (filler : ByteArray) (j : ℕ) (c ss : ByteArray) (hj : j < hops.size)
    (hsz : seeds'.size = hops.size)
    (henc : kemEncap kem (hops[j]!).publicKey (seeds'[j]!) = .ok (c, ss))
    (hagree : ∀ k, k ≠ j → seeds[k]! = seeds'[k]!) (i : ℕ) (hi : i ≤ j) :
    fillerAtF kem kdfS streamS geom hops seeds filler j
        (ksOf streamS geom (keyTuple (deriveHopKeys kdfS ss))) i
      = RSOR.fillerAt kem kdfS streamS geom hops seeds' filler i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [fillerAtF, RSOR.fillerAt]
    rw [ih (by omega)]
    unfold tailFillerOf tailFiller
    rw [show (hops.extract i hops.size).size = hops.size - i by simp]
    congr 1
    rw [← tailPadOf_kemHopKeys kem kdfS streamS geom]
    apply tailPadOf_congr
    intro m hm
    have hlt : i + m < hops.size := by omega
    have hk : kemHopKeys kem kdfS (hops.extract i hops.size) (seeds'.extract i seeds'.size) m
        = kemHopKeys kem kdfS hops seeds' (i + m) := by
      unfold kemHopKeys
      rw [getElem!_extract_from _ _ _ hlt, getElem!_extract_from _ _ _ (by omega)]
    show (if i + m = j then _ else _) = headerKeystream streamS geom
      (kemHopKeys kem kdfS (hops.extract i hops.size) (seeds'.extract i seeds'.size) m)
    rw [hk]
    split_ifs with hij
    · have : kemHopKeys kem kdfS hops seeds' (i + m) = deriveHopKeys kdfS ss := by
        rw [hij]
        unfold kemHopKeys
        rw [henc]
      rw [this]
      rfl
    · have : kemHopKeys kem kdfS hops seeds (i + m)
          = kemHopKeys kem kdfS hops seeds' (i + m) := by
        unfold kemHopKeys
        rw [hagree _ hij]
      rw [this]

/-- The keyed filler of the layer for position `i` has one block for each slot the path does
not use, and one for each hop before `i`. -/
theorem fillerAtF_size (hrouting : geom.routingInfoLength
      = geom.perHopRoutingInfoLength * geom.nrHops)
    (hops : Array PathHop) (seeds : Array (Vector UInt8 32)) (filler : ByteArray) (j : ℕ)
    (U : ByteArray) (hlen : hops.size ≤ geom.nrHops)
    (hf : filler.size = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)
    (hU : U.size = geom.routingInfoLength + geom.perHopRoutingInfoLength) (i : ℕ)
    (hi : i < hops.size) :
    (fillerAtF kem kdfS streamS geom hops seeds filler j U i).size
      = (geom.nrHops - hops.size + i) * geom.perHopRoutingInfoLength := by
  induction i with
  | zero => simpa [fillerAtF] using hf
  | succ i ih =>
    have hpad : (tailPadOf geom (fun k => if i + k = j then U
        else headerKeystream streamS geom (kemHopKeys kem kdfS hops seeds (i + k)))
        (hops.size - i - 1)).size = geom.perHopRoutingInfoLength := by
      refine tailPadOf_size geom _ _ (fun m _ => ?_) ?_
      · show (if i + m = j then U else _).size = _
        split_ifs
        · exact hU
        · exact streamS.keystream_size _ _ _
      · rw [Nat.sub_add_cancel (by omega), hrouting,
          Nat.mul_comm geom.perHopRoutingInfoLength]
        exact le_trans (Nat.mul_le_mul_right _ (by omega : hops.size - i ≤ geom.nrHops))
          (Nat.le_add_right _ _)
    rw [fillerAtF, tailFillerOf, ByteArray.size_append, hpad]
    split_ifs with hc
    · rw [ih (by omega), ← Nat.succ_mul]
      congr 1
    · rw [show geom.nrHops - hops.size + (i + 1) = 0 + 1 by omega, Nat.one_mul]
      exact Nat.zero_add _

theorem extract_extract_one {α : Type} (a : Array α) (i : ℕ) :
    (a.extract i a.size).extract 1 (a.extract i a.size).size = a.extract (i + 1) a.size := by
  apply Array.ext
  · simp
    omega
  · intro k h1 h2
    simp only [Array.getElem_extract]
    congr 1
    omega

theorem extract_getElem!_congr {α : Type} [Inhabited α] (a b : Array α) (i m : ℕ)
    (hsz : a.size = b.size) (h : a[i + m]? = b[i + m]?) :
    (a.extract i a.size)[m]! = (b.extract i b.size)[m]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getD_eq_getD_getElem?, Array.getElem?_extract, Array.getElem?_extract, hsz, h]

/-- `RSOR.layer` with hop `j`'s ciphertext `c` and keys `t` given: the layer for position
`i`. -/
def layerPK (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (c : ByteArray) (t : KeyTuple) (i : ℕ) : Except String ByteArray :=
  let seeds := d.1.toArray.extract 0 hops.size
  packetK kem cipher macS kdfS streamS geom (seeds.extract i seeds.size)
    (fillerAtF kem kdfS streamS geom hops seeds
      ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
      j (ksOf streamS geom t) i)
    (hops.extract i hops.size) payload (j - i) c t

/-- Whether a keyed layer can be built does not depend on the ciphertext and keys given. -/
theorem layerPK_ok_congr (hops : Array PathHop) (d : RSOR.Draw geom) (payload pkt : ByteArray)
    (j : ℕ) (c c' : ByteArray) (t t' : KeyTuple) (i : ℕ)
    (h : layerPK kem cipher macS kdfS streamS geom hops d payload j c t i = .ok pkt) :
    ∃ pkt', layerPK kem cipher macS kdfS streamS geom hops d payload j c' t' i = .ok pkt' :=
  packetK_ok_congr kem cipher macS kdfS streamS geom _ _ _ _ _ payload pkt (j - i) c c' t t' h

set_option maxHeartbeats 1000000 in
/-- **Each hop before the keyed one forwards the next keyed layer.** -/
theorem layerPK_step (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload pkt privKey : ByteArray) (j : ℕ)
    (c : ByteArray) (t : KeyTuple) (i : ℕ) (hi : i < j) (hj : j < hops.size)
    (hlen : hops.size ≤ geom.nrHops) (hc : c.size = kem.ciphertextSize)
    (henc : ∀ m, m < hops.size → m ≠ j →
      ∃ ct ss, kemEncap kem (hops[m]!).publicKey (d.1.toArray[m]!) = .ok (ct, ss))
    (hrel : kem.Reliable (kem.stateFromSeed d.1.toArray[i]!))
    (hpp : kemSelfPublicKeyBytes kem privKey = (hops[i]!).publicKey)
    (hcmdnn : ∀ x ∈ (hops[i]!).commands, x ≠ RoutingCommand.null)
    (hcmdnh : ∀ x ∈ (hops[i]!).commands, ∀ id m, x ≠ RoutingCommand.nextNodeHop id m)
    (hpk : layerPK kem cipher macS kdfS streamS geom hops d payload j c t i = .ok pkt) :
    ∃ (replayTag mac : Vector UInt8 32) (fwd : Vector UInt8 pkt.size),
      unwrapKEM kem cipher macS kdfS streamS geom privKey pkt
        = .ok (none, replayTag,
            (hops[i]!).commands ++ [RoutingCommand.nextNodeHop (hops[i + 1]!).id mac],
            some fwd) ∧
      layerPK kem cipher macS kdfS streamS geom hops d payload j c t (i + 1)
        = .ok (ofVector fwd) ∧
      pkt = wrapHop kem cipher macS streamS geom (hops.extract i hops.size)
        (kemHopCt kem (hops.extract i hops.size)
          ((d.1.toArray.extract 0 hops.size).extract i (d.1.toArray.extract 0 hops.size).size) 0)
        (kemHopKeys kem kdfS (hops.extract i hops.size)
          ((d.1.toArray.extract 0 hops.size).extract i (d.1.toArray.extract 0 hops.size).size) 0)
        (ofVector fwd) := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  unfold layerPK at hpk ⊢
  dsimp only at hpk ⊢
  obtain ⟨S, hSdef⟩ : ∃ S, S = d.1.toArray.extract 0 hops.size := ⟨_, rfl⟩
  rw [← hSdef] at hpk ⊢
  have hSsz : S.size = hops.size := by
    rw [hSdef]
    simp
    omega
  have hSget : ∀ m, m < hops.size → S[m]! = d.1.toArray[m]! := fun m hm => by
    rw [hSdef, getElem!_extract_zero _ _ _ hm (by rw [Vector.size_toArray]; exact hlen)]
  have hpi : (hops.extract i hops.size).size = hops.size - i := by simp
  have hsi : (S.extract i S.size).size = hops.size - i := by simp [hSsz]
  have hpget : ∀ m, i + m < hops.size → (hops.extract i hops.size)[m]! = hops[i + m]! :=
    fun m hm => getElem!_extract_from hops i m hm
  have hsget : ∀ m, i + m < hops.size → (S.extract i S.size)[m]! = S[i + m]! :=
    fun m hm => getElem!_extract_from S i m (by omega)
  have hF : ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) *
      geom.perHopRoutingInfoLength)).size
      = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength := by
    have hle : (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength
        ≤ geom.perHopRoutingInfoLength * geom.nrHops := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector, hrouting]
    omega
  obtain ⟨replayTag, mac, fwd, hun, hfwd, hwrap⟩ := packetK_step kem cipher macS kdfS streamS geom
    hvalid hmactag h16 (S.extract i S.size) _ (hops.extract i hops.size) payload pkt privKey
    (j - i) c t
    (by omega) (by rw [hpi]; omega) (by rw [hpi]; omega) (by rw [hpi, hsi])
    (fun _ => by
      rw [fillerAtF_size kem kdfS streamS geom hrouting hops S _ j (ksOf streamS geom t) hlen hF
        (show (ksOf streamS geom t).size = _ from streamS.keystream_size _ _ _) i (by omega),
        hpi]
      congr 1
      omega)
    hc
    (fun m hm hmj => by
      rw [hpi] at hm
      rw [hpget m (by omega), hsget m (by omega), hSget _ (by omega)]
      exact henc (i + m) (by omega) (by omega))
    (by rw [hsget 0 (by omega), Nat.add_zero, hSget i (by omega)]; exact hrel)
    (by rw [hpget 0 (by omega), Nat.add_zero]; exact hpp)
    (by rw [hpget 0 (by omega), Nat.add_zero]; exact hcmdnn)
    (by rw [hpget 0 (by omega), Nat.add_zero]; exact hcmdnh) hpk
  rw [hpget 0 (by omega), hpget 1 (by omega), Nat.add_zero] at hun
  refine ⟨replayTag, mac, fwd, hun, ?_, hwrap⟩
  rw [extract_extract_one, extract_extract_one, hpi] at hfwd
  have hfill : fillerAtF kem kdfS streamS geom hops S
        ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
        j (ksOf streamS geom t) (i + 1)
      = (if geom.nrHops > hops.size - i then fillerAtF kem kdfS streamS geom hops S
            ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
            j (ksOf streamS geom t) i else ByteArray.empty)
        ++ tailPadOf geom (fun k => if k = j - i then ksOf streamS geom t
            else headerKeystream streamS geom
              (kemHopKeys kem kdfS (hops.extract i hops.size) (S.extract i S.size) k))
          (hops.size - i - 1) := by
    rw [fillerAtF, tailFillerOf]
    congr 1
    refine tailPadOf_congr geom _ _ _ fun m hm => ?_
    show (if i + m = j then _ else _) = (if m = j - i then _ else _)
    have hk : kemHopKeys kem kdfS (hops.extract i hops.size) (S.extract i S.size) m
        = kemHopKeys kem kdfS hops S (i + m) := by
      unfold kemHopKeys
      rw [hpget m (by omega), hsget m (by omega)]
    rw [hk]
    split_ifs <;> first | rfl | omega
  rw [hfill, show j - (i + 1) = j - i - 1 by omega]
  exact hfwd

/-- Layer `i` from layer `i + n`: `wrapHop` once for each hop from `i` on, with the ciphertexts
and keys the seeds give. -/
def wrapUp (hops : Array PathHop) (d : RSOR.Draw geom) : ℕ → ℕ → ByteArray → ByteArray
  | _, 0, L => L
  | i, n + 1, L => wrapHop kem cipher macS streamS geom (hops.extract i hops.size)
      (kemHopCt kem (hops.extract i hops.size)
        ((d.1.toArray.extract 0 hops.size).extract i (d.1.toArray.extract 0 hops.size).size) 0)
      (kemHopKeys kem kdfS (hops.extract i hops.size)
        ((d.1.toArray.extract 0 hops.size).extract i (d.1.toArray.extract 0 hops.size).size) 0)
      (wrapUp hops d (i + 1) n L)

/-- **A keyed layer before the keyed hop is that hop's layer, wrapped.** The hops in between
have keys with private keys, their seeds do not make the KEM fail, and none carries commands of
its own that end a path. -/
theorem layerPK_chain (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ) (c : ByteArray)
    (t : KeyTuple) (hj : j < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hc : c.size = kem.ciphertextSize)
    (henc : ∀ m, m < hops.size → m ≠ j →
      ∃ ct ss, kemEncap kem (hops[m]!).publicKey (d.1.toArray[m]!) = .ok (ct, ss))
    (hrel : ∀ m, m < j → kem.Reliable (kem.stateFromSeed d.1.toArray[m]!))
    (hsk : ∀ m, m < j → ∃ privKey, kemSelfPublicKeyBytes kem privKey = (hops[m]!).publicKey)
    (hcmdnn : ∀ m, m < j → ∀ x ∈ (hops[m]!).commands, x ≠ RoutingCommand.null)
    (hcmdnh : ∀ m, m < j → ∀ x ∈ (hops[m]!).commands, ∀ id b,
      x ≠ RoutingCommand.nextNodeHop id b)
    (n i : ℕ) (hi : i + n = j) (pkt : ByteArray)
    (hpk : layerPK kem cipher macS kdfS streamS geom hops d payload j c t i = .ok pkt) :
    ∃ L, layerPK kem cipher macS kdfS streamS geom hops d payload j c t j = .ok L ∧
      pkt = wrapUp kem cipher macS kdfS streamS geom hops d i n L := by
  induction n generalizing i pkt with
  | zero =>
    obtain rfl : i = j := by omega
    exact ⟨pkt, hpk, rfl⟩
  | succ n ih =>
    obtain ⟨privKey, hpp⟩ := hsk i (by omega)
    obtain ⟨-, -, fwd, -, hfwd, hwrap⟩ := layerPK_step kem cipher macS kdfS streamS geom hvalid
      hmactag h16 hops d payload
      pkt privKey j c t i (by omega) hj hlen hc henc (hrel i (by omega)) hpp
      (hcmdnn i (by omega)) (hcmdnh i (by omega)) hpk
    obtain ⟨L, hL, heq⟩ := ih (i + 1) (by omega) (ofVector fwd) hfwd
    exact ⟨L, hL, by rw [hwrap, heq]; rfl⟩

/-- The layer for a position past the keyed hop: built from the seeds, with the keyed filler. -/
def layerPast (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (U : ByteArray) (i : ℕ) : Except String ByteArray :=
  let seeds := d.1.toArray.extract 0 hops.size
  newKEMPacket kem cipher macS kdfS streamS geom (seeds.extract i seeds.size)
    (fillerAtF kem kdfS streamS geom hops seeds
      ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
      j U i)
    (hops.extract i hops.size) payload

set_option maxHeartbeats 2000000 in
/-- **What the keyed hop does with its layer, before the end of the path.** With the keys `t`
it accepts the layer, reads its commands and the next hop's name, and forwards the next layer,
which is built from the seeds and depends on `t` through its filler only. Its own layer is, in
closed form, its ciphertext, its routing info under its keystream, one tag over both, and the
next layer's payload under its payload key. -/
theorem layerPK_self (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload pkt privKey : ByteArray) (j : ℕ)
    (c : ByteArray) (t : KeyTuple) (s : Vector UInt8 32) (ss : ByteArray)
    (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hencj : kemEncap kem (hops[j]!).publicKey s = .ok (c, ss))
    (hrel : kem.Reliable (kem.stateFromSeed s))
    (henc : ∀ m, m < hops.size → m ≠ j →
      ∃ ct ss, kemEncap kem (hops[m]!).publicKey (d.1.toArray[m]!) = .ok (ct, ss))
    (hpp : kemSelfPublicKeyBytes kem privKey = (hops[j]!).publicKey)
    (hcmdnn : ∀ x ∈ (hops[j]!).commands, x ≠ RoutingCommand.null)
    (hcmdnh : ∀ x ∈ (hops[j]!).commands, ∀ id m, x ≠ RoutingCommand.nextNodeHop id m)
    (hpk : layerPK kem cipher macS kdfS streamS geom hops d payload j c t j = .ok pkt) :
    ∃ (replayTag mac : Vector UInt8 32) (fwd : Vector UInt8 pkt.size) (frag : ByteArray),
      procKeys kem cipher macS streamS geom t pkt
        = some (none, replayTag,
            (hops[j]!).commands ++ [RoutingCommand.nextNodeHop (hops[j + 1]!).id mac],
            some (ofVector fwd)) ∧
      layerPast kem cipher macS kdfS streamS geom hops d payload j (ksOf streamS geom t) (j + 1)
        = .ok (ofVector fwd) ∧
      kemRiFragment kem geom (hops.extract j hops.size)
          #[ByteArray.empty, (ofVector fwd).extract 2 (2 + kem.ciphertextSize)]
          ((ofVector fwd).extract (2 + kem.ciphertextSize + geom.routingInfoLength)
            (2 + kem.ciphertextSize + geom.routingInfoLength + macLength))
          (hops.extract j hops.size).size 0 = .ok frag ∧
      pkt = layerIn cipher macS c t.1 t.2.1 t.2.2.1
        ((ksOf streamS geom t).extract 0 geom.routingInfoLength)
        (frag ++ (ofVector fwd).extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength))
        ((ofVector fwd).extract (payloadOffset kem geom) pkt.size) := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hcsz : c.size = kem.ciphertextSize := kemEncap_size kem _ _ c ss hencj
  have hkt := keyTuple_keysKDF t ss
  unfold layerPK at hpk
  unfold layerPast
  dsimp only at hpk ⊢
  obtain ⟨S, hSdef⟩ : ∃ S, S = d.1.toArray.extract 0 hops.size := ⟨_, rfl⟩
  rw [← hSdef] at hpk ⊢
  have hSsz : S.size = hops.size := by
    rw [hSdef]
    simp
    omega
  have hSget : ∀ m, m < hops.size → S[m]! = d.1.toArray[m]! := fun m hm => by
    rw [hSdef, getElem!_extract_zero _ _ _ hm (by rw [Vector.size_toArray]; exact hlen)]
  have hpi : (hops.extract j hops.size).size = hops.size - j := by simp
  have hsi : (S.extract j S.size).size = hops.size - j := by simp [hSsz]
  have hpget : ∀ m, j + m < hops.size → (hops.extract j hops.size)[m]! = hops[j + m]! :=
    fun m hm => getElem!_extract_from hops j m hm
  have hsget : ∀ m, j + m < hops.size → (S.extract j S.size)[m]! = S[j + m]! :=
    fun m hm => getElem!_extract_from S j m (by omega)
  have hF : ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) *
      geom.perHopRoutingInfoLength)).size
      = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength := by
    have hle : (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength
        ≤ geom.perHopRoutingInfoLength * geom.nrHops := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector, hrouting]
    omega
  have hget : ∀ {α : Type} [Inhabited α] (f : Fin (hops.extract j hops.size).size → α) (i : ℕ)
      (hi : i < (hops.extract j hops.size).size), (Array.ofFn f)[i]! = f ⟨i, hi⟩ :=
    fun f i hi => by
      rw [getElem!_pos _ i (by simpa using hi)]
      simp only [Array.getElem_ofFn]
  rw [Nat.sub_self] at hpk
  unfold packetK at hpk
  obtain ⟨KE, hKE⟩ : ∃ KE : Array ByteArray, KE = Array.ofFn
      (fun i : Fin (hops.extract j hops.size).size => if i.val = 0 then c
        else kemHopCt kem (hops.extract j hops.size) (S.extract j S.size) i) := ⟨_, rfl⟩
  rw [← hKE] at hpk
  have hKE0 : KE[0]! = c := by
    rw [hKE, hget _ 0 (by rw [hpi]; omega)]
    rfl
  -- The keyed hop's keys, as the output of the key derivation that returns `t`.
  obtain ⟨KS', hKS'⟩ : ∃ KS' : Array HopKeys, KS' = Array.ofFn
      (fun i : Fin (hops.extract j hops.size).size => if i.val = 0
        then deriveHopKeys (keysKDF t) ss
        else kemHopKeys kem kdfS (hops.extract j hops.size) (S.extract j S.size) i) := ⟨_, rfl⟩
  have hfield : ∀ i : ℕ, keyTuple (KS'[i]!) = keyTuple ((Array.ofFn
      (fun i : Fin (hops.extract j hops.size).size => if i.val = 0 then hopKeysOf t
        else kemHopKeys kem kdfS (hops.extract j hops.size) (S.extract j S.size) i))[i]!) := by
    intro i
    by_cases hi : i < (hops.extract j hops.size).size
    · rw [hKS', hget _ i hi, hget _ i hi]
      dsimp only
      split_ifs
      · exact hkt
      · rfl
    · rw [hKS', getElem!_neg _ i (by simpa using hi), getElem!_neg _ i (by simpa using hi)]
  have hswap := (newKEMPacketFrom_congr kem cipher macS streamS geom _ KS' _ _ _ payload
    (fun i => congrArg (·.2.2.1) (hfield i)) (fun i => congrArg (·.2.2.2) (hfield i))
    (fun i => congrArg (·.2.1) (hfield i)) (fun i => congrArg (·.1) (hfield i))).trans hpk
  have hK0 : KS'[0]! = deriveHopKeys (keysKDF t) ss := by
    rw [hKS', hget _ 0 (by rw [hpi]; omega)]
    rfl
  have hksize : ∀ i (hi : i < KE.size), (KE[i]'hi).size = kem.ciphertextSize := by
    intro i hi
    have hi' : i < hops.size - j := by
      rw [hKE] at hi
      simpa using hi
    rw [← getElem!_pos KE i hi, hKE, hget _ i (by rw [hpi]; exact hi')]
    dsimp only
    split_ifs with hi0
    · exact hcsz
    · obtain ⟨ct, ss', he⟩ := henc (j + i) (by omega) (by omega)
      unfold kemHopCt
      rw [hpget i (by omega), hsget i (by omega), hSget _ (by omega), he]
      exact kemEncap_size kem _ _ ct ss' he
  have hfsz : geom.nrHops > (hops.extract j hops.size).size →
      (fillerAtF kem kdfS streamS geom hops S
        ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
        j (ksOf streamS geom t) j).size
        = (geom.nrHops - (hops.extract j hops.size).size) * geom.perHopRoutingInfoLength :=
    fun _ => by
      rw [fillerAtF_size kem kdfS streamS geom hrouting hops S _ j (ksOf streamS geom t) hlen hF
        (show (ksOf streamS geom t).size = _ from streamS.keystream_size _ _ _) j (by omega),
        hpi]
      congr 1
      omega
  have hkey : ∃ seed ss', kem.Reliable (kem.stateFromSeed seed) ∧
      kemEncap kem ((hops.extract j hops.size)[0]!).publicKey seed = Except.ok (KE[0]!, ss') ∧
      KS'[0]! = deriveHopKeys (keysKDF t) ss' := by
    refine ⟨s, ss, hrel, ?_, hK0⟩
    rw [hKE0, hpget 0 (by omega), Nat.add_zero]
    exact hencj
  have hpp' : kemSelfPublicKeyBytes kem privKey = ((hops.extract j hops.size)[0]!).publicKey := by
    rw [hpget 0 (by omega), Nat.add_zero]
    exact hpp
  have hnn' : ∀ x ∈ ((hops.extract j hops.size)[0]!).commands, x ≠ RoutingCommand.null := by
    rw [hpget 0 (by omega), Nat.add_zero]
    exact hcmdnn
  have hnh' : ∀ x ∈ ((hops.extract j hops.size)[0]!).commands, ∀ id m,
      x ≠ RoutingCommand.nextNodeHop id m := by
    rw [hpget 0 (by omega), Nat.add_zero]
    exact hcmdnh
  obtain ⟨h2, -⟩ := newKEMPacketFrom_unwrapKEM kem cipher macS (keysKDF t) streamS geom hvalid
    hmactag h16 KE KS' _ (hops.extract j hops.size) payload pkt privKey (by rw [hpi]; omega) hfsz
    (by rw [hKE]; simp) (by rw [hKS']; simp) hksize hpp' hkey hnn' hnh' hswap
  obtain ⟨replayTag, mac, fwd, hun, hfwd⟩ := h2 (by rw [hpi]; omega)
  obtain ⟨replayTag', cmds', fwd', frag, hun', hfrag, hpkt⟩ := newKEMPacketFrom_layer kem cipher
    macS (keysKDF t) streamS geom hvalid hmactag h16 KE KS' _ (hops.extract j hops.size) payload pkt
    privKey (by rw [hpi]; omega) (by rw [hpi]; omega) hfsz (by rw [hKE]; simp) hksize hpp' hkey
        hnn' hnh'
    hswap
  have hff : fwd' = fwd := by
    have := hun'.symm.trans hun
    injection this with this
    injection this with _ this
    injection this with _ this
    injection this with _ this
    injection this
  rw [hff] at hfrag hpkt
  rw [hpget 0 (by omega), hpget 1 (by omega), Nat.add_zero] at hun
  refine ⟨replayTag, mac, fwd, frag, ?_, ?_, hfrag, ?_⟩
  · refine procWith_keysKDF kem cipher macS streamS geom t (kemDecap kem privKey) pkt _ ?_
    unfold procWith
    rw [show unwrapKEMWith kem cipher macS (keysKDF t) streamS geom (kemDecap kem privKey) pkt
      = _ from hun]
    rfl
  · rw [extract_extract_one, hpi] at hfwd
    have hfill : fillerAtF kem kdfS streamS geom hops S
          ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
          j (ksOf streamS geom t) (j + 1)
        = (if geom.nrHops > hops.size - j then fillerAtF kem kdfS streamS geom hops S
              ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
              j (ksOf streamS geom t) j else ByteArray.empty)
          ++ tailPadOf geom (fun i => headerKeystream streamS geom (KS'[i]!))
            (hops.size - j - 1) := by
      rw [fillerAtF, tailFillerOf]
      congr 1
      refine tailPadOf_congr geom _ _ _ fun m hm => ?_
      show (if j + m = j then _ else _) = headerKeystream streamS geom (KS'[m]!)
      rw [hKS', hget _ m (by rw [hpi]; omega)]
      dsimp only
      have hk : kemHopKeys kem kdfS (hops.extract j hops.size) (S.extract j S.size) m
          = kemHopKeys kem kdfS hops S (j + m) := by
        unfold kemHopKeys
        rw [hpget m (by omega), hsget m (by omega)]
      by_cases hm0 : m = 0
      · subst hm0
        simp only [Nat.add_zero, ↓reduceIte]
        unfold headerKeystream ksOf
        rw [show (deriveHopKeys (keysKDF t) ss).headerEncryption = t.2.2.2 from
            congrArg (·.2.2.2) hkt,
          show (deriveHopKeys (keysKDF t) ss).headerEncryptionIV = t.2.1 from
            congrArg (·.2.1) hkt]
      · simp only [show ¬ (j + m = j) by omega, hm0, ↓reduceIte, hk]
    rw [hfill, newKEMPacket_eq_newKEMPacketFrom kem cipher macS kdfS streamS geom
      (S.extract (j + 1) S.size) _ (hops.extract (j + 1) hops.size) payload
      (KE.extract 1 KE.size) (KS'.extract 1 KS'.size) (by simp; omega) (by simp; omega) (by
          simp [hSsz])
      (by
        intro _
        rw [← hfill, fillerAtF_size kem kdfS streamS geom hrouting hops S _ j
          (ksOf streamS geom t) hlen hF
          (show (ksOf streamS geom t).size = _ from streamS.keystream_size _ _ _) (j + 1) hj]
        congr 1
        simp
        omega)
      (by rw [hKE]; simp; omega) (by rw [hKS']; simp; omega)
      (by
        intro i hi
        have hi' : j + 1 + i < hops.size := by
          simp at hi
          omega
        obtain ⟨ct, ss', he⟩ := henc (j + 1 + i) hi' (by omega)
        refine ⟨ct, ss', ?_, ?_, ?_⟩
        · rw [getElem!_extract_from hops (j + 1) i hi',
            getElem!_extract_from S (j + 1) i (by omega), hSget _ hi']
          exact he
        · rw [getElem!_extract_from KE 1 i (by rw [hKE]; simp; omega), hKE,
            hget _ (1 + i) (by rw [hpi]; omega)]
          simp only [show ¬ (1 + i = 0) by omega, ↓reduceIte]
          unfold kemHopCt
          rw [hpget _ (by omega), hsget _ (by omega), hSget _ (by omega),
            show j + (1 + i) = j + 1 + i by omega, he]
        · rw [getElem!_extract_from KS' 1 i (by rw [hKS']; simp; omega), hKS',
            hget _ (1 + i) (by rw [hpi]; omega)]
          simp only [show ¬ (1 + i = 0) by omega, ↓reduceIte]
          unfold kemHopKeys
          rw [hpget _ (by omega), hsget _ (by omega), hSget _ (by omega),
            show j + (1 + i) = j + 1 + i by omega, he])]
    exact hfwd
  · refine hpkt.trans ?_
    rw [hKE0, hK0]
    unfold ksOf
    rw [show (deriveHopKeys (keysKDF t) ss).headerEncryption = t.2.2.2 from
        congrArg (·.2.2.2) hkt,
      show (deriveHopKeys (keysKDF t) ss).headerEncryptionIV = t.2.1 from congrArg (·.2.1) hkt,
      show (deriveHopKeys (keysKDF t) ss).payloadEncryption = t.1 from congrArg (·.1) hkt,
      show (deriveHopKeys (keysKDF t) ss).headerMAC = t.2.2.1 from congrArg (·.2.2.1) hkt]

/-- The three parts of a byte string written as `P ++ T ++ Q`. -/
theorem three_parts (P T Q : ByteArray) :
    (P ++ T ++ Q).extract 0 P.size = P ∧
      (P ++ T ++ Q).extract P.size (P.size + T.size) = T ∧
      (P ++ T ++ Q).extract (P.size + T.size) (P ++ T ++ Q).size = Q := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Util.Bytes.extract_append_of_le _ _ (by rw [ByteArray.size_append]; omega)]
    exact Util.Bytes.extract_append_left _ _
  · rw [Util.Bytes.extract_append_of_le _ _ (by rw [ByteArray.size_append])]
    exact Util.Bytes.extract_append_right _ _
  · rw [Util.Bytes.extract_append_of_ge _ _ (by rw [ByteArray.size_append]),
      ByteArray.size_append, ByteArray.size_append, ← ByteArray.size_append,
      Nat.sub_self, Nat.add_sub_cancel_left]
    exact ByteArray.extract_zero_size

/-- The bytes of the keyed hop's layer in front of its tag, before the end of the path: its
ciphertext and its routing info under its keystream `U`. They do not use its MAC key. -/
def relayFront (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (c U : ByteArray) : ByteArray :=
  match layerPast kem cipher macS kdfS streamS geom hops d payload j U (j + 1) with
  | .ok fwd => v0AD ++ c ++ xorBytes
      ((match kemRiFragment kem geom (hops.extract j hops.size)
          #[ByteArray.empty, fwd.extract 2 (2 + kem.ciphertextSize)]
          (fwd.extract (2 + kem.ciphertextSize + geom.routingInfoLength)
            (2 + kem.ciphertextSize + geom.routingInfoLength + macLength))
          (hops.extract j hops.size).size 0 with
        | .ok f => f
        | .error _ => ByteArray.empty)
        ++ fwd.extract (2 + kem.ciphertextSize)
          (2 + kem.ciphertextSize + geom.routingInfoLength - geom.perHopRoutingInfoLength))
      (U.extract 0 geom.routingInfoLength)
  | .error _ => ByteArray.empty

/-- The bytes of the keyed hop's layer behind its tag, before the end of the path: the next
layer's payload under its payload encryption `encf`. -/
def relayBack (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (U : ByteArray) (encf : ByteArray → ByteArray) : ByteArray :=
  match layerPast kem cipher macS kdfS streamS geom hops d payload j U (j + 1) with
  | .ok fwd => encf (fwd.extract (payloadOffset kem geom) fwd.size)
  | .error _ => ByteArray.empty

set_option maxHeartbeats 1000000 in
/-- **The keyed hop's layer in three parts, before the end of the path**: the bytes in front,
their tag under its MAC key, and the payload behind. Only the tag uses the MAC key. -/
theorem layerPK_self_parts (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload pkt privKey : ByteArray) (j : ℕ)
    (c : ByteArray) (t : KeyTuple) (s : Vector UInt8 32) (ss : ByteArray)
    (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hencj : kemEncap kem (hops[j]!).publicKey s = .ok (c, ss))
    (hrel : kem.Reliable (kem.stateFromSeed s))
    (henc : ∀ m, m < hops.size → m ≠ j →
      ∃ ct ss, kemEncap kem (hops[m]!).publicKey (d.1.toArray[m]!) = .ok (ct, ss))
    (hpp : kemSelfPublicKeyBytes kem privKey = (hops[j]!).publicKey)
    (hcmdnn : ∀ x ∈ (hops[j]!).commands, x ≠ RoutingCommand.null)
    (hcmdnh : ∀ x ∈ (hops[j]!).commands, ∀ id m, x ≠ RoutingCommand.nextNodeHop id m)
    (hpk : layerPK kem cipher macS kdfS streamS geom hops d payload j c t j = .ok pkt) :
    pkt = relayFront kem cipher macS kdfS streamS geom hops d payload j c (ksOf streamS geom t)
        ++ ofVector (macS.mac (ofVector t.2.2.1)
          (relayFront kem cipher macS kdfS streamS geom hops d payload j c (ksOf streamS geom t)))
        ++ relayBack kem cipher macS kdfS streamS geom hops d payload j (ksOf streamS geom t)
            (encOf cipher t) ∧
      (relayFront kem cipher macS kdfS streamS geom hops d payload j c (ksOf streamS geom t)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength := by
  obtain ⟨replayTag, mac, fwd, frag, hproc, hpast, hfrag, hpkt⟩ := layerPK_self kem cipher macS
      kdfS streamS geom hvalid
    hmactag h16 hops d payload pkt privKey j c t s ss hj hlen hencj hrel henc hpp hcmdnn hcmdnh
    hpk
  have hsz := procKeys_size kem cipher macS streamS geom t pkt _ hproc
  have hfs : (ofVector fwd).size = pkt.size := Util.Bytes.size_ofVector fwd
  have hform : pkt = relayFront kem cipher macS kdfS streamS geom hops d payload j c (ksOf
      streamS geom t)
      ++ ofVector (macS.mac (ofVector t.2.2.1)
        (relayFront kem cipher macS kdfS streamS geom hops d payload j c (ksOf streamS geom t)))
      ++ relayBack kem cipher macS kdfS streamS geom hops d payload j (ksOf streamS geom t)
          (encOf cipher t) := by
    refine hpkt.trans ?_
    unfold relayFront relayBack layerIn encOf
    rw [hpast]
    dsimp only
    rw [hfrag, hfs, ByteArray.append_empty]
  refine ⟨hform, ?_⟩
  have hlen' := congrArg ByteArray.size hform
  have hback : (relayBack kem cipher macS kdfS streamS geom hops d payload j (ksOf streamS geom
      t) (encOf cipher t)).size
      = pkt.size - payloadOffset kem geom := by
    unfold relayBack encOf
    rw [hpast]
    dsimp only
    rw [cipher.encrypt_size, ByteArray.size_extract, hfs]
    omega
  rw [ByteArray.size_append, ByteArray.size_append, Util.Bytes.size_ofVector, hmactag, hback]
    at hlen'
  unfold payloadOffset at hlen' hsz
  have : macLength = 32 := rfl
  omega

set_option maxHeartbeats 2000000 in
/-- **What the keyed hop does with its layer, at the end of the path.** With the keys `t` it
accepts the layer and gets its commands and the payload. Its layer is `pkt1` on its ciphertext
and keys. -/
theorem layerPK_self_last (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload pkt privKey : ByteArray) (j : ℕ)
    (c : ByteArray) (t : KeyTuple) (s : Vector UInt8 32) (ss : ByteArray)
    (hj : j + 1 = hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hencj : kemEncap kem (hops[j]!).publicKey s = .ok (c, ss))
    (hrel : kem.Reliable (kem.stateFromSeed s))
    (hpp : kemSelfPublicKeyBytes kem privKey = (hops[j]!).publicKey)
    (hcmdnn : ∀ x ∈ (hops[j]!).commands, x ≠ RoutingCommand.null)
    (hcmdnh : ∀ x ∈ (hops[j]!).commands, ∀ id m, x ≠ RoutingCommand.nextNodeHop id m)
    (hpk : layerPK kem cipher macS kdfS streamS geom hops d payload j c t j = .ok pkt) :
    (∃ replayTag : Vector UInt8 32, procKeys kem cipher macS streamS geom t pkt
      = some (some (if hasSurbReply (hops[j]!).commands
          then (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload else payload),
        replayTag, (hops[j]!).commands, none)) ∧
    (∃ frag, kemRiFragment kem geom #[hops[j]!] #[c] ByteArray.empty 1 0 = .ok frag) ∧
    pkt = pkt1 kem cipher macS streamS geom c t
      (fillerAtF kem kdfS streamS geom hops (d.1.toArray.extract 0 hops.size)
        ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
        j (ksOf streamS geom t) j) (hops[j]!) payload := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hcsz : c.size = kem.ciphertextSize := kemEncap_size kem _ _ c ss hencj
  have hkt := keyTuple_keysKDF t ss
  unfold layerPK at hpk
  dsimp only at hpk ⊢
  obtain ⟨S, hSdef⟩ : ∃ S, S = d.1.toArray.extract 0 hops.size := ⟨_, rfl⟩
  rw [← hSdef] at hpk ⊢
  have hSsz : S.size = hops.size := by
    rw [hSdef]
    simp
    omega
  have hSget : ∀ m, m < hops.size → S[m]! = d.1.toArray[m]! := fun m hm => by
    rw [hSdef, getElem!_extract_zero _ _ _ hm (by rw [Vector.size_toArray]; exact hlen)]
  have hpi : (hops.extract j hops.size).size = hops.size - j := by simp
  have hsi : (S.extract j S.size).size = hops.size - j := by simp [hSsz]
  have hpget : ∀ m, j + m < hops.size → (hops.extract j hops.size)[m]! = hops[j + m]! :=
    fun m hm => getElem!_extract_from hops j m hm
  have hsget : ∀ m, j + m < hops.size → (S.extract j S.size)[m]! = S[j + m]! :=
    fun m hm => getElem!_extract_from S j m (by omega)
  have hF : ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) *
      geom.perHopRoutingInfoLength)).size
      = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength := by
    have hle : (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength
        ≤ geom.perHopRoutingInfoLength * geom.nrHops := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector, hrouting]
    omega
  have hget : ∀ {α : Type} [Inhabited α] (f : Fin (hops.extract j hops.size).size → α) (i : ℕ)
      (hi : i < (hops.extract j hops.size).size), (Array.ofFn f)[i]! = f ⟨i, hi⟩ :=
    fun f i hi => by
      rw [getElem!_pos _ i (by simpa using hi)]
      simp only [Array.getElem_ofFn]
  rw [Nat.sub_self] at hpk
  unfold packetK at hpk
  obtain ⟨KE, hKE⟩ : ∃ KE : Array ByteArray, KE = Array.ofFn
      (fun i : Fin (hops.extract j hops.size).size => if i.val = 0 then c
        else kemHopCt kem (hops.extract j hops.size) (S.extract j S.size) i) := ⟨_, rfl⟩
  rw [← hKE] at hpk
  have hKE0 : KE[0]! = c := by
    rw [hKE, hget _ 0 (by rw [hpi]; omega)]
    rfl
  -- The keyed hop's keys, as the output of the key derivation that returns `t`.
  obtain ⟨KS', hKS'⟩ : ∃ KS' : Array HopKeys, KS' = Array.ofFn
      (fun i : Fin (hops.extract j hops.size).size => if i.val = 0
        then deriveHopKeys (keysKDF t) ss
        else kemHopKeys kem kdfS (hops.extract j hops.size) (S.extract j S.size) i) := ⟨_, rfl⟩
  have hfield : ∀ i : ℕ, keyTuple (KS'[i]!) = keyTuple ((Array.ofFn
      (fun i : Fin (hops.extract j hops.size).size => if i.val = 0 then hopKeysOf t
        else kemHopKeys kem kdfS (hops.extract j hops.size) (S.extract j S.size) i))[i]!) := by
    intro i
    by_cases hi : i < (hops.extract j hops.size).size
    · rw [hKS', hget _ i hi, hget _ i hi]
      dsimp only
      split_ifs
      · exact hkt
      · rfl
    · rw [hKS', getElem!_neg _ i (by simpa using hi), getElem!_neg _ i (by simpa using hi)]
  have hswap := (newKEMPacketFrom_congr kem cipher macS streamS geom _ KS' _ _ _ payload
    (fun i => congrArg (·.2.2.1) (hfield i)) (fun i => congrArg (·.2.2.2) (hfield i))
    (fun i => congrArg (·.2.1) (hfield i)) (fun i => congrArg (·.1) (hfield i))).trans hpk
  have hK0 : KS'[0]! = deriveHopKeys (keysKDF t) ss := by
    rw [hKS', hget _ 0 (by rw [hpi]; omega)]
    rfl
  have hksize : ∀ i (hi : i < KE.size), (KE[i]'hi).size = kem.ciphertextSize := by
    intro i hi
    have hi' : i < hops.size - j := by
      rw [hKE] at hi
      simpa using hi
    rw [← getElem!_pos KE i hi, hKE, hget _ i (by rw [hpi]; exact hi')]
    dsimp only
    split_ifs with hi0
    · exact hcsz
    · omega
  have hfsz : geom.nrHops > (hops.extract j hops.size).size →
      (fillerAtF kem kdfS streamS geom hops S
        ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
        j (ksOf streamS geom t) j).size
        = (geom.nrHops - (hops.extract j hops.size).size) * geom.perHopRoutingInfoLength :=
    fun _ => by
      rw [fillerAtF_size kem kdfS streamS geom hrouting hops S _ j (ksOf streamS geom t) hlen hF
        (show (ksOf streamS geom t).size = _ from streamS.keystream_size _ _ _) j (by omega),
        hpi]
      congr 1
      omega
  have hkey : ∃ seed ss', kem.Reliable (kem.stateFromSeed seed) ∧
      kemEncap kem ((hops.extract j hops.size)[0]!).publicKey seed = Except.ok (KE[0]!, ss') ∧
      KS'[0]! = deriveHopKeys (keysKDF t) ss' := by
    refine ⟨s, ss, hrel, ?_, hK0⟩
    rw [hKE0, hpget 0 (by omega), Nat.add_zero]
    exact hencj
  have hpp' : kemSelfPublicKeyBytes kem privKey = ((hops.extract j hops.size)[0]!).publicKey := by
    rw [hpget 0 (by omega), Nat.add_zero]
    exact hpp
  have hnn' : ∀ x ∈ ((hops.extract j hops.size)[0]!).commands, x ≠ RoutingCommand.null := by
    rw [hpget 0 (by omega), Nat.add_zero]
    exact hcmdnn
  have hnh' : ∀ x ∈ ((hops.extract j hops.size)[0]!).commands, ∀ id m,
      x ≠ RoutingCommand.nextNodeHop id m := by
    rw [hpget 0 (by omega), Nat.add_zero]
    exact hcmdnh
  obtain ⟨-, h1⟩ := newKEMPacketFrom_unwrapKEM kem cipher macS (keysKDF t) streamS geom hvalid
    hmactag h16 KE KS' _ (hops.extract j hops.size) payload pkt privKey (by rw [hpi]; omega) hfsz
    (by rw [hKE]; simp) (by rw [hKS']; simp) hksize hpp' hkey hnn' hnh' hswap
  obtain ⟨replayTag, hun⟩ := h1 (by rw [hpi]; omega)
  rw [hpget 0 (by omega), Nat.add_zero] at hun
  refine ⟨⟨replayTag, ?_⟩, ?_⟩
  · refine procWith_keysKDF kem cipher macS streamS geom t (kemDecap kem privKey) pkt _ ?_
    unfold procWith
    rw [show unwrapKEMWith kem cipher macS (keysKDF t) streamS geom (kemDecap kem privKey) pkt
      = _ from hun]
    rfl
  · have hP : hops.extract j hops.size = #[hops[j]!] :=
      Array.ext (by simp; omega) fun i h1 h2 => by
        have hi0 : i = 0 := by simpa using h2
        subst hi0
        simp [getElem!_pos hops j (by omega)]
    have hKEeq : KE = #[c] := by
      rw [hKE]
      exact Array.ext (by simp; omega) fun i h1 h2 => by
        have hi0 : i = 0 := by simpa using h2
        subst hi0
        simp
    have hKSeq : (Array.ofFn (fun i : Fin (hops.extract j hops.size).size =>
        if i.val = 0 then hopKeysOf t
        else kemHopKeys kem kdfS (hops.extract j hops.size) (S.extract j S.size) i))
        = #[hopKeysOf t] :=
      Array.ext (by simp; omega) fun i h1 h2 => by
        have hi0 : i = 0 := by simpa using h2
        subst hi0
        simp
    rw [hKEeq, hKSeq, hP] at hpk
    exact newKEMPacketFrom_one kem cipher macS streamS geom c (hopKeysOf t) _ _ payload pkt hpk

/-- The bytes of the keyed hop's layer in front of its tag, at the end of the path: its
ciphertext and its routing info under its keystream `U`. They do not use its MAC key. -/
def relayFrontLast (hops : Array PathHop) (d : RSOR.Draw geom) (j : ℕ) (c U : ByteArray) :
    ByteArray :=
  v0AD ++ c ++ xorBytes
    ((match kemRiFragment kem geom #[hops[j]!] #[c] ByteArray.empty 1 0 with
      | .ok f => f
      | .error _ => ByteArray.empty)
      ++ (if geom.nrHops > 1 then fillerAtF kem kdfS streamS geom hops
            (d.1.toArray.extract 0 hops.size)
            ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength))
            j U j
          else ByteArray.empty))
    (U.extract 0 (geom.routingInfoLength + geom.perHopRoutingInfoLength - (0 + 1) *
        geom.perHopRoutingInfoLength))

/-- The bytes of the keyed hop's layer behind its tag, at the end of the path: the payload
under its payload encryption `encf`. -/
def relayBackLast (payload : ByteArray) (encf : ByteArray → ByteArray) : ByteArray :=
  encf ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)

set_option maxHeartbeats 1000000 in
/-- **The keyed hop's layer in three parts, at the end of the path**: the bytes in front, their
tag under its MAC key, and the payload behind. Only the tag uses the MAC key. -/
theorem layerPK_self_last_parts (hvalid : geom.ValidForKEM kem)
    (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload pkt privKey : ByteArray) (j : ℕ)
    (c : ByteArray) (t : KeyTuple) (s : Vector UInt8 32) (ss : ByteArray)
    (hj : j + 1 = hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hencj : kemEncap kem (hops[j]!).publicKey s = .ok (c, ss))
    (hrel : kem.Reliable (kem.stateFromSeed s))
    (hpp : kemSelfPublicKeyBytes kem privKey = (hops[j]!).publicKey)
    (hcmdnn : ∀ x ∈ (hops[j]!).commands, x ≠ RoutingCommand.null)
    (hcmdnh : ∀ x ∈ (hops[j]!).commands, ∀ id m, x ≠ RoutingCommand.nextNodeHop id m)
    (hpk : layerPK kem cipher macS kdfS streamS geom hops d payload j c t j = .ok pkt) :
    pkt = relayFrontLast kem kdfS streamS geom hops d j c (ksOf streamS geom t)
        ++ ofVector (macS.mac (ofVector t.2.2.1)
          (relayFrontLast kem kdfS streamS geom hops d j c (ksOf streamS geom t)))
        ++ relayBackLast geom payload (encOf cipher t) ∧
      (relayFrontLast kem kdfS streamS geom hops d j c (ksOf streamS geom t)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength := by
  obtain ⟨-, ⟨frag, hfrag⟩, hpkt⟩ := layerPK_self_last kem cipher macS kdfS streamS geom hvalid
      hmactag h16 hops d payload
    pkt privKey j c t s ss hj hlen hencj hrel hpp hcmdnn hcmdnh hpk
  obtain ⟨hnnh, hperhopEq, hrouting, -⟩ := id hvalid
  have hcsz : c.size = kem.ciphertextSize := kemEncap_size kem _ _ c ss hencj
  refine ⟨?_, ?_⟩
  · refine hpkt.trans ?_
    unfold pkt1 hdr1 relayFrontLast relayBackLast encOf ksOf
    dsimp only
    rw [ByteArray.append_empty]
    rfl
  · unfold relayFrontLast
    rw [hfrag]
    dsimp only
    have hfr := kemRiFragment_size kem geom #[hops[j]!] #[c] ByteArray.empty 1 0 (by omega)
      (by omega) hnnh rfl (fun i hi => by
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact hcsz) frag hfrag
    have hF : ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) *
        geom.perHopRoutingInfoLength)).size
        = (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength := by
      have hle : (geom.nrHops - hops.size) * geom.perHopRoutingInfoLength
          ≤ geom.perHopRoutingInfoLength * geom.nrHops := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      rw [ByteArray.size_extract, Util.Bytes.size_ofVector, hrouting]
      omega
    have h0 : v0AD.size = 2 := rfl
    rw [ByteArray.size_append, ByteArray.size_append, size_xorBytes, ByteArray.size_append, hfr,
      h0, hcsz]
    split_ifs with hn
    · rw [fillerAtF_size kem kdfS streamS geom hrouting hops _ _ j (ksOf streamS geom t) hlen hF
        (show (ksOf streamS geom t).size = _ from streamS.keystream_size _ _ _) j (by omega),
        show geom.nrHops - hops.size + j = geom.nrHops - 1 by omega, hrouting]
      have : geom.perHopRoutingInfoLength + (geom.nrHops - 1) * geom.perHopRoutingInfoLength
          = geom.perHopRoutingInfoLength * geom.nrHops := by
        obtain ⟨m, hm⟩ : ∃ m, geom.nrHops = m + 1 := ⟨geom.nrHops - 1, by omega⟩
        rw [hm, Nat.add_sub_cancel]
        ring
      omega
    · have hn1 : geom.nrHops = 1 := by omega
      rw [hrouting, hn1, Nat.mul_one]
      rfl

/-- `RSOR.layer` with hop `j`'s ciphertext `c`, header keystream `U`, tagging function `tagf`
and payload encryption `encf` given: the layer for position `i`. -/
def layerF (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (c U : ByteArray) (tagf encf : ByteArray → ByteArray) (i : ℕ) : Option ByteArray :=
  let seeds := d.1.toArray.extract 0 hops.size
  packetF kem cipher macS kdfS streamS geom (seeds.extract i seeds.size)
    (fillerAtF kem kdfS streamS geom hops seeds
      ((ofVector d.2).extract 0 ((geom.nrHops - hops.size) * geom.perHopRoutingInfoLength)) j U i)
    (hops.extract i hops.size) payload (j - i) c U tagf encf

/-- The keyed layer with the keystream, tagging function and payload encryption of the keys
`t` is the keyed layer for `t`. -/
theorem layerF_eq_layerPK (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray)
    (j : ℕ) (c : ByteArray) (t : KeyTuple) (i : ℕ) :
    layerF kem cipher macS kdfS streamS geom hops d payload j c (ksOf streamS geom t)
        (tagOf macS t) (encOf cipher t) i
      = (layerPK kem cipher macS kdfS streamS geom hops d payload j c t i).toOption :=
  (packetK_eq_packetF kem cipher macS kdfS streamS geom _ _ _ payload (j - i) c t).symm

/-- With the ciphertext that the seed `s` gives at hop `j` and the keystream, tagging function
and payload encryption of its keys, `layerF` is the layer built from the draw with `s` at
position `j`, for a layer up to hop `j`'s. -/
theorem layerF_real (hops : Array PathHop) (d : RSOR.Draw geom) (payload pkt : ByteArray)
    (j i : ℕ) (s : Vector UInt8 32) (c ss : ByteArray) (hi : i ≤ j) (hj : j < hops.size)
    (hlen : hops.size ≤ geom.nrHops)
    (henc : kemEncap kem (hops[j]!).publicKey s = .ok (c, ss))
    (hpkt : RSOR.layer kem cipher macS kdfS streamS geom hops (d.1.setIfInBounds j s, d.2)
      payload i = .ok pkt) :
    layerF kem cipher macS kdfS streamS geom hops d payload j c
      (ksOf streamS geom (keyTuple (deriveHopKeys kdfS ss)))
      (tagOf macS (keyTuple (deriveHopKeys kdfS ss)))
      (encOf cipher (keyTuple (deriveHopKeys kdfS ss))) i = some pkt := by
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
  unfold layerF
  dsimp only
  rw [fillerAtF_real kem kdfS streamS geom hops _ _ _ j c ss hj hsz (by rw [hs]; exact henc)
    (fun k hk => by
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hget k hk]) i hi,
    ← packetK_eq_packetF,
    packetK_congr kem cipher macS kdfS streamS geom _ _ _ _ _ _ _ _ fun m hm =>
      extract_getElem!_congr _ _ i m hSS (hget (i + m) (by omega)),
    h1]
  rfl

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

/-- The layer of `q`'s onion for forward position `i`, with the KEM ciphertext, header
keystream, tagging function and payload encryption of the hop at position `j` given. -/
def onionF (q : RSOR.Request kem geom) (r : RSOR.Randomness geom) (j : ℕ) (c : kem.Ciphertext)
    (U : ByteArray) (tagf encf : ByteArray → ByteArray) (i : ℕ) : RSOR.Onion geom :=
  match layerF kem cipher macS kdfS streamS geom (RSOR.path kem q.fwd [.recipient q.receiver]) r.1
      (RSOR.body kem macS kdfS streamS geom q r) j (ofVector (kem.encodeCiphertext c)) U tagf
      encf i with
  | some pkt => RSOR.split geom pkt
  | none => default

/-- The layer of `q`'s onion for forward position `i`, with the KEM ciphertext and keys of the
hop at position `j` given. -/
def onionK (q : RSOR.Request kem geom) (r : RSOR.Randomness geom) (j : ℕ) (c : kem.Ciphertext)
    (t : KeyTuple) (i : ℕ) : RSOR.Onion geom :=
  onionF kem cipher macS kdfS streamS geom q r j c (ksOf streamS geom t) (tagOf macS t)
    (encOf cipher t) i

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
  have h : layerF kem cipher macS kdfS streamS geom
      (RSOR.path kem q.fwd [.recipient q.receiver]) r.1
      (RSOR.body kem macS kdfS streamS geom q r) j (ofVector (kem.encodeCiphertext c))
      (ksOf streamS geom (keyTuple (deriveHopKeys kdfS ss)))
      (tagOf macS (keyTuple (deriveHopKeys kdfS ss)))
      (encOf cipher (keyTuple (deriveHopKeys kdfS ss))) i = some pkt :=
    layerF_real kem cipher macS kdfS streamS geom _ r.1 _ pkt j i s _ ss hi
      (by rw [hn]; exact j.isLt)
      (by rw [hn]; exact q.fwd.length_le) (by rw [hpub]; exact henc) hpkt
  have hform : RSOR.form kem cipher macS kdfS streamS geom q (setSeed geom r j s) i
      = RSOR.split geom pkt := by
    unfold RSOR.form
    rw [hpkt]
  rw [hform]
  unfold onionK onionF
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
