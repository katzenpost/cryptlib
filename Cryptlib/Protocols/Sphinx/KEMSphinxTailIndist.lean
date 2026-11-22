/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.OracleComp.Constructions.SampleableType
import Cryptlib.Protocols.Sphinx.KEMSphinxTail

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open OracleComp ENNReal
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

/-! # KEM-Sphinx tail indistinguishability, up to one keystream block

`newKEMPacket_unwrapKEM_tail` says the packet the first hop forwards is a fresh packet on the
rest of the path whose filler ends in `tailPad`. Here `tailPad` is split into the first hop's
keystream block and a mask that depends only on the rest of the path (`tailPad_eq_mask`), and
the probabilistic consequence is drawn: replace that one block by a uniform block and the
forwarded packet has exactly the distribution of a fresh packet (`prEvent_tailIdeal_eq_fresh`).
So an adversary's advantage in telling the forwarded packet from a fresh one equals its
advantage in telling the first hop's keystream block from a uniform one
(`tailAdvantage_eq`).

This is a variant of tail indistinguishability (Kuhn, Beck and Strufe, S&P 2020, Definition 6),
not that definition:

- the honest hop is the first hop of the path;
- the adversary is given the packet alone, with no oracle for the honest hop;
- the packet it must tell apart is built on the rest of the path directly, where the paper's
  is a layer of a second onion that also passes the honest hop.

Not proved: that the first hop's keystream block is hard to tell from uniform, which is an
assumption on the KEM, the KDF and the stream cipher together. `hrel` asks that the KEM never
fail to decapsulate, and `hok` that every packet can be built. -/

/-- `xorBytes` with two masks of the first argument's width, in either order. -/
theorem xorBytes_left_comm (a b c : ByteArray) (hab : a.size = b.size) (hbc : b.size = c.size) :
    xorBytes a (xorBytes b c) = xorBytes b (xorBytes a c) := by
  apply ByteArray.ext_getElem
  · simp [hab]
  · intro i h1 h2
    have hia : i < a.size := by simpa using h1
    have hib : i < b.size := by simpa using h2
    have hic : i < c.size := by omega
    rw [xorBytes_getElem a (xorBytes b c) i hia, dif_pos (by simpa using hib),
      xorBytes_getElem b c i hib, dif_pos hic,
      xorBytes_getElem b (xorBytes a c) i hib, dif_pos (by simpa using hia),
      xorBytes_getElem a c i hia, dif_pos hic]
    rw [← UInt8.xor_assoc, UInt8.xor_comm a[i] b[i], UInt8.xor_assoc]

/-- The part of `tailPad` that does not depend on the first hop: the XOR of `tailPadBlock` over
hops `1` to `i + 1`, written over the rest of the path and its seeds. -/
def tailMask (kem : KEM) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)
    (restPath : Array PathHop) (restSeeds : Array (Vector UInt8 32)) : Nat → ByteArray
  | 0 => tailPadBlock streamS geom (kemHopKeys kem kdfS restPath restSeeds 0) 1
  | i + 1 => xorBytes (tailPadBlock streamS geom (kemHopKeys kem kdfS restPath restSeeds (i + 1))
      (i + 2)) (tailMask kem kdfS streamS geom restPath restSeeds i)

/-- A `tailPadBlock` inside the keystream is one routing-info block wide. -/
theorem tailPadBlock_size (streamS : StreamCipher) (geom : Geometry) (k : HopKeys) (j : Nat)
    (h : (j + 1) * geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength + geom.perHopRoutingInfoLength) :
    (tailPadBlock streamS geom k j).size = geom.perHopRoutingInfoLength := by
  have hsm : (j + 1) * geom.perHopRoutingInfoLength
      = j * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength := Nat.succ_mul _ _
  unfold tailPadBlock headerKeystream
  rw [ByteArray.size_extract, streamS.keystream_size]
  omega

/-- Hops up to the geometry's path length have their block inside the keystream. -/
theorem block_le (geom : Geometry)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops) (j : Nat)
    (hj : j ≤ geom.nrHops) :
    (j + 1) * geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength + geom.perHopRoutingInfoLength := by
  rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength geom.nrHops, ← Nat.succ_mul]
  exact Nat.mul_le_mul_right _ (by omega)

/-- A hop's keys on the rest of the path are its keys on the whole path. -/
theorem kemHopKeys_rest (kem : KEM) (kdfS : KDF) (path : Array PathHop)
    (seeds : Array (Vector UInt8 32)) (hseeds : seeds.size = path.size) (i : Nat)
    (hi : i + 1 < path.size) :
    kemHopKeys kem kdfS (path.extract 1 path.size) (seeds.extract 1 seeds.size) i
      = kemHopKeys kem kdfS path seeds (i + 1) := by
  unfold kemHopKeys
  rw [getElem!_extract_from path 1 i (by omega), getElem!_extract_from seeds 1 i (by omega),
    Nat.add_comm 1 i]

/-- `tailMask` is one routing-info block wide. -/
theorem tailMask_size (kem : KEM) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)
    (restPath : Array PathHop) (restSeeds : Array (Vector UInt8 32))
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops) (i : Nat)
    (hi : i + 1 ≤ geom.nrHops) :
    (tailMask kem kdfS streamS geom restPath restSeeds i).size = geom.perHopRoutingInfoLength := by
  cases i with
  | zero => exact tailPadBlock_size streamS geom _ 1 (block_le geom hrouting 1 (by omega))
  | succ i =>
    show (xorBytes _ _).size = _
    rw [size_xorBytes]
    exact tailPadBlock_size streamS geom _ (i + 2) (block_le geom hrouting (i + 2) (by omega))

/-- `tailPad` is the first hop's keystream block XORed with a mask that depends only on the
rest of the path. -/
theorem tailPad_eq_mask (kem : KEM) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)
    (path : Array PathHop) (seeds : Array (Vector UInt8 32)) (hseeds : seeds.size = path.size)
    (hgen : path.size ≤ geom.nrHops)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops) (i : Nat)
    (hi : i + 1 < path.size) :
    tailPad kem kdfS streamS geom path seeds (i + 1)
      = xorBytes (tailPadBlock streamS geom (kemHopKeys kem kdfS path seeds 0) 0)
          (tailMask kem kdfS streamS geom (path.extract 1 path.size)
            (seeds.extract 1 seeds.size) i) := by
  have hb0 : (tailPadBlock streamS geom (kemHopKeys kem kdfS path seeds 0) 0).size
      = geom.perHopRoutingInfoLength :=
    tailPadBlock_size streamS geom _ 0 (block_le geom hrouting 0 (by omega))
  induction i with
  | zero =>
    show xorBytes (tailPadBlock streamS geom (kemHopKeys kem kdfS path seeds (0 + 1)) (0 + 1))
        (tailPadBlock streamS geom (kemHopKeys kem kdfS path seeds 0) 0)
      = xorBytes _ (tailPadBlock streamS geom (kemHopKeys kem kdfS (path.extract 1 path.size)
          (seeds.extract 1 seeds.size) 0) 1)
    rw [kemHopKeys_rest kem kdfS path seeds hseeds 0 hi]
    exact xorBytes_comm_of_size_eq _ _ (by
      rw [hb0, tailPadBlock_size streamS geom _ (0 + 1) (block_le geom hrouting (0 + 1) (by omega))])
  | succ i ih =>
    show xorBytes (tailPadBlock streamS geom (kemHopKeys kem kdfS path seeds (i + 1 + 1)) (i + 1 + 1))
        (tailPad kem kdfS streamS geom path seeds (i + 1))
      = xorBytes _ (xorBytes (tailPadBlock streamS geom (kemHopKeys kem kdfS
          (path.extract 1 path.size) (seeds.extract 1 seeds.size) (i + 1)) (i + 2))
          (tailMask kem kdfS streamS geom (path.extract 1 path.size)
            (seeds.extract 1 seeds.size) i))
    rw [ih (by omega), kemHopKeys_rest kem kdfS path seeds hseeds (i + 1) hi]
    exact xorBytes_left_comm _ _ _
      (by rw [hb0, tailPadBlock_size streamS geom _ (i + 1 + 1)
        (block_le geom hrouting (i + 1 + 1) (by omega))])
      (by rw [hb0, tailMask_size kem kdfS streamS geom _ _ hrouting i (by omega)])

/-- The filler of a packet on the rest of the path: `filler`, then `block` masked by
`tailMask`. With `block` the first hop's keystream block this is `tailFiller`. -/
def restFiller (kem : KEM) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)
    (restPath : Array PathHop) {a b : Nat} (restSeeds : Vector (Vector UInt8 32) restPath.size)
    (filler : Vector UInt8 a) (block : Vector UInt8 b) : Vector UInt8 (a + b) :=
  Util.Bytes.toVecN (a + b) (ofVector filler ++ xorBytes (ofVector block)
    (tailMask kem kdfS streamS geom restPath restSeeds.toArray (restPath.size - 1)))

theorem ofVector_restFiller (kem : KEM) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)
    (restPath : Array PathHop) {a b : Nat} (restSeeds : Vector (Vector UInt8 32) restPath.size)
    (filler : Vector UInt8 a) (block : Vector UInt8 b) :
    ofVector (restFiller kem kdfS streamS geom restPath restSeeds filler block)
      = ofVector filler ++ xorBytes (ofVector block)
          (tailMask kem kdfS streamS geom restPath restSeeds.toArray (restPath.size - 1)) :=
  Util.Bytes.ofVector_toVecN _ (by simp)

/-- For fixed seeds, `restFiller` is a bijection from a filler and a block to a longer
filler. -/
theorem restFiller_bijective (kem : KEM) (kdfS : KDF) (streamS : StreamCipher) (geom : Geometry)
    (restPath : Array PathHop) {a b : Nat} (restSeeds : Vector (Vector UInt8 32) restPath.size) :
    Function.Bijective (Function.uncurry
      (restFiller kem kdfS streamS geom restPath restSeeds (a := a) (b := b))) := by
  constructor
  · rintro ⟨f1, b1⟩ ⟨f2, b2⟩ h
    have h' : ofVector (restFiller kem kdfS streamS geom restPath restSeeds f1 b1)
        = ofVector (restFiller kem kdfS streamS geom restPath restSeeds f2 b2) :=
      congrArg ofVector h
    rw [ofVector_restFiller, ofVector_restFiller] at h'
    have hl := congrArg (fun x => x.extract 0 a) h'
    have hr := congrArg (fun x => x.extract a (a + b)) h'
    rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by simp),
      Cryptlib.Util.Bytes.extract_append_of_le _ _ (by simp)] at hl
    rw [Cryptlib.Util.Bytes.extract_append_of_ge _ _ (by simp),
      Cryptlib.Util.Bytes.extract_append_of_ge _ _ (by simp)] at hr
    simp only [Cryptlib.Util.Bytes.size_ofVector, Nat.sub_self, Nat.add_sub_cancel_left] at hl hr
    have hl' : ofVector f1 = ofVector f2 := by
      have e1 := ByteArray.extract_zero_size (b := ofVector f1)
      have e2 := ByteArray.extract_zero_size (b := ofVector f2)
      simp only [Cryptlib.Util.Bytes.size_ofVector] at e1 e2
      rw [← e1, ← e2]; exact hl
    have hr' : ofVector b1 = ofVector b2 := by
      have e1 := ByteArray.extract_zero_size (b := xorBytes (ofVector b1)
        (tailMask kem kdfS streamS geom restPath restSeeds.toArray (restPath.size - 1)))
      have e2 := ByteArray.extract_zero_size (b := xorBytes (ofVector b2)
        (tailMask kem kdfS streamS geom restPath restSeeds.toArray (restPath.size - 1)))
      simp only [size_xorBytes, Cryptlib.Util.Bytes.size_ofVector] at e1 e2
      rw [e1, e2] at hr
      have := congrArg (fun x => xorBytes x
        (tailMask kem kdfS streamS geom restPath restSeeds.toArray (restPath.size - 1))) hr
      simpa only [xorBytes_xorBytes] using this
    have hf : f1 = f2 := by
      have := congrArg (Util.Bytes.toVecN a) hl'
      simpa only [Util.Bytes.toVecN_ofVector] using this
    have hb : b1 = b2 := by
      have := congrArg (Util.Bytes.toVecN b) hr'
      simpa only [Util.Bytes.toVecN_ofVector] using this
    rw [hf, hb]
  · intro z
    refine ⟨(Util.Bytes.toVecN a ((ofVector z).extract 0 a), Util.Bytes.toVecN b (xorBytes ((ofVector z).extract a (a + b))
      (tailMask kem kdfS streamS geom restPath restSeeds.toArray (restPath.size - 1)))), ?_⟩
    show restFiller kem kdfS streamS geom restPath restSeeds _ _ = z
    unfold restFiller
    rw [Util.Bytes.ofVector_toVecN _ (by simp), Util.Bytes.ofVector_toVecN _ (by simp), xorBytes_xorBytes]
    have hz : (ofVector z).extract 0 a ++ (ofVector z).extract a (a + b) = ofVector z := by
      have := Cryptlib.Util.Bytes.append_extract (ofVector z) a (by simp)
      simpa only [Cryptlib.Util.Bytes.size_ofVector] using this
    rw [hz, Util.Bytes.toVecN_ofVector]

section Games

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- A fresh packet on `restPath`, or `none` when it cannot be built. -/
def freshView (restPath : Array PathHop) (payload : ByteArray) {c : Nat}
    (restSeeds : Vector (Vector UInt8 32) restPath.size) (filler : Vector UInt8 c) :
    Option ByteArray :=
  (newKEMPacket kem cipher macS kdfS streamS geom restSeeds.toArray (ofVector filler) restPath
    payload).toOption

/-- What the first hop forwards from a packet built on `hop0` followed by `restPath`, or `none`
when the packet cannot be built or the hop forwards nothing. -/
def forwardedView (hop0 : PathHop) (restPath : Array PathHop) (payload privKey : ByteArray)
    {a : Nat} (seed0 : Vector UInt8 32) (restSeeds : Vector (Vector UInt8 32) restPath.size)
    (filler : Vector UInt8 a) : Option ByteArray :=
  match newKEMPacket kem cipher macS kdfS streamS geom (#[seed0] ++ restSeeds.toArray)
      (ofVector filler) (#[hop0] ++ restPath) payload with
  | .error _ => none
  | .ok pkt =>
    match unwrapKEM kem cipher macS kdfS streamS geom privKey pkt with
    | .ok (_, _, _, some fwd) => some (ofVector fwd)
    | _ => none

/-- The first hop's keystream block that ends up in the forwarded packet's filler. -/
def firstBlock (hop0 : PathHop) (seed0 : Vector UInt8 32) :
    Vector UInt8 geom.perHopRoutingInfoLength :=
  Util.Bytes.toVecN geom.perHopRoutingInfoLength
    (tailPadBlock streamS geom (kemHopKeys kem kdfS #[hop0] #[seed0] 0) 0)

/-- The real game: build a packet from uniform seeds and filler, and give out what the first hop
forwards. -/
def tailReal (hop0 : PathHop) (restPath : Array PathHop) (payload privKey : ByteArray) (a : Nat) :
    ProbComp (Option ByteArray) := do
  let seed0 ← $ᵗ (Vector UInt8 32)
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let filler ← $ᵗ (Vector UInt8 a)
  return forwardedView kem cipher macS kdfS streamS geom hop0 restPath payload privKey seed0
    restSeeds filler

/-- The real game as `forwardedView_eq` rewrites it: a packet on the rest of the path whose
filler ends in the first hop's keystream block, masked. -/
def tailRealBlock (hop0 : PathHop) (restPath : Array PathHop) (payload : ByteArray) (a : Nat) :
    ProbComp (Option ByteArray) := do
  let seed0 ← $ᵗ (Vector UInt8 32)
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let filler ← $ᵗ (Vector UInt8 a)
  return freshView kem cipher macS kdfS streamS geom restPath payload restSeeds
    (restFiller kem kdfS streamS geom restPath restSeeds filler
      (firstBlock kem kdfS streamS geom hop0 seed0))

/-- The ideal game: as `tailRealBlock`, with a uniform block in place of the first hop's. -/
def tailIdeal (restPath : Array PathHop) (payload : ByteArray) (a b : Nat) :
    ProbComp (Option ByteArray) := do
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let filler ← $ᵗ (Vector UInt8 a)
  let block ← $ᵗ (Vector UInt8 b)
  return freshView kem cipher macS kdfS streamS geom restPath payload restSeeds
    (restFiller kem kdfS streamS geom restPath restSeeds filler block)

/-- The fresh game: a packet built on the rest of the path from uniform seeds and filler. -/
def tailFresh (restPath : Array PathHop) (payload : ByteArray) (c : Nat) :
    ProbComp (Option ByteArray) := do
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let filler ← $ᵗ (Vector UInt8 c)
  return freshView kem cipher macS kdfS streamS geom restPath payload restSeeds filler

/-- **With a uniform block in place of the first hop's keystream block, the forwarded packet is
distributed exactly as a fresh packet on the rest of the path.** -/
theorem prEvent_tailIdeal_eq_tailFresh (restPath : Array PathHop) (payload : ByteArray)
    (a b : Nat) (p : Option ByteArray → Prop) :
    Pr{let v ← tailIdeal kem cipher macS kdfS streamS geom restPath payload a b}[p v]
      = Pr{let v ← tailFresh kem cipher macS kdfS streamS geom restPath payload (a + b)}[p v] := by
  unfold tailIdeal tailFresh
  refine prEvent_bind_congr _ _ _ _ _ fun restSeeds => ?_
  have h := SampleableType.prEvent_uniformSample_pair_of_bijective
    (restFiller_bijective kem kdfS streamS geom restPath restSeeds (a := a) (b := b))
    (fun z => p (freshView kem cipher macS kdfS streamS geom restPath payload restSeeds z))
  simp only [prEvent_norm] at h ⊢
  exact h

/-- A byte array of size zero is empty. -/
theorem eq_empty_of_size_zero (b : ByteArray) (h : b.size = 0) : b = ByteArray.empty := by
  apply ByteArray.ext_getElem
  · simpa using h
  · intro i h1
    omega

/-- **What the first hop forwards is a fresh packet on the rest of the path whose filler ends in
the first hop's keystream block, masked.** `newKEMPacket_unwrapKEM_tail` in the terms of the
games. -/
theorem forwardedView_eq (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hop0 : PathHop) (restPath : Array PathHop) (payload privKey : ByteArray)
    (hrest : 1 ≤ restPath.size)
    (hpp : kemSelfPublicKeyBytes kem privKey = hop0.publicKey)
    (hrel : ∀ seed, kem.Reliable (kem.stateFromSeed seed))
    (hcmdnn : ∀ c ∈ hop0.commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ hop0.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (seed0 : Vector UInt8 32) (restSeeds : Vector (Vector UInt8 32) restPath.size)
    (filler : Vector UInt8
      ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength))
    (pkt : ByteArray)
    (hnk : newKEMPacket kem cipher macS kdfS streamS geom (#[seed0] ++ restSeeds.toArray)
      (ofVector filler) (#[hop0] ++ restPath) payload = Except.ok pkt) :
    forwardedView kem cipher macS kdfS streamS geom hop0 restPath payload privKey seed0 restSeeds
        filler
      = freshView kem cipher macS kdfS streamS geom restPath payload restSeeds
          (restFiller kem kdfS streamS geom restPath restSeeds filler
            (firstBlock kem kdfS streamS geom hop0 seed0)) := by
  have hpsize : (#[hop0] ++ restPath).size = restPath.size + 1 := by simp; omega
  have hpath0 : (#[hop0] ++ restPath)[0]! = hop0 := by simp
  have hpext : (#[hop0] ++ restPath).extract 1 (#[hop0] ++ restPath).size = restPath := by simp
  have hsext : (#[seed0] ++ restSeeds.toArray).extract 1 (#[seed0] ++ restSeeds.toArray).size
      = restSeeds.toArray := by simp
  obtain ⟨tag, cmds, fwd, hunwrap, htail⟩ := newKEMPacket_unwrapKEM_tail kem cipher macS kdfS
    streamS geom hvalid hmactag h16 (#[seed0] ++ restSeeds.toArray) (ofVector filler)
    (#[hop0] ++ restPath) payload pkt privKey (by omega) (by rw [hpath0]; exact hpp)
    (fun j _ => hrel _) (by rw [hpath0]; exact hcmdnn) (by rw [hpath0]; exact hcmdnh) hnk
  obtain ⟨-, hdr, sprpKeys, t, hcreate, -, -, -⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ payload pkt hnk
  obtain ⟨-, hple, hesize, -⟩ :=
    createKEMHeader_unfold kem macS kdfS streamS geom _ _ _ hdr sprpKeys hcreate
  obtain ⟨-, -, hrouting, -, -, -⟩ := id hvalid
  have hfill : tailFiller kem kdfS streamS geom (#[hop0] ++ restPath)
      (#[seed0] ++ restSeeds.toArray) (ofVector filler)
      = ofVector (restFiller kem kdfS streamS geom restPath restSeeds filler
          (firstBlock kem kdfS streamS geom hop0 seed0)) := by
    rw [ofVector_restFiller]
    unfold tailFiller
    have h1 : (if geom.nrHops > (#[hop0] ++ restPath).size then ofVector filler
        else ByteArray.empty) = ofVector filler := by
      split
      · rfl
      · next hc =>
        refine (eq_empty_of_size_zero _ ?_).symm
        rw [Util.Bytes.size_ofVector, Nat.sub_eq_zero_of_le (by omega), Nat.zero_mul]
    have hk0 : kemHopKeys kem kdfS (#[hop0] ++ restPath) (#[seed0] ++ restSeeds.toArray) 0
        = kemHopKeys kem kdfS #[hop0] #[seed0] 0 := by
      unfold kemHopKeys
      simp
    rw [h1, show (#[hop0] ++ restPath).size - 1 = (restPath.size - 1) + 1 from by omega,
      tailPad_eq_mask kem kdfS streamS geom _ _ hesize hple hrouting (restPath.size - 1)
        (by omega), hpext, hsext, hk0]
    unfold firstBlock
    rw [Util.Bytes.ofVector_toVecN _
      (tailPadBlock_size streamS geom _ 0 (block_le geom hrouting 0 (by omega)))]
  unfold forwardedView freshView
  rw [hpext, hsext, hfill] at htail
  rw [hnk, htail]
  dsimp only
  rw [hunwrap]
  rfl

/-- The real game is `tailRealBlock`, when every packet can be built. -/
theorem tailReal_eq (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hop0 : PathHop) (restPath : Array PathHop) (payload privKey : ByteArray)
    (hrest : 1 ≤ restPath.size)
    (hpp : kemSelfPublicKeyBytes kem privKey = hop0.publicKey)
    (hrel : ∀ seed, kem.Reliable (kem.stateFromSeed seed))
    (hcmdnn : ∀ c ∈ hop0.commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ hop0.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (hok : ∀ (seed0 : Vector UInt8 32) (restSeeds : Vector (Vector UInt8 32) restPath.size)
      (filler : Vector UInt8
        ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)),
      ∃ pkt, newKEMPacket kem cipher macS kdfS streamS geom (#[seed0] ++ restSeeds.toArray)
        (ofVector filler) (#[hop0] ++ restPath) payload = Except.ok pkt) :
    tailReal kem cipher macS kdfS streamS geom hop0 restPath payload privKey
        ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)
      = tailRealBlock kem cipher macS kdfS streamS geom hop0 restPath payload
        ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) := by
  have heq : ∀ (seed0 : Vector UInt8 32) (restSeeds : Vector (Vector UInt8 32) restPath.size)
      (filler : Vector UInt8
        ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)),
      forwardedView kem cipher macS kdfS streamS geom hop0 restPath payload privKey seed0
          restSeeds filler
        = freshView kem cipher macS kdfS streamS geom restPath payload restSeeds
            (restFiller kem kdfS streamS geom restPath restSeeds filler
              (firstBlock kem kdfS streamS geom hop0 seed0)) := by
    intro seed0 restSeeds filler
    obtain ⟨pkt, hnk⟩ := hok seed0 restSeeds filler
    exact forwardedView_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 hop0 restPath
      payload privKey hrest hpp hrel hcmdnn hcmdnh seed0 restSeeds filler pkt hnk
  unfold tailReal tailRealBlock
  simp only [heq]

/-- **Tail indistinguishability for KEM-Sphinx, up to one keystream block.** The advantage in
telling what the first hop forwards from a fresh packet on the rest of the path equals the
advantage in telling the first hop's keystream block from a uniform block, inside
`tailRealBlock`. `p` is the adversary's test on what it is given. -/
theorem tailAdvantage_eq (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hop0 : PathHop) (restPath : Array PathHop) (payload privKey : ByteArray)
    (hrest : 1 ≤ restPath.size)
    (hpp : kemSelfPublicKeyBytes kem privKey = hop0.publicKey)
    (hrel : ∀ seed, kem.Reliable (kem.stateFromSeed seed))
    (hcmdnn : ∀ c ∈ hop0.commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ hop0.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (hok : ∀ (seed0 : Vector UInt8 32) (restSeeds : Vector (Vector UInt8 32) restPath.size)
      (filler : Vector UInt8
        ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)),
      ∃ pkt, newKEMPacket kem cipher macS kdfS streamS geom (#[seed0] ++ restSeeds.toArray)
        (ofVector filler) (#[hop0] ++ restPath) payload = Except.ok pkt)
    (p : Option ByteArray → Prop) :
    |(Pr{let v ← tailReal kem cipher macS kdfS streamS geom hop0 restPath payload privKey
                  ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)}[p v]).toReal
      - (Pr{let v ← tailFresh kem cipher macS kdfS streamS geom restPath payload
                      ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength
                        + geom.perHopRoutingInfoLength)}[p v]).toReal|
    = |(Pr{let v ← tailRealBlock kem cipher macS kdfS streamS geom hop0 restPath payload
                    ((geom.nrHops - (restPath.size + 1))
                      * geom.perHopRoutingInfoLength)}[p v]).toReal
      - (Pr{let v ← tailIdeal kem cipher macS kdfS streamS geom restPath payload
                      ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)
                      geom.perHopRoutingInfoLength}[p v]).toReal| := by
  rw [tailReal_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 hop0 restPath payload
    privKey hrest hpp hrel hcmdnn hcmdnh hok, prEvent_tailIdeal_eq_tailFresh]

end Games

end Cryptlib.Protocols.Sphinx.KEMSphinx
