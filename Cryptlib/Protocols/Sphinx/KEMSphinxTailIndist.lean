/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.CryptoFoundations.PRG
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
forwarded packet has exactly the distribution of a fresh packet (`prEvent_tailIdeal_eq_tailFresh`).
So an adversary's advantage in telling the forwarded packet from a fresh one equals its
advantage in telling the first hop's keystream block from a uniform one
(`tailAdvantage_eq`).

This is a variant of tail indistinguishability (Kuhn, Beck and Strufe, S&P 2020, Definition 6),
not that definition:

- the honest hop is the first hop of the path;
- the adversary is given the packet alone, with no oracle for the honest hop;
- the packet it must tell apart is built on the rest of the path directly, where the paper's
  is a layer of a second onion that also passes the honest hop.

`tailAdvantage_eq` asks that every seed be `Reliable` for the KEM and that every packet can be
built. `tailAdvantage_le` asks neither: it holds for any KEM, perfectly correct or not, and
bounds the advantage by the same block advantage plus the probability of `tailBad`, the draws
with an unreliable seed or an unbuildable packet. It uses reliability of every seed, though only
the first hop decapsulates, so the bound is looser than it need be.

`tailAdvantage_le_prg` then bounds the block advantage. The block is a function of the first
hop's seed alone, a composition of two generators in the sense of VCVio's `PRGScheme`:
`hopKeyPRG`, the KEM followed by the KDF, and `lastBlockPRG`, the stream cipher. The advantage
is at most the sum of the advantages against the two.

This file fixes the honest hop's key and gives the adversary no oracle. `KEMSphinxTailGame`
generates the key in the game and splits `hopKeyPRG` into VCVio's IND-CPA experiment for the KEM
and a generator for the KDF. `KEMSphinxTailOracle`, `KEMSphinxTailChain` and `KEMSphinxTailDef6`
add the honest relay's oracle and put the honest relay at any position, which gives the game of
Definition 6. -/

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
    (hcmdnn : ∀ c ∈ hop0.commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ hop0.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (seed0 : Vector UInt8 32) (restSeeds : Vector (Vector UInt8 32) restPath.size)
    (filler : Vector UInt8
      ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength))
    (hrel : ∀ j, j < restPath.size + 1 →
      kem.Reliable (kem.stateFromSeed (#[seed0] ++ restSeeds.toArray)[j]!))
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
    (fun j hj => hrel j (by omega)) (by rw [hpath0]; exact hcmdnn) (by rw [hpath0]; exact hcmdnh) hnk
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
      payload privKey hrest hpp hcmdnn hcmdnh seed0 restSeeds filler (fun _ _ => hrel _) pkt hnk
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

/-- Two events that agree off a bad set differ in probability by at most the probability of
the bad set. -/
theorem prEvent_toReal_sub_le_of_bad {α β : Type} (mx : ProbComp α) (f g : α → β)
    (bad : α → Prop) (h : ∀ x, ¬ bad x → f x = g x) (p : β → Prop) :
    |(Pr{let x ← mx}[p (f x)]).toReal - (Pr{let x ← mx}[p (g x)]).toReal|
      ≤ (Pr{let x ← mx}[bad x]).toReal := by
  have key : ∀ f g : α → β, (∀ x, ¬ bad x → f x = g x) →
      (Pr{let x ← mx}[p (f x)]).toReal
        ≤ (Pr{let x ← mx}[p (g x)]).toReal + (Pr{let x ← mx}[bad x]).toReal := by
    intro f g h
    have h1 : Pr{let x ← mx}[p (f x)] ≤ Pr{let x ← mx}[p (g x)] + Pr{let x ← mx}[bad x] :=
      (prEvent_mono mx _ _ fun x hx => by
        by_cases hb : bad x
        · exact Or.inr hb
        · exact Or.inl (h x hb ▸ hx)).trans (prEvent_or_le mx _ _)
    have h2 := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h1
    rwa [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at h2
  rw [abs_sub_le_iff]
  exact ⟨by linarith [key f g h], by linarith [key g f fun x hx => (h x hx).symm]⟩

/-- The draws of the real game. -/
def tailDraw (restPath : Array PathHop) (a : Nat) :
    ProbComp (Vector UInt8 32 × Vector (Vector UInt8 32) restPath.size × Vector UInt8 a) := do
  let seed0 ← $ᵗ (Vector UInt8 32)
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let filler ← $ᵗ (Vector UInt8 a)
  return (seed0, restSeeds, filler)

/-- The draws the exact theorem does not cover: some seed is not `Reliable` for the KEM, or the
packet cannot be built. For a perfectly correct KEM the first part never holds. -/
def tailBad (hop0 : PathHop) (restPath : Array PathHop) (payload : ByteArray) {a : Nat}
    (d : Vector UInt8 32 × Vector (Vector UInt8 32) restPath.size × Vector UInt8 a) : Prop :=
  ¬ ((∀ j, j < restPath.size + 1 →
        kem.Reliable (kem.stateFromSeed (#[d.1] ++ d.2.1.toArray)[j]!)) ∧
    ∃ pkt, newKEMPacket kem cipher macS kdfS streamS geom (#[d.1] ++ d.2.1.toArray)
      (ofVector d.2.2) (#[hop0] ++ restPath) payload = Except.ok pkt)

theorem tailReal_eq_map (hop0 : PathHop) (restPath : Array PathHop) (payload privKey : ByteArray)
    (a : Nat) :
    tailReal kem cipher macS kdfS streamS geom hop0 restPath payload privKey a
      = (fun d => forwardedView kem cipher macS kdfS streamS geom hop0 restPath payload privKey
          d.1 d.2.1 d.2.2) <$> tailDraw restPath a := by
  simp [tailReal, tailDraw]

theorem tailRealBlock_eq_map (hop0 : PathHop) (restPath : Array PathHop) (payload : ByteArray)
    (a : Nat) :
    tailRealBlock kem cipher macS kdfS streamS geom hop0 restPath payload a
      = (fun d => freshView kem cipher macS kdfS streamS geom restPath payload d.2.1
          (restFiller kem kdfS streamS geom restPath d.2.1 d.2.2
            (firstBlock kem kdfS streamS geom hop0 d.1))) <$> tailDraw restPath a := by
  simp [tailRealBlock, tailDraw]

/-- **Tail indistinguishability for KEM-Sphinx, up to one keystream block, for any KEM.** The
advantage in telling what the first hop forwards from a fresh packet on the rest of the path is
at most the advantage in telling the first hop's keystream block from a uniform block, plus the
probability of `tailBad`. Nothing is assumed of the KEM beyond its `Reliable` predicate: a
perfectly correct KEM has no unreliable seeds, and a KEM that can fail pays the probability of
drawing one. `tailAdvantage_eq` is the case where `tailBad` never happens. -/
theorem tailAdvantage_le (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hop0 : PathHop) (restPath : Array PathHop) (payload privKey : ByteArray)
    (hrest : 1 ≤ restPath.size)
    (hpp : kemSelfPublicKeyBytes kem privKey = hop0.publicKey)
    (hcmdnn : ∀ c ∈ hop0.commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ hop0.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (p : Option ByteArray → Prop) :
    |(Pr{let v ← tailReal kem cipher macS kdfS streamS geom hop0 restPath payload privKey
                  ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)}[p v]).toReal
      - (Pr{let v ← tailFresh kem cipher macS kdfS streamS geom restPath payload
                      ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength
                        + geom.perHopRoutingInfoLength)}[p v]).toReal|
    ≤ |(Pr{let v ← tailRealBlock kem cipher macS kdfS streamS geom hop0 restPath payload
                    ((geom.nrHops - (restPath.size + 1))
                      * geom.perHopRoutingInfoLength)}[p v]).toReal
      - (Pr{let v ← tailIdeal kem cipher macS kdfS streamS geom restPath payload
                      ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)
                      geom.perHopRoutingInfoLength}[p v]).toReal|
      + (Pr{let d ← tailDraw restPath
                    ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)}[
          tailBad kem cipher macS kdfS streamS geom hop0 restPath payload d]).toReal := by
  have hb : |(Pr{let v ← tailReal kem cipher macS kdfS streamS geom hop0 restPath payload privKey
                  ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)}[p v]).toReal
      - (Pr{let v ← tailRealBlock kem cipher macS kdfS streamS geom hop0 restPath payload
                    ((geom.nrHops - (restPath.size + 1))
                      * geom.perHopRoutingInfoLength)}[p v]).toReal|
      ≤ (Pr{let d ← tailDraw restPath
                    ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)}[
          tailBad kem cipher macS kdfS streamS geom hop0 restPath payload d]).toReal := by
    rw [tailReal_eq_map, tailRealBlock_eq_map, prEvent_map, prEvent_map]
    refine prEvent_toReal_sub_le_of_bad _ _ _ _ (fun d hd => ?_) p
    obtain ⟨hrel, pkt, hnk⟩ := Classical.not_not.mp hd
    exact forwardedView_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 hop0 restPath
      payload privKey hrest hpp hcmdnn hcmdnh d.1 d.2.1 d.2.2 hrel pkt hnk
  rw [← prEvent_tailIdeal_eq_tailFresh]
  exact (abs_sub_le _ _ _).trans (by linarith)

/-! ## The keystream block as a pseudorandom generator

The first hop's keystream block is a function of its seed alone: encapsulate to the hop's key,
derive the header key and IV, take the last block of the keystream. That is a composition of two
generators in the sense of VCVio's `PRGScheme`, and the advantage against the block is at most
the sum of the advantages against the two. -/

open PRGScheme

/-- The first hop's header key and IV as a generator from its seed: KEM encapsulation to the
hop's public key, then the KDF. -/
def hopKeyPRG (hop0 : PathHop) :
    PRGScheme (Vector UInt8 32) (Vector UInt8 32 × Vector UInt8 16) :=
  ⟨fun seed0 => ((kemHopKeys kem kdfS #[hop0] #[seed0] 0).headerEncryption,
    (kemHopKeys kem kdfS #[hop0] #[seed0] 0).headerEncryptionIV)⟩

/-- The last block of the header keystream as a generator from the header key and IV. -/
def lastBlockPRG :
    PRGScheme (Vector UInt8 32 × Vector UInt8 16) (Vector UInt8 geom.perHopRoutingInfoLength) :=
  ⟨fun k => Util.Bytes.toVecN geom.perHopRoutingInfoLength
    ((streamS.keystream (ofVector k.1) (ofVector k.2)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength)).extract
      (geom.routingInfoLength + geom.perHopRoutingInfoLength
        - (0 + 1) * geom.perHopRoutingInfoLength)
      (geom.routingInfoLength + geom.perHopRoutingInfoLength
        - 0 * geom.perHopRoutingInfoLength))⟩

theorem firstBlock_eq (hop0 : PathHop) (seed0 : Vector UInt8 32) :
    firstBlock kem kdfS streamS geom hop0 seed0
      = (lastBlockPRG streamS geom).gen ((hopKeyPRG kem kdfS hop0).gen seed0) := rfl

/-- The adversary against the block that a test `p` on the forwarded packet gives: build the
packet on the rest of the path around the block, and apply `p`. -/
def tailBlockAdversary (restPath : Array PathHop) (payload : ByteArray) (a : Nat)
    (p : Option ByteArray → Prop) [DecidablePred p] :
    PRGAdversary (Vector UInt8 geom.perHopRoutingInfoLength) := fun block => do
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let filler ← $ᵗ (Vector UInt8 a)
  return decide (p (freshView kem cipher macS kdfS streamS geom restPath payload restSeeds
    (restFiller kem kdfS streamS geom restPath restSeeds filler block)))

/-- A generator that is a composition is at most as weak as its two parts together. -/
theorem prg_comp_le {S M R : Type} [SampleableType S] [SampleableType M] [SampleableType R]
    (f : PRGScheme S M) (g : PRGScheme M R) (A : PRGAdversary R) :
    |(Pr{let x ← prgRealExperiment ⟨fun s => g.gen (f.gen s)⟩ A}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment A}[x = true]).toReal|
      ≤ |(Pr{let x ← prgRealExperiment f (fun m => A (g.gen m))}[x = true]).toReal
          - (Pr{let x ← prgIdealExperiment (fun m => A (g.gen m))}[x = true]).toReal|
        + |(Pr{let x ← prgRealExperiment g A}[x = true]).toReal
          - (Pr{let x ← prgIdealExperiment A}[x = true]).toReal| :=
  abs_sub_le _ _ _

theorem prEvent_tailRealBlock_eq_prg (hop0 : PathHop) (restPath : Array PathHop)
    (payload : ByteArray) (a : Nat) (p : Option ByteArray → Prop) [DecidablePred p] :
    Pr{let v ← tailRealBlock kem cipher macS kdfS streamS geom hop0 restPath payload a}[p v]
      = Pr{let x ← prgRealExperiment ⟨firstBlock kem kdfS streamS geom hop0⟩
                    (tailBlockAdversary kem cipher macS kdfS streamS geom restPath payload a p)}[
          x = true] := by
  unfold tailRealBlock prgRealExperiment tailBlockAdversary
  simp only [prEvent_norm, decide_eq_true_eq]

theorem prEvent_tailIdeal_eq_prg (restPath : Array PathHop)
    (payload : ByteArray) (a : Nat) (p : Option ByteArray → Prop) [DecidablePred p] :
    Pr{let v ← tailIdeal kem cipher macS kdfS streamS geom restPath payload a
                  geom.perHopRoutingInfoLength}[p v]
      = Pr{let x ← prgIdealExperiment
                    (tailBlockAdversary kem cipher macS kdfS streamS geom restPath payload a p)}[
          x = true] := by
  unfold tailIdeal prgIdealExperiment tailBlockAdversary
  simp only [prEvent_norm, decide_eq_true_eq]
  symm
  rw [OracleComp.prEvent_bind_bind_swap_of_uniform]
  have h := prEvent_bind_congr ($ᵗ (Vector (Vector UInt8 32) restPath.size))
    (fun b => do
      let blk ← $ᵗ (Vector UInt8 geom.perHopRoutingInfoLength)
      let fl ← $ᵗ (Vector UInt8 a)
      pure (p (freshView kem cipher macS kdfS streamS geom restPath payload b
        (restFiller kem kdfS streamS geom restPath b fl blk))))
    (fun b => do
      let fl ← $ᵗ (Vector UInt8 a)
      let blk ← $ᵗ (Vector UInt8 geom.perHopRoutingInfoLength)
      pure (p (freshView kem cipher macS kdfS streamS geom restPath payload b
        (restFiller kem kdfS streamS geom restPath b fl blk))))
    (fun x => x) (fun x => x)
    (fun b => by
      simp only [id_map']
      rw [OracleComp.prEvent_bind_bind_swap_of_uniform])
  simpa only [prEvent_norm, id_map'] using h

/-- `tailBlockAdversary` against the header key and IV: it expands them to the block itself. -/
def tailKeyAdversary (restPath : Array PathHop) (payload : ByteArray) (a : Nat)
    (p : Option ByteArray → Prop) [DecidablePred p] :
    PRGAdversary (Vector UInt8 32 × Vector UInt8 16) := fun k =>
  tailBlockAdversary kem cipher macS kdfS streamS geom restPath payload a p
    ((lastBlockPRG streamS geom).gen k)

/-- **Tail indistinguishability for KEM-Sphinx, reduced to two generators, for any KEM.** The
advantage in telling what the first hop forwards from a fresh packet on the rest of the path is
at most the sum of three terms: the advantage of `tailKeyAdversary` in telling the first hop's
header key and IV, derived by the KEM and the KDF from a uniform seed, from a uniform key and
IV; the advantage of `tailBlockAdversary` in telling the last keystream block under a uniform
key and IV from a uniform block; and the probability of `tailBad`. -/
theorem tailAdvantage_le_prg (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (hop0 : PathHop) (restPath : Array PathHop) (payload privKey : ByteArray)
    (hrest : 1 ≤ restPath.size)
    (hpp : kemSelfPublicKeyBytes kem privKey = hop0.publicKey)
    (hcmdnn : ∀ c ∈ hop0.commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ hop0.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (p : Option ByteArray → Prop) [DecidablePred p] :
    |(Pr{let v ← tailReal kem cipher macS kdfS streamS geom hop0 restPath payload privKey
                  ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)}[p v]).toReal
      - (Pr{let v ← tailFresh kem cipher macS kdfS streamS geom restPath payload
                      ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength
                        + geom.perHopRoutingInfoLength)}[p v]).toReal|
    ≤ |(Pr{let x ← prgRealExperiment (hopKeyPRG kem kdfS hop0)
                    (tailKeyAdversary kem cipher macS kdfS streamS geom restPath payload
                      ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)
                      p)}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment
                      (tailKeyAdversary kem cipher macS kdfS streamS geom restPath payload
                        ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)
                        p)}[x = true]).toReal|
      + |(Pr{let x ← prgRealExperiment (lastBlockPRG streamS geom)
                      (tailBlockAdversary kem cipher macS kdfS streamS geom restPath payload
                        ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)
                        p)}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment
                      (tailBlockAdversary kem cipher macS kdfS streamS geom restPath payload
                        ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)
                        p)}[x = true]).toReal|
      + (Pr{let d ← tailDraw restPath
                    ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)}[
          tailBad kem cipher macS kdfS streamS geom hop0 restPath payload d]).toReal := by
  have h1 := tailAdvantage_le kem cipher macS kdfS streamS geom hvalid hmactag h16 hop0 restPath
    payload privKey hrest hpp hcmdnn hcmdnh p
  rw [prEvent_tailRealBlock_eq_prg, prEvent_tailIdeal_eq_prg] at h1
  exact h1.trans (add_le_add (prg_comp_le (hopKeyPRG kem kdfS hop0) (lastBlockPRG streamS geom)
    (tailBlockAdversary kem cipher macS kdfS streamS geom restPath payload _ p)) le_rfl)

end Games

end Cryptlib.Protocols.Sphinx.KEMSphinx
