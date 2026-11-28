/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTailChain

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
open Cryptlib.Util.Bytes (ofVector)

/-! # Tail indistinguishability, with the honest relay at any position

The setup for the hybrid chain of `KEMSphinxTailOracle`, with the adversary choosing the whole
path, and the game of Kuhn, Beck and Strufe's Definition 6 as its consequence. -/

section Uniform

/-- A filler followed by a block, masked: a longer filler. -/
def padFiller {a b c : Nat} (_hc : a + b = c) (mask : ByteArray) (f : Vector UInt8 a)
    (blk : Vector UInt8 b) : Vector UInt8 c :=
  Util.Bytes.toVecN c (ofVector f ++ xorBytes (ofVector blk) mask)

theorem ofVector_padFiller {a b c : Nat} (hc : a + b = c) (mask : ByteArray) (f : Vector UInt8 a)
    (blk : Vector UInt8 b) :
    ofVector (padFiller hc mask f blk) = ofVector f ++ xorBytes (ofVector blk) mask :=
  Util.Bytes.ofVector_toVecN _ (by simp [hc])

theorem padFiller_bijective {a b c : Nat} (hc : a + b = c) (mask : ByteArray) :
    Function.Bijective (Function.uncurry (padFiller hc mask (a := a) (b := b))) := by
  subst hc
  constructor
  · rintro ⟨f1, b1⟩ ⟨f2, b2⟩ h
    have h' : ofVector (padFiller rfl mask f1 b1) = ofVector (padFiller rfl mask f2 b2) :=
      congrArg ofVector h
    rw [ofVector_padFiller, ofVector_padFiller] at h'
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
      have e1 := ByteArray.extract_zero_size (b := xorBytes (ofVector b1) mask)
      have e2 := ByteArray.extract_zero_size (b := xorBytes (ofVector b2) mask)
      simp only [size_xorBytes, Cryptlib.Util.Bytes.size_ofVector] at e1 e2
      rw [e1, e2] at hr
      have := congrArg (fun x => xorBytes x mask) hr
      simpa only [xorBytes_xorBytes] using this
    have hf : f1 = f2 := by
      have := congrArg (Util.Bytes.toVecN a) hl'
      simpa only [Util.Bytes.toVecN_ofVector] using this
    have hb : b1 = b2 := by
      have := congrArg (Util.Bytes.toVecN b) hr'
      simpa only [Util.Bytes.toVecN_ofVector] using this
    rw [hf, hb]
  · intro z
    refine ⟨(Util.Bytes.toVecN a ((ofVector z).extract 0 a),
      Util.Bytes.toVecN b (xorBytes ((ofVector z).extract a (a + b)) mask)), ?_⟩
    show padFiller rfl mask _ _ = z
    unfold padFiller
    rw [Util.Bytes.ofVector_toVecN _ (by simp), Util.Bytes.ofVector_toVecN _ (by simp),
      xorBytes_xorBytes]
    have hz : (ofVector z).extract 0 a ++ (ofVector z).extract a (a + b) = ofVector z := by
      have := Cryptlib.Util.Bytes.append_extract (ofVector z) a (by simp)
      simpa only [Cryptlib.Util.Bytes.size_ofVector] using this
    rw [hz, Util.Bytes.toVecN_ofVector]

/-- The last `m` bytes of a uniform string are uniform. -/
theorem evalDistEq_suffix {δ : Type} (n m : Nat) (hm : m ≤ n) (J : ByteArray → ProbComp δ) :
    ($ᵗ (Vector UInt8 n) >>= fun u => J ((ofVector u).extract (n - m) n))
      =ᵈ ($ᵗ (Vector UInt8 m) >>= fun v => J (ofVector v)) := by
  have hc : (n - m) + m = n := by omega
  have h1 := evalDistEq_pair_of_bijective (padFiller_bijective hc (zeroBytes m))
    (fun u : Vector UInt8 n => J ((ofVector u).extract (n - m) n))
  have hs : ∀ (x : Vector UInt8 (n - m)) (y : Vector UInt8 m),
      (ofVector (padFiller hc (zeroBytes m) x y)).extract (n - m) n = ofVector y := by
    intro x y
    rw [ofVector_padFiller, xorBytes_zeroBytes,
      Cryptlib.Util.Bytes.extract_append_of_ge _ _ (by simp)]
    have e := ByteArray.extract_zero_size (b := ofVector y)
    simp only [Cryptlib.Util.Bytes.size_ofVector] at e ⊢
    rw [Nat.sub_self, show n - (n - m) = m from by omega]
    exact e
  simp only [hs] at h1
  exact h1.symm.trans (OracleComp.EvalDistEq.bind_const _ _)

/-- **A uniform filler followed by the masked tail of a uniform keystream is one uniform
filler.** -/
theorem evalDistEq_filler_suffix {δ : Type} (a b c L : Nat) (hc : a + b = c) (hb : b ≤ L)
    (mask : ByteArray) (J : ByteArray → ProbComp δ) :
    (do let f ← $ᵗ (Vector UInt8 a); let u ← $ᵗ (Vector UInt8 L)
        J (ofVector f ++ xorBytes ((ofVector u).extract (L - b) L) mask))
      =ᵈ ($ᵗ (Vector UInt8 c) >>= fun z => J (ofVector z)) := by
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun f =>
    evalDistEq_suffix L b hb fun v => J (ofVector f ++ xorBytes v mask)) ?_
  have h := evalDistEq_pair_of_bijective (padFiller_bijective hc mask)
    (fun z : Vector UInt8 c => J (ofVector z))
  simpa only [ofVector_padFiller] using h

end Uniform

section Arrays

variable {α : Type} [Inhabited α]

omit [Inhabited α] in
theorem size_mid (pre rest : Array α) (x : α) :
    (pre ++ #[x] ++ rest).size = pre.size + 1 + rest.size := by simp

theorem getElem!_mid_lt (pre rest : Array α) (x : α) (i : Nat) (h : i < pre.size) :
    (pre ++ #[x] ++ rest)[i]! = pre[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos pre i h,
    Array.getElem_append_left (by simp; omega), Array.getElem_append_left h]

theorem getElem!_mid_eq (pre rest : Array α) (x : α) :
    (pre ++ #[x] ++ rest)[pre.size]! = x := by
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_append_left (by simp),
    Array.getElem_append_right (Nat.le_refl _)]
  simp

theorem getElem!_mid_gt (pre rest : Array α) (x : α) (i : Nat) :
    (pre ++ #[x] ++ rest)[pre.size + 1 + i]! = rest[i]! := by
  by_cases h : i < rest.size
  · rw [getElem!_pos _ _ (by simp; omega), getElem!_pos rest i h,
      Array.getElem_append_right (by simp)]
    simp
  · rw [getElem!_neg _ _ (by simp; omega), getElem!_neg rest i h]

theorem getElem!_mid_ne (pre rest : Array α) (x y : α) (m : Nat) (h : m ≠ pre.size) :
    (pre ++ #[x] ++ rest)[m]! = (pre ++ #[y] ++ rest)[m]! := by
  by_cases h1 : m < pre.size
  · rw [getElem!_mid_lt _ _ _ _ h1, getElem!_mid_lt _ _ _ _ h1]
  · obtain ⟨i, rfl⟩ : ∃ i, m = pre.size + 1 + i := ⟨m - pre.size - 1, by omega⟩
    rw [getElem!_mid_gt, getElem!_mid_gt]

theorem extract_mid (pre rest : Array α) (x : α) :
    (pre ++ #[x] ++ rest).extract (pre.size + 1) (pre ++ #[x] ++ rest).size = rest := by
  apply Array.ext
  · simp
  · intro i h1 h2
    have := getElem!_mid_gt pre rest x i
    rw [getElem!_pos _ _ (by simp; omega), getElem!_pos rest i h2] at this
    simp only [Array.getElem_extract]
    exact this

theorem list_getElem!_append_lt (l : List α) (x : α) (i : Nat) (h : i < l.length) :
    (l ++ [x])[i]! = l[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos l i h, List.getElem_append_left h]

theorem list_getElem!_append_eq (l : List α) (x : α) : (l ++ [x])[l.length]! = x := by
  rw [getElem!_pos _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

end Arrays

section Setup

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- A hop's commands are those of a relay that forwards: no `null` and no `nextNodeHop`, which
the sender adds itself. -/
def relayCommands (hop : PathHop) : Prop :=
  ∀ c ∈ hop.commands, c ≠ RoutingCommand.null ∧ ∀ id m, c ≠ RoutingCommand.nextNodeHop id m

/-- The hops before the honest relay are usable: one private key for each, each deriving the
hop's public key, each hop forwarding, and the whole path no longer than the geometry allows. -/
def validPrefix (pre : Array PathHop) (sks : List ByteArray) (rest : Array PathHop) : Prop :=
  sks.length = pre.size ∧ pre.size + 1 + rest.size ≤ geom.nrHops ∧
  ∀ i, i < pre.size → kemSelfPublicKeyBytes kem sks[i]! = (pre[i]!).publicKey ∧
    relayCommands (pre[i]!)

/-- What the adversary submits: the hops before the honest relay with their private keys, the
honest relay's name and commands, the hops after it, and the message. -/
structure TIChoice where
  pre : Array PathHop
  preSK : List ByteArray
  tmpl : PathHop
  rest : Array PathHop
  payload : ByteArray

/-- The challenger's check of the adversary's submission. -/
def TIChoice.valid (ch : TIChoice) : Prop :=
  1 ≤ ch.rest.size ∧ relayCommands ch.tmpl ∧ validPrefix kem geom ch.pre ch.preSK ch.rest

/-- The challenger's randomness other than the honest relay's seed: the hops before the honest
relay that the challenge onion takes, the seeds for them and for the hops after, and the
filler. -/
structure TIOth where
  pre : Array PathHop
  preSK : List ByteArray
  preSeeds : Array (Vector UInt8 32)
  restSeeds : Array (Vector UInt8 32)
  filler : ByteArray

/-- A sampled prefix, replaced by the empty one when it would make the path too long. -/
def normPrefix (rest : Array PathHop) (p : Array PathHop × List ByteArray) :
    Array PathHop × List ByteArray :=
  if p.1.size + 1 + rest.size ≤ geom.nrHops then p else (#[], [])

variable (prefixOf : TIChoice → ProbComp (Array PathHop × List ByteArray))

/-- Draw the challenger's randomness. `prefixOf` gives the hops before the honest relay: the
adversary's own for its onion, a random choice for the alternative onion. -/
def tiDrawOth (ch : TIChoice) : ProbComp TIOth := do
  let p ← prefixOf ch
  let preSeeds ← $ᵗ (Vector (Vector UInt8 32) (normPrefix geom ch.rest p).1.size)
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) ch.rest.size)
  let filler ← $ᵗ (Vector UInt8 ((geom.nrHops - ch.rest.size
    - ((normPrefix geom ch.rest p).1.size + 1)) * geom.perHopRoutingInfoLength))
  return ⟨(normPrefix geom ch.rest p).1, (normPrefix geom ch.rest p).2, preSeeds.toArray,
    restSeeds.toArray, ofVector filler⟩

def tiDrawFr (ch : TIChoice) : ProbComp (Array (Vector UInt8 32) × ByteArray) := do
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) ch.rest.size)
  let filler ← $ᵗ (Vector UInt8 ((geom.nrHops - ch.rest.size) * geom.perHopRoutingInfoLength))
  return (restSeeds.toArray, ofVector filler)

open Classical in
/-- The real challenge: build the onion on the whole path, have every hop up to and including
the honest relay process it, and give out what the honest relay forwards. -/
noncomputable def tiRealView (pk : kem.PublicKey) (sk : kem.PrivateKey) (ch : TIChoice)
    (s : Vector UInt8 32) (o : TIOth) : Option ByteArray :=
  if TIChoice.valid kem geom ch then
    match newKEMPacket kem cipher macS kdfS streamS geom (o.preSeeds ++ #[s] ++ o.restSeeds) o.filler
        (o.pre ++ #[honestHop kem ch.tmpl pk] ++ ch.rest) ch.payload with
    | .ok pkt => chainForward kem cipher macS kdfS streamS geom (o.preSK ++ [ofVector (kem.encodePrivateKey sk)]) pkt
    | .error _ => none
  else none

/-- The mask on the blocks the hops append: everything in them but the honest relay's
keystream. It does not depend on the honest relay's key or seed. -/
def tiMask (ch : TIChoice) (o : TIOth) : ByteArray :=
  padsS geom (Function.update
      (ksReal kem kdfS streamS geom (o.pre ++ #[ch.tmpl] ++ ch.rest)
        (o.preSeeds ++ #[default] ++ o.restSeeds))
      o.pre.size (zeroBytes (ksLen geom)))
    (o.pre.size + 1 + ch.rest.size) (o.pre.size + 1) 0

open Classical in
/-- The challenge with the honest relay's header keystream given directly. -/
noncomputable def tiKsView (ch : TIChoice) (o : TIOth) (u : Keystream geom) : Option ByteArray :=
  if TIChoice.valid kem geom ch then
    (newKEMPacket kem cipher macS kdfS streamS geom o.restSeeds
      (o.filler ++ xorBytes ((ofVector u).extract
        (ksLen geom - (o.pre.size + 1) * geom.perHopRoutingInfoLength) (ksLen geom))
        (tiMask kem kdfS streamS geom ch o)) ch.rest ch.payload).toOption
  else none

open Classical in
/-- The fresh challenge: an onion built on the hops after the honest relay alone. -/
noncomputable def tiFreshView (ch : TIChoice) (y : Array (Vector UInt8 32) × ByteArray) :
    Option ByteArray :=
  if TIChoice.valid kem geom ch then
    (newKEMPacket kem cipher macS kdfS streamS geom y.1 y.2 ch.rest ch.payload).toOption
  else none

/-- The draws the exact theorem does not cover, for a submission the challenger accepts. -/
def tiSetupBad (pk : kem.PublicKey) (sk : kem.PrivateKey) (ch : TIChoice) (s : Vector UInt8 32)
    (o : TIOth) : Prop :=
  TIChoice.valid kem geom ch ∧
  ¬ (o.preSeeds.size = o.pre.size ∧ o.restSeeds.size = ch.rest.size ∧
    o.filler.size = (geom.nrHops - (o.pre.size + 1 + ch.rest.size))
      * geom.perHopRoutingInfoLength ∧
    validPrefix kem geom o.pre o.preSK ch.rest ∧
    kemSelfPublicKeyBytes kem (ofVector (kem.encodePrivateKey sk))
      = ofVector (kem.encodePublicKey pk) ∧
    (∀ j, j < o.pre.size + 1 + ch.rest.size →
      kem.Reliable (kem.stateFromSeed (o.preSeeds ++ #[s] ++ o.restSeeds)[j]!)) ∧
    ∃ pkt, newKEMPacket kem cipher macS kdfS streamS geom (o.preSeeds ++ #[s] ++ o.restSeeds) o.filler
      (o.pre ++ #[honestHop kem ch.tmpl pk] ++ ch.rest) ch.payload = Except.ok pkt)

set_option maxHeartbeats 1000000 in
/-- **Off the bad draws, the real challenge depends on the honest relay's seed only through the
relay's header keystream.** -/
theorem tiRealView_eq (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (pk : kem.PublicKey) (sk : kem.PrivateKey) (ch : TIChoice) (s : Vector UInt8 32) (o : TIOth)
    (hgood : ¬ tiSetupBad kem cipher macS kdfS streamS geom pk sk ch s o) :
    tiRealView kem cipher macS kdfS streamS geom pk sk ch s o
      = tiKsView kem cipher macS kdfS streamS geom ch o (honestKeystream kem kdfS streamS geom pk s) := by
  unfold tiRealView tiKsView
  by_cases hv : TIChoice.valid kem geom ch
  · rw [if_pos hv, if_pos hv]
    obtain ⟨hps, hrs, hfs, ⟨hsl, hlen, hpre⟩, hpp, hrel, pkt, hnk⟩ :=
      Classical.not_not.mp fun hb => hgood ⟨hv, hb⟩
    obtain ⟨hrest, htc, -⟩ := hv
    obtain ⟨-, -, hrouting, -, -, -⟩ := id hvalid
    rw [hnk]
    dsimp only
    have hl : (o.preSK ++ [ofVector (kem.encodePrivateKey sk)]).length = o.pre.size + 1 := by
      simp [hsl]
    have hch := chainForward_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 ch.payload
      (o.preSK ++ [ofVector (kem.encodePrivateKey sk)])
      (o.pre ++ #[honestHop kem ch.tmpl pk] ++ ch.rest) (o.preSeeds ++ #[s] ++ o.restSeeds)
      o.filler pkt
      (by rw [hl, size_mid]; omega)
      (by rw [size_mid]; exact hfs)
      (fun i hi => by
        rw [hl] at hi
        by_cases h1 : i < o.pre.size
        · rw [list_getElem!_append_lt _ _ i (by omega), getElem!_mid_lt _ _ _ i h1]
          exact (hpre i h1).1
        · obtain rfl : i = o.preSK.length := by omega
          rw [list_getElem!_append_eq, hsl, getElem!_mid_eq]
          exact hpp)
      (fun j hj => hrel j (by rw [size_mid] at hj; exact hj))
      (fun i hi => by
        rw [hl] at hi
        by_cases h1 : i < o.pre.size
        · rw [getElem!_mid_lt _ _ _ i h1]
          exact (hpre i h1).2
        · obtain rfl : i = o.pre.size := by omega
          rw [getElem!_mid_eq]
          exact htc)
      hnk
    rw [hch, hl, extract_mid]
    have hse : (o.preSeeds ++ #[s] ++ o.restSeeds).extract (o.pre.size + 1)
        (o.preSeeds ++ #[s] ++ o.restSeeds).size = o.restSeeds := by
      rw [← hps]
      exact extract_mid _ _ _
    rw [hse, size_mid]
    have hksh : ksReal kem kdfS streamS geom (o.pre ++ #[honestHop kem ch.tmpl pk] ++ ch.rest)
        (o.preSeeds ++ #[s] ++ o.restSeeds) o.pre.size
        = ofVector (honestKeystream kem kdfS streamS geom pk s) := by
      have hk : kemHopKeys kem kdfS (o.pre ++ #[honestHop kem ch.tmpl pk] ++ ch.rest)
          (o.preSeeds ++ #[s] ++ o.restSeeds) o.pre.size
          = kemHopKeys kem kdfS #[honestHop kem ch.tmpl pk] #[s] 0 := by
        have e2 : (o.preSeeds ++ #[s] ++ o.restSeeds)[o.pre.size]! = s := by
          rw [← hps]
          exact getElem!_mid_eq _ _ _
        unfold kemHopKeys
        rw [getElem!_mid_eq, e2]
        simp
      unfold ksReal honestKeystream
      rw [hk, kemHopKeys_encapOf kem kdfS _ pk rfl s]
      exact (Util.Bytes.ofVector_toVecN _ (streamS.keystream_size _ _ _)).symm
    have hmask : Function.update (ksReal kem kdfS streamS geom
          (o.pre ++ #[honestHop kem ch.tmpl pk] ++ ch.rest) (o.preSeeds ++ #[s] ++ o.restSeeds))
          o.pre.size (zeroBytes (ksLen geom))
        = Function.update (ksReal kem kdfS streamS geom (o.pre ++ #[ch.tmpl] ++ ch.rest)
          (o.preSeeds ++ #[default] ++ o.restSeeds)) o.pre.size (zeroBytes (ksLen geom)) := by
      funext m
      by_cases hm : m = o.pre.size
      · rw [hm, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hm, Function.update_of_ne hm]
        unfold ksReal kemHopKeys
        rw [getElem!_mid_ne o.pre ch.rest (honestHop kem ch.tmpl pk) ch.tmpl m hm,
          getElem!_mid_ne o.preSeeds o.restSeeds s default m (by rw [hps]; exact hm)]
    have hpads := padsS_update geom
      (ksReal kem kdfS streamS geom (o.pre ++ #[honestHop kem ch.tmpl pk] ++ ch.rest)
        (o.preSeeds ++ #[s] ++ o.restSeeds))
      (ksReal_size kem kdfS streamS geom _ _) hrouting (o.pre.size + 1 + ch.rest.size) hlen
      o.pre.size (by omega) (ofVector (honestKeystream kem kdfS streamS geom pk s))
      (by simp) o.pre.size 0 (by omega)
    rw [← hksh, Function.update_eq_self, hmask] at hpads
    rw [hpads, hksh]
    rfl
  · rw [if_neg hv, if_neg hv]

/-- **With a uniform keystream in place of the honest relay's, the challenge is distributed as
the fresh one.** -/
theorem tiKs_fresh (hvalid : geom.ValidForKEM kem) (ch : TIChoice)
    (K : Option ByteArray → ProbComp Bool) :
    (do let o ← tiDrawOth geom prefixOf ch; let u ← $ᵗ (Keystream geom)
        K (tiKsView kem cipher macS kdfS streamS geom ch o u))
      =ᵈ (tiDrawFr geom ch >>= fun y => K (tiFreshView kem cipher macS kdfS streamS geom ch y)) := by
  obtain ⟨-, -, hrouting, -, -, -⟩ := id hvalid
  by_cases hv : TIChoice.valid kem geom ch
  · unfold tiDrawOth tiDrawFr
    simp only [bind_assoc, pure_bind, tiKsView, tiFreshView, if_pos hv]
    have hj : ∀ p : Array PathHop × List ByteArray,
        (normPrefix geom ch.rest p).1.size + 1 + ch.rest.size ≤ geom.nrHops := by
      intro p
      unfold normPrefix
      split
      · assumption
      · have := hv.2.2.2.1
        simp only [Array.size_empty]
        omega
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun p => EvalDistEq.bind_right _
      fun preSeeds => EvalDistEq.bind_right _ fun restSeeds =>
      evalDistEq_filler_suffix _ _
        ((geom.nrHops - ch.rest.size) * geom.perHopRoutingInfoLength) (ksLen geom)
        (by
          rw [← Nat.add_mul]
          congr 1
          have := hj p
          omega)
        (block_le geom hrouting _ (by have := hj p; omega))
        (tiMask kem kdfS streamS geom ch
          ⟨(normPrefix geom ch.rest p).1, (normPrefix geom ch.rest p).2, preSeeds.toArray,
            restSeeds.toArray, ByteArray.empty⟩)
        (fun x => K (newKEMPacket kem cipher macS kdfS streamS geom restSeeds.toArray x ch.rest ch.payload).toOption)) ?_
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun p =>
      OracleComp.EvalDistEq.bind_const _ _) ?_
    exact OracleComp.EvalDistEq.bind_const _ _
  · simp only [tiKsView, tiFreshView, if_neg hv]
    have h1 : (do let _ ← tiDrawOth geom prefixOf ch; let _ ← $ᵗ (Keystream geom); K none)
        =ᵈ K none :=
      (EvalDistEq.bind_right _ fun _ => OracleComp.EvalDistEq.bind_const _ _).trans
        (OracleComp.EvalDistEq.bind_const _ _)
    exact h1.trans (OracleComp.EvalDistEq.bind_const _ _).symm

/-- The setup for the hybrid chain with the honest relay at any position. -/
noncomputable def tiSetup (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength) :
    TailSetup kem kdfS streamS geom where
  Ch := TIChoice
  Oth := TIOth
  Fr := Array (Vector UInt8 32) × ByteArray
  drawOth := tiDrawOth geom prefixOf
  drawFr := tiDrawFr geom
  realView := tiRealView kem cipher macS kdfS streamS geom
  ksView := tiKsView kem cipher macS kdfS streamS geom
  freshView := tiFreshView kem cipher macS kdfS streamS geom
  bad := tiSetupBad kem cipher macS kdfS streamS geom
  real_eq := fun pk sk ch s o h => tiRealView_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 pk sk ch s o h
  ks_fresh := fun ch K => tiKs_fresh kem cipher macS kdfS streamS geom prefixOf hvalid ch K

end Setup

section Def6

open PRGScheme

variable {kem : KEM} (cipher : WideBlockCipher) (macS : MAC) {kdfS : KDF} {streamS : StreamCipher}
  {geom : Geometry} [SampleableType kem.Plaintext]

/-- The bound of the hybrid chain: the advantage against the KEM with a decapsulation oracle,
against the KDF as a generator, against the stream cipher as a generator, and the probability
of the bad draws. -/
noncomputable def tioBound {S : TailSetup kem kdfS streamS geom} (A : TIOAdversary S) : ℝ :=
  |(Pr{let x ← kemOExp (tioKEMAdv cipher macS A) true}[x = true]).toReal
      - (Pr{let x ← kemOExp (tioKEMAdv cipher macS A) false}[x = true]).toReal|
    + |(Pr{let x ← prgRealExperiment (secretKeyPRG kem kdfS)
                    (tioKeyAdv cipher macS A)}[x = true]).toReal
      - (Pr{let x ← prgIdealExperiment (tioKeyAdv cipher macS A)}[x = true]).toReal|
    + |(Pr{let x ← prgRealExperiment (keystreamPRG streamS geom)
                    (tioKSAdv cipher macS A)}[x = true]).toReal
      - (Pr{let x ← prgIdealExperiment (tioKSAdv cipher macS A)}[x = true]).toReal|
    + (Pr{let d ← tioDraw cipher macS A}[
        S.bad (keygenOf kem d.1).1 (keygenOf kem d.1).2 d.2.1.1 d.2.2.1 d.2.2.2]).toReal

theorem tioAdvantage_le_bound {S : TailSetup kem kdfS streamS geom} (A : TIOAdversary S) :
    |(Pr{let x ← tioReal cipher macS A}[x = true]).toReal
      - (Pr{let x ← tioFresh cipher macS A}[x = true]).toReal| ≤ tioBound cipher macS A :=
  tioAdvantage_le cipher macS A

variable (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

/-- The adversary's own choice of the hops before the honest relay. -/
def ownPrefix (ch : TIChoice) : ProbComp (Array PathHop × List ByteArray) :=
  pure (ch.pre, ch.preSK)

/-- An adversary does not depend on how the challenger chooses the hops before the honest
relay. -/
def TIOAdversary.withPrefix {p : TIChoice → ProbComp (Array PathHop × List ByteArray)}
    (A : TIOAdversary (tiSetup kem cipher macS kdfS streamS geom p hvalid hmactag h16))
    (q : TIChoice → ProbComp (Array PathHop × List ByteArray)) :
    TIOAdversary (tiSetup kem cipher macS kdfS streamS geom q hvalid hmactag h16) :=
  ⟨A.St, A.pre, A.post⟩

/-- **Tail indistinguishability for KEM-Sphinx with the honest relay at any position.** The
adversary is given the honest relay's public key and its oracle, before and after the challenge.
It submits a path through the honest relay, with key pairs for the hops before it, and a
message. Its advantage in telling what the honest relay forwards from a fresh onion on the hops
after the relay is at most `tioBound`. -/
theorem tiAnyPosition_le
    (A : TIOAdversary (tiSetup kem cipher macS kdfS streamS geom ownPrefix hvalid hmactag h16)) :
    |(Pr{let x ← tioReal cipher macS A}[x = true]).toReal
      - (Pr{let x ← tioFresh cipher macS A}[x = true]).toReal| ≤ tioBound cipher macS A :=
  tioAdvantage_le cipher macS A

/-- The game of Kuhn, Beck and Strufe's Definition 6. For `b = false` the adversary is given the
layer of its own onion that the honest relay forwards. For `b = true` it is given the same layer
of an alternative onion, with the same message and the same hops after the honest relay, whose
hops before the honest relay are drawn by `alt`. -/
noncomputable def ti6Game (alt : TIChoice → ProbComp (Array PathHop × List ByteArray))
    (A : TIOAdversary (tiSetup kem cipher macS kdfS streamS geom ownPrefix hvalid hmactag h16)) (b : Bool) :
    ProbComp Bool :=
  if b then tioReal cipher macS (A.withPrefix cipher macS hvalid hmactag h16 alt)
  else tioReal cipher macS A

/-- **Tail indistinguishability (Definition 6) for KEM-Sphinx.** For any way `alt` of drawing the
alternative onion's hops before the honest relay, the adversary's advantage in telling its own
onion's layer from the alternative's is at most the bound of the hybrid chain for each of the
two. -/
theorem ti6Advantage_le (alt : TIChoice → ProbComp (Array PathHop × List ByteArray))
    (A : TIOAdversary (tiSetup kem cipher macS kdfS streamS geom ownPrefix hvalid hmactag h16)) :
    |(Pr{let x ← ti6Game cipher macS hvalid hmactag h16 alt A false}[x = true]).toReal
      - (Pr{let x ← ti6Game cipher macS hvalid hmactag h16 alt A true}[x = true]).toReal|
    ≤ tioBound cipher macS A
      + tioBound cipher macS (A.withPrefix cipher macS hvalid hmactag h16 alt) := by
  have h0 := tioAdvantage_le_bound cipher macS A
  have hf : tioFresh cipher macS (A.withPrefix cipher macS hvalid hmactag h16 alt)
      = tioFresh cipher macS A := rfl
  simp only [ti6Game, if_true, Bool.false_eq_true, if_false]
  obtain ⟨A', hA'⟩ : ∃ A', A' = A.withPrefix cipher macS hvalid hmactag h16 alt := ⟨_, rfl⟩
  rw [← hA'] at hf ⊢
  have h1 := tioAdvantage_le_bound cipher macS A'
  rw [hf] at h1
  have t := abs_sub_le (Pr{let x ← tioReal cipher macS A}[x = true]).toReal
    (Pr{let x ← tioFresh cipher macS A}[x = true]).toReal
    (Pr{let x ← tioReal cipher macS A'}[x = true]).toReal
  rw [abs_sub_comm (Pr{let x ← tioFresh cipher macS A}[x = true]).toReal] at t
  linarith

end Def6

end Cryptlib.Protocols.Sphinx.KEMSphinx
