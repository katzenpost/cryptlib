/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only

`wApprox_eq` and `cs2_bound` are adapted from VCVio's `LatticeCrypto/MLDSA/Scheme.lean` and
`Extern/MLDSA/Laws.lean`, Copyright (c) 2026 Quang Dao and Oleksandr Vovkotrub, released under the
Apache License 2.0.
-/

import LatticeCrypto.MLDSA.Signature
import LatticeCrypto.MLDSA.Concrete.Rounding
import Cryptlib.Primitives.Sign.MLDSA.Sampling
import Cryptlib.Primitives.Sign.Sign
import Cryptlib.Util.Bytes

/-! # ML-DSA (FIPS 204) correctness

VCVio's ML-DSA specification with the concrete rounding, NTT and encodings, and the samplers of
`Sampling.lean` over pure-Lean SHAKE. `correct`: for keys generated from any seed, a signature the
bounded signing loop returns verifies. VCVio proves this from five facts about the primitives; the
rounding and NTT facts are VCVio's concrete lemmas, the key identity `wApprox_eq` follows from
`t = A·s₁ + s₂` and Power2Round alone, and the challenge-product bound `cs2_bound` from the
samplers' output ranges.

`scheme` is ML-DSA as a `Signature`: external-mode signing with an empty context (`M' = 0 ‖ 0 ‖ M`),
hedged with 32 bytes of randomness per signature drawn from the signing state, a private key that
is its 32-byte seed `ξ` (so every private key is honestly generated), and keys and signatures in
their FIPS 204 byte encodings. Signing aborts if the loop gives up after `maxAttempts` tries, or if
the encodings of the key or signature would not decode back to them; then `correct` gives
`verify_sign`. -/

namespace Cryptlib.Primitives.Sign.FIPS204

open MLDSA MLDSA.Concrete LatticeCrypto TransformOps

/-- ML-DSA's primitives for a parameter set. -/
def prims (p : Params) : Primitives p where
  High := High
  Power2High := Power2High
  Hint := Hint
  expandSeed := fun seed => expandSeed seed p
  expandA := fun rho => expandA rho p
  expandS := fun rhoPrime => expandS rhoPrime p
  expandMask := fun rhoPrime kappa => expandMask rhoPrime kappa p
  sampleInBall := fun cTilde => sampleInBall p cTilde
  hashMessage := hashMessage
  hashPrivateSeed := hashPrivateSeed
  hashCommitment := fun mu w1 => hashCommitmentBytes mu (ByteArray.mk w1.toArray) p
  hashPublicKey := fun rho t1 => hashPublicKeyBytes (pkEncode p rho t1)
  highBits := MLDSA.Concrete.highBits p
  highBitsShift := MLDSA.Concrete.highBitsShift p
  lowBits := MLDSA.Concrete.lowBits p
  makeHint := MLDSA.Concrete.makeHint p
  useHint := MLDSA.Concrete.useHint p
  power2Round := MLDSA.Concrete.power2Round
  power2RoundShift := MLDSA.Concrete.power2RoundShift
  w1Encode := MLDSA.Concrete.w1Encode p
  hintWeight := fun h => h.toList.foldl (fun acc hi => acc + MLDSA.Concrete.hintWeight hi) 0

instance ops : NTTRingOps := concreteNTTRingOps

variable (p : Params)

theorem useHint_makeHint (hp : p.isApproved) (z r : Rq) (hz : polyNorm z ≤ p.gamma2) :
    (prims p).useHint ((prims p).makeHint z r) r = (prims p).highBits (r + z) := by
  apply concreteRounding_useHint_correct_of_isApproved p hp z r
  rwa [← polyNorm_eq_cInfNorm]

theorem hide_low (hp : p.isApproved) (r s : Rq) (b : ℕ) (hs : polyNorm s ≤ b)
    (hlow : polyNorm ((prims p).lowBits r) + b < p.gamma2) :
    (prims p).highBits (r + s) = (prims p).highBits r := by
  apply concreteRounding_hide_low_of_isApproved p hp r s b
  · rwa [← polyNorm_eq_cInfNorm]
  · rw [← polyNorm_eq_cInfNorm]; exact hlow

/-- The key identity `A·z - c·(t₁·2^d) = A·y - c·s₂ + c·t₀` for `z = y + c·s₁` and keys from a seed,
from `t = A·s₁ + s₂`, Power2Round and the NTT laws. -/
theorem wApprox_eq {pk : PublicKey p (prims p)} {sk : SecretKey p} (seed : Bytes 32)
    (hkeygen : keyGenFromSeed p (prims p) seed = (pk, sk)) :
    ∀ (c : Rq) (y : RqVec p.l),
      computeWApprox p (prims p) ((prims p).expandA pk.rho) c (y + c • sk.s1) pk.t1 =
      ((prims p).expandA pk.rho) * y - c • sk.s2 + c • sk.t0 := by
  intro c y
  let laws := concreteNTTRingLaws
  set aHat := (prims p).expandA pk.rho
  simp only [computeWApprox]
  refine Vector.ext fun i hi => ?_
  simp only [Vector.getElem_add, Vector.getElem_sub,
    ops.hatVec_add, ops.unhatVec_sub, ops.matVecMul_add, ops.unhatVec_add]
  have h_kg : (prims p).power2RoundShiftVec pk.t1 + sk.t0 = aHat * sk.s1 + sk.s2 := by
    simp only [keyGenFromSeed, Prod.mk.injEq] at hkeygen
    obtain ⟨hpk, hsk⟩ := hkeygen
    have hrho  := congr_arg PublicKey.rho hpk.symm
    have hs1   := congr_arg SecretKey.s1 hsk.symm
    have hs2   := congr_arg SecretKey.s2 hsk.symm
    have haHat : aHat = (prims p).expandA ((prims p).expandSeed seed).1 := by simp [aHat, hrho]
    rw [show pk.t1 = ((prims p).power2RoundVec (aHat * sk.s1 + sk.s2)).1 from by
          rw [hs1, hs2, haHat]; exact congr_arg PublicKey.t1 hpk.symm,
        show sk.t0 = ((prims p).power2RoundVec (aHat * sk.s1 + sk.s2)).2 from by
          rw [hs1, hs2, haHat]; exact congr_arg SecretKey.t0 hsk.symm]
    refine Vector.ext fun i hi => ?_
    simp only [Vector.getElem_add, Primitives.power2RoundShiftVec, Primitives.power2RoundVec,
      Vector.map_map, Vector.getElem_map, Function.comp]
    exact concretePower2Round_high_low_decomp _
  have hAs1_hat : ops.matVecMul aHat (ops.hatVec sk.s1) =
      ops.hatVec ((prims p).power2RoundShiftVec pk.t1 + sk.t0 - sk.s2) := by
    rw [h_kg]
    refine Vector.ext fun j hj => ?_
    simp only [hatVec, HMul.hMul, coeffMatVecMul, unhatVec, matVecMul,
               Vector.getElem_map, Vector.getElem_sub, Vector.getElem_add]
    have hcancel : (fromHat (dot ops aHat[j] (Vector.map toHat sk.s1)) : Rq) +
        sk.s2[j] - sk.s2[j] = fromHat (dot ops aHat[j] (Vector.map toHat sk.s1)) := by
      abel
    rw [hcancel, laws.toHat_fromHat]
  have hMatScalarComm : ops.matVecMul aHat (ops.hatVec (c • sk.s1)) =
      ops.scalarVecMul (toHat c) (ops.matVecMul aHat (ops.hatVec sk.s1)) := by
    have hNTTSmul : ops.hatVec (c • sk.s1) = ops.scalarVecMul (toHat c) (ops.hatVec sk.s1) := by
      refine Vector.ext fun j hj => ?_
      simp only [hatVec, scalarVecMul, Vector.getElem_map]
      change ops.toHat (ops.coeffScalarVecMul c sk.s1)[j] = _
      simp only [coeffScalarVecMul, unhatVec, scalarVecMul, hatVec,
                 Vector.map_map, Vector.getElem_map, Function.comp_apply, laws.toHat_fromHat]
    rw [hNTTSmul]
    refine Vector.ext fun j hj => ?_
    simp only [matVecMul, scalarVecMul, Vector.getElem_map]
    exact ops.dot_scalar_right (toHat c) _ _
  simp only [hMatScalarComm, hAs1_hat]
  change (aHat * y)[i] +
      (ops.coeffScalarVecMul c ((prims p).power2RoundShiftVec pk.t1 + sk.t0 - sk.s2))[i] -
      (ops.coeffScalarVecMul c ((prims p).power2RoundShiftVec pk.t1))[i] =
      (aHat * y)[i] - (ops.coeffScalarVecMul c sk.s2)[i] + (ops.coeffScalarVecMul c sk.t0)[i]
  simp only [ops.coeffScalarVecMul_sub, ops.coeffScalarVecMul_add, Vector.getElem_sub,
    Vector.getElem_add]
  abel

/-- `‖c · s‖∞ ≤ τ · η = β` for a challenge and an `η`-bounded secret: `SampleInBall` has at most `τ`
nonzero `±1` coefficients. -/
theorem cs2_bound (cTilde : CommitHashBytes p) {k : ℕ} (s : RqVec k) (hs : polyVecBounded s p.eta)
    (j : Fin k) : cInfNorm (((prims p).sampleInBall cTilde • s).get j) ≤ p.beta := by
  change cInfNorm ((concreteNTTRingOps.coeffScalarVecMul ((prims p).sampleInBall cTilde) s).get j) ≤
    p.beta
  rw [coeffScalarVecMul_get (laws := concreteNTTRingLaws)]
  refine le_trans (cInfNorm_mul_le (sampleInBall p cTilde) (s.get j)) ?_
  have hl1 : l1Norm (sampleInBall p cTilde) ≤ p.tau := sampleInBall_l1Norm p cTilde
  have hsj : cInfNorm (s.get j) ≤ p.eta := by
    have := (PolyVec.cInfNorm_le_iff (ops := normOps)).mp hs j
    rwa [← polyNorm_eq_cInfNorm]
  exact Nat.mul_le_mul hl1 hsj

/-- ML-DSA is correct: for keys from any seed, a signature the signing loop returns verifies. -/
theorem correct (hp : p.isApproved) (seed : Bytes 32) (msg : List Byte)
    (sig : FIPSSignature p (prims p)) (rhoDoublePrime : Bytes 64) (maxAttempts : ℕ)
    (h_sign : fipsSignLoop p (prims p) (keyGenFromSeed p (prims p) seed).2
      ((prims p).expandA (keyGenFromSeed p (prims p) seed).1.rho)
      ((prims p).hashMessage (keyGenFromSeed p (prims p) seed).2.tr msg)
      rhoDoublePrime maxAttempts = some sig) :
    fipsVerify p (prims p) (keyGenFromSeed p (prims p) seed).1 msg sig = true := by
  rcases hk : keyGenFromSeed p (prims p) seed with ⟨pk, sk⟩
  rw [hk] at h_sign
  have hs2 : polyVecBounded sk.s2 p.eta := by
    have h := congrArg Prod.snd hk
    simp only [keyGenFromSeed] at h
    rw [← h]
    exact (expandS_bound _ p).2
  exact fipsSign_fipsVerify_correct' p (prims p) pk sk msg sig rhoDoublePrime maxAttempts
    ((validKeyPair_eq_true_iff p (prims p) pk sk).mpr ⟨seed, hk⟩) (useHint_makeHint p hp)
    (hide_low p hp) (wApprox_eq p seed hk) (cs2_bound p sig.cTilde sk.s2 hs2) h_sign

/-! ## As a `Signature` -/

open Cryptlib.Primitives.Sign.Sign
open Cryptlib.Util.Bytes (ofVector toVecN ofVector_toVecN)

/-- External ML-DSA's `M' = 0 ‖ |ctx| ‖ ctx ‖ M`, with an empty context. -/
def messagePrime (m : ByteArray) : List Byte := 0 :: 0 :: m.toList

/-- Signing attempts before giving up; ML-DSA-65 needs about five on average. -/
def maxAttempts : Nat := 1000

/-- A counter and a seed: the `i`-th signature's 32 random bytes are `SHAKE-256(seed ‖ i)`. -/
abbrev State := Nat × Vector UInt8 32

def rnd (s : State) : Bytes 32 :=
  toVecN 32 (VCVio.Algorithms.Keccak.shake256 (ofVector s.2 ++ ⟨(Array.range 8).map fun j =>
    (s.1 >>> (8 * j)).toUInt8⟩) 32)

def keys (p : Params) (seed : Bytes 32) : PublicKey p (prims p) × SecretKey p :=
  keyGenFromSeed p (prims p) seed

def pkBytes (p : Params) (pk : PublicKey p (prims p)) : ByteArray := pkEncode p pk.rho pk.t1

def sigBytes (p : Params) (sig : FIPSSignature p (prims p)) : ByteArray :=
  sigEncode p sig.cTilde sig.z sig.h

/-- The encodings of a key and a signature decode back to them, at their FIPS 204 sizes. -/
def Encodes (p : Params) (pk : PublicKey p (prims p)) (sig : FIPSSignature p (prims p)) : Prop :=
  (pkBytes p pk).size = p.publicKeyBytes ∧ pkDecode p (pkBytes p pk) = (pk.rho, pk.t1) ∧
    (sigBytes p sig).size = p.signatureBytes ∧
    sigDecode p (sigBytes p sig) = some (sig.cTilde, sig.z, sig.h)

instance (p : Params) : DecidableEq (prims p).Power2High := inferInstanceAs (DecidableEq Rq)
instance (p : Params) : DecidableEq (prims p).Hint := inferInstanceAs (DecidableEq Hint)

instance (p : Params) (pk : PublicKey p (prims p)) (sig : FIPSSignature p (prims p)) :
    Decidable (Encodes p pk sig) := by
  unfold Encodes
  refine @instDecidableAnd _ _ (Nat.decEq _ _) (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _
    (Nat.decEq _ _) ?_))
  · exact decEq _ _
  · exact decEq _ _

/-- Signing with a key pair and its matrix `Â`. -/
def signWith (p : Params) (k : PublicKey p (prims p) × SecretKey p) (aHat : TqMatrix p.k p.l)
    (m : ByteArray) : EStateM SignError State (Vector UInt8 p.signatureBytes) := fun s =>
  let mu := (prims p).hashMessage k.2.tr (messagePrime m)
  match fipsSignLoop p (prims p) k.2 aHat mu
      ((prims p).hashPrivateSeed k.2.key (rnd s) mu) maxAttempts with
  | none => .error .aborted (s.1 + 1, s.2)
  | some sig =>
    if Encodes p k.1 sig then .ok (toVecN _ (sigBytes p sig)) (s.1 + 1, s.2)
    else .error .aborted (s.1 + 1, s.2)

def signM (p : Params) (seed : Bytes 32) (m : ByteArray) :
    EStateM SignError State (Vector UInt8 p.signatureBytes) :=
  let k := keys p seed
  signWith p k ((prims p).expandA k.1.rho) m

/-- A private key expanded once: its key pair and the matrix `Â`, which `signM` derives again for
every signature. -/
structure Expanded (p : Params) where
  seed : Bytes 32
  keys : PublicKey p (prims p) × SecretKey p
  aHat : TqMatrix p.k p.l
  keys_eq : keys = FIPS204.keys p seed
  aHat_eq : aHat = (prims p).expandA keys.1.rho

def expand (p : Params) (seed : Bytes 32) : Expanded p :=
  let k := keys p seed
  { seed, keys := k, aHat := (prims p).expandA k.1.rho, keys_eq := rfl, aHat_eq := rfl }

/-- `signM` with the key already expanded. -/
def signExpanded (p : Params) (e : Expanded p) (m : ByteArray) :
    EStateM SignError State (Vector UInt8 p.signatureBytes) :=
  signWith p e.keys e.aHat m

theorem signExpanded_eq (p : Params) (e : Expanded p) (m : ByteArray) :
    signExpanded p e m = signM p e.seed m := by
  obtain ⟨seed, keys, aHat, hk, ha⟩ := e
  subst hk ha
  rfl

def verifyBytes (p : Params) (pk : Vector UInt8 p.publicKeyBytes) (m : ByteArray)
    (sig : Vector UInt8 p.signatureBytes) : Bool :=
  let (rho, t1) := pkDecode p (ofVector pk)
  match sigDecode p (ofVector sig) with
  | some (cTilde, z, h) => fipsVerify p (prims p) ⟨rho, t1⟩ (messagePrime m) ⟨cTilde, z, h⟩
  | none => false

theorem verify_signM (p : Params) (hp : p.isApproved) (seed : Bytes 32) (m : ByteArray) (s : State)
    (σ : Vector UInt8 p.signatureBytes) (s' : State) (h : signM p seed m s = .ok σ s') :
    verifyBytes p (toVecN _ (pkBytes p (keys p seed).1)) m σ = true := by
  unfold signM signWith at h
  dsimp only at h
  split at h
  · nomatch h
  · rename_i sig hloop
    split at h
    · rename_i henc
      obtain ⟨hpks, hpkd, hsigs, hsigd⟩ := henc
      cases h
      have hv := correct p hp seed (messagePrime m) sig _ maxAttempts hloop
      unfold verifyBytes
      rw [ofVector_toVecN _ hpks, ofVector_toVecN _ hsigs, hpkd, hsigd]
      exact hv
    · nomatch h

def scheme (p : Params) (hp : p.isApproved) : Signature where
  State := State
  PublicKey := Vector UInt8 p.publicKeyBytes
  PrivateKey := Vector UInt8 32
  Sig := Vector UInt8 p.signatureBytes
  seedSize := 32
  publicKeySize := p.publicKeyBytes
  privateKeySize := 32
  sigSize := p.signatureBytes
  encodePublicKey := id
  decodePublicKey := some
  encodePrivateKey := id
  decodePrivateKey := some
  encodeSig := id
  decodeSig := some
  privateKeyFromSeed := id
  pub := fun seed => toVecN _ (pkBytes p (keys p seed).1)
  sign := signM p
  verify := verifyBytes p
  decode_encode_pub := fun _ => rfl
  decode_encode_priv := fun _ => rfl
  decode_encode_sig := fun _ => rfl
  verify_sign := verify_signM p hp

theorem mldsa65_approved : MLDSA.mldsa65.isApproved := Or.inr (Or.inl rfl)

/-- ML-DSA-65 as a `Signature`: 1952-byte public keys and 3309-byte signatures. -/
def mldsa65Signature : Signature := scheme MLDSA.mldsa65 mldsa65_approved

example : MLDSA.mldsa65.publicKeyBytes = 1952 ∧ MLDSA.mldsa65.signatureBytes = 3309 := by decide

end Cryptlib.Primitives.Sign.FIPS204
