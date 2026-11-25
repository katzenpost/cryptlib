/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxHop
import Cryptlib.Protocols.Sphinx.KEMSphinxRSOR

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

/-! # Replacing an honest node's keys while it keeps answering

`hopChain_le` replaces the honest node's keys for one KEM ciphertext with uniform ones, in games
where the node then refuses that ciphertext. In the games of `Protocols.RSOR` the node does not
refuse it: a relay processes any header it has not seen. `keyedChain_le` is the same replacement
for a node that goes on answering packets with the challenge ciphertext, with the keys the game
holds for it. With the real keys that node is the honest node (`procImplK_real`).

The node's key pair is drawn as a relay's is in `KEMSphinx.RSOR`: the public key is the one its
private key gives, so the adversary is handed a `Key`. The KEM game `kemExpK` draws it the same
way. -/

section Keyed

open PRGScheme

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- The honest node's oracle from a decapsulation oracle, except that a packet with the
ciphertext `c` is answered by `f`. -/
def procFromDecC (c : kem.Ciphertext) (f : ByteArray → ProcResult) :
    QueryImpl procSpec (OracleComp (decSpec kem)) :=
  QueryImpl.add unifSpec.passthrough fun pkt =>
    match kem.decodeCiphertext
        (toVecN kem.ciphertextSize (pkt.extract 2 (2 + kem.ciphertextSize))) with
    | none => pure (procWith kem cipher macS kdfS streamS geom
        (fun _ => throw "sphinx: invalid key/ciphertext encoding") pkt)
    | some c' =>
      if kem.encodeCiphertext c' = kem.encodeCiphertext c then pure (f pkt)
      else do
        let r ← (liftM ((kem.Ciphertext →ₒ Option kem.Plaintext).query c') :
          OracleComp (decSpec kem) _)
        pure (procWith kem cipher macS kdfS streamS geom (fun _ => decAnswer kem r) pkt)

/-- The honest node's oracle with the keys `t` for the ciphertext `c`. -/
def procImplK (sk : kem.PrivateKey) (c : kem.Ciphertext) (t : KeyTuple) :
    QueryImpl procSpec ProbComp :=
  decImplX kem sk c ∘ₛ procFromDecC kem cipher macS kdfS streamS geom c
    (procKeys kem cipher macS streamS geom t)

/-- With the keys the KDF derives from the ciphertext's own secret, the keyed oracle is the
honest node's. -/
theorem procImplK_real (sk : kem.PrivateKey) (c : kem.Ciphertext) (K : kem.Plaintext)
    (h : decapOf kem sk c = some K) :
    procImplK kem cipher macS kdfS streamS geom sk c ((hopKeysPRG kem kdfS).gen K)
      = procImpl kem cipher macS kdfS streamS geom sk := by
  ext t
  cases t with
  | inl t =>
    simp [procImplK, procFromDecC, decImplX, procImpl, QueryImpl.add_eq_hAdd]
    exact (QueryImpl.simulateQ_add_liftM_query_left (QueryImpl.id' unifSpec) _ t).trans (by simp)
  | inr pkt =>
    have hk := kemDecap_encodePrivateKey kem sk (pkt.extract 2 (2 + kem.ciphertextSize))
    simp only [procImplK, QueryImpl.apply_compose, procFromDecC, decImplX, procImpl,
      QueryImpl.add_eq_hAdd, QueryImpl.add_apply_inr]
    cases hdc : kem.decodeCiphertext
        (toVecN kem.ciphertextSize (pkt.extract 2 (2 + kem.ciphertextSize))) with
    | none =>
      rw [hdc] at hk
      unfold procWith
      rw [unwrapKEMWith_const kem cipher macS kdfS streamS geom (kemDecap kem _), hk]
      simp
    | some c' =>
      rw [hdc] at hk
      dsimp only at hk ⊢
      by_cases he : kem.encodeCiphertext c' = kem.encodeCiphertext c
      · obtain rfl : c' = c := by
          have := congrArg kem.decodeCiphertext he
          rwa [kem.decode_encode_ct, kem.decode_encode_ct, Option.some.injEq] at this
        rw [h] at hk
        rw [ite_cond_eq_true _ _ (eq_true he), simulateQ_pure]
        rw [procWith_eq_procKeys kem cipher macS kdfS streamS geom _ pkt
          (ofVector (kem.encodePlaintext K)) (hk.trans rfl)]
        rfl
      · simp only [ite_cond_eq_false _ _ (eq_false he), simulateQ_bind, simulateQ_pure]
        rw [QueryImpl.simulateQ_add_liftM_query_right]
        unfold procWith
        rw [unwrapKEMWith_const kem cipher macS kdfS streamS geom (kemDecap kem _), hk]
        simp [he]

/-- What the challenger does between the adversary's two phases, and how the game is scored,
in terms of the honest node's KEM ciphertext and its four keys. -/
structure KeyedSetup (kem : KEM) (V R : Type) where
  /-- The adversary's choice. -/
  Ch : Key kem → Type
  /-- The challenger's randomness other than the seed of the encapsulation to the honest node. -/
  Oth : Type
  drawOth : {pk : Key kem} → Ch pk → ProbComp Oth
  /-- The challenge. -/
  view : {pk : Key kem} → Ch pk → Oth → kem.Ciphertext → KeyTuple → V
  /-- The game's output, from the adversary's answer. -/
  final : {pk : Key kem} → Ch pk → Oth → kem.Ciphertext → KeyTuple → R → Bool

variable {kem} {V R : Type} (S : KeyedSetup kem V R)

/-- An adversary with the honest node's oracle in both phases. -/
structure KeyedAdversary where
  St : Type
  pre : (pk : Key kem) → OracleComp procSpec (S.Ch pk × St)
  post : St → V → OracleComp procSpec R

variable {S} (A : KeyedAdversary S)
variable [SampleableType kem.Plaintext]

/-- An adversary against the KEM with a decapsulation oracle: it is given a relay's public key, a
ciphertext and a key, and guesses whether the key is the ciphertext's shared secret or uniform.
After the challenge the oracle refuses the challenge ciphertext. -/
structure KEMAdversaryK (kem : KEM) where
  St : Key kem → Type
  pre : (pk : Key kem) → OracleComp (decSpec kem) (St pk)
  post : {pk : Key kem} → St pk → kem.Ciphertext → kem.Plaintext → OracleComp (decSpec kem) Bool

/-- The experiment for `KEMAdversaryK`, with the real key for `b = true`. -/
def kemExpK (B : KEMAdversaryK kem) (b : Bool) : ProbComp Bool := do
  let kRand ← $ᵗ kem.Plaintext
  let k ← keygen kem
  let st ← simulateQ (decImpl kem k.2) (B.pre k.1)
  let s ← $ᵗ (Vector UInt8 32)
  simulateQ (decImplX kem k.2 (encapOf kem k.1.1 s).1)
    (B.post st (encapOf kem k.1.1 s).1 (if b then (encapOf kem k.1.1 s).2 else kRand))

/-- The game of `hopGame`, with the node answering packets that carry the challenge ciphertext
with the game's keys. -/
def keyedGame (sel : kem.Plaintext → kem.Plaintext → KeyTuple → KeyTuple) : ProbComp Bool := do
  let kR ← $ᵗ kem.Plaintext
  let u ← $ᵗ KeyTuple
  let k ← keygen kem
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom k.2) (A.pre k.1)
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  let r ← simulateQ (procImplK kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s).1
      (sel (encapOf kem k.1.1 s).2 kR u))
    (A.post cs.2 (S.view cs.1 o (encapOf kem k.1.1 s).1 (sel (encapOf kem k.1.1 s).2 kR u)))
  return S.final cs.1 o (encapOf kem k.1.1 s).1 (sel (encapOf kem k.1.1 s).2 kR u) r

/-- The node's keys are the KDF of the encapsulated secret. -/
abbrev keyedReal : ProbComp Bool :=
  keyedGame cipher macS kdfS streamS geom A fun K _ _ => (hopKeysPRG kem kdfS).gen K

/-- The node's keys are uniform. -/
abbrev keyedIdeal : ProbComp Bool :=
  keyedGame cipher macS kdfS streamS geom A fun _ _ u => u

/-- The KEM adversary that `A` gives: it answers the node's oracle with its decapsulation
oracle, and packets with the challenge ciphertext with the keys it derives from the key it is
given. -/
def keyedKEMAdv : KEMAdversaryK kem where
  St pk := S.Ch pk × A.St
  pre pk := simulateQ (procFromDec kem cipher macS kdfS streamS geom) (A.pre pk)
  post cs c k := do
    let o ← (liftM (S.drawOth cs.1) : OracleComp (decSpec kem) S.Oth)
    let r ← simulateQ (procFromDecC kem cipher macS kdfS streamS geom c
        (procKeys kem cipher macS streamS geom ((hopKeysPRG kem kdfS).gen k)))
      (A.post cs.2 (S.view cs.1 o c ((hopKeysPRG kem kdfS).gen k)))
    pure (S.final cs.1 o c ((hopKeysPRG kem kdfS).gen k) r)

/-- `kemExpK` for `keyedKEMAdv`, written out. -/
def keyedKS (b : Bool) : ProbComp Bool := do
  let kR ← $ᵗ kem.Plaintext
  let k ← keygen kem
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom k.2) (A.pre k.1)
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  let r ← simulateQ (procImplK kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s).1
      ((hopKeysPRG kem kdfS).gen (if b then (encapOf kem k.1.1 s).2 else kR)))
    (A.post cs.2 (S.view cs.1 o (encapOf kem k.1.1 s).1
      ((hopKeysPRG kem kdfS).gen (if b then (encapOf kem k.1.1 s).2 else kR))))
  return S.final cs.1 o (encapOf kem k.1.1 s).1
    ((hopKeysPRG kem kdfS).gen (if b then (encapOf kem k.1.1 s).2 else kR)) r

theorem kemExpK_keyedKEMAdv (b : Bool) :
    kemExpK (keyedKEMAdv cipher macS kdfS streamS geom A) b
      = keyedKS cipher macS kdfS streamS geom A b := by
  unfold kemExpK keyedKEMAdv keyedKS procImplK
  have hl : ∀ (sk : kem.PrivateKey) (c : kem.Ciphertext) {α : Type} (x : ProbComp α),
      simulateQ (decImplX kem sk c) (liftM x : OracleComp (decSpec kem) α) = x := by
    intro sk c α x
    unfold decImplX
    rw [QueryImpl.add_eq_hAdd, QueryImpl.simulateQ_add_liftM_left]
    simp
  simp only [simulateQ_bind, simulateQ_pure, ← QueryImpl.simulateQ_compose,
    decImpl_compose_procFromDec, hl]

/-- The adversary against the KDF's output that `A` gives. -/
def keyedKeyAdv : PRGAdversary KeyTuple := fun t => do
  let k ← keygen kem
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom k.2) (A.pre k.1)
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  let r ← simulateQ (procImplK kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s).1
      (t))
    (A.post cs.2 (S.view cs.1 o (encapOf kem k.1.1 s).1 (t)))
  return S.final cs.1 o (encapOf kem k.1.1 s).1 (t) r

theorem keyedKS_true_evalDistEq :
    keyedKS cipher macS kdfS streamS geom A true
      =ᵈ keyedReal cipher macS kdfS streamS geom A := by
  unfold keyedKS keyedReal keyedGame
  simp only [ite_true]
  exact EvalDistEq.bind_right _ fun kR => (OracleComp.EvalDistEq.bind_const _ _).symm

theorem keyedKS_false_evalDistEq :
    keyedKS cipher macS kdfS streamS geom A false
      =ᵈ prgRealExperiment (hopKeysPRG kem kdfS) (keyedKeyAdv cipher macS kdfS streamS geom A) := by
  unfold keyedKS prgRealExperiment keyedKeyAdv
  simp only [Bool.false_eq_true, ite_false]
  exact EvalDistEq.rfl

theorem prgIdeal_keyedKeyAdv_evalDistEq :
    prgIdealExperiment (keyedKeyAdv cipher macS kdfS streamS geom A)
      =ᵈ keyedIdeal cipher macS kdfS streamS geom A := by
  unfold prgIdealExperiment keyedKeyAdv keyedIdeal keyedGame
  exact (OracleComp.EvalDistEq.bind_const _ _).symm

/-- What replacing the honest node's keys with uniform ones costs: the advantage of
`keyedKEMAdv` against the KEM plus the advantage of `keyedKeyAdv` against the KDF as a
generator. -/
noncomputable def keyedCost : ℝ :=
  |(Pr{let x ← kemExpK (keyedKEMAdv cipher macS kdfS streamS geom A) true}[x = true]).toReal
      - (Pr{let x ← (kemExpK (keyedKEMAdv cipher macS kdfS streamS geom A)
          false)}[x = true]).toReal|
    + |(Pr{let x ← prgRealExperiment (hopKeysPRG kem kdfS)
                      (keyedKeyAdv cipher macS kdfS streamS geom A)}[x = true]).toReal
      - (Pr{let x ← prgIdealExperiment
                      (keyedKeyAdv cipher macS kdfS streamS geom A)}[x = true]).toReal|

/-- **The keyed chain.** Replacing the honest node's keys with uniform ones, while the node goes
on answering with them, changes the game's outcome by at most `keyedCost`. -/
theorem keyedChain_le :
    |(Pr{let x ← keyedReal cipher macS kdfS streamS geom A}[x = true]).toReal
      - (Pr{let x ← keyedIdeal cipher macS kdfS streamS geom A}[x = true]).toReal|
    ≤ keyedCost cipher macS kdfS streamS geom A := by
  unfold keyedCost
  have e1 := (keyedKS_true_evalDistEq cipher macS kdfS streamS geom A).prEvent_eq
    (fun x => x = true)
  have e0 := (keyedKS_false_evalDistEq cipher macS kdfS streamS geom A).prEvent_eq
    (fun x => x = true)
  have e2 := (prgIdeal_keyedKeyAdv_evalDistEq cipher macS kdfS streamS geom A).prEvent_eq
    (fun x => x = true)
  rw [kemExpK_keyedKEMAdv, kemExpK_keyedKEMAdv, e1, e0, e2]
  exact abs_sub_le _ _ _

end Keyed

/-! ## The games of `Protocols.RSOR`, with one relay behind an oracle -/

section Games

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry) (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

/-- The honest node's oracle answers a sampling query by sampling. -/
theorem simulateQ_procImpl_liftM (sk : kem.PrivateKey) {α : Type} (x : ProbComp α) :
    simulateQ (procImpl kem cipher macS kdfS streamS geom sk) (liftM x : OracleComp procSpec α)
      = x := by
  unfold procImpl
  rw [QueryImpl.add_eq_hAdd, QueryImpl.simulateQ_add_liftM_left]
  simp

/-- KEM Sphinx as the scheme of the games. -/
abbrev sphinx : Protocols.RSOR.Scheme :=
  RSOR.scheme kem cipher macS kdfS streamS geom hvalid hmactag h16

/-- The honest relays of a game, with the relay `.relay` answered by an oracle for its unwrapped
packets, and the other two by their secret keys. `sk .relay` is not used. -/
def viaOracle (sk : Role → kem.PrivateKey)
    (patch : Protocols.RSOR.Patch (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16)) :
    QueryImpl
      (Protocols.RSOR.oracleSpec (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))
      (StateT (Protocols.RSOR.Log (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))
        (OracleComp procSpec)) :=
  Protocols.RSOR.oracle
    (fun h o => if h = .relay then
        RSOR.stepOf geom <$>
          (liftM ((ByteArray →ₒ ProcResult).query (RSOR.join o)) : OracleComp procSpec ProcResult)
      else pure (RSOR.proc kem cipher macS kdfS streamS geom (sk h) o))
    (fun h msg o => if h = .relay then
        RSOR.replyOf cipher geom msg <$>
          (liftM ((ByteArray →ₒ ProcResult).query (RSOR.join o)) : OracleComp procSpec ProcResult)
      else pure (RSOR.reply kem cipher macS kdfS streamS geom (sk h) msg o))
    patch

/-- Answering that oracle with the relay's secret key gives the honest relays of the game. The
keys `viaOracle` is given need only agree with the game's for the other two relays. -/
theorem viaOracle_honest
    (hon : Protocols.RSOR.Honest (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))
    (sk sk' : Role → kem.PrivateKey) (hsk : ∀ h, h ≠ .relay → sk h = sk' h)
    (patch : Protocols.RSOR.Patch (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))
    {α : Type}
    (oa : OracleComp
      (Protocols.RSOR.oracleSpec (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16)) α)
    (log : Protocols.RSOR.Log (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16)) :
    simulateQ (procImpl kem cipher macS kdfS streamS geom (sk' .relay))
        ((simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 sk patch)
          oa).run log)
      = (simulateQ (Protocols.RSOR.honest hon sk' patch) oa).run log := by
  refine simulateQ_StateT_compose _ _ _ (fun q log => ?_) oa log
  rcases q with (t | ⟨h, o⟩) | ⟨h, msg, o⟩
  · simp only [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle]
    simpa using simulateQ_procImpl_liftM kem cipher macS kdfS streamS geom (sk' .relay)
      (liftM (OracleSpec.query t))
  · by_cases hs : (h, o.1) ∈ log.seen
    · simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.process, hs]
    · by_cases hr : h = .relay
      · subst hr
        simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.process,
          hs, simulateQ_procImpl_liftM]
        rfl
      · simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.process,
          hs, hr, simulateQ_procImpl_liftM, hsk h hr]
        rfl
  · by_cases hs : (h, o) ∈ log.held
    · by_cases hr : h = .relay
      · subst hr
        simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.answer, hs]
        rfl
      · simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.answer,
          hs, hr, hsk h hr]
        rfl
    · simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.answer, hs]

end Games

end Cryptlib.Protocols.Sphinx.KEMSphinx
