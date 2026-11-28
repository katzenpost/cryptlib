/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxLayer

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

/-! # Games where the adversary sees the packet entering the honest node

In the tail game the adversary never sees the honest hop's KEM ciphertext. In the games here it
does: it is given a packet addressed to the honest node. The honest node keeps a replay cache, so
after the challenge its oracle refuses any packet that carries the challenge's KEM ciphertext.
(The replay tag is a hash of that ciphertext.)

`hopChain_le` is the part every such game shares. It replaces the honest node's four keys with
uniform ones, at the cost of the KEM, in the standard game with a decapsulation oracle that
refuses the challenge ciphertext, and of the KDF as a generator on a uniform shared secret. -/

section HopChain

open PRGScheme

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- The KDF on a shared secret, as a generator of the four keys KEM Sphinx uses. -/
def hopKeysPRG : PRGScheme kem.Plaintext KeyTuple :=
  ⟨fun K => keyTuple (deriveHopKeys kdfS (ofVector (kem.encodePlaintext K)))⟩

/-- The decapsulation oracle that refuses one ciphertext. -/
def decImplX (sk : kem.PrivateKey) (c : kem.Ciphertext) : QueryImpl (decSpec kem) ProbComp :=
  QueryImpl.add unifSpec.passthrough fun c' =>
    pure (if kem.encodeCiphertext c' = kem.encodeCiphertext c then none else decapOf kem sk c')

/-- The honest node's oracle with one entry in its replay cache: a packet that carries the KEM
ciphertext `c` is refused. -/
def procImplX (sk : kem.PrivateKey) (c : kem.Ciphertext) : QueryImpl procSpec ProbComp :=
  decImplX kem sk c ∘ₛ procFromDec kem cipher macS kdfS streamS geom

/-- What the challenger does between the adversary's two phases, and how the game is scored,
both in terms of the honest node's KEM ciphertext and its four keys. -/
structure HopSetup (kem : KEM) (V R : Type) where
  /-- The adversary's choice. -/
  Ch : Type
  /-- The challenger's randomness other than the seed of the encapsulation to the honest node. -/
  Oth : Type
  drawOth : Ch → ProbComp Oth
  /-- The challenge. -/
  view : kem.PublicKey → Ch → Oth → kem.Ciphertext → KeyTuple → V
  /-- The game's output, from the adversary's answer. -/
  final : kem.PublicKey → Ch → Oth → kem.Ciphertext → KeyTuple → R → Bool

variable {kem} {V R : Type} (S : HopSetup kem V R)

/-- An adversary with the honest node's oracle in both phases. -/
structure HopAdversary where
  St : Type
  pre : ByteArray → OracleComp procSpec (S.Ch × St)
  post : St → V → OracleComp procSpec R

variable {S} (A : HopAdversary S)
variable [SampleableType kem.Plaintext]

/-- The game, with the honest node's keys chosen by `sel` from the encapsulated secret, an
independent uniform secret, and an independent uniform key tuple. -/
def hopGame (sel : kem.Plaintext → kem.Plaintext → KeyTuple → KeyTuple) : ProbComp Bool := do
  let kR ← $ᵗ kem.Plaintext
  let u ← $ᵗ KeyTuple
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  let r ← simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem ks).2
      (encapOf kem (keygenOf kem ks).1 s).1)
    (A.post cs.2 (S.view (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1
      (sel (encapOf kem (keygenOf kem ks).1 s).2 kR u)))
  return S.final (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1
    (sel (encapOf kem (keygenOf kem ks).1 s).2 kR u) r

/-- The honest node's keys are the KDF of the encapsulated secret. -/
abbrev hopReal : ProbComp Bool :=
  hopGame cipher macS kdfS streamS geom A fun K _ _ => (hopKeysPRG kem kdfS).gen K

/-- The honest node's keys are uniform. -/
abbrev hopIdeal : ProbComp Bool :=
  hopGame cipher macS kdfS streamS geom A fun _ _ u => u

/-- An adversary against the KEM with a decapsulation oracle: it is given the public key, a
ciphertext and a key, and guesses whether the key is the ciphertext's shared secret or uniform.
After the challenge the oracle refuses the challenge ciphertext. -/
structure KEMCCAAdversary (kem : KEM) where
  St : Type
  pre : kem.PublicKey → OracleComp (decSpec kem) St
  post : St → kem.PublicKey → kem.Ciphertext → kem.Plaintext → OracleComp (decSpec kem) Bool

/-- The experiment for `KEMCCAAdversary`, with the real key for `b = true`. -/
def kemCCAExp (B : KEMCCAAdversary kem) (b : Bool) : ProbComp Bool := do
  let kRand ← $ᵗ kem.Plaintext
  let ks ← $ᵗ (Vector UInt8 32)
  let st ← simulateQ (decImpl kem (keygenOf kem ks).2) (B.pre (keygenOf kem ks).1)
  let s ← $ᵗ (Vector UInt8 32)
  simulateQ (decImplX kem (keygenOf kem ks).2 (encapOf kem (keygenOf kem ks).1 s).1)
    (B.post st (keygenOf kem ks).1 (encapOf kem (keygenOf kem ks).1 s).1
      (if b then (encapOf kem (keygenOf kem ks).1 s).2 else kRand))

/-- The KEM adversary that `A` gives: it answers the node's oracle with its decapsulation
oracle, and derives the node's keys from the key it is given. -/
def hopKEMAdv : KEMCCAAdversary kem where
  St := S.Ch × A.St
  pre pk := simulateQ (procFromDec kem cipher macS kdfS streamS geom)
    (A.pre (ofVector (kem.encodePublicKey pk)))
  post cs pk c k := do
    let o ← (liftM (S.drawOth cs.1) : OracleComp (decSpec kem) S.Oth)
    let r ← simulateQ (procFromDec kem cipher macS kdfS streamS geom)
      (A.post cs.2 (S.view pk cs.1 o c ((hopKeysPRG kem kdfS).gen k)))
    pure (S.final pk cs.1 o c ((hopKeysPRG kem kdfS).gen k) r)

/-- `kemCCAExp` for `hopKEMAdv`, written out. -/
def hopKS (b : Bool) : ProbComp Bool := do
  let kR ← $ᵗ kem.Plaintext
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  let r ← simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem ks).2
      (encapOf kem (keygenOf kem ks).1 s).1)
    (A.post cs.2 (S.view (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1
      ((hopKeysPRG kem kdfS).gen (if b then (encapOf kem (keygenOf kem ks).1 s).2 else kR))))
  return S.final (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1
    ((hopKeysPRG kem kdfS).gen (if b then (encapOf kem (keygenOf kem ks).1 s).2 else kR)) r

theorem kemCCAExp_hopKEMAdv (b : Bool) :
    kemCCAExp (hopKEMAdv cipher macS kdfS streamS geom A) b
      = hopKS cipher macS kdfS streamS geom A b := by
  unfold kemCCAExp hopKEMAdv hopKS pkBytes procImplX
  have hl : ∀ (sk : kem.PrivateKey) (c : kem.Ciphertext) {α : Type} (x : ProbComp α),
      simulateQ (decImplX kem sk c) (liftM x : OracleComp (decSpec kem) α) = x := by
    intro sk c α x
    unfold decImplX
    rw [QueryImpl.add_eq_hAdd, QueryImpl.simulateQ_add_liftM_left]
    simp
  simp only [simulateQ_bind, simulateQ_pure, ← QueryImpl.simulateQ_compose,
    decImpl_compose_procFromDec, hl]

/-- The adversary against the KDF's output that `A` gives: it generates the honest key pair
itself and runs the whole game around the key tuple. -/
def hopKeyAdv : PRGAdversary KeyTuple := fun t => do
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  let r ← simulateQ (procImplX kem cipher macS kdfS streamS geom (keygenOf kem ks).2
      (encapOf kem (keygenOf kem ks).1 s).1)
    (A.post cs.2 (S.view (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1 t))
  return S.final (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1 t r

theorem hopKS_true_evalDistEq :
    hopKS cipher macS kdfS streamS geom A true =ᵈ hopReal cipher macS kdfS streamS geom A := by
  unfold hopKS hopReal hopGame
  simp only [if_true]
  exact EvalDistEq.bind_right _ fun kR => (OracleComp.EvalDistEq.bind_const _ _).symm

theorem hopKS_false_evalDistEq :
    hopKS cipher macS kdfS streamS geom A false
      =ᵈ prgRealExperiment (hopKeysPRG kem kdfS) (hopKeyAdv cipher macS kdfS streamS geom A) := by
  unfold hopKS prgRealExperiment hopKeyAdv
  simp only [Bool.false_eq_true, if_false]
  exact EvalDistEq.rfl

theorem prgIdeal_hopKeyAdv_evalDistEq :
    prgIdealExperiment (hopKeyAdv cipher macS kdfS streamS geom A)
      =ᵈ hopIdeal cipher macS kdfS streamS geom A := by
  unfold prgIdealExperiment hopKeyAdv hopIdeal hopGame
  exact (OracleComp.EvalDistEq.bind_const _ _).symm

/-- **The shared chain.** Replacing the honest node's keys with uniform ones changes the game's
outcome by at most the advantage of `hopKEMAdv` against the KEM plus the advantage of
`hopKeyAdv` against the KDF as a generator. -/
theorem hopChain_le :
    |(Pr{let x ← hopReal cipher macS kdfS streamS geom A}[x = true]).toReal
      - (Pr{let x ← hopIdeal cipher macS kdfS streamS geom A}[x = true]).toReal|
    ≤ |(Pr{let x ← kemCCAExp (hopKEMAdv cipher macS kdfS streamS geom A) true}[x = true]).toReal
        - (Pr{let x ← kemCCAExp (hopKEMAdv cipher macS kdfS streamS geom A) false}[x = true]).toReal|
      + |(Pr{let x ← prgRealExperiment (hopKeysPRG kem kdfS)
                        (hopKeyAdv cipher macS kdfS streamS geom A)}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment
                        (hopKeyAdv cipher macS kdfS streamS geom A)}[x = true]).toReal| := by
  have e1 := (hopKS_true_evalDistEq cipher macS kdfS streamS geom A).prEvent_eq (fun x => x = true)
  have e0 := (hopKS_false_evalDistEq cipher macS kdfS streamS geom A).prEvent_eq (fun x => x = true)
  have e2 := (prgIdeal_hopKeyAdv_evalDistEq cipher macS kdfS streamS geom A).prEvent_eq
    (fun x => x = true)
  rw [kemCCAExp_hopKEMAdv, kemCCAExp_hopKEMAdv, e1, e0, e2]
  exact abs_sub_le _ _ _

end HopChain

end Cryptlib.Protocols.Sphinx.KEMSphinx
