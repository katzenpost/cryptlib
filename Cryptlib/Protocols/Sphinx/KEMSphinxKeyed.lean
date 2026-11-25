/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxHop

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

/-! # Replacing an honest node's keys while it keeps answering

`hopChain_le` replaces the honest node's keys for one KEM ciphertext with uniform ones, in games
where the node then refuses that ciphertext. In the games of `Protocols.RSOR` the node does not
refuse it: a relay processes any header it has not seen. `keyedChain_le` is the same replacement
for a node that goes on answering packets with the challenge ciphertext, with the keys the game
holds for it. With the real keys that node is the honest node (`procImplK_real`). -/

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
        rw [if_pos he, simulateQ_pure]
        rw [procWith_eq_procKeys kem cipher macS kdfS streamS geom _ pkt
          (ofVector (kem.encodePlaintext K)) (hk.trans rfl)]
        rfl
      · simp only [if_neg he, simulateQ_bind, simulateQ_pure]
        rw [QueryImpl.simulateQ_add_liftM_query_right]
        unfold procWith
        rw [unwrapKEMWith_const kem cipher macS kdfS streamS geom (kemDecap kem _), hk]
        simp [he]

variable {kem} {V R : Type} {S : HopSetup kem V R} (A : HopAdversary S)
variable [SampleableType kem.Plaintext]

/-- The game of `hopGame`, with the node answering packets that carry the challenge ciphertext
with the game's keys. -/
def keyedGame (sel : kem.Plaintext → kem.Plaintext → KeyTuple → KeyTuple) : ProbComp Bool := do
  let kR ← $ᵗ kem.Plaintext
  let u ← $ᵗ KeyTuple
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  let r ← simulateQ (procImplK kem cipher macS kdfS streamS geom (keygenOf kem ks).2
      (encapOf kem (keygenOf kem ks).1 s).1 (sel (encapOf kem (keygenOf kem ks).1 s).2 kR u))
    (A.post cs.2 (S.view (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1
      (sel (encapOf kem (keygenOf kem ks).1 s).2 kR u)))
  return S.final (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1
    (sel (encapOf kem (keygenOf kem ks).1 s).2 kR u) r

/-- The node's keys are the KDF of the encapsulated secret. -/
abbrev keyedReal : ProbComp Bool :=
  keyedGame cipher macS kdfS streamS geom A fun K _ _ => (hopKeysPRG kem kdfS).gen K

/-- The node's keys are uniform. -/
abbrev keyedIdeal : ProbComp Bool :=
  keyedGame cipher macS kdfS streamS geom A fun _ _ u => u

/-- The KEM adversary that `A` gives: it answers the node's oracle with its decapsulation
oracle, and packets with the challenge ciphertext with the keys it derives from the key it is
given. -/
def keyedKEMAdv : KEMCCAAdversary kem where
  St := S.Ch × A.St
  pre pk := simulateQ (procFromDec kem cipher macS kdfS streamS geom)
    (A.pre (ofVector (kem.encodePublicKey pk)))
  post cs pk c k := do
    let o ← (liftM (S.drawOth cs.1) : OracleComp (decSpec kem) S.Oth)
    let r ← simulateQ (procFromDecC kem cipher macS kdfS streamS geom c
        (procKeys kem cipher macS streamS geom ((hopKeysPRG kem kdfS).gen k)))
      (A.post cs.2 (S.view pk cs.1 o c ((hopKeysPRG kem kdfS).gen k)))
    pure (S.final pk cs.1 o c ((hopKeysPRG kem kdfS).gen k) r)

/-- `kemCCAExp` for `keyedKEMAdv`, written out. -/
def keyedKS (b : Bool) : ProbComp Bool := do
  let kR ← $ᵗ kem.Plaintext
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  let r ← simulateQ (procImplK kem cipher macS kdfS streamS geom (keygenOf kem ks).2
      (encapOf kem (keygenOf kem ks).1 s).1
      ((hopKeysPRG kem kdfS).gen (if b then (encapOf kem (keygenOf kem ks).1 s).2 else kR)))
    (A.post cs.2 (S.view (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1
      ((hopKeysPRG kem kdfS).gen (if b then (encapOf kem (keygenOf kem ks).1 s).2 else kR))))
  return S.final (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1
    ((hopKeysPRG kem kdfS).gen (if b then (encapOf kem (keygenOf kem ks).1 s).2 else kR)) r

theorem kemCCAExp_keyedKEMAdv (b : Bool) :
    kemCCAExp (keyedKEMAdv cipher macS kdfS streamS geom A) b
      = keyedKS cipher macS kdfS streamS geom A b := by
  unfold kemCCAExp keyedKEMAdv keyedKS pkBytes procImplK
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
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  let r ← simulateQ (procImplK kem cipher macS kdfS streamS geom (keygenOf kem ks).2
      (encapOf kem (keygenOf kem ks).1 s).1 t)
    (A.post cs.2 (S.view (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1 t))
  return S.final (keygenOf kem ks).1 cs.1 o (encapOf kem (keygenOf kem ks).1 s).1 t r

theorem keyedKS_true_evalDistEq :
    keyedKS cipher macS kdfS streamS geom A true
      =ᵈ keyedReal cipher macS kdfS streamS geom A := by
  unfold keyedKS keyedReal keyedGame
  simp only [if_true]
  exact EvalDistEq.bind_right _ fun kR => (OracleComp.EvalDistEq.bind_const _ _).symm

theorem keyedKS_false_evalDistEq :
    keyedKS cipher macS kdfS streamS geom A false
      =ᵈ prgRealExperiment (hopKeysPRG kem kdfS) (keyedKeyAdv cipher macS kdfS streamS geom A) := by
  unfold keyedKS prgRealExperiment keyedKeyAdv
  simp only [Bool.false_eq_true, if_false]
  exact EvalDistEq.rfl

theorem prgIdeal_keyedKeyAdv_evalDistEq :
    prgIdealExperiment (keyedKeyAdv cipher macS kdfS streamS geom A)
      =ᵈ keyedIdeal cipher macS kdfS streamS geom A := by
  unfold prgIdealExperiment keyedKeyAdv keyedIdeal keyedGame
  exact (OracleComp.EvalDistEq.bind_const _ _).symm

/-- **The keyed chain.** Replacing the honest node's keys with uniform ones, while the node goes
on answering with them, changes the game's outcome by at most the advantage of `keyedKEMAdv`
against the KEM plus the advantage of `keyedKeyAdv` against the KDF as a generator. -/
theorem keyedChain_le :
    |(Pr{let x ← keyedReal cipher macS kdfS streamS geom A}[x = true]).toReal
      - (Pr{let x ← keyedIdeal cipher macS kdfS streamS geom A}[x = true]).toReal|
    ≤ |(Pr{let x ← kemCCAExp (keyedKEMAdv cipher macS kdfS streamS geom A) true}[x = true]).toReal
        - (Pr{let x ← (kemCCAExp (keyedKEMAdv cipher macS kdfS streamS geom A)
            false)}[x = true]).toReal|
      + |(Pr{let x ← prgRealExperiment (hopKeysPRG kem kdfS)
                        (keyedKeyAdv cipher macS kdfS streamS geom A)}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment
                        (keyedKeyAdv cipher macS kdfS streamS geom A)}[x = true]).toReal| := by
  have e1 := (keyedKS_true_evalDistEq cipher macS kdfS streamS geom A).prEvent_eq
    (fun x => x = true)
  have e0 := (keyedKS_false_evalDistEq cipher macS kdfS streamS geom A).prEvent_eq
    (fun x => x = true)
  have e2 := (prgIdeal_keyedKeyAdv_evalDistEq cipher macS kdfS streamS geom A).prEvent_eq
    (fun x => x = true)
  rw [kemCCAExp_keyedKEMAdv, kemCCAExp_keyedKEMAdv, e1, e0, e2]
  exact abs_sub_le _ _ _

end Keyed

end Cryptlib.Protocols.Sphinx.KEMSphinx
