/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.CryptoFoundations.KeyEncapMech
import Cryptlib.Protocols.Sphinx.KEMSphinxTailGame

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

/-! # The honest relay's oracle

In the tail game of Kuhn, Beck and Strufe the adversary may have the honest relay process any
packet, before and after the challenge. Here that oracle is defined, and shown to be computable
from a decapsulation oracle alone, which is what lets a KEM adversary answer it. -/

section ProcOracle

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- What the honest relay returns for a packet: `none` when it rejects it, otherwise the payload,
replay tag, commands and forwarded packet. -/
abbrev ProcResult :=
  Option (Option ByteArray × Vector UInt8 32 × List RoutingCommand × Option ByteArray)

/-- Process a packet with decapsulation given as a function. -/
def procWith (dec : ByteArray → Except String ByteArray) (pkt : ByteArray) : ProcResult :=
  match unwrapKEMWith kem cipher macS kdfS streamS geom dec pkt with
  | .ok (p, t, c, f) => some (p, t, c, f.map ofVector)
  | .error _ => none

/-- `unwrapKEMWith` calls its decapsulation function on one ciphertext only. -/
theorem unwrapKEMWith_const (dec : ByteArray → Except String ByteArray) (pkt : ByteArray) :
    unwrapKEMWith kem cipher macS kdfS streamS geom dec pkt
      = unwrapKEMWith kem cipher macS kdfS streamS geom
          (fun _ => dec (pkt.extract 2 (2 + kem.ciphertextSize))) pkt := by
  unfold unwrapKEMWith
  rfl

/-- The oracles of the tail game: uniform sampling and the honest relay. -/
abbrev procSpec := unifSpec + (ByteArray →ₒ ProcResult)

/-- The honest relay's oracle, answered with its private key. -/
def procImpl (sk : kem.PrivateKey) : QueryImpl procSpec ProbComp :=
  QueryImpl.add unifSpec.passthrough fun pkt =>
    pure (procWith kem cipher macS kdfS streamS geom
      (kemDecap kem (ofVector (kem.encodePrivateKey sk))) pkt)

/-- The oracles of a KEM adversary: uniform sampling and decapsulation. -/
abbrev decSpec := unifSpec + (kem.Ciphertext →ₒ Option kem.Plaintext)

/-- The decapsulation oracle, answered with the private key and with no ciphertext refused. -/
def decImpl (sk : kem.PrivateKey) : QueryImpl (decSpec kem) ProbComp :=
  QueryImpl.add unifSpec.passthrough fun c => pure (decapOf kem sk c)

/-- The bytes-level decapsulation result for a decapsulation oracle's answer. -/
def decAnswer (r : Option kem.Plaintext) : Except String ByteArray :=
  match r with
  | some k => pure (ofVector (kem.encodePlaintext k))
  | none => throw "sphinx: KEM decapsulation failed"

/-- The honest relay's oracle, answered with a decapsulation oracle in place of the private
key. -/
def procFromDec : QueryImpl procSpec (OracleComp (decSpec kem)) :=
  QueryImpl.add unifSpec.passthrough fun pkt =>
    match kem.decodeCiphertext
        (toVecN kem.ciphertextSize (pkt.extract 2 (2 + kem.ciphertextSize))) with
    | none => pure (procWith kem cipher macS kdfS streamS geom
        (fun _ => throw "sphinx: invalid key/ciphertext encoding") pkt)
    | some c => do
      let r ← (liftM ((kem.Ciphertext →ₒ Option kem.Plaintext).query c) : OracleComp (decSpec kem) _)
      pure (procWith kem cipher macS kdfS streamS geom (fun _ => decAnswer kem r) pkt)

/-- Bytes-level decapsulation with an encoded private key, in terms of `decapOf`. -/
theorem kemDecap_encodePrivateKey (sk : kem.PrivateKey) (ct : ByteArray) :
    kemDecap kem (ofVector (kem.encodePrivateKey sk)) ct
      = match kem.decodeCiphertext (toVecN kem.ciphertextSize ct) with
        | none => throw "sphinx: invalid key/ciphertext encoding"
        | some c => decAnswer kem (decapOf kem sk c) := by
  unfold kemDecap decapOf decAnswer
  rw [Cryptlib.Protocols.Sphinx.Common.toVecN_ofVector, kem.decode_encode_priv]
  cases kem.decodeCiphertext (toVecN kem.ciphertextSize ct) with
  | none => rfl
  | some c =>
    dsimp only
    cases kem.decap sk c (kem.stateFromSeed (Vector.replicate 32 0)) with
    | ok k t => rfl
    | error e t => rfl

/-- Answering the relay's oracle through the decapsulation oracle is answering it with the
private key. -/
theorem decImpl_compose_procFromDec (sk : kem.PrivateKey) :
    decImpl kem sk ∘ₛ procFromDec kem cipher macS kdfS streamS geom
      = procImpl kem cipher macS kdfS streamS geom sk := by
  ext t
  cases t with
  | inl t =>
    simp [procFromDec, decImpl, procImpl, QueryImpl.add_eq_hAdd]
    exact (QueryImpl.simulateQ_add_liftM_query_left (QueryImpl.id' unifSpec) _ t).trans (by simp)
  | inr pkt =>
    have hk := kemDecap_encodePrivateKey kem sk (pkt.extract 2 (2 + kem.ciphertextSize))
    simp only [QueryImpl.apply_compose, procFromDec, decImpl, procImpl, QueryImpl.add_eq_hAdd,
      QueryImpl.add_apply_inr]
    unfold procWith
    rw [unwrapKEMWith_const kem cipher macS kdfS streamS geom (kemDecap kem _), hk]
    cases kem.decodeCiphertext
        (toVecN kem.ciphertextSize (pkt.extract 2 (2 + kem.ciphertextSize))) with
    | none => simp
    | some c =>
      simp only [simulateQ_bind, simulateQ_pure]
      rw [QueryImpl.simulateQ_add_liftM_query_right]
      simp

end ProcOracle

/-! # The hybrid chain, for any way of producing the challenge

`TailSetup` abstracts what the challenger does between the adversary's two phases: it draws its
randomness, and the challenge is a function of that and of the honest hop's seed. Two facts are
asked of it. Off a bad set, the challenge depends on the honest hop's seed only through the hop's
header keystream. And with a uniform keystream in its place, the challenge is distributed as the
fresh one. The chain then bounds the adversary's advantage for any such setup. -/

section Chain

open PRGScheme

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- A hop's whole header keystream. -/
abbrev Keystream := Vector UInt8 (geom.routingInfoLength + geom.perHopRoutingInfoLength)

/-- The header keystream as a generator from the header key and IV: the stream cipher. -/
def keystreamPRG : PRGScheme (Vector UInt8 32 × Vector UInt8 16) (Keystream geom) :=
  ⟨fun k => Util.Bytes.toVecN _ (streamS.keystream (ofVector k.1) (ofVector k.2)
    (geom.routingInfoLength + geom.perHopRoutingInfoLength))⟩

/-- The honest hop's header keystream, from its public key and the sender's seed for it. -/
def honestKeystream (pk : kem.PublicKey) (s : Vector UInt8 32) : Keystream geom :=
  (keystreamPRG streamS geom).gen ((secretKeyPRG kem kdfS).gen (encapOf kem pk s).2)

/-- What the challenger does between the adversary's two phases. -/
structure TailSetup where
  /-- The adversary's choice: path, message, and whatever else it submits. -/
  Ch : Type
  /-- The challenger's randomness other than the honest hop's seed. -/
  Oth : Type
  /-- The randomness of the fresh challenge. -/
  Fr : Type
  drawOth : Ch → ProbComp Oth
  drawFr : Ch → ProbComp Fr
  /-- The real challenge. -/
  realView : kem.PublicKey → kem.PrivateKey → Ch → Vector UInt8 32 → Oth → Option ByteArray
  /-- The challenge with the honest hop's header keystream given directly. -/
  ksView : Ch → Oth → Keystream geom → Option ByteArray
  /-- The fresh challenge. -/
  freshView : Ch → Fr → Option ByteArray
  /-- The draws the exact theorem does not cover. -/
  bad : kem.PublicKey → kem.PrivateKey → Ch → Vector UInt8 32 → Oth → Prop
  real_eq : ∀ pk sk ch s o, ¬ bad pk sk ch s o →
    realView pk sk ch s o = ksView ch o (honestKeystream kem kdfS streamS geom pk s)
  ks_fresh : ∀ ch (K : Option ByteArray → ProbComp Bool),
    (do let o ← drawOth ch; let u ← $ᵗ (Keystream geom); K (ksView ch o u))
      =ᵈ (drawFr ch >>= fun y => K (freshView ch y))

variable {kem kdfS streamS geom}
variable (S : TailSetup kem kdfS streamS geom)

/-- The adversary of the tail game with the honest relay's oracle, in both phases. -/
structure TIOAdversary where
  St : Type
  pre : ByteArray → OracleComp procSpec (S.Ch × St)
  post : St → Option ByteArray → OracleComp procSpec Bool

variable {S}
variable (A : TIOAdversary S)

/-- The real game. -/
def tioReal : ProbComp Bool := do
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2) (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.post cs.2 (S.realView (keygenOf kem ks).1 (keygenOf kem ks).2 cs.1 s o))

/-- The fresh game. -/
def tioFresh : ProbComp Bool := do
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2) (A.pre (pkBytes kem ks))
  let y ← S.drawFr cs.1
  simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2) (A.post cs.2 (S.freshView cs.1 y))

/-- The draws of the real game up to the challenge. -/
def tioDraw : ProbComp (Vector UInt8 32 × (S.Ch × A.St) × Vector UInt8 32 × S.Oth) := do
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2) (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let o ← S.drawOth cs.1
  return (ks, cs, s, o)

/-- An adversary against the KEM with a decapsulation oracle that refuses nothing, and no
challenge ciphertext: it is given the public key and a key, and guesses whether the key is the
shared secret of a withheld encapsulation or uniform. -/
structure KEMOAdversary (kem : KEM) where
  St : Type
  pre : kem.PublicKey → OracleComp (decSpec kem) St
  post : St → kem.Plaintext → OracleComp (decSpec kem) Bool

variable [SampleableType kem.Plaintext]

/-- The experiment for `KEMOAdversary`, with the real key for `b = true`. -/
def kemOExp (B : KEMOAdversary kem) (b : Bool) : ProbComp Bool := do
  let ks ← $ᵗ (Vector UInt8 32)
  let st ← simulateQ (decImpl kem (keygenOf kem ks).2) (B.pre (keygenOf kem ks).1)
  let s ← $ᵗ (Vector UInt8 32)
  let kRand ← $ᵗ kem.Plaintext
  simulateQ (decImpl kem (keygenOf kem ks).2)
    (B.post st (if b then (encapOf kem (keygenOf kem ks).1 s).2 else kRand))

/-- The KEM adversary that `A` gives: it answers the relay's oracle with its decapsulation
oracle, and builds the challenge from the key it is given. -/
def tioKEMAdv : KEMOAdversary kem where
  St := S.Ch × A.St
  pre pk := simulateQ (procFromDec kem cipher macS kdfS streamS geom) (A.pre (ofVector (kem.encodePublicKey pk)))
  post cs k := do
    let o ← (liftM (S.drawOth cs.1) : OracleComp (decSpec kem) S.Oth)
    simulateQ (procFromDec kem cipher macS kdfS streamS geom) (A.post cs.2 (S.ksView cs.1 o
      ((keystreamPRG streamS geom).gen ((secretKeyPRG kem kdfS).gen k))))

/-- `kemOExp` for `tioKEMAdv`, written out. -/
def tioKS (b : Bool) : ProbComp Bool := do
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2) (A.pre (pkBytes kem ks))
  let s ← $ᵗ (Vector UInt8 32)
  let kRand ← $ᵗ kem.Plaintext
  let o ← S.drawOth cs.1
  simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2)
    (A.post cs.2 (S.ksView cs.1 o ((keystreamPRG streamS geom).gen ((secretKeyPRG kem kdfS).gen
      (if b then (encapOf kem (keygenOf kem ks).1 s).2 else kRand)))))

theorem kemOExp_tioKEMAdv (b : Bool) :
    kemOExp (tioKEMAdv cipher macS A) b = tioKS cipher macS A b := by
  unfold kemOExp tioKEMAdv tioKS pkBytes
  have hl : ∀ (sk : kem.PrivateKey) {α : Type} (x : ProbComp α),
      simulateQ (decImpl kem sk) (liftM x : OracleComp (decSpec kem) α) = x := by
    intro sk α x
    unfold decImpl
    rw [QueryImpl.add_eq_hAdd, QueryImpl.simulateQ_add_liftM_left]
    simp
  simp only [simulateQ_bind, ← QueryImpl.simulateQ_compose, decImpl_compose_procFromDec, hl]

/-- The adversary against a header keystream that `A` gives: it generates the honest key pair
itself, runs `A`'s first phase, builds the challenge around the keystream, and runs `A`'s
second phase. -/
def tioKSAdv : PRGAdversary (Keystream geom) := fun u => do
  let ks ← $ᵗ (Vector UInt8 32)
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2) (A.pre (pkBytes kem ks))
  let o ← S.drawOth cs.1
  simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2) (A.post cs.2 (S.ksView cs.1 o u))

/-- `tioKSAdv` against a header key and IV: it expands them to the keystream. -/
def tioKeyAdv : PRGAdversary (Vector UInt8 32 × Vector UInt8 16) := fun k =>
  tioKSAdv cipher macS A ((keystreamPRG streamS geom).gen k)

/-- The real game, with the honest hop's header keystream in the challenge. -/
def tioRealKS : ProbComp Bool :=
  tioDraw cipher macS A >>= fun d =>
    simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem d.1).2)
      (A.post d.2.1.2 (S.ksView d.2.1.1 d.2.2.2
        (honestKeystream kem kdfS streamS geom (keygenOf kem d.1).1 d.2.2.1)))

omit [SampleableType kem.Plaintext] in
theorem tioReal_sub_tioRealKS_le :
    |(Pr{let x ← tioReal cipher macS A}[x = true]).toReal
      - (Pr{let x ← tioRealKS cipher macS A}[x = true]).toReal|
    ≤ (Pr{let d ← tioDraw cipher macS A}[
        S.bad (keygenOf kem d.1).1 (keygenOf kem d.1).2 d.2.1.1 d.2.2.1 d.2.2.2]).toReal := by
  have hr : tioReal cipher macS A = tioDraw cipher macS A >>= fun d =>
      simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem d.1).2)
        (A.post d.2.1.2 (S.realView (keygenOf kem d.1).1 (keygenOf kem d.1).2 d.2.1.1
          d.2.2.1 d.2.2.2)) := by
    unfold tioReal tioDraw
    simp only [bind_assoc, pure_bind]
  rw [hr]
  exact prEvent_bind_toReal_sub_le_of_bad (tioDraw cipher macS A) _ _
    (fun d => S.bad (keygenOf kem d.1).1 (keygenOf kem d.1).2 d.2.1.1 d.2.2.1 d.2.2.2)
    (fun d hd => by rw [S.real_eq _ _ _ _ _ hd]) (fun x => x = true)

theorem tioKS_true_evalDistEq : tioKS cipher macS A true =ᵈ tioRealKS cipher macS A := by
  unfold tioKS tioRealKS tioDraw honestKeystream
  simp only [bind_assoc, pure_bind, if_true]
  refine EvalDistEq.bind_right _ fun ks => EvalDistEq.bind_right _ fun cs =>
    EvalDistEq.bind_right _ fun s => ?_
  exact OracleComp.EvalDistEq.bind_const _ _

theorem tioKS_false_evalDistEq :
    tioKS cipher macS A false
      =ᵈ prgRealExperiment (secretKeyPRG kem kdfS) (tioKeyAdv cipher macS A) := by
  unfold tioKS prgRealExperiment tioKeyAdv tioKSAdv
  simp only [Bool.false_eq_true, if_false]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun ks => EvalDistEq.bind_right _ fun cs =>
    OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun ks =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

omit [SampleableType kem.Plaintext] in
theorem prgIdeal_tioKSAdv_evalDistEq :
    prgIdealExperiment (tioKSAdv cipher macS A) =ᵈ tioFresh cipher macS A := by
  unfold prgIdealExperiment tioKSAdv tioFresh
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun ks => ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun cs => ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact S.ks_fresh cs.1 fun v =>
    simulateQ (procImpl kem cipher macS kdfS streamS geom (keygenOf kem ks).2) (A.post cs.2 v)

/-- **The hybrid chain.** For any `TailSetup`, the advantage of an adversary with the honest
relay's oracle in telling the real challenge from the fresh one is at most the sum of:

- the advantage of `tioKEMAdv` against the KEM, with a decapsulation oracle and no challenge
  ciphertext;
- the advantage of `tioKeyAdv` in telling the header key and IV the KDF derives from a uniform
  shared secret from a uniform key and IV;
- the advantage of `tioKSAdv` in telling the header keystream under a uniform key and IV from a
  uniform string;
- the probability of the setup's bad draws. -/
theorem tioAdvantage_le :
    |(Pr{let x ← tioReal cipher macS A}[x = true]).toReal
      - (Pr{let x ← tioFresh cipher macS A}[x = true]).toReal|
    ≤ |(Pr{let x ← kemOExp (tioKEMAdv cipher macS A) true}[x = true]).toReal
        - (Pr{let x ← kemOExp (tioKEMAdv cipher macS A) false}[x = true]).toReal|
      + |(Pr{let x ← prgRealExperiment (secretKeyPRG kem kdfS)
                        (tioKeyAdv cipher macS A)}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment (tioKeyAdv cipher macS A)}[x = true]).toReal|
      + |(Pr{let x ← prgRealExperiment (keystreamPRG streamS geom)
                        (tioKSAdv cipher macS A)}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment (tioKSAdv cipher macS A)}[x = true]).toReal|
      + (Pr{let d ← tioDraw cipher macS A}[
          S.bad (keygenOf kem d.1).1 (keygenOf kem d.1).2 d.2.1.1 d.2.2.1 d.2.2.2]).toReal := by
  have h1 := tioReal_sub_tioRealKS_le cipher macS A
  have e1 := (tioKS_true_evalDistEq cipher macS A).prEvent_eq (fun x => x = true)
  have e0 := (tioKS_false_evalDistEq cipher macS A).prEvent_eq (fun x => x = true)
  have e4 := (prgIdeal_tioKSAdv_evalDistEq cipher macS A).prEvent_eq (fun x => x = true)
  have hd : prgIdealExperiment (tioKeyAdv cipher macS A)
      = prgRealExperiment (keystreamPRG streamS geom) (tioKSAdv cipher macS A) := rfl
  rw [kemOExp_tioKEMAdv, kemOExp_tioKEMAdv, e1, e0, hd, ← e4]
  have t1 := abs_sub_le
    (Pr{let x ← tioReal cipher macS A}[x = true]).toReal
    (Pr{let x ← tioRealKS cipher macS A}[x = true]).toReal
    (Pr{let x ← prgIdealExperiment (tioKSAdv cipher macS A)}[x = true]).toReal
  have t2 := abs_sub_le
    (Pr{let x ← tioRealKS cipher macS A}[x = true]).toReal
    (Pr{let x ← prgRealExperiment (secretKeyPRG kem kdfS)
                    (tioKeyAdv cipher macS A)}[x = true]).toReal
    (Pr{let x ← prgIdealExperiment (tioKSAdv cipher macS A)}[x = true]).toReal
  have t3 := abs_sub_le
    (Pr{let x ← prgRealExperiment (secretKeyPRG kem kdfS)
                    (tioKeyAdv cipher macS A)}[x = true]).toReal
    (Pr{let x ← prgRealExperiment (keystreamPRG streamS geom)
                    (tioKSAdv cipher macS A)}[x = true]).toReal
    (Pr{let x ← prgIdealExperiment (tioKSAdv cipher macS A)}[x = true]).toReal
  linarith

end Chain

end Cryptlib.Protocols.Sphinx.KEMSphinx
