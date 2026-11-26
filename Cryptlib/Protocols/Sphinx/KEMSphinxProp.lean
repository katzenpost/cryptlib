/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxKeyedMac

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

/-! # A game of the onion properties as a keyed game

Each of the properties is a game with three honest relays. To replace the keys of one of them,
the game is written with that relay behind an oracle for its unwrapped packets: the adversary
of the keyed game draws the other two relays' keys and answers for all three. This is done
here once, for any property and for any of the three roles. -/

section PropGame

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

variable (P : Protocols.RSOR.Property (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))
  (ρ : Role) (names : Role → RSOR.Name)

/-- The key pairs of the two honest relays that are not `ρ`: `k₁` for the role after `ρ`, `k₂`
for the other. The entry at `ρ` is not used. -/
def keysOf (ρ : Role) (k₁ k₂ : Key kem × kem.PrivateKey) : Role → Key kem × kem.PrivateKey :=
  fun h => if h = (match ρ with | .relay => .back | .back => .sender | .sender => .relay)
    then k₁ else k₂

/-- The honest relays of a game, with the public key `pk` at the role `ρ` and the public keys
of `keys` at the other two. -/
def honAt (pk : Key kem) (keys : Role → Key kem × kem.PrivateKey) : Protocols.RSOR.Honest 𝒮 :=
  fun h => ⟨names h, if h = ρ then pk else (keys h).1⟩

/-- What the adversary's first phase leaves the challenger: the key pairs of the two honest
relays that are not behind the oracle, and the challenge. The key pair at `ρ` is not used. -/
structure PropCh (pk : Key kem) where
  keys : Role → Key kem × kem.PrivateKey
  c : P.Challenge (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names pk keys)

/-- A game of the property `P` around the ciphertext of the relay `ρ`'s layer: `draw` is what
the challenger draws besides the seed of that ciphertext, and `view` the world it shows. -/
def propSetupOf (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : Key kem} → PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
        pk
      → Oth → kem.Ciphertext → KeyTuple → Protocols.RSOR.World 𝒮) :
    KeyedSetup kem (Protocols.RSOR.World 𝒮) Bool where
  Ch := PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
  Oth := Oth
  drawOth _ := draw
  view := view
  final _ _ _ _ out := out

/-- The adversary of the keyed game that an adversary of `P` gives. It draws the keys of the
two honest relays that are not behind the oracle, and answers for all three. -/
def propAdvOf (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : Key kem} → PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
        pk
      → Oth → kem.Ciphertext → KeyTuple → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) :
    KeyedAdversary (propSetupOf kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth
        draw view) where
  St := A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey)
  pre pk := do
    let k₁ ← (liftM (keygen kem) : OracleComp procSpec _)
    let k₂ ← (liftM (keygen kem) : OracleComp procSpec _)
    let keys := keysOf kem ρ k₁ k₂
    let out ← (simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ (fun h
        => (keys h).2) {})
      (A.choose (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names pk keys))).run
          {}
    return (⟨keys, out.1.1⟩, (out.1.2, out.2, fun h => (keys h).2))
  post st w :=
    (simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ st.2.2 w.patch)
        (A.guess st.1 w.onion)).run' st.2.1

/-- The first phase of `propAdvOf`, answered by the honest relay `ρ`: it is the first phase of
the adversary of `P` against the game's honest relays. -/
theorem propAdv_pre (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : Key kem} → PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
        pk
      → Oth → kem.Ciphertext → KeyTuple → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) (k : Key kem × kem.PrivateKey) :
    simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
        ((propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw view
            A).pre k.1)
      = (do
        let k₁ ← keygen kem
        let k₂ ← keygen kem
        let out ← (simulateQ (Protocols.RSOR.honest
            (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf kem ρ
                k₁ k₂))
            (fun h => if h = ρ then k.2 else (keysOf kem ρ k₁ k₂ h).2) {})
          (A.choose (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf
              kem ρ k₁ k₂)))).run {}
        return (⟨keysOf kem ρ k₁ k₂, out.1.1⟩,
          (out.1.2, out.2, fun h => (keysOf kem ρ k₁ k₂ h).2))) := by
  have hv : ∀ (k₁ k₂ : Key kem × kem.PrivateKey) {α : Type}
      (oa : OracleComp (Protocols.RSOR.oracleSpec 𝒮) α),
      simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
          ((simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ
            (fun h => (keysOf kem ρ k₁ k₂ h).2) {}) oa).run {})
        = (simulateQ (Protocols.RSOR.honest
            (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf kem ρ
                k₁ k₂))
            (fun h => if h = ρ then k.2 else (keysOf kem ρ k₁ k₂ h).2) {}) oa).run {} :=
    fun k₁ k₂ _ oa => by
      have h := viaOracle_honest kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ
        (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf kem ρ k₁
            k₂))
        (fun h => (keysOf kem ρ k₁ k₂ h).2)
        (fun h => if h = ρ then k.2 else (keysOf kem ρ k₁ k₂ h).2)
        (fun h hr => (ite_eq_right hr).symm) {} oa {}
      rwa [ite_eq_left rfl] at h
  unfold propAdvOf
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_procImpl_liftM, hv]

/-- The second phase of `propAdvOf`, answered by the keyed relay with the keys of the
ciphertext's own secret: it is the second phase of the adversary of `P` against the game's
honest relays. -/
theorem propAdv_post (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : Key kem} → PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
        pk
      → Oth → kem.Ciphertext → KeyTuple → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) (k : Key kem × kem.PrivateKey)
    (keys : Role → Key kem × kem.PrivateKey)
    (c : kem.Ciphertext) (K : kem.Plaintext) (hdec : decapOf kem k.2 c = some K)
    (st : A.State) (log : Protocols.RSOR.Log 𝒮) (w : Protocols.RSOR.World 𝒮) :
    simulateQ (procImplK kem cipher macS kdfS streamS geom k.2 c ((hopKeysPRG kem kdfS).gen K))
        ((propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw view
            A).post
          (st, log, fun h => (keys h).2) w)
      = (simulateQ (Protocols.RSOR.honest
            (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 keys)
            (fun h => if h = ρ then k.2 else (keys h).2) w.patch)
          (A.guess st w.onion)).run' log := by
  have hv := viaOracle_honest kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ
    (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 keys)
    (fun h => (keys h).2) (fun h => if h = ρ then k.2 else (keys h).2)
    (fun h hr => (ite_eq_right hr).symm) w.patch (A.guess st w.onion) log
  rw [ite_eq_left rfl] at hv
  rw [procImplK_real kem cipher macS kdfS streamS geom k.2 c K hdec]
  unfold propAdvOf
  simp only [StateT.run', simulateQ_map]
  exact congrArg (fun x => (·.1) <$> x) hv

/-- The draws of a world of `P`: the honest relays' key pairs, the adversary's first phase, the
challenger's draws, and the seed of the encapsulation to the honest relay `ρ`. -/
structure PropDraw (Oth : Type) (A : P.Adversary) where
  k : Key kem × kem.PrivateKey
  keys : Role → Key kem × kem.PrivateKey
  c : P.Challenge (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 keys)
  st : A.State
  log : Protocols.RSOR.Log 𝒮
  o : Oth
  s : Vector UInt8 32

/-- The draw of `PropDraw`. -/
def propDrawOf (Oth : Type) (draw : ProbComp Oth) (A : P.Adversary) :
    ProbComp (PropDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A) := do
  let k ← keygen kem
  let k₁ ← keygen kem
  let k₂ ← keygen kem
  let out ← (simulateQ (Protocols.RSOR.honest
      (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf kem ρ k₁ k₂))
      (fun h => if h = ρ then k.2 else (keysOf kem ρ k₁ k₂ h).2) {})
    (A.choose (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf kem ρ
        k₁ k₂)))).run {}
  let o ← draw
  let s ← $ᵗ (Vector UInt8 32)
  return ⟨k, keysOf kem ρ k₁ k₂, out.1.1, out.1.2, out.2, o, s⟩

/-- **The game with the relay `ρ`'s key pair drawn first.** A world of `P` is the game played
from the honest relays `honAt`, with `ρ`'s key pair drawn before the other two. -/
theorem play_evalDistEq_honAt (A : P.Adversary) (b : Bool) :
    Protocols.RSOR.Property.play names A b
      =ᵈ (do
        let k ← keygen kem
        let k₁ ← keygen kem
        let k₂ ← keygen kem
        Protocols.RSOR.Property.playFrom
          (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf kem ρ k₁
              k₂))
          (fun h => if h = ρ then k.2 else (keysOf kem ρ k₁ k₂ h).2) A b) := by
  have hsk : ∀ (hon : Protocols.RSOR.Honest 𝒮) (sk sk' : Role → kem.PrivateKey), sk = sk' →
      Protocols.RSOR.Property.playFrom hon sk A b
        =ᵈ Protocols.RSOR.Property.playFrom hon sk' A b := fun _ _ _ h => h ▸ EvalDistEq.rfl
  unfold Protocols.RSOR.Property.play
  cases ρ with
  | relay =>
    refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
      EvalDistEq.bind_right _ fun k₂ => ?_
    have h1 : Protocols.RSOR.Property.honestOf (S := 𝒮) names k k₁ k₂
        = honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay names k.1 (keysOf kem
            .relay k₁ k₂) := by
      funext h
      cases h <;> rfl
    rw [h1]
    exact hsk _ _ _ (funext fun h => by cases h <;> rfl)
  | back =>
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
      EvalDistEq.bind_right _ fun k₂ => ?_
    have h1 : Protocols.RSOR.Property.honestOf (S := 𝒮) names k₂ k k₁
        = honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .back names k.1 (keysOf kem
            .back k₁ k₂) := by
      funext h
      cases h <;> rfl
    rw [h1]
    exact hsk _ _ _ (funext fun h => by cases h <;> rfl)
  | sender =>
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
      EvalDistEq.bind_right _ fun k₂ => ?_
    have h1 : Protocols.RSOR.Property.honestOf (S := 𝒮) names k₁ k₂ k
        = honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .sender names k.1 (keysOf kem
            .sender k₁ k₂) := by
      funext h
      cases h <;> rfl
    rw [h1]
    exact hsk _ _ _ (funext fun h => by cases h <;> rfl)

variable [SampleableType kem.Plaintext]

/-- The keyed game of `propAdvOf` with the real keys, as the draws of its world and then the
second phase on the world it shows. -/
theorem keyedReal_propAdvOf_evalDistEq (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : Key kem} → PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
        pk
      → Oth → kem.Ciphertext → KeyTuple → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) :
    keyedReal cipher macS kdfS streamS geom
        (propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw view A)
      =ᵈ propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw A >>=
          fun d =>
        simulateQ (procImplK kem cipher macS kdfS streamS geom d.k.2 (encapOf kem d.k.1.1 d.s).1
            ((hopKeysPRG kem kdfS).gen (encapOf kem d.k.1.1 d.s).2))
          ((propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw view
              A).post
            (d.st, d.log, fun h => (d.keys h).2)
            (view ⟨d.keys, d.c⟩ d.o (encapOf kem d.k.1.1 d.s).1
              ((hopKeysPRG kem kdfS).gen (encapOf kem d.k.1.1 d.s).2))) := by
  unfold keyedReal keyedGame propDrawOf
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
  simp only [propAdv_pre]
  simp only [propSetupOf, bind_assoc, pure_bind, bind_pure]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
    EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

end PropGame

end Cryptlib.Protocols.Sphinx.KEMSphinx
