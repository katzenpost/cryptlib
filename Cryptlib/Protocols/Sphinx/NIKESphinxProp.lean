/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxGame
import Cryptlib.Protocols.Sphinx.KEMSphinxKeyed

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.KEMSphinx (ProcResult procSpec relayImpl simulateQ_relayImpl_liftM)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion join stepOf replyOf)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Protocols.RSOR (Role)

/-! # The games of `Protocols.RSOR` for NIKE Sphinx, with one relay behind an oracle

To reduce a property of NIKE Sphinx to the key game, the honest relay whose keys are replaced
answers through an oracle for its unwrapped packets, as in the proofs for KEM Sphinx. -/

section Games

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

/-- A relay's step, read from what it returns for the packet. -/
theorem proc_eq_stepOf (sk : nike.PrivateKey) (o : Onion geom) :
    RSOR.proc nike cipher macS kdfS streamS geom sk o
      = stepOf geom (procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) (join o)) := by
  unfold RSOR.proc
  rw [unwrap_eq_procWith]
  rcases procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) (join o) with
    _ | ⟨_ | p, t, cmds, _ | fwd⟩ <;> rfl

/-- A relay's reply, read from what it returns for the packet. -/
theorem reply_eq_replyOf (sk : nike.PrivateKey) (m : Msg geom) (o : Onion geom) :
    RSOR.reply nike cipher macS kdfS streamS geom sk m o
      = replyOf cipher geom m
        (procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) (join o)) := by
  unfold RSOR.reply
  rw [unwrap_eq_procWith]
  rcases procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) (join o) with
    _ | ⟨_ | p, t, cmds, _ | fwd⟩ <;> rfl

/-- The relay's oracle answers a sampling query by sampling. -/
theorem simulateQ_procImpl_liftM (sk : nike.PrivateKey) {α : Type} (x : ProbComp α) :
    simulateQ (procImpl nike cipher macS kdfS streamS geom sk) (liftM x : OracleComp procSpec α)
      = x := by
  unfold procImpl
  rw [QueryImpl.add_eq_hAdd, QueryImpl.simulateQ_add_liftM_left]
  simp

/-- NIKE Sphinx as the scheme of the games. -/
abbrev sphinx : Protocols.RSOR.Scheme :=
  RSOR.scheme nike cipher macS kdfS streamS geom hvalid hmactag h16

variable (ρ : Role)

/-- The honest relays of a game, with the relay `ρ` answered by an oracle for its unwrapped
packets, and the other two by their secret keys. `sk ρ` is not used. -/
def viaOracle (sk : Role → nike.PrivateKey)
    (patch : Protocols.RSOR.Patch (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16)) :
    QueryImpl
      (Protocols.RSOR.oracleSpec (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16))
      (StateT (Protocols.RSOR.Log (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16))
        (OracleComp procSpec)) :=
  Protocols.RSOR.oracle
    (fun h o => if h = ρ then
        stepOf geom <$>
          (liftM ((ByteArray →ₒ ProcResult).query (join o)) : OracleComp procSpec ProcResult)
      else pure (RSOR.proc nike cipher macS kdfS streamS geom (sk h) o))
    (fun h msg o => if h = ρ then
        replyOf cipher geom msg <$>
          (liftM ((ByteArray →ₒ ProcResult).query (join o)) : OracleComp procSpec ProcResult)
      else pure (RSOR.reply nike cipher macS kdfS streamS geom (sk h) msg o))
    patch

/-- Answering that oracle with the relay's secret key gives the honest relays of the game. The
keys `viaOracle` is given need only agree with the game's for the other two relays. -/
theorem viaOracle_honest
    (hon : Protocols.RSOR.Honest (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16))
    (sk sk' : Role → nike.PrivateKey) (hsk : ∀ h, h ≠ ρ → sk h = sk' h)
    (patch : Protocols.RSOR.Patch (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16))
    {α : Type}
    (oa : OracleComp
      (Protocols.RSOR.oracleSpec (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16)) α)
    (log : Protocols.RSOR.Log (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16)) :
    simulateQ (procImpl nike cipher macS kdfS streamS geom (sk' ρ))
        ((simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ sk patch)
          oa).run log)
      = (simulateQ (Protocols.RSOR.honest hon sk' patch) oa).run log := by
  refine simulateQ_StateT_compose _ _ _ (fun q log => ?_) oa log
  rcases q with (t | ⟨h, o⟩) | ⟨h, msg, o⟩
  · simp only [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle]
    simpa using simulateQ_procImpl_liftM nike cipher macS kdfS streamS geom (sk' ρ)
      (liftM (OracleSpec.query t))
  · by_cases hs : (h, o.1) ∈ log.seen
    · simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.process, hs]
    · by_cases hr : h = ρ
      · subst hr
        simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.process,
          hs, simulateQ_procImpl_liftM]
        rw [show (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16).proc (sk' h)
            (hon h).name o = _ from proc_eq_stepOf nike cipher macS kdfS streamS geom (sk' h) o]
        rfl
      · simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.process,
          hs, hr, simulateQ_procImpl_liftM, hsk h hr]
        rfl
  · by_cases hs : (h, o) ∈ log.held
    · by_cases hr : h = ρ
      · subst hr
        simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.answer, hs]
        rw [show (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16).reply (sk' h)
            (hon h).name msg o = _ from
          reply_eq_replyOf nike cipher macS kdfS streamS geom (sk' h) msg o]
        rfl
      · simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.answer,
          hs, hr, hsk h hr]
        rfl
    · simp [viaOracle, Protocols.RSOR.honest, Protocols.RSOR.oracle, Protocols.RSOR.answer, hs]

/-- **The relay behind an oracle, for any answers.** Answering `viaOracle`'s oracle with the
answers `ans` gives the honest relays of the game with `ρ` processing a packet by `ans`.
The relay's log is then in front of `ans`: a header it has seen is refused before `ans` is
asked. -/
theorem viaOracle_relayImpl (ans : ByteArray → ProcResult) (sk : Role → nike.PrivateKey)
    (patch : Protocols.RSOR.Patch (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16))
    {α : Type}
    (oa : OracleComp
      (Protocols.RSOR.oracleSpec (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16)) α)
    (log : Protocols.RSOR.Log (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16)) :
    simulateQ (relayImpl ans)
        ((simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ sk patch)
          oa).run log)
      = (simulateQ (Protocols.RSOR.oracle (m := ProbComp)
          (fun h o => pure (if h = ρ then stepOf geom (ans (join o))
            else RSOR.proc nike cipher macS kdfS streamS geom (sk h) o))
          (fun h msg o => pure (if h = ρ then
              replyOf cipher geom msg (ans (join o))
            else RSOR.reply nike cipher macS kdfS streamS geom (sk h) msg o))
          patch) oa).run log := by
  refine simulateQ_StateT_compose _ _ _ (fun q log => ?_) oa log
  rcases q with (t | ⟨h, o⟩) | ⟨h, msg, o⟩
  · simp only [viaOracle, Protocols.RSOR.oracle]
    simpa using simulateQ_relayImpl_liftM ans (liftM (OracleSpec.query t))
  · by_cases hs : (h, o.1) ∈ log.seen
    · simp [viaOracle, Protocols.RSOR.oracle, Protocols.RSOR.process, hs]
    · by_cases hr : h = ρ
      · subst hr
        simp [viaOracle, Protocols.RSOR.oracle, Protocols.RSOR.process, hs,
          simulateQ_relayImpl_liftM]
        rfl
      · simp [viaOracle, Protocols.RSOR.oracle, Protocols.RSOR.process, hs, hr,
          simulateQ_relayImpl_liftM]
        rfl
  · by_cases hs : (h, o) ∈ log.held
    · by_cases hr : h = ρ
      · subst hr
        simp [viaOracle, Protocols.RSOR.oracle, Protocols.RSOR.answer, hs]
        rfl
      · simp [viaOracle, Protocols.RSOR.oracle, Protocols.RSOR.answer, hs, hr]
        rfl
    · simp [viaOracle, Protocols.RSOR.oracle, Protocols.RSOR.answer, hs]

end Games

/-! ## A property's adversary as an adversary on the key game -/

section PropGame

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

variable (P : Protocols.RSOR.Property (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
    h16))
  (ρ : Role) (names : Role → Name)

/-- The key pairs of the two honest relays that are not `ρ`: `k₁` for the role after `ρ`, `k₂`
for the other. The entry at `ρ` is not used. -/
def keysOf (ρ : Role) (k₁ k₂ : RSOR.Key nike × nike.PrivateKey) :
    Role → RSOR.Key nike × nike.PrivateKey :=
  fun h => if h = (match ρ with | .relay => .back | .back => .sender | .sender => .relay)
    then k₁ else k₂

/-- The honest relays of a game, with the public key `pk` at the role `ρ` and the public keys
of `keys` at the other two. -/
def honAt (pk : RSOR.Key nike) (keys : Role → RSOR.Key nike × nike.PrivateKey) :
    Protocols.RSOR.Honest 𝒮 :=
  fun h => ⟨names h, if h = ρ then pk else (keys h).1⟩

/-- What the adversary's first phase leaves the challenger: the key pairs of the two honest
relays that are not behind the oracle, and the challenge. -/
structure PropCh (pk : RSOR.Key nike) where
  keys : Role → RSOR.Key nike × nike.PrivateKey
  c : P.Challenge (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names pk keys)

/-- **The adversary on the key game that an adversary of `P` gives.** It draws the keys of the
two honest relays that are not behind the oracle and answers for all three. `place` is the path
and the place of the relay `ρ` whose keys the game replaces, `draw` what the challenger draws
besides that path's secret, and `view` the world it shows, from the path's first group element
and the hops' keys. -/
def propAdvOf (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) : KeyAdversary nike where
  St pk := PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names pk × A.State ×
      Protocols.RSOR.Log 𝒮
  pre pk := do
    let k₁ ← (liftM (RSOR.keygen nike) : OracleComp procSpec _)
    let k₂ ← (liftM (RSOR.keygen nike) : OracleComp procSpec _)
    let keys := keysOf nike ρ k₁ k₂
    let out ← (simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ (fun h
        => (keys h).2) {})
      (A.choose (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names pk keys))).run
          {}
    return (place ⟨keys, out.1.1⟩, (⟨keys, out.1.1⟩, out.1.2, out.2))
  post st a ks := do
    let o ← (liftM draw : OracleComp procSpec _)
    (simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ (fun h =>
        (st.1.keys h).2) (view st.1 o a ks).patch)
      (A.guess st.2.1 (view st.1 o a ks).onion)).run' st.2.2

/-- The first phase of `propAdvOf`, answered by the honest relay `ρ`: it is the first phase of
the adversary of `P` against the game's honest relays. -/
theorem propAdv_pre (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom
    hvalid hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) (k : RSOR.Key nike × nike.PrivateKey) :
    simulateQ (procImpl nike cipher macS kdfS streamS geom k.2)
        ((propAdvOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw
            view A).pre k.1)
      = (do
        let k₁ ← RSOR.keygen nike
        let k₂ ← RSOR.keygen nike
        let out ← (simulateQ (Protocols.RSOR.honest
            (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf nike ρ
                k₁ k₂))
            (fun h => if h = ρ then k.2 else (keysOf nike ρ k₁ k₂ h).2) {})
          (A.choose (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1
              (keysOf nike ρ k₁ k₂)))).run {}
        return (place ⟨keysOf nike ρ k₁ k₂, out.1.1⟩,
          (⟨keysOf nike ρ k₁ k₂, out.1.1⟩, out.1.2, out.2))) := by
  have hv : ∀ (k₁ k₂ : RSOR.Key nike × nike.PrivateKey) {α : Type}
      (oa : OracleComp (Protocols.RSOR.oracleSpec 𝒮) α),
      simulateQ (procImpl nike cipher macS kdfS streamS geom k.2)
          ((simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ (fun h =>
              (keysOf nike ρ k₁ k₂ h).2) {}) oa).run {})
        = (simulateQ (Protocols.RSOR.honest
            (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf nike ρ
                k₁ k₂))
            (fun h => if h = ρ then k.2 else (keysOf nike ρ k₁ k₂ h).2) {}) oa).run {} :=
    fun k₁ k₂ _ oa => by
      have h := viaOracle_honest nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ
        (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf nike ρ k₁
            k₂))
        (fun h => (keysOf nike ρ k₁ k₂ h).2)
        (fun h => if h = ρ then k.2 else (keysOf nike ρ k₁ k₂ h).2)
        (fun h hr => (ite_eq_right hr).symm) {} oa {}
      rwa [ite_eq_left rfl] at h
  unfold propAdvOf
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_procImpl_liftM, hv]

/-- The second phase of `propAdvOf`, answered by the honest relay `ρ`: the challenger's draw,
then the second phase of the adversary of `P` against the game's honest relays, on the world
shown. -/
theorem propAdv_post (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom
    hvalid hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) (k : RSOR.Key nike × nike.PrivateKey)
    (ch : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names k.1) (st :
        A.State) (log : Protocols.RSOR.Log 𝒮)
    (a : ByteArray) (ks : List HopKeys) :
    simulateQ (procImpl nike cipher macS kdfS streamS geom k.2)
        ((propAdvOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw
            view A).post (ch, st, log) a ks)
      = (do
        let o ← draw
        (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid hmactag
            h16 ρ names k.1 ch.keys)
            (fun h => if h = ρ then k.2 else (ch.keys h).2) (view ch o a ks).patch)
          (A.guess st (view ch o a ks).onion)).run' log) := by
  unfold propAdvOf
  simp only [simulateQ_bind, simulateQ_procImpl_liftM]
  refine bind_congr fun o => ?_
  have hv := viaOracle_honest nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ (honAt nike
      cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 ch.keys)
    (fun h => (ch.keys h).2) (fun h => if h = ρ then k.2 else (ch.keys h).2)
    (fun h hr => (ite_eq_right hr).symm) (view ch o a ks).patch
    (A.guess st (view ch o a ks).onion) log
  rw [ite_eq_left rfl] at hv
  simp only [StateT.run', simulateQ_map]
  exact congrArg (fun x => (·.1) <$> x) hv

/-- **The key game's real world, played by `propAdvOf`.** It is the game of `P` against the
honest relays, on the world `view` shows from the sender's own group element and hop keys. -/
theorem keyGame_true_propAdvOf
    (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P
        ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) :
    keyGame cipher macS kdfS streamS geom (propAdvOf nike cipher macS kdfS streamS geom hvalid
        hmactag h16 P ρ names place Oth draw view A) true
      = (do
        let _ ← $ᵗ (KEMSphinx.KeyTuple × Vector UInt8 32)
        let k ← RSOR.keygen nike
        let k₁ ← RSOR.keygen nike
        let k₂ ← RSOR.keygen nike
        let out ← (simulateQ (Protocols.RSOR.honest
            (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf nike ρ
                k₁ k₂))
            (fun h => if h = ρ then k.2 else (keysOf nike ρ k₁ k₂ h).2) {})
          (A.choose (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1
              (keysOf nike ρ k₁ k₂)))).run {}
        let d ← $ᵗ Vector UInt8 nike.privateKeySize
        let ch : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names k.1 :=
            ⟨keysOf nike ρ k₁ k₂, out.1.1⟩
        let c := (nike.decodePrivateKey d).getD default
        let hops := (place ch).1.modify (place ch).2 fun h =>
          { h with publicKey := Util.Bytes.ofVector (nike.encodePublicKey k.1.1) }
        let keys := RSOR.hopKeys nike kdfS c hops hops.size
        if (place ch).2 < hops.size then do
          let o ← draw
          (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid
              hmactag h16 ρ names k.1 ch.keys)
              (fun h => if h = ρ then k.2 else (ch.keys h).2)
              (view ch o (groupElem nike c keys.toArray 0) keys).patch)
            (A.guess out.1.2 (view ch o (groupElem nike c keys.toArray 0) keys).onion)).run' out.2
        else pure false) := by
  unfold keyGame
  simp only [propAdv_pre, bind_assoc, pure_bind]
  refine bind_congr fun u => ?_
  simp only [RSOR.keygen, bind_assoc, pure_bind]
  refine bind_congr fun s => bind_congr fun s₁ => bind_congr fun s₂ => bind_congr fun out =>
    bind_congr fun d => ?_
  simp only [ite_true, hopKeysWith_hopKey]
  split
  · next hlt =>
    rw [procImplK_hopKeys nike cipher macS kdfS streamS geom _ _ _ _ _ hlt ?_]
    · exact propAdv_post nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place
        Oth draw view A (⟨nike.derivePublicKey (nike.privateKeyFromSeed s), _, rfl⟩,
          nike.privateKeyFromSeed s) _ _ _ _ _
    · rw [getElem!_pos (Array.modify _ _ _) _ hlt]
      simp [Array.getElem_modify]
  · rfl

/-- **The game with the relay `ρ`'s key pair drawn first.** A world of `P` is the game played
from the honest relays `honAt`, with `ρ`'s key pair drawn before the other two. -/
theorem play_evalDistEq_honAt (A : P.Adversary) (b : Bool) :
    Protocols.RSOR.Property.play names A b
      =ᵈ (do
        let k ← RSOR.keygen nike
        let k₁ ← RSOR.keygen nike
        let k₂ ← RSOR.keygen nike
        Protocols.RSOR.Property.playFrom
          (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf nike ρ k₁
              k₂))
          (fun h => if h = ρ then k.2 else (keysOf nike ρ k₁ k₂ h).2) A b) := by
  have hsk : ∀ (hon : Protocols.RSOR.Honest 𝒮) (sk sk' : Role → nike.PrivateKey), sk = sk' →
      Protocols.RSOR.Property.playFrom hon sk A b
        =ᵈ Protocols.RSOR.Property.playFrom hon sk' A b := fun _ _ _ h => h ▸ EvalDistEq.rfl
  unfold Protocols.RSOR.Property.play
  cases ρ with
  | relay =>
    refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
      EvalDistEq.bind_right _ fun k₂ => ?_
    have h1 : Protocols.RSOR.Property.honestOf (S := 𝒮) names k k₁ k₂
        = honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay names k.1 (keysOf nike
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
        = honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .back names k.1 (keysOf nike
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
        = honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .sender names k.1 (keysOf nike
            .sender k₁ k₂) := by
      funext h
      cases h <;> rfl
    rw [h1]
    exact hsk _ _ _ (funext fun h => by cases h <;> rfl)

/-- The draws of the key game's real world for `propAdvOf`: the honest relays' key pairs, the
adversary's first phase, the challenger's draws, and the secret of the path the game is about. -/
structure PropDraw (Oth : Type) (A : P.Adversary) where
  k : RSOR.Key nike × nike.PrivateKey
  keys : Role → RSOR.Key nike × nike.PrivateKey
  c : P.Challenge (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 keys)
  st : A.State
  log : Protocols.RSOR.Log 𝒮
  o : Oth
  d : Vector UInt8 nike.privateKeySize

/-- The draw of `PropDraw`. -/
def propDrawOf (Oth : Type) (draw : ProbComp Oth) (A : P.Adversary) :
    ProbComp (PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A) := do
  let k ← RSOR.keygen nike
  let k₁ ← RSOR.keygen nike
  let k₂ ← RSOR.keygen nike
  let out ← (simulateQ (Protocols.RSOR.honest
      (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf nike ρ k₁
          k₂))
      (fun h => if h = ρ then k.2 else (keysOf nike ρ k₁ k₂ h).2) {})
    (A.choose (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ names k.1 (keysOf nike
        ρ k₁ k₂)))).run {}
  let o ← draw
  let d ← $ᵗ Vector UInt8 nike.privateKeySize
  return ⟨k, keysOf nike ρ k₁ k₂, out.1.1, out.1.2, out.2, o, d⟩

/-- The second phase of the key game's real world on a draw: the adversary of `P` against the
honest relays, on the world `view` shows from the sender's own group element and hop keys. -/
def propRealOf (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
        Oth A) : ProbComp Bool :=
  let ch : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names D.k.1 := ⟨D.keys,
      D.c⟩
  let c := (nike.decodePrivateKey D.d).getD default
  let hops := (place ch).1.modify (place ch).2 fun h =>
    { h with publicKey := Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1) }
  let keys := RSOR.hopKeys nike kdfS c hops hops.size
  if (place ch).2 < hops.size then
    (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16
        ρ names D.k.1 D.keys)
        (fun h => if h = ρ then D.k.2 else (D.keys h).2)
        (view ch D.o (groupElem nike c keys.toArray 0) keys).patch)
      (A.guess D.st (view ch D.o (groupElem nike c keys.toArray 0) keys).onion)).run' D.log
  else pure false

/-- **The key game's real world, as its draws and then the second phase.** -/
theorem keyGame_true_evalDistEq
    (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P
        ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) :
    keyGame cipher macS kdfS streamS geom (propAdvOf nike cipher macS kdfS streamS geom hvalid
        hmactag h16 P ρ names place Oth draw view A) true
      =ᵈ propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw A >>=
        propRealOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth view A
            := by
  rw [keyGame_true_propAdvOf]
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
  unfold propDrawOf propRealOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
    EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => ?_
  refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  refine EvalDistEq.bind_right _ fun d => ?_
  split
  · exact EvalDistEq.rfl
  · exact (OracleComp.EvalDistEq.bind_const _ _).symm

/-- The second phase of `propAdvOf`, answered by a relay that is handed the keys `t` for the
element `e`: the challenger's draw, then the second phase of the adversary of `P` against the
honest relays, `ρ` answering with the handed keys. -/
theorem propAdv_postK (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom
    hvalid hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) (k : RSOR.Key nike × nike.PrivateKey)
    (ch : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names k.1) (st :
        A.State) (log : Protocols.RSOR.Log 𝒮)
    (e : ByteArray) (t : HopKeys) (a : ByteArray) (ks : List HopKeys) :
    simulateQ (procImplK nike cipher macS kdfS streamS geom k.2 e t)
        ((propAdvOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw
            view A).post (ch, st, log) a ks)
      = (do
        let o ← draw
        (simulateQ (Protocols.RSOR.oracle (m := ProbComp)
            (fun h o => pure (if h = ρ then
                stepOf geom (procWith nike cipher macS streamS geom (keysExcept nike kdfS k.2 e t)
                    (join o))
              else RSOR.proc nike cipher macS kdfS streamS geom (ch.keys h).2 o))
            (fun h msg o => pure (if h = ρ then
                replyOf cipher geom msg (procWith nike cipher macS streamS geom (keysExcept nike
                    kdfS k.2 e t) (join o))
              else RSOR.reply nike cipher macS kdfS streamS geom (ch.keys h).2 msg o))
            (view ch o a ks).patch)
          (A.guess st (view ch o a ks).onion)).run' log) := by
  have hi : procImplK nike cipher macS kdfS streamS geom k.2 e t
      = relayImpl (procWith nike cipher macS streamS geom (keysExcept nike kdfS k.2 e t)) := rfl
  rw [hi]
  unfold propAdvOf
  simp only [simulateQ_bind, simulateQ_relayImpl_liftM]
  refine bind_congr fun o => ?_
  have hv := viaOracle_relayImpl nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ (procWith
      nike cipher macS streamS geom (keysExcept nike kdfS k.2 e t))
    (fun h => (ch.keys h).2) (view ch o a ks).patch (A.guess st (view ch o a ks).onion) log
  simp only [StateT.run', simulateQ_map]
  exact congrArg (fun x => (·.1) <$> x) hv

/-- The second phase of the key game's other world on a draw: the adversary of `P` against the
honest relays, on the world `view` shows from the hop keys with the relay's replaced by the
uniform `u`, the relay `ρ` answering the element of its place with the replacement. -/
def propIdealOf (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) (u : KEMSphinx.KeyTuple × Vector UInt8 32)
    (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A) : ProbComp
        Bool :=
  let ch : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names D.k.1 := ⟨D.keys,
      D.c⟩
  let c := (nike.decodePrivateKey D.d).getD default
  let hops := (place ch).1.modify (place ch).2 fun h =>
    { h with publicKey := Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1) }
  let keys := hopKeysWith nike kdfS c hops (place ch).2 (keysOfDraw u) hops.size
  if (place ch).2 < hops.size then
    (simulateQ (Protocols.RSOR.oracle (m := ProbComp)
        (fun h o => pure (if h = ρ then
            stepOf geom (procWith nike cipher macS streamS geom (keysExcept nike kdfS D.k.2
              (groupElem nike c keys.toArray (place ch).2) keys.toArray[(place ch).2]!) (join o))
          else RSOR.proc nike cipher macS kdfS streamS geom (D.keys h).2 o))
        (fun h msg o => pure (if h = ρ then
            replyOf cipher geom msg (procWith nike cipher macS streamS geom (keysExcept nike kdfS
                D.k.2
              (groupElem nike c keys.toArray (place ch).2) keys.toArray[(place ch).2]!) (join o))
          else RSOR.reply nike cipher macS kdfS streamS geom (D.keys h).2 msg o))
        (view ch D.o (groupElem nike c keys.toArray 0) keys).patch)
      (A.guess D.st (view ch D.o (groupElem nike c keys.toArray 0) keys).onion)).run' D.log
  else pure false

/-- **The key game's other world, as its draws and then the second phase.** -/
theorem keyGame_false_evalDistEq
    (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P
        ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) :
    keyGame cipher macS kdfS streamS geom (propAdvOf nike cipher macS kdfS streamS geom hvalid
        hmactag h16 P ρ names place Oth draw view A) false
      =ᵈ ($ᵗ (KEMSphinx.KeyTuple × Vector UInt8 32)) >>= fun u =>
        propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw A >>=
            propIdealOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth
            view A u := by
  unfold keyGame
  simp only [propAdv_pre, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun u => ?_
  unfold propDrawOf propIdealOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
    EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => ?_
  refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  refine EvalDistEq.bind_right _ fun d => ?_
  simp only [Bool.false_eq_true, ite_false]
  split
  · rw [propAdv_postK]
  · exact (OracleComp.EvalDistEq.bind_const _ _).symm

end PropGame

end Cryptlib.Protocols.Sphinx.NIKESphinx
