/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxGame
import Cryptlib.Protocols.Sphinx.RelayMac
import Cryptlib.Protocols.RSORPayload

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

/-- `viaOracle` does not use the key it is given for `ρ`. -/
theorem viaOracle_congr (sk sk' : Role → nike.PrivateKey)
    (hsk : ∀ h, h ≠ ρ → sk h = sk' h)
    (patch : Protocols.RSOR.Patch (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16)) :
    viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ sk patch
      = viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ sk' patch := by
  unfold viaOracle
  congr 1
  · funext h o
    by_cases hr : h = ρ
    · simp [hr]
    · simp [hr, hsk h hr]
  · funext h msg o
    by_cases hr : h = ρ
    · simp [hr]
    · simp [hr, hsk h hr]

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

/-! ## The key game's other world as a relay game -/

/-- A hop's uniform draws other than its MAC key. -/
abbrev Rest := KEMSphinx.RestKeys × Vector UInt8 32

/-- A hop's keys from its MAC key and its other draws. -/
def restKeys (r : Rest) (km : Vector UInt8 32) : HopKeys :=
  keysOfDraw (KEMSphinx.withMAC r.1 km, r.2)

/-- The path of a draw, the honest relay's key at its place. -/
def drawHops (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    {Oth : Type} {A : P.Adversary} (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag
        h16 P ρ names Oth A) : Array PathHop :=
  (place (⟨D.keys, D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
      D.k.1)).1.modify
    (place (⟨D.keys, D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
        D.k.1)).2 fun h =>
      { h with publicKey := Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1) }

/-- The honest relay's place on the path of a draw. -/
def drawPos (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    {Oth : Type} {A : P.Adversary} (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag
        h16 P ρ names Oth A) : ℕ :=
  (place (⟨D.keys, D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
      D.k.1)).2

/-- The sender's secret of a draw. -/
def drawKey {Oth : Type} {A : P.Adversary} (D : PropDraw nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names Oth A) : nike.PrivateKey :=
  (nike.decodePrivateKey D.d).getD default

/-- The hops' keys of a draw, the honest relay's from its MAC key and its other draws. -/
def drawKeys (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    {Oth : Type} {A : P.Adversary} (x : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid
        hmactag h16 P ρ names Oth A)
    (km : Vector UInt8 32) : List HopKeys :=
  hopKeysWith nike kdfS (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
      x.2) (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x.2)
    (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x.2) (restKeys
        x.1 km) (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place
        x.2).size

/-- The element that reaches the honest relay's place. -/
def drawElem (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    {Oth : Type} {A : P.Adversary} (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag
        h16 P ρ names Oth A) : ByteArray :=
  groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names D)
    (RSOR.hopKeys nike kdfS (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names D) (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place D)
      (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place D)).toArray
          (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place D)

/-- The world a draw shows, for a MAC key of the honest relay. -/
def drawView (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    {Oth : Type}
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    {A : P.Adversary} (x : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P
        ρ names Oth A) (km : Vector UInt8 32) :
    Protocols.RSOR.World 𝒮 :=
  view (⟨x.2.keys, x.2.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
      x.2.k.1) x.2.o
    (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names x.2)
        (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x
        km).toArray 0)
    (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x km)

/-- The adversary's second phase on a world, the relay `ρ` behind its oracle. A place off the
path loses. -/
def drawRun (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    {Oth : Type} {A : P.Adversary} (x : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid
        hmactag h16 P ρ names Oth A)
    (w : Protocols.RSOR.World 𝒮) : OracleComp procSpec Bool :=
  if drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x.2 < (drawHops
      nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x.2).size then
    (simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ (fun h =>
        (x.2.keys h).2) w.patch) (A.guess x.2.st w.onion)).run'
      x.2.log
  else pure false

/-- **The key game's other world is a relay game.** The relay answers a packet with the element
of its place by the replaced keys, and any other with its own key. -/
theorem keyGame_false_evalDistEq_gameAll
    (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P
        ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) :
    keyGame cipher macS kdfS streamS geom (propAdvOf nike cipher macS kdfS streamS geom hvalid
        hmactag h16 P ρ names place Oth draw view A) false
      =ᵈ Relay.gameAll
        (do
          let r ← $ᵗ Rest
          let D ← propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth
              draw A
          return (r, D))
        (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize)
          = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x.2))
        (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
        (fun x km => procWith nike cipher macS streamS geom (fun _ => .ok (restKeys x.1 km)))
        (drawView nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place view)
            (drawRun nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place) := by
  have hbij : Function.Bijective (Function.uncurry
      fun (km : Vector UInt8 32) (r : Rest) => (KEMSphinx.withMAC r.1 km, r.2)) :=
    Function.bijective_iff_has_inverse.2
      ⟨fun u => (u.1.2.2.1, KEMSphinx.restOf u.1, u.2), fun ⟨_, ⟨_, _, _⟩, _⟩ => rfl,
        fun ⟨⟨_, _, _, _⟩, _⟩ => rfl⟩
  unfold keyGame Relay.gameAll
  refine EvalDistEq.trans (KEMSphinx.evalDistEq_pair_of_bijective hbij _).symm ?_
  refine EvalDistEq.bind_right _ fun km => ?_
  unfold propDrawOf
  simp only [propAdv_pre, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun r => EvalDistEq.bind_right _ fun k =>
    EvalDistEq.bind_right _ fun k₁ => EvalDistEq.bind_right _ fun k₂ =>
    EvalDistEq.bind_right _ fun out => ?_
  refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  refine EvalDistEq.bind_right _ fun d => ?_
  simp only [Bool.false_eq_true, ite_false]
  split
  · next hlt =>
    have of_eq : ∀ {a b : ProbComp Bool}, a = b → a =ᵈ b := fun h => h ▸ EvalDistEq.rfl
    have hK : ∀ a t, procImplK nike cipher macS kdfS streamS geom k.2 a t
        = relayImpl (procWith nike cipher macS streamS geom (keysExcept nike kdfS k.2 a t)) :=
      fun _ _ => rfl
    rw [hK]
    unfold propAdvOf
    simp only [simulateQ_bind, simulateQ_relayImpl_liftM]
    refine EvalDistEq.bind_right _ fun o => of_eq ?_
    simp only [drawRun, drawView, drawKeys, drawHops, drawPos, drawKey, restKeys, hlt, ite_true]
    congr 2
    funext pkt
    rw [procWith_keysExcept]
    unfold Relay.ansOf
    simp only [drawElem, drawHops, drawPos, drawKey,
      groupElem_hopKeysWith nike kdfS _ _ _ _ _ (le_of_lt hlt)]
    rw [toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS _ _ _ _ _ hlt)]
    split
    · next he => exact (ite_eq_left (decide_eq_true he)).symm
    · next he => exact (ite_eq_right fun h => he (of_decide_eq_true h)).symm
  · next hlt =>
    simp only [drawRun, drawHops, drawPos, hlt, ite_false, simulateQ_pure]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm

/-- The header the relay's MAC covers, cut or padded to that length. -/
def macMsg {Oth : Type} {A : P.Adversary}
    (M : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        ByteArray)
    (x : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A) :
        ByteArray :=
  Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (M x))

/-- The draws of the MAC step: the relay's draws other than its MAC key, and the game's. -/
abbrev macDraw (Oth : Type) (draw : ProbComp Oth) (A : P.Adversary) :
    ProbComp (Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth
        A) := do
  let r ← $ᵗ Rest
  let D ← propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw A
  return (r, D)

/-- The key game's other world with the relay answering the element of its place under the
header `M` with its tag only. -/
abbrev macOnly (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary) (M : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P
        ρ names Oth A → ByteArray) : ProbComp Bool :=
  Relay.gameOnly macS (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth
      draw A) (2 + nike.publicKeySize + geom.routingInfoLength) (macMsg nike cipher macS kdfS
      streamS geom hvalid hmactag h16 P ρ names M)
    (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize)
      = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x.2))
    (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
    (fun x tag => procWith nike cipher (Primitives.MAC.MAC.const tag) streamS geom
      (fun _ => .ok (restKeys x.1 default)))
    (drawView nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place view) (drawRun
        nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place)

/-- The forgery adversary of the MAC step. -/
abbrev macForge (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth) (A : P.Adversary)
    (M : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        ByteArray)
    (viewT : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A
        → Vector UInt8 macS.tagSize
      → Protocols.RSOR.World 𝒮) : Primitives.MAC.ForgeAdversary macS :=
  Relay.forgeAdv macS (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth
      draw A) (2 + nike.publicKeySize + geom.routingInfoLength) (macMsg nike cipher macS kdfS
      streamS geom hvalid hmactag h16 P ρ names M)
    (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize)
      = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x.2))
    (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
    (fun x tag => procWith nike cipher (Primitives.MAC.MAC.const tag) streamS geom
      (fun _ => .ok (restKeys x.1 default)))
    viewT (drawRun nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place)

/-- **The MAC step for the key game's other world.** If the world shown uses the honest relay's
MAC key for one tag only, the tag of the bytes `M` of the challenge header, the relay may answer
the element of its place under that header only, at the cost of a forgery against the MAC and
the chance of a draw that is not `good`. -/
theorem keyGame_false_sub_gameOnly_le
    (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P
        ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth)
    (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names pk → Oth → ByteArray → List HopKeys
      → Protocols.RSOR.World 𝒮)
    (A : P.Adversary)
    (M : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        ByteArray)
    (viewT : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A
        → Vector UInt8 macS.tagSize
      → Protocols.RSOR.World 𝒮)
    (good : Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Prop)
    (hM : ∀ x, good x → (M x).size = (2 + nike.publicKeySize + geom.routingInfoLength))
    (hview : ∀ x km, good x → drawView nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names place view x km
      = viewT x (macS.mac (Util.Bytes.ofVector km) (M x))) :
    |(Pr{let b ← (keyGame cipher macS kdfS streamS geom
          (propAdvOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw
              view A) false)}[b = true]).toReal
      - (Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place
          Oth draw view A M)}[b = true]).toReal|
    ≤ (Pr{let b ← (Primitives.MAC.forgeExp macS
          (macForge nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw
              A M viewT))}[b = true]).toReal
      + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth
          draw A)}[¬ good x]).toReal := by
  rw [(keyGame_false_evalDistEq_gameAll nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
      names place Oth draw view A).prEvent_eq
    (fun b => b = true)]
  have hsz : ∀ x, (macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names M x).size
      = (2 + nike.publicKeySize + geom.routingInfoLength) := fun x => Util.Bytes.size_ofVector _
  refine Relay.gameAll_sub_gameOnly_le macS _ (2 + nike.publicKeySize + geom.routingInfoLength)
      (macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names M) _ _
    (fun x km => procWith nike cipher macS streamS geom (fun _ => .ok (restKeys x.1 km))) _ _ viewT
        _ good
    (fun x km hg => ?_) (fun x km pkt hh => ?_) (fun x km pkt _ hsome hne => ?_)
  · rw [hview x km hg]
    unfold macMsg
    rw [Util.Bytes.ofVector_toVecN _ (hM x hg)]
  · have hpre : pkt.extract 0 (2 + nike.publicKeySize + geom.routingInfoLength) = macMsg nike
      cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names M x := by
      have h1 := congrArg (fun b : ByteArray => b.extract 0 (2 + nike.publicKeySize +
          geom.routingInfoLength)) hh
      simp only [ByteArray.extract_extract, Nat.zero_add] at h1
      rw [Nat.min_eq_left (Nat.le_add_right _ _)] at h1
      rw [h1]
      have h2 := Util.Bytes.extract_append_left (macMsg nike cipher macS kdfS streamS geom hvalid
          hmactag h16 P ρ names M x)
        (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (macMsg nike cipher macS kdfS
            streamS geom hvalid hmactag h16 P ρ names M x)))
      rwa [hsz x] at h2
    rw [procWith_const nike cipher macS streamS geom (restKeys x.1 km) default pkt, hpre]
    rfl
  · exact procWith_forgery nike cipher macS streamS geom hmactag _ pkt _ (restKeys x.1 km) rfl
      hsome hne

end PropGame

/-! ## A relay that answers one header -/

section OneHeader

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

/-- The relay's answers when it is handed the keys `t` for the element `a` and answers that
element under the header `Mb` with the tag `tag` only. -/
def onlyAns (sk : nike.PrivateKey) (a : ByteArray) (t : HopKeys) (Mb : ByteArray)
    (tag : Vector UInt8 macS.tagSize) (pkt : ByteArray) : ProcResult :=
  if pkt.extract 2 (2 + nike.publicKeySize) = a then
    if pkt.extract 0 ((2 + nike.publicKeySize + geom.routingInfoLength) + macS.tagSize) = Mb ++
        Util.Bytes.ofVector tag then
      procWith nike cipher (Primitives.MAC.MAC.const tag) streamS geom (fun _ => .ok t) pkt
    else none
  else procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) pkt

/-- The relay's answers when it refuses the element `a`. -/
def noneAns (sk : nike.PrivateKey) (a : ByteArray) (pkt : ByteArray) : ProcResult :=
  if pkt.extract 2 (2 + nike.publicKeySize) = a then none
  else procWith nike cipher macS streamS geom (relayKeys nike kdfS sk) pkt

/-- **What a relay that answers one header does with an onion.** Under that header it decrypts
the onion's payload with its payload key and goes on from the decrypted block; under any other
it refuses the element. -/
theorem onlyAns_join (hvalid : geom.ValidForNIKE nike) (hmactag : macS.tagSize = macLength)
    (sk : nike.PrivateKey) (a : ByteArray) (t : HopKeys) (Mb : ByteArray)
    (tag : Vector UInt8 macS.tagSize) (Hv : Vector UInt8 geom.headerLength)
    (hH : Util.Bytes.ofVector Hv = Mb ++ Util.Bytes.ofVector tag)
    (hcar : (Util.Bytes.ofVector Hv).extract 2 (2 + nike.publicKeySize) = a)
    (o : Onion geom) :
    onlyAns nike cipher macS kdfS streamS geom sk a t Mb tag (join o)
      = if o.1 = Hv then
          procD nike (Primitives.MAC.MAC.const tag) streamS geom (L := (geom.payloadTagLength +
              geom.forwardPayloadLength)) (fun _ => .ok t)
            (fun _ _ => Util.Bytes.toVecN _ (cipher.decrypt t.payloadEncryption.toArray
              (Util.Bytes.ofVector t.headerEncryptionIV) (Util.Bytes.ofVector o.2))) (join o)
        else noneAns nike cipher macS kdfS streamS geom sk a (join o) := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have hoff : (2 + nike.publicKeySize + geom.routingInfoLength) + macS.tagSize = geom.headerLength
      := by
    rw [hhdr, hmactag]
    rfl
  have e1 : (join o).extract 0 geom.headerLength = Util.Bytes.ofVector o.1 := by
    unfold join
    simpa using Cryptlib.Util.Bytes.extract_append_left (Util.Bytes.ofVector o.1)
      (Util.Bytes.ofVector o.2)
  have e2 : (join o).extract geom.headerLength (join o).size = Util.Bytes.ofVector o.2 := by
    unfold join
    simpa using Cryptlib.Util.Bytes.extract_append_right (Util.Bytes.ofVector o.1)
      (Util.Bytes.ofVector o.2)
  have e3 : (join o).extract 2 (2 + nike.publicKeySize)
      = (Util.Bytes.ofVector o.1).extract 2 (2 + nike.publicKeySize) := by
    rw [← e1]
    exact (KEMSphinx.extract_of_prefix_eq (n := geom.headerLength)
      (by rw [ByteArray.extract_extract]; simp) 2 (2 + nike.publicKeySize)
      (by rw [hhdr]; unfold Constants.adLength; omega)).symm
  have hpoff : 2 + nike.publicKeySize + geom.routingInfoLength + macLength
      = geom.headerLength := by
    rw [hhdr]
    rfl
  unfold onlyAns noneAns
  rw [hoff, e1, e3]
  by_cases ho : o.1 = Hv
  · rw [ite_eq_left ho, ho, hcar, ite_eq_left rfl, ite_eq_left hH]
    rw [procWith_eq_procD nike cipher (Primitives.MAC.MAC.const tag) streamS geom (L :=
        (geom.payloadTagLength + geom.forwardPayloadLength))
      (fun _ => .ok t) (join o) (by rw [hpoff, e2, Util.Bytes.size_ofVector])]
    refine procD_congr nike _ streamS geom _ _ _ (join o) fun k hk => ?_
    obtain rfl : t = k := by injection hk
    rw [hpoff, e2, Util.Bytes.toVecN_ofVector]
  · rw [ite_eq_right ho]
    have hne : Util.Bytes.ofVector o.1 ≠ Mb ++ Util.Bytes.ofVector tag := fun h =>
      ho (by simpa using congrArg (Util.Bytes.toVecN geom.headerLength) (h.trans hH.symm))
    rw [ite_eq_right hne]

end OneHeader

/-! ## The oracle of a relay that answers one header -/

section OneHeaderOracle

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- **The honest relays, one of them answering one header, decrypt one block under it.** The
relays' oracle, with the relay `ρ` answering the element `a` under one header only, is the
oracle in which `ρ` decrypts the payload under that header with its payload key and goes on
from the decrypted block, and refuses the element under any other header. -/
theorem oracle_onlyAns (ρ : Role) (sk : Role → nike.PrivateKey) (a : ByteArray) (t : HopKeys)
    (Mb : ByteArray) (tag : Vector UInt8 macS.tagSize) (Hv : Vector UInt8 geom.headerLength)
    (hH : Util.Bytes.ofVector Hv = Mb ++ Util.Bytes.ofVector tag)
    (hcar : (Util.Bytes.ofVector Hv).extract 2 (2 + nike.publicKeySize) = a)
    (patch : Protocols.RSOR.Patch 𝒮) :
    Protocols.RSOR.oracle (S := 𝒮) (m := ProbComp)
        (fun h o => pure (if h = ρ then stepOf geom (onlyAns nike cipher macS kdfS streamS geom (sk
            ρ) a t Mb tag (join o))
          else RSOR.proc nike cipher macS kdfS streamS geom (sk h) o))
        (fun h msg o => pure (if h = ρ then replyOf cipher geom msg (onlyAns nike cipher macS kdfS
            streamS geom (sk ρ) a t Mb tag (join o))
          else RSOR.reply nike cipher macS kdfS streamS geom (sk h) msg o))
        patch
      = Protocols.RSOR.withDec (S := 𝒮) ρ Hv (fun o => o.2)
        (fun o y => stepOf geom (procD nike (Primitives.MAC.MAC.const tag) streamS geom (fun _ =>
            .ok t) (fun _ _ => y) (join o)))
        (fun msg o y => replyOf cipher geom msg (procD nike (Primitives.MAC.MAC.const tag) streamS
            geom (fun _ => .ok t) (fun _ _ => y) (join o)))
        (fun h o => if h = ρ then stepOf geom (noneAns nike cipher macS kdfS streamS geom (sk ρ) a
            (join o))
          else RSOR.proc nike cipher macS kdfS streamS geom (sk h) o)
        (fun h msg o => if h = ρ then replyOf cipher geom msg (noneAns nike cipher macS kdfS
            streamS geom (sk ρ) a (join o))
          else RSOR.reply nike cipher macS kdfS streamS geom (sk h) msg o)
        (fun y => Util.Bytes.toVecN _ (cipher.decrypt t.payloadEncryption.toArray
          (Util.Bytes.ofVector t.headerEncryptionIV) (Util.Bytes.ofVector y)))
        patch := by
  have e := fun (o : Onion geom) =>
    onlyAns_join nike cipher macS kdfS streamS geom hvalid hmactag (sk ρ) a t Mb tag Hv hH hcar o
  unfold Protocols.RSOR.withDec
  congr 1
  · funext h o
    refine congrArg pure ?_
    by_cases hr : h = ρ
    · by_cases ho : o.1 = Hv
      · exact ((ite_eq_left hr).trans (congrArg (stepOf geom) ((e o).trans (ite_eq_left ho)))).trans
          (ite_eq_left ⟨hr, ho⟩).symm
      · exact ((ite_eq_left hr).trans (congrArg (stepOf geom) ((e o).trans (ite_eq_right
          ho)))).trans
          ((ite_eq_right fun hc => ho hc.2).trans (ite_eq_left hr)).symm
    · exact (ite_eq_right hr).trans ((ite_eq_right fun hc => hr hc.1).trans (ite_eq_right hr)).symm
  · funext h msg o
    refine congrArg pure ?_
    by_cases hr : h = ρ
    · by_cases ho : o.1 = Hv
      · exact ((ite_eq_left hr).trans (congrArg (replyOf cipher geom msg) ((e o).trans (ite_eq_left
          ho)))).trans
          (ite_eq_left ⟨hr, ho⟩).symm
      · exact ((ite_eq_left hr).trans (congrArg (replyOf cipher geom msg) ((e o).trans
          (ite_eq_right ho)))).trans
          ((ite_eq_right fun hc => ho hc.2).trans (ite_eq_left hr)).symm
    · exact (ite_eq_right hr).trans ((ite_eq_right fun hc => hr hc.1).trans (ite_eq_right hr)).symm

/-- **The second phase against a relay that answers one header**, behind its oracle, is the
second phase against the one-decryption oracle. -/
theorem relayImpl_onlyAns_run (ρ : Role) (sk : Role → nike.PrivateKey) (a : ByteArray)
    (t : HopKeys) (Mb : ByteArray) (tag : Vector UInt8 macS.tagSize)
    (Hv : Vector UInt8 geom.headerLength)
    (hH : Util.Bytes.ofVector Hv = Mb ++ Util.Bytes.ofVector tag)
    (hcar : (Util.Bytes.ofVector Hv).extract 2 (2 + nike.publicKeySize) = a)
    (patch : Protocols.RSOR.Patch 𝒮) {α : Type}
    (oa : OracleComp (Protocols.RSOR.oracleSpec 𝒮) α) (log : Protocols.RSOR.Log 𝒮) :
    simulateQ (relayImpl (onlyAns nike cipher macS kdfS streamS geom (sk ρ) a t Mb tag))
        ((simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ sk patch)
            oa).run' log)
      = (simulateQ (Protocols.RSOR.withDec (S := 𝒮) ρ Hv (fun o => o.2)
          (fun o y => stepOf geom (procD nike (Primitives.MAC.MAC.const tag) streamS geom (fun _ =>
              .ok t) (fun _ _ => y) (join o)))
          (fun msg o y => replyOf cipher geom msg (procD nike (Primitives.MAC.MAC.const tag)
              streamS geom (fun _ => .ok t) (fun _ _ => y) (join o)))
          (fun h o => if h = ρ then stepOf geom (noneAns nike cipher macS kdfS streamS geom (sk ρ)
              a (join o))
            else RSOR.proc nike cipher macS kdfS streamS geom (sk h) o)
          (fun h msg o => if h = ρ then replyOf cipher geom msg (noneAns nike cipher macS kdfS
              streamS geom (sk ρ) a (join o))
            else RSOR.reply nike cipher macS kdfS streamS geom (sk h) msg o)
          (fun y => Util.Bytes.toVecN _ (cipher.decrypt t.payloadEncryption.toArray
            (Util.Bytes.ofVector t.headerEncryptionIV) (Util.Bytes.ofVector y)))
          patch) oa).run' log := by
  rw [← oracle_onlyAns nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ sk a t Mb tag Hv hH
      hcar patch]
  simp only [StateT.run', simulateQ_map]
  exact congrArg (fun x => (·.1) <$> x)
    (viaOracle_relayImpl nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ (onlyAns nike
        cipher macS kdfS streamS geom (sk ρ) a t Mb tag) sk patch oa log)

end OneHeaderOracle

end Cryptlib.Protocols.Sphinx.NIKESphinx
