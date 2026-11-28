/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUExitDraws

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Common (commandsToBytes zeroPadTo toVec32 xorBytes)
open Cryptlib.Protocols.Sphinx.KEMSphinx (procSpec ProcResult relayImpl keysKs keysTag keysEnc)
open Cryptlib.Protocols.Sphinx.Common (v0AD)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion split join stepOf replyOf)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Protocols.RSOR (Role)

/-! # TLU→ for NIKE Sphinx

The last comparison of the two worlds over their draws, and the bound for TLU→: the chains of
`NIKESphinxTLU.lean` and `NIKESphinxTLUNext.lean` for the two worlds, joined by the comparison
of `NIKESphinxTLUFn.lean` to `NIKESphinxTLUExitDraws.lean`. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

set_option maxHeartbeats 4000000 in
/-- **World 1 is world 0 with the hops after the relay from an independent secret, over the
draws**, off the draws of world 1 that are not good. -/
theorem fin_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let b ← (finDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A >>=
        finOwnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[b = true]).toReal
      - (Pr{let b ← (world0B nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (exitE
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[b = true]).toReal|
    ≤ (Pr{let x ← (finDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[¬ finAll
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x]).toReal := by
  have hD := (finDraw_bind nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (fun x =>
      (pure x : ProbComp _))) (fun x => ¬ finAll nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x)
  rw [bind_pure] at hD
  rw [(finDraw_bind nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (finOwnRun nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names A)) (fun b => b = true),
    (world0B_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (exitE nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names A)) (fun b => b = true), hD]
  refine KEMSphinx.abs_prEvent_bind_sub_le _ _ _
    (fun p => finRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names >>= fun r =>
        (pure (finX nike cipher macS kdfS streamS geom hvalid hmactag h16 p r) : ProbComp _)) _ fun
        p => ?_
  refine (fin_fixed_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names A p).trans
      (le_of_eq ?_)
  rw [show (finRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names >>= fun r => (pure
      (finX nike cipher macS kdfS streamS geom hvalid hmactag h16 p r) : ProbComp _))
      = (fun r => finX nike cipher macS kdfS streamS geom hvalid hmactag h16 p r) <$> finRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names from by
    simp only [map_eq_bind_pure_comp, Function.comp_def], prEvent_map]

set_option maxHeartbeats 4000000 in
/-- **`world0E` with the end-of-path game `exitE` is world 0 after its chain.** -/
theorem world0E_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    world0E nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (exitE nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names A) =ᵈ PRGScheme.prgIdealExperiment
        (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) A) := by
  have h1 : world0E nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (exitE nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      =ᵈ (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) A >>= fun D => do
        let U ← $ᵗ (KEMSphinx.Keystream geom)
        let km ← $ᵗ (Vector UInt8 32)
        let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        let seed ← $ᵗ (Vector UInt8 32)
        strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names) A (km, seed, D) U u v) := by
    unfold world0E exitE
    refine EvalDistEq.bind_right _ fun D => EvalDistEq.bind_right _ fun U => EvalDistEq.bind_right
        _ fun km => EvalDistEq.bind_right _ fun u => EvalDistEq.bind_right _ fun v => ?_
    by_cases hc : (D.c.pos : ℕ) + 1 < D.c.req.fwd.hops.length
    · simp only [hc, ↓reduceIte]
      exact EvalDistEq.rfl
    · simp only [hc, ↓reduceIte]
      exact OracleComp.EvalDistEq.bind_const _ _
  refine h1.trans ?_
  unfold PRGScheme.prgIdealExperiment forwardStreamAdv
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U => OracleComp.EvalDistEq.bind_bind_swap _
      _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U => EvalDistEq.bind_right _ fun km =>
      EvalDistEq.bind_right _ fun D => EvalDistEq.bind_right _ fun u =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U => EvalDistEq.bind_right _ fun km =>
      EvalDistEq.bind_right _ fun D => OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U => EvalDistEq.bind_right _ fun km =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact EvalDistEq.rfl

set_option maxHeartbeats 4000000 in
/-- **TLU→ for NIKE Sphinx, down to its terms.** The advantage in telling the adversary's own
onion from a replacement that ends at the honest relay is at most the sum of: the chain of
each world down to its draws (the chance that the onion shown does not build, the key game's
advantage, a forgery against the MAC, the payload cipher's one-block advantage, the keystream
generator's advantage, and the chances of the draws that are not good for these); for the
original's hidden layer in world 1, the chance of a draw that is not good, the key game's
advantage, the chance that the adversary sends a packet carrying the original's element (once
when the relay starts to refuse it, once when it answers it again), the keystream generator's
advantage, and the chance of a draw on which the bytes under the relay's tag do not carry the
replacement's element; for the last comparison, the chance of a draw of world 1 that is not
good, the chance of a draw of world 0 whose path does not build, and the blinding advantage on
the NIKE. No term is a distance between two games of the scheme; the events are not bounded
here. -/
theorem forwardUnlinkable_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) :
    ((Protocols.RSOR.forwardUnlinkable (S := 𝒮)).advantage names A).toReal
      ≤ ((Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)}[forwardBad nike cipher
        macS kdfS streamS geom hvalid hmactag h16 D]).toReal
      + (keyAdvantage cipher macS kdfS streamS geom (forwardAdv nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) A)
      + ((Pr{let b ← (Primitives.MAC.forgeExp macS
            (macForge nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
                macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
                geom hvalid hmactag h16 names)) _
              (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).draw A (forwardMsg
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names))
              (forwardViewT nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
                  cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[b = true]).toReal
        + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names _ (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).draw
            A)}[¬ (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x).size = (2 +
                nike.publicKeySize + geom.routingInfoLength)]).toReal)
      + ((Pr{let z ← (payDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)}[¬ payGood nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names)
            z.2]).toReal
        + |(Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _
              (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
                  cipher macS kdfS streamS geom hvalid hmactag h16 names) A).adv true)}[b =
                  true]).toReal
            - (Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _
              (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
                  cipher macS kdfS streamS geom hvalid hmactag h16 names) A).adv false)}[b =
                  true]).toReal|
        + |(Pr{let b ← (PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
              (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A))}[b =
                  true]).toReal
            - (Pr{let b ← (PRGScheme.prgIdealExperiment
              (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A))}[b =
                  true]).toReal|)))
        + ((Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd1
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)}[shortBad nike cipher macS
        kdfS streamS geom hvalid hmactag h16 D]).toReal
      + (keyAdvantage cipher macS kdfS streamS geom (forwardAdv nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) A)
      + ((Pr{let b ← (Primitives.MAC.forgeExp macS
            (macForge nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (forwardPlace nike cipher
                macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
                geom hvalid hmactag h16 names)) _
              (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).draw A (forwardMsg
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names))
              (forwardViewT nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
                  cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[b = true]).toReal
        + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names _ (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).draw
            A)}[¬ (forwardMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names) x).size = (2 +
                nike.publicKeySize + geom.routingInfoLength)]).toReal)
      + ((Pr{let z ← (payDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)}[¬ payGood nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names)
            z.2]).toReal
        + |(Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _
              (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
                  cipher macS kdfS streamS geom hvalid hmactag h16 names) A).adv true)}[b =
                  true]).toReal
            - (Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _
              (forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
                  cipher macS kdfS streamS geom hvalid hmactag h16 names) A).adv false)}[b =
                  true]).toReal|
        + |(Pr{let b ← (PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
              (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A))}[b =
                  true]).toReal
            - (Pr{let b ← (PRGScheme.prgIdealExperiment
              (forwardStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A))}[b =
                  true]).toReal|)))
        + (Pr{let z ← (nextDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            A)}[nextBad
        nike cipher macS kdfS streamS geom hvalid hmactag h16 z]).toReal
        + keyAdvantage cipher macS kdfS streamS geom (nextAdv nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names A)
        + (Pr{let b ← (Relay.gameChal
        (do
          let u ← $ᵗ (KEMSphinx.KeyTuple × Vector UInt8 32)
          let p ← nextPre nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
          return (u, p))
        (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize) = nextElemI nike cipher macS
            kdfS streamS geom hvalid hmactag h16 x))
        (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
        (nextRunI nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) fun _ _ =>
            none)}[b = true]).toReal
        + |(Pr{let b ← (PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
            (nextStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[b =
            true]).toReal - (Pr{let b ← (PRGScheme.prgIdealExperiment (nextStreamAdv nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names A))}[b = true]).toReal|
        + ((Pr{let b ← (Relay.gameChal (finDraw nike cipher macS kdfS streamS geom hvalid hmactag
            h16
        names A) (finChal nike cipher macS kdfS streamS geom hvalid hmactag h16) (finOwn nike
        cipher macS kdfS streamS geom hvalid hmactag h16)
          (finRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) fun _ _ =>
              none)}[b = true]).toReal
      + (Pr{let x ← (finDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[¬
          finCar nike cipher macS kdfS streamS geom hvalid hmactag h16 x]).toReal)
        + (Pr{let x ← (finDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[¬
            finAll nike cipher macS kdfS streamS geom hvalid hmactag h16 x]).toReal
        + (Pr{let D ← (forwardDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A)}[fwdBad0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 D]).toReal
        + blindAdvantage kdfS (blindAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            A (exitE nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)) := by
  have h0 := forward_world0_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have h1 := forward_world1_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have h2 := prgIdeal_fwd1_sub_keyGame_le nike cipher macS kdfS streamS geom hvalid hmactag h16
      names A
  have h3 := keyGame_false_nextAdv_sub_le nike cipher macS kdfS streamS geom hvalid hmactag h16
      names A
  have h4 := (nextGame_none_evalDistEq_prgReal nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names A) (fun b => b = true)
  have h5 := prgIdeal_nextStreamAdv_sub_le nike cipher macS kdfS streamS geom hvalid hmactag h16
      names A
  have h6 := fin_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have h7 := world0E_sub_world0B_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names A
      (exitE nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)
  have h8 := (world0E_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      (fun b => b = true)
  have hk : keyAdvantage cipher macS kdfS streamS geom (nextAdv nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names A)
      = |(Pr{let x ← (keyGame cipher macS kdfS streamS geom (nextAdv nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names A) true)}[x
          = true]).toReal
        - (Pr{let x ← (keyGame cipher macS kdfS streamS geom (nextAdv nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names A) false)}[x
          = true]).toReal| := rfl
  refine (le_of_eq (Protocols.RSOR.Property.advantage_toReal
    (P := Protocols.RSOR.forwardUnlinkable (S := 𝒮)) names A)).trans ?_
  rw [h4] at h3
  rw [h8] at h7
  rw [hk]
  have a0 := abs_le.mp h0
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  have a3 := abs_le.mp h3
  have a5 := abs_le.mp h5
  have a6 := abs_le.mp h6
  have a7 := abs_le.mp h7
  have ak := neg_abs_le ((Pr{let x ← (keyGame cipher macS kdfS streamS geom (nextAdv nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names A)
      true)}[x = true]).toReal
    - (Pr{let x ← (keyGame cipher macS kdfS streamS geom (nextAdv nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names A) false)}[x
      = true]).toReal)
  have ak' := le_abs_self ((Pr{let x ← (keyGame cipher macS kdfS streamS geom (nextAdv nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names A)
      true)}[x = true]).toReal
    - (Pr{let x ← (keyGame cipher macS kdfS streamS geom (nextAdv nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names A) false)}[x
      = true]).toReal)
  have ap := neg_abs_le ((Pr{let b ← (PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS
      geom) (nextStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[b =
      true]).toReal - (Pr{let b ← (PRGScheme.prgIdealExperiment (nextStreamAdv nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names A))}[b = true]).toReal)
  have ap' := le_abs_self ((Pr{let b ← (PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS
      geom) (nextStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[b =
      true]).toReal - (Pr{let b ← (PRGScheme.prgIdealExperiment (nextStreamAdv nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names A))}[b = true]).toReal)
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
