/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLUStream1

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

/-! # SLU← for NIKE Sphinx: down to a uniform keystream at the honest relay

The steps at the honest relay, chained: the key game, the MAC, the payload cipher and the
keystream generator, in each world. What is left is the distance between the two worlds played
from a uniform header keystream at the relay, an ideal payload cipher there, and the relay
answering one header. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

variable (W : Protocols.RSOR.BackSwap (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
  h16))

/-- **SLU← for NIKE Sphinx, down to a uniform keystream at the honest relay.** The advantage
is at most, for each world: the chance of a draw on which its packets do not build; the
advantage of its adversary in the key game; a forgery against the MAC and the chance that the
bytes under the relay's tag do not have a header's length; the chance of a draw that is not
good for the payload step and a one-query advantage against the payload cipher; and the
keystream generator's advantage. To these is added the distance between the two worlds played
from a uniform header keystream at the relay. -/
theorem backwardUnlinkable_le_stream (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) :
    ((Protocols.RSOR.backwardWith W).advantage names A).toReal
      ≤ (Pr{let D ← (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A)}[backBad0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W D]).toReal
        + (Pr{let D ← (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W) A)}[backBad1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 W D]).toReal
        + keyAdvantage cipher macS kdfS streamS geom (backAdv0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 W names A)
        + keyAdvantage cipher macS kdfS streamS geom (backAdv1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 W names A)
        + (Pr{let b ← (Primitives.MAC.forgeExp macS (macForge nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
            macS kdfS streamS geom hvalid hmactag h16 W names) _ (backDraw0 nike geom) A (backM0
            nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewT0 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W)))}[b = true]).toReal
        + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A)}[¬ (backM0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W x).size = (2 + nike.publicKeySize +
            geom.routingInfoLength)]).toReal
        + (Pr{let b ← (Primitives.MAC.forgeExp macS (macForge nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
            macS kdfS streamS geom hvalid hmactag h16 W names) _ (swapDraw nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W) A (backM1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 W) (backViewT1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            W)))}[b = true]).toReal
        + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W) A)}[¬ (backM1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 W x).size = (2 + nike.publicKeySize + geom.routingInfoLength)]).toReal
        + (Pr{let z ← (propPayDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A)}[¬ backGoodP0
            nike cipher macS kdfS streamS geom hvalid hmactag h16 W z.2]).toReal
        + |(Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _ (propPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) _ (backDraw0
            nike geom) A (backM0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
            (backPlain0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W)).adv true)}[b = true]).toReal -
            (Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _ (propPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) _ (backDraw0
            nike geom) A (backM0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
            (backPlain0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W)).adv false)}[b = true]).toReal|
        + (Pr{let z ← (propPayDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W) A)}[¬ backGoodP1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 W z.2]).toReal
        + |(Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _ (propPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) _ (swapDraw
            nike cipher macS kdfS streamS geom hvalid hmactag h16 W) A (backM1 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W) (backPlain1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 W) (backViewE1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            W)).adv true)}[b = true]).toReal - (Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp
            cipher _ (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) _ (swapDraw nike cipher macS kdfS streamS geom hvalid
            hmactag h16 W) A (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
            (backPlain1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W)).adv false)}[b = true]).toReal|
        + |(Pr{let b ← (PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
            (propStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W) A (propStrRun nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W names) A (backMS1 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W) (backPlainS1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 W) (backViewS1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            W))))}[b = true]).toReal
          - (Pr{let b ← (PRGScheme.prgIdealExperiment (propStreamAdv nike cipher macS kdfS streamS
              geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike
              cipher macS kdfS streamS geom hvalid hmactag h16 W) A (propStrRun nike cipher macS
              kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A (backMS1
              nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backPlainS1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 W) (backViewS1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W))))}[b = true]).toReal|
        + |(Pr{let b ← (PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
            (propStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A (propStrRun nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A
            (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backPlainS0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewS0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W))))}[b = true]).toReal
          - (Pr{let b ← (PRGScheme.prgIdealExperiment (propStreamAdv nike cipher macS kdfS streamS
              geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0
              nike geom) A (propStrRun nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) A (backMS0 nike cipher macS kdfS streamS geom hvalid
              hmactag h16 W) (backPlainS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
              (backViewS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W))))}[b =
              true]).toReal|
        + |(Pr{let b ← (PRGScheme.prgIdealExperiment (propStreamAdv nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W) A (propStrRun nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
            nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A (backMS1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 W) (backPlainS1 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W) (backViewS1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 W))))}[b = true]).toReal
          - (Pr{let b ← (PRGScheme.prgIdealExperiment (propStreamAdv nike cipher macS kdfS streamS
              geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0
              nike geom) A (propStrRun nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) A (backMS0 nike cipher macS kdfS streamS geom hvalid
              hmactag h16 W) (backPlainS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
              (backViewS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W))))}[b =
              true]).toReal| := by
  have key : ∀ (adv b0 b1 k0 k1 g1 g0 m1 m0 e1 e0 i1 i0 f0 s0 f1 s1 gd0 o0 gd1 o1 : ℝ),
      adv ≤ b0 + b1 + k0 + k1 + |g1 - g0| → |g0 - m0| ≤ f0 + s0 → |g1 - m1| ≤ f1 + s1 →
      |m0 - e0| ≤ gd0 + o0 → |m1 - e1| ≤ gd1 + o1 →
      adv ≤ b0 + b1 + k0 + k1 + f0 + s0 + f1 + s1 + gd0 + o0 + gd1 + o1 + |e1 - i1|
        + |e0 - i0| + |i1 - i0| := by
    intro adv b0 b1 k0 k1 g1 g0 m1 m0 e1 e0 i1 i0 f0 s0 f1 s1 gd0 o0 gd1 o1 h hm0 hm1 hp0 hp1
    have t1 := abs_sub_le g1 m1 g0
    have t2 := abs_sub_le m1 e1 g0
    have t3 := abs_sub_le e1 i1 g0
    have t4 := abs_sub_le i1 i0 g0
    have t5 := abs_sub_le i0 e0 g0
    have t6 := abs_sub_le e0 m0 g0
    rw [abs_sub_comm i0 e0] at t5
    rw [abs_sub_comm e0 m0] at t6
    have t7 := abs_sub_comm m0 g0
    linarith
  have hk := backwardUnlinkable_le_keyGame nike cipher macS kdfS streamS geom hvalid hmactag h16 W
      names A
  have m0 := backward0_keyGame_sub_macOnly_le nike cipher macS kdfS streamS geom hvalid hmactag h16
      W names A
  have m1 := backward1_keyGame_sub_macOnly_le nike cipher macS kdfS streamS geom hvalid hmactag h16
      W names A
  have p0 := backward0_macOnly_sub_pay_le nike cipher macS kdfS streamS geom hvalid hmactag h16 W
      names A
  have p1 := backward1_macOnly_sub_pay_le nike cipher macS kdfS streamS geom hvalid hmactag h16 W
      names A
  rw [(backward0_pay_evalDistEq_prg nike cipher macS kdfS streamS geom hvalid hmactag h16 W names
      A).prEvent_eq (fun b => b = true)] at p0
  rw [(backward1_pay_evalDistEq_prg nike cipher macS kdfS streamS geom hvalid hmactag h16 W names
      A).prEvent_eq (fun b => b = true)] at p1
  exact key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk m0 m1 p0 p1

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
