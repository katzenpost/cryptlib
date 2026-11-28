/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLUChain

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

/-! # SLU← for NIKE Sphinx: through the onion built like a reply layer

As for KEM Sphinx, SLU← is split through the world in which the honest relay sends on an onion
built like a reply layer (`replySwap`): telling that onion from the fresh forward onion, and
SLU← with that onion sent on. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- An onion built like a reply layer: the header of a packet over the rest of the backward
path that ends in a reply, and a uniform payload. With it goes the header of the packet's last
layer. -/
def replySwap :
    Protocols.RSOR.BackSwap (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16) where
  X := RSOR.Randomness nike geom × Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
  draw := do
    let r' ← $ᵗ (RSOR.Randomness nike geom)
    let b ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    return (r', b)
  of c x :=
    (match RSOR.layer nike cipher macS kdfS streamS geom
        (RSOR.path nike (c.req.back.drop c.pos) [.surbReply x.1.2.2.2]) x.1.1
        ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0 with
      | .ok pkt => ((split geom pkt).1, x.2)
      | .error _ => (default : Onion geom),
    match RSOR.layer nike cipher macS kdfS streamS geom
        (RSOR.path nike (c.req.back.drop c.pos) [.surbReply x.1.2.2.2]) x.1.1
        ⟨Array.replicate geom.forwardPayloadLength 0⟩
        ((c.req.back.drop c.pos).hops.length - 1) with
      | .ok pkt => (split geom pkt).1
      | .error _ => (default : Onion geom).1)

/-- **SLU← for NIKE Sphinx, split through the onion built like a reply layer.** The advantage
is at most the advantage in telling the fresh forward onion from that onion in world 1, the
terms of `backwardUnlinkable_le_stream` with that onion sent on, and the distance between the
two worlds with it, played from a uniform header keystream at the honest relay. -/
theorem backwardUnlinkable_le_split (names : Role → Name)
    (A : (Protocols.RSOR.backwardWith (Protocols.RSOR.freshSwap (S := 𝒮))).Adversary) :
    ((Protocols.RSOR.backwardWith (Protocols.RSOR.freshSwap (S := 𝒮))).advantage names A).toReal
      ≤ ((Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap nike cipher macS
          kdfS streamS geom hvalid hmactag h16)).advantage names
          (Protocols.RSOR.swapPair.cast (replySwap nike cipher macS kdfS streamS geom hvalid
              hmactag h16) A)).toReal
        + ((Pr{let D ← (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) .relay names _ (backDraw0 nike geom) (Protocols.RSOR.backwardWith.cast
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) A))}[backBad0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16) D]).toReal
        + (Pr{let D ← (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) .relay names _ (swapDraw nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))
            (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16) A))}[backBad1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) D]).toReal
        + keyAdvantage cipher macS kdfS streamS geom (backAdv0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16)
            names (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom
            hvalid hmactag h16) A))
        + keyAdvantage cipher macS kdfS streamS geom (backAdv1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16)
            names (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom
            hvalid hmactag h16) A))
        + (Pr{let b ← (Primitives.MAC.forgeExp macS (macForge nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16)) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag
            h16) names) _ (backDraw0 nike geom) (Protocols.RSOR.backwardWith.cast (replySwap nike
            cipher macS kdfS streamS geom hvalid hmactag h16) A) (backM0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) (backViewT0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))))}[b = true]).toReal
        + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) .relay names _ (backDraw0 nike geom) (Protocols.RSOR.backwardWith.cast
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) A))}[¬ (backM0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16) x).size = (2 + nike.publicKeySize +
            geom.routingInfoLength)]).toReal
        + (Pr{let b ← (Primitives.MAC.forgeExp macS (macForge nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16)) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag
            h16) names) _ (swapDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))
            (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16) A) (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16)) (backViewT1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16))))}[b = true]).toReal
        + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) .relay names _ (swapDraw nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))
            (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16) A))}[¬ (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) x).size = (2 +
            nike.publicKeySize + geom.routingInfoLength)]).toReal
        + (Pr{let z ← (propPayDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) .relay names _ (backDraw0 nike geom) (Protocols.RSOR.backwardWith.cast
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) A))}[¬ backGoodP0
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16) z.2]).toReal
        + |(Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _ (propPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith (replySwap nike
            cipher macS kdfS streamS geom hvalid hmactag h16)) .relay names (backPlace nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom
            hvalid hmactag h16) names) _ (backDraw0 nike geom) (Protocols.RSOR.backwardWith.cast
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) A) (backM0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16)) (backPlain0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))
            (backViewE0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike
            cipher macS kdfS streamS geom hvalid hmactag h16))).adv true)}[b = true]).toReal -
            (Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _ (propPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith (replySwap nike
            cipher macS kdfS streamS geom hvalid hmactag h16)) .relay names (backPlace nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom
            hvalid hmactag h16) names) _ (backDraw0 nike geom) (Protocols.RSOR.backwardWith.cast
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) A) (backM0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16)) (backPlain0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))
            (backViewE0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike
            cipher macS kdfS streamS geom hvalid hmactag h16))).adv false)}[b = true]).toReal|
        + (Pr{let z ← (propPayDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) .relay names _ (swapDraw nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))
            (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16) A))}[¬ backGoodP1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) z.2]).toReal
        + |(Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _ (propPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith (replySwap nike
            cipher macS kdfS streamS geom hvalid hmactag h16)) .relay names (backPlace nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom
            hvalid hmactag h16) names) _ (swapDraw nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))
            (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16) A) (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16)) (backPlain1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16)) (backViewE1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))).adv
            true)}[b = true]).toReal - (Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) names) _
            (swapDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher
            macS kdfS streamS geom hvalid hmactag h16)) (Protocols.RSOR.backwardWith.cast
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) A) (backM1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16)) (backPlain1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))
            (backViewE1 nike cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike
            cipher macS kdfS streamS geom hvalid hmactag h16))).adv false)}[b = true]).toReal|
        + |(Pr{let b ← (PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
            (propStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) .relay names _ (swapDraw nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))
            (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16) A) (propStrRun nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) names)
            (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16) A) (backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16)) (backPlainS1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16)) (backViewS1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16)))))}[b =
            true]).toReal
          - (Pr{let b ← (PRGScheme.prgIdealExperiment (propStreamAdv nike cipher macS kdfS streamS
              geom hvalid hmactag h16 (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS
              streamS geom hvalid hmactag h16)) .relay names _ (swapDraw nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid
              hmactag h16)) (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS
              streamS geom hvalid hmactag h16) A) (propStrRun nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS
              streamS geom hvalid hmactag h16)) .relay names (backPlace nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid
              hmactag h16) names) (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS
              kdfS streamS geom hvalid hmactag h16) A) (backMS1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))
              (backPlainS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike
              cipher macS kdfS streamS geom hvalid hmactag h16)) (backViewS1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid
              hmactag h16)))))}[b = true]).toReal|
        + |(Pr{let b ← (PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
            (propStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) .relay names _ (backDraw0 nike geom) (Protocols.RSOR.backwardWith.cast
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) A) (propStrRun nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16)) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher
            macS kdfS streamS geom hvalid hmactag h16) names) (Protocols.RSOR.backwardWith.cast
            (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) A) (backMS0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16)) (backPlainS0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16))
            (backViewS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike
            cipher macS kdfS streamS geom hvalid hmactag h16)))))}[b = true]).toReal
          - (Pr{let b ← (PRGScheme.prgIdealExperiment (propStreamAdv nike cipher macS kdfS streamS
              geom hvalid hmactag h16 (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS
              streamS geom hvalid hmactag h16)) .relay names _ (backDraw0 nike geom)
              (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom
              hvalid hmactag h16) A) (propStrRun nike cipher macS kdfS streamS geom hvalid hmactag
              h16 (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
              hmactag h16)) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) names)
              (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom
              hvalid hmactag h16) A) (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16
              (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16)) (backPlainS0 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
              streamS geom hvalid hmactag h16)) (backViewS0 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag
              h16)))))}[b = true]).toReal|
        + |(Pr{let b ← (PRGScheme.prgIdealExperiment (propStreamAdv nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16)) .relay names _ (swapDraw nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid
            hmactag h16)) (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16) A) (propStrRun nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16)) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag
            h16) names) (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS
            geom hvalid hmactag h16) A) (backMS1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16)) (backPlainS1
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
            streamS geom hvalid hmactag h16)) (backViewS1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16)))))}[b =
            true]).toReal
          - (Pr{let b ← (PRGScheme.prgIdealExperiment (propStreamAdv nike cipher macS kdfS streamS
              geom hvalid hmactag h16 (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS
              streamS geom hvalid hmactag h16)) .relay names _ (backDraw0 nike geom)
              (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom
              hvalid hmactag h16) A) (propStrRun nike cipher macS kdfS streamS geom hvalid hmactag
              h16 (Protocols.RSOR.backwardWith (replySwap nike cipher macS kdfS streamS geom hvalid
              hmactag h16)) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) names)
              (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom
              hvalid hmactag h16) A) (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16
              (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16)) (backPlainS0 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (replySwap nike cipher macS kdfS
              streamS geom hvalid hmactag h16)) (backViewS0 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag
              h16)))))}[b = true]).toReal|) :=
  (Protocols.RSOR.backwardWith_advantage_le (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap nike
      cipher macS kdfS streamS geom hvalid hmactag h16) names A).trans
    (add_le_add le_rfl (backwardUnlinkable_le_stream nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16) names
        (Protocols.RSOR.backwardWith.cast (replySwap nike cipher macS kdfS streamS geom hvalid
        hmactag h16) A)))

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
