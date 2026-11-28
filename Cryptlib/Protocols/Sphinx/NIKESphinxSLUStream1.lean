/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLUStream

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

/-! # SLU← for NIKE Sphinx: the keystream step for world 1

As for world 0 (`backward0_pay_evalDistEq_prg`). -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

variable (W : Protocols.RSOR.BackSwap (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
  h16))

/-- World 1 on the backward path, from the reply block's header and the header of the relay's
own reply layer. -/
theorem backViewT1At_back_form (names : Role → Name) {pk : RSOR.Key nike}
    (ch : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names pk) (o : RSOR.Randomness nike geom × W.X) (a : ByteArray) (K : List
        HopKeys) (j : ℕ)
    (tag : ByteArray) (k : ℕ) (hp : ch.c.pos.val = k + 1)
    (hb : 0 < ch.c.req.back.hops.length) :
    backViewT1At nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o a K j tag
      = Protocols.RSOR.BackwardChallenge.world1With ch.c
        (backOnionOfHdr nike cipher macS kdfS streamS geom ch.c.req o.1 hb
          (backHdrOfTag nike cipher macS streamS geom ch.c.req o.1 a K j tag))
        (some (backLayerOfTag nike cipher macS streamS geom k ch.c.req o.1 a K j tag).1)
        none (W.of ch.c o.2).1 (W.of ch.c o.2).2 := by
  have hlt : ch.c.pos.val < ch.c.req.back.hops.length := ch.c.pos.isLt
  have hk : k < ch.c.req.back.hops.length := by omega
  unfold backViewT1At
  rw [hp]
  dsimp only
  rw [ite_eq_left hk, ite_eq_right (Nat.succ_ne_zero k)]
  rfl

theorem backM1_exit {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : Rest
    × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
    W) .relay names (RSOR.Randomness nike geom × W.X) A) (hp : x.2.c.pos.val = 0) :
    backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x = onionMsg nike macS streamS
        geom x.2.c.req x.2.o.1
      (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names x.2) (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) x default).toArray 0)
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          x default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2) := by
  unfold backM1 backMsg1At
  dsimp only
  rw [hp]

theorem backM1_back {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : Rest
    × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
    W) .relay names (RSOR.Randomness nike geom × W.X) A) (k : ℕ) (hp : x.2.c.pos.val = k + 1) :
    backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x = backMsg nike macS streamS
        geom x.2.c.req x.2.o.1
      (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names x.2) (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) x default).toArray 0)
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          x default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2) := by
  unfold backM1 backMsg1At
  dsimp only
  rw [hp]

theorem backPlain1_back {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) (k : ℕ) (hp : x.2.2.2.2.c.pos.val = k + 1) :
    backPlain1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x = default := by
  unfold backPlain1
  rw [hp]

/-- The bytes under the honest relay's tag in world 1, from its header keystream. -/
def backMS1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropStrX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × W.X) A) (U : KEMSphinx.Keystream geom) : ByteArray :=
  match x.2.2.c.pos.val with
  | 0 => onionMsgStream nike macS streamS geom x.2.2.c.req x.2.2.o.1 (groupElem nike (drawKey nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      x.2.2) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default) default)
      (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          x.2.2) (Util.Bytes.ofVector U)
  | _ + 1 => hdrMsg geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
      cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      x) default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)) (keysTag macS (drawKeys nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (blindElem nike
      (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
      default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2)

/-- The sender's block in world 1; it does not read the keystream. -/
def backPlainS1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropStrX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × W.X) A) (_U : KEMSphinx.Keystream geom) : Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength) :=
  match x.2.2.c.pos.val with
  | 0 => Util.Bytes.toVecN _ (onionBlock nike cipher macS kdfS streamS geom x.2.2.c.req
      x.2.2.o.1 (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2))
  | _ + 1 => default

/-- World 1 at the exit, from the honest relay's header keystream and the encrypted block. -/
def backStrExitW1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) (U : KEMSphinx.Keystream geom) (e :
    ByteArray) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1With x.2.2.c
    (onionOfStream nike cipher macS kdfS streamS geom 0 x.2.2.c.req x.2.2.o.1 (groupElem nike
        (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names x.2.2) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray 0)
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default) default)
          (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U) (Util.Bytes.ofVector
          (macS.mac (Util.Bytes.ofVector x.1) (backMS1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 W x U))) e)
    none
    (some (onionOfStream nike cipher macS kdfS streamS geom (x.2.2.c.req.fwd.hops.length - 1)
      x.2.2.c.req x.2.2.o.1 (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray 0) (drawKeys
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default) default)
          (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)
      (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1) (backMS1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 W x U))) e).1)
    (W.of x.2.2.c x.2.2.o.2).1 (W.of x.2.2.c x.2.2.o.2).2

/-- World 1 on the backward path, from the honest relay's header keystream. -/
def backStrW1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropStrX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × W.X) A) (U : KEMSphinx.Keystream geom) (k : ℕ) (hb : 0 <
    x.2.2.c.req.back.hops.length) :
    Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1With x.2.2.c
    (backOnionOfHdr nike cipher macS kdfS streamS geom x.2.2.c.req x.2.2.o.1 hb
      (backHdrBytes nike geom x.2.2.c.req x.2.2.o.1 (Function.update (keysKs geom streamS (drawKeys
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
          default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)) (Function.update
          (keysTag macS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) fun _ => Util.Bytes.ofVector (macS.mac
          (Util.Bytes.ofVector x.1) (backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          W x U))) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
          default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray)))
    (some (backHdrFn nike geom x.2.2.c.req x.2.2.o.1 (Function.update (keysKs geom streamS
        (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)) (Function.update (keysTag macS
        (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) fun _ => Util.Bytes.ofVector (macS.mac
        (Util.Bytes.ofVector x.1) (backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W
        x U))) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray 0) (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) k))
    none (W.of x.2.2.c x.2.2.o.2).1 (W.of x.2.2.c x.2.2.o.2).2

/-- **World 1 from the honest relay's header keystream.** -/
def backViewS1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropStrX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × W.X) A) (U : KEMSphinx.Keystream geom) (e : Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) : Protocols.RSOR.World 𝒮 :=
  match x.2.2.c.pos.val with
  | 0 => backStrExitW1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U
      (Util.Bytes.ofVector e)
  | k + 1 => backStrW1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U k
      (Nat.zero_lt_of_lt x.2.2.c.pos.isLt)

theorem backMS1_exit {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) (U : KEMSphinx.Keystream geom) (hp :
    x.2.2.c.pos.val = 0) :
    backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U = onionMsgStream nike macS
        streamS geom x.2.2.c.req x.2.2.o.1 (groupElem nike (drawKey nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray 0)
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default) default)
          (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U) := by
  unfold backMS1
  rw [hp]

theorem backMS1_back {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) (U : KEMSphinx.Keystream geom) (k : ℕ)
    (hp : x.2.2.c.pos.val = k + 1) :
    backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U
      = hdrMsg geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (drawPos nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)
          (Util.Bytes.ofVector U)) (keysTag macS (drawKeys nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names x) default) default).toArray) (blindElem nike (groupElem nike (drawKey nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names x.2.2) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back
          [.surbReply x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply
          x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) := by
  unfold backMS1
  rw [hp]

theorem backPlainS1_exit {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) (U : KEMSphinx.Keystream geom) (hp :
    x.2.2.c.pos.val = 0) :
    backPlainS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U = Util.Bytes.toVecN _
        (onionBlock nike cipher macS kdfS streamS geom
      x.2.2.c.req x.2.2.o.1 (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2)) := by
  unfold backPlainS1
  rw [hp]

theorem backPlainS1_back {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) (U : KEMSphinx.Keystream geom) (k : ℕ)
    (hp : x.2.2.c.pos.val = k + 1) :
    backPlainS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U = default := by
  unfold backPlainS1
  rw [hp]

theorem backViewS1_exit {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) (U : KEMSphinx.Keystream geom) (e : Vector
    UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hp : x.2.2.c.pos.val = 0) :
    backViewS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U e = backStrExitW1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 W x U (Util.Bytes.ofVector e) := by
  unfold backViewS1
  rw [hp]

theorem backViewS1_back {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) (U : KEMSphinx.Keystream geom) (e : Vector
    UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) (k : ℕ)
    (hp : x.2.2.c.pos.val = k + 1) (hb : 0 < x.2.2.c.req.back.hops.length) :
    backViewS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U e = backStrW1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 W x U k hb := by
  unfold backViewS1
  rw [hp]

set_option maxHeartbeats 4000000 in
/-- **World 1's payload game with the ideal cipher reads the honest relay's header key and IV
through its keystream only.** -/
theorem backPay1_ideal_eq (names : Role → Name) (A : (Protocols.RSOR.backwardWith W).Adversary) (iv
    : Vector UInt8 16)
    (km he seed : Vector UInt8 32) (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) (u v
        : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) :
    propPayIdealRun nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) _ (swapDraw nike cipher macS kdfS streamS geom hvalid hmactag
        h16 W) A (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backPlain1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 W)
        (backViewE1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) ((iv, km, he, seed, D)
            : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) u v
      = (propStrRun nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) A (backMS1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 W) (backPlainS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
          (backViewS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)) ((km, seed, D) :
          PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) u v := by
  have hposD := backPos_lt nike cipher macS kdfS streamS geom hvalid hmactag h16 W D
  have hall : (∀ i, i ≠ (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) D) → (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
      geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names (RSOR.Randomness nike geom × W.X) A) default) default).toArray[i]! = (drawKeys nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness
      nike geom × W.X) A)) default) default).toArray[i]!)
      ∧ (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default).toArray[(drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) D)]! = { (drawKeys nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
          default) default).toArray[(drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) D)]! with
        headerEncryption := ((drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
            PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            default) default).toArray[(drawPos nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W names) D)]!).headerEncryption
        headerEncryptionIV := ((drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
            PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            default) default).toArray[(drawPos nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W names) D)]!).headerEncryptionIV }
      ∧ keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default).toArray
        = Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × W.X) A)) default) default).toArray) (drawPos nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
          (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
              D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
              default) default).toArray (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
              h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W names) D))
      ∧ keysTag macS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default).toArray = keysTag macS (drawKeys nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
          default) default).toArray
      ∧ ∀ a, blindElem nike a (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default).toArray = blindElem nike a (drawKeys nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
          default) default).toArray := by
    unfold drawKeys
    exact hopKeysWith_streamKey nike macS kdfS streamS geom _ _ _ (restKeys (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
        default).1 default)
      (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) :
          PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
          default).1 default) rfl _ hposD
  obtain ⟨hne, hK, hks, htg, hge⟩ := hall
  have hU : Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))
      = streamS.keystream (Util.Bytes.ofVector he) (Util.Bytes.ofVector iv)
        (geom.routingInfoLength + geom.perHopRoutingInfoLength) :=
    Util.Bytes.ofVector_toVecN _ (streamS.keystream_size _ _ _)
  have hKj : (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (RSOR.Randomness nike geom × W.X) A) default) default).toArray[(drawPos nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
      cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)]! = restKeys (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) default).1
      default := by
    unfold drawKeys
    exact toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS _ _ _ _ _ hposD)
  have hKS : keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (RSOR.Randomness nike geom × W.X) A) default) default).toArray (drawPos nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
      cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) = Util.Bytes.ofVector
      ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) := by
    unfold keysKs
    rw [hKj]
    exact hU.symm
  obtain hk | ⟨k, hk⟩ : D.c.pos.val = 0 ∨ ∃ k, D.c.pos.val = k + 1 := by
    cases h : D.c.pos.val with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, rfl⟩
  · have hjp : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) D) < (RSOR.path nike D.c.req.fwd [.recipient
      D.c.req.receiver]).size :=
      lt_of_eq_of_lt (backPos_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W D hk)
          (lt_of_lt_of_eq
        (Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2 D.c.req.fwd_ne)))
        (RSOR.path_size nike _ _).symm)
    have hjl : D.c.req.fwd.hops.length - 1 ≤ (drawPos nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) D) := (backPos_exit nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W D hk).ge
    have hpl : peels nike cipher streamS geom (drawKeys nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
        PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × W.X) A) default) default)
        (D.c.req.fwd.hops.length - 1)
        = peels nike cipher streamS geom (drawKeys nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × W.X) A)) default) default) (D.c.req.fwd.hops.length - 1)
            := by
      unfold drawKeys
      exact peels_hopKeysWith nike cipher kdfS streamS geom _ _ _ (restKeys (propPayRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default).1 default)
        (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) :
            PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
            default).1 default) rfl _ _ hjl
    have hsk := fun (a tag e : ByteArray) => onion_streamKey nike cipher macS kdfS streamS geom 0
      D.c.req D.o.1 a (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
          seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
          default) default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) D) tag e hjp hne hK rfl
    have hskL := fun (a tag e : ByteArray) => onion_streamKey nike cipher macS kdfS streamS geom
      (D.c.req.fwd.hops.length - 1) D.c.req D.o.1 a (drawKeys nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km,
          he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
          seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
          default) default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) D) tag e hjp hne hK hpl
    have hM : backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
        default) = backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) :
        PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × W.X) A) ((KEMSphinx.keystreamPRG streamS
        geom).gen (he, iv)) :=
      (backM1_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) hk).trans (((hsk (groupElem nike (drawKey nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom ×
          W.X) A) default) default).toArray 0) .empty .empty).2.1).trans
        (by rw [hKS]; exact (backMS1_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W
            ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) hk).symm))
    have hplain : backPlain1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) =
        backPlainS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) :
        PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × W.X) A) ((KEMSphinx.keystreamPRG streamS
        geom).gen (he, iv)) :=
      (backPlain1_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he, seed,
          D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          hk).trans ((congrArg (Util.Bytes.toVecN _)
        (hsk .empty .empty .empty).2.2).trans (backPlainS1_exit nike cipher macS kdfS streamS geom
            hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike
            geom × W.X) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) hk).symm)
    have hon : (onionOfEnc nike cipher macS kdfS streamS geom 0 D.c.req D.o.1 (groupElem nike
        (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names D) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (RSOR.Randomness nike geom × W.X) A) default) default).toArray 0) (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × W.X) A) default) default) (drawPos nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
        nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector
        (macS.mac (Util.Bytes.ofVector km) (backM1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × W.X) A) default)))) (Util.Bytes.ofVector u))
        = (onionOfStream nike cipher macS kdfS streamS geom 0 D.c.req D.o.1 (groupElem nike
            (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv,
            km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × W.X) A)) default) default) (drawPos nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
            nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))) (Util.Bytes.ofVector (macS.mac
            (Util.Bytes.ofVector km) (backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            W ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))))) (Util.Bytes.ofVector u)) :=
      ((hsk (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv,
          km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default).toArray 0) _ _).1).trans (by rw [hKS, hM])
    have honL : (onionOfEnc nike cipher macS kdfS streamS geom (D.c.req.fwd.hops.length - 1)
        D.c.req D.o.1 (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) default)
        default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (RSOR.Randomness nike geom × W.X) A) default) default) (drawPos nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
        nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector
        (macS.mac (Util.Bytes.ofVector km) (backM1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × W.X) A) default)))) (Util.Bytes.ofVector u))
        = (onionOfStream nike cipher macS kdfS streamS geom (D.c.req.fwd.hops.length - 1) D.c.req
            D.o.1 (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv,
            km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × W.X) A)) default) default) (drawPos nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
            nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))) (Util.Bytes.ofVector (macS.mac
            (Util.Bytes.ofVector km) (backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            W ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))))) (Util.Bytes.ofVector u)) :=
      ((hskL (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv,
          km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default).toArray 0) _ _).1).trans (by rw [hKS, hM])
    have hview : backViewE1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) u =
        backViewS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) :
        PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × W.X) A) ((KEMSphinx.keystreamPRG streamS
        geom).gen (he, iv)) u :=
      (backViewE1_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he, seed,
          D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) u
          hk).trans ((congrArg₂ (fun (on ex : Onion geom) =>
        Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) D.c on none (some ex.1) (W.of D.c
            D.o.2).1 (W.of D.c D.o.2).2) hon honL).trans
        (backViewS1_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) :
            PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) u hk).symm)
    exact propPayIdealRun_eq_strRun nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) _ (swapDraw nike cipher macS kdfS streamS geom hvalid hmactag
        h16 W) A (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
      (backPlain1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W) (backMS1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 W) (backPlainS1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          W)
      (backViewS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) iv km he seed D u v hM
          hplain hview
  · have hlt : D.c.pos.val < D.c.req.back.hops.length := D.c.pos.isLt
    have hb : 0 < D.c.req.back.hops.length := Nat.zero_lt_of_lt hlt
    have hkl : k < D.c.req.back.hops.length := by omega
    have hA : (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) default)
        default).toArray 0) = (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
        nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × W.X) A)) default) default).toArray 0) := rfl
    have hM : backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
        default) = backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) :
        PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × W.X) A) ((KEMSphinx.keystreamPRG streamS
        geom).gen (he, iv)) :=
      (backM1_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) k hk).trans ((show backMsg nike macS streamS geom D.c.req D.o.1
          (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (RSOR.Randomness nike geom × W.X) A) default) default).toArray 0)
              (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
              D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
              default) default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) D)
        = hdrMsg geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × W.X) A)) default) default).toArray) (drawPos nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
            (Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))) (keysTag
            macS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
            seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
            default) default).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D)
            (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
            seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
            default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × W.X) A)) default) default).toArray) (RSOR.filler nike geom
            (RSOR.path nike D.c.req.back [.surbReply D.o.1.2.2.2]) D.o.1.2.1) (RSOR.path nike
            D.c.req.back [.surbReply D.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
            macS kdfS streamS geom hvalid hmactag h16 W names) D) from by
          unfold backMsg
          rw [hks, hKS, htg, hge (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher
              macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
              names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (RSOR.Randomness nike geom × W.X) A) default) default).toArray 0),
              hA]).trans (backMS1_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W
              ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
              ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) k hk).symm)
    have hplain : backPlain1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) =
        backPlainS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) :
        PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × W.X) A) ((KEMSphinx.keystreamPRG streamS
        geom).gen (he, iv)) :=
      (backPlain1_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he, seed,
          D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) k
          hk).trans (backPlainS1_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km,
          seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) k hk).symm
    have ha : (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) default)
        default).toArray 0).size = nike.publicKeySize := Util.Bytes.size_ofVector _
    have ht : (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names (RSOR.Randomness nike geom × W.X) A) default)))).size = macLength :=
      (Util.Bytes.size_ofVector _).trans hmactag
    have hlK : D.c.req.back.hops.length ≤ (drawKeys nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
        PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × W.X) A) default) default).length := by
      unfold drawKeys
      rw [hopKeysWith_length]
      exact (backHops_size_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W D k hk).ge
    have h1 : backHdrOfTag nike cipher macS streamS geom D.c.req D.o.1 (groupElem nike (drawKey
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names D) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (RSOR.Randomness nike geom × W.X) A) default) default).toArray 0) (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × W.X) A) default) default) (drawPos nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
        nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
          (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
              D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
              default))))
        = backHdrBytes nike geom D.c.req D.o.1 (Function.update (keysKs geom streamS (drawKeys nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) :
            PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
            default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))) (Function.update (keysTag macS
            (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
            seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
            default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W names) D) fun _ => Util.Bytes.ofVector (macS.mac
            (Util.Bytes.ofVector km) (backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            W ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))))) (blindElem nike (groupElem nike
            (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × W.X) A)) default) default).toArray 0) (drawKeys nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) :
            PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
            default) default).toArray) :=
      (backHdrOfTag_eq nike cipher macS streamS geom hvalid hmactag D.c.req D.o.1 (groupElem nike
          (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv,
          km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default)
        (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
            W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W
            names) D) (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he,
            seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            default)))) hb ha ht).trans
        (by rw [hks, hKS, htg, hge (groupElem nike (drawKey nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (RSOR.Randomness nike geom × W.X) A) default) default).toArray 0), hM, hA])
    have h2 : (backLayerOfTag nike cipher macS streamS geom k D.c.req D.o.1 (groupElem nike
        (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names D) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (RSOR.Randomness nike geom × W.X) A) default) default).toArray 0) (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × W.X) A) default) default) (drawPos nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
        nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
          (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
              D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
              default))))).1
        = backHdrFn nike geom D.c.req D.o.1 (Function.update (keysKs geom streamS (drawKeys nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) :
            PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
            default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))) (Function.update (keysTag macS
            (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
            seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
            default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W names) D) fun _ => Util.Bytes.ofVector (macS.mac
            (Util.Bytes.ofVector km) (backMS1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            W ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))))) (blindElem nike (groupElem nike
            (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × W.X) A)) default) default).toArray 0) (drawKeys nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) :
            PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
            default) default).toArray) k :=
      (backLayerOfTag_fst nike cipher macS streamS geom hvalid hmactag h16 k D.c.req D.o.1
        (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv,
            km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km,
            he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            default) default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector
            km) (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom ×
            W.X) A) default)))) hkl ((le_of_lt hkl).trans hlK) ha
        ht).trans (by rw [hks, hKS, htg, hge (groupElem nike (drawKey nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (RSOR.Randomness nike geom × W.X) A) default) default).toArray 0), hM, hA])
    have mid1 : backViewT1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X)
        A) default) (macS.mac (Util.Bytes.ofVector km) (backM1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × W.X) A) default)))
        = Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) D.c
          (backOnionOfHdr nike cipher macS kdfS streamS geom D.c.req D.o.1 hb
            (backHdrOfTag nike cipher macS streamS geom D.c.req D.o.1 (groupElem nike (drawKey nike
                cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
                .relay names D) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS
                geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he,
                seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
                default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid
                hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
                macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
                kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
                ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
                h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X)
                A) default) default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) D)
              (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM1 nike cipher macS kdfS
                  streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
                  hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he,
                  seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
                  (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
                  default))))))
          (some (backLayerOfTag nike cipher macS streamS geom k D.c.req D.o.1 (groupElem nike
              (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (RSOR.Randomness nike geom × W.X) A) default) default).toArray 0)
              (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
              D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
              default) default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) D)
            (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM1 nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
                hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
                D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
                default))))).1)
          none (W.of D.c D.o.2).1 (W.of D.c D.o.2).2 :=
      backViewT1At_back_form nike cipher macS kdfS streamS geom hvalid hmactag h16 W names
          (⟨D.keys, D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names D.k.1) D.o (groupElem nike (drawKey nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names D) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
          default) default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) D)
        (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D)
            : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            default)))) k hk hb
    have mid3 : backStrW1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) :
        PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × W.X) A) ((KEMSphinx.keystreamPRG streamS
        geom).gen (he, iv)) k hb
        = Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) D.c
          (backOnionOfHdr nike cipher macS kdfS streamS geom D.c.req D.o.1 hb
            (backHdrBytes nike geom D.c.req D.o.1 (Function.update (keysKs geom streamS (drawKeys
                nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
                W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W
                names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
                streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
                seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
                default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid
                hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
                macS kdfS streamS geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector
                ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))) (Function.update (keysTag
                macS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS
                geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay
                nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
                W) .relay names ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid
                hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom
                × W.X) A)) default) default).toArray) (drawPos nike cipher macS kdfS streamS geom
                hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
                cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) fun _ =>
                Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backMS1 nike cipher macS
                kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS
                kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
                (RSOR.Randomness nike geom × W.X) A) ((KEMSphinx.keystreamPRG streamS geom).gen
                (he, iv))))) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS
                geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys
                nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
                W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W
                names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
                streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
                seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
                default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid
                hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
                macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
                kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
                (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher
                macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
                names (RSOR.Randomness nike geom × W.X) A)) default) default).toArray)))
          (some (backHdrFn nike geom D.c.req D.o.1 (Function.update (keysKs geom streamS (drawKeys
              nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W
              names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
              seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
              default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
              h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector
              ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))) (Function.update (keysTag macS
              (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom ×
              W.X) A)) default) default).toArray) (drawPos nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
              cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) fun _ =>
              Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backMS1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (RSOR.Randomness nike geom × W.X) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he,
              iv))))) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W
              names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
              seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A))
              default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
              kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher
              macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
              names (RSOR.Randomness nike geom × W.X) A)) default) default).toArray) k))
          none (W.of D.c D.o.2).1 (W.of D.c D.o.2).2 := rfl
    have hview : backViewE1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) u =
        backViewS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) :
        PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × W.X) A) ((KEMSphinx.keystreamPRG streamS
        geom).gen (he, iv)) u :=
      (backViewE1_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he, seed,
          D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) u k
          hk).trans ((mid1.trans
        ((congrArg₂ (fun hd ls => Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) D.c
          (backOnionOfHdr nike cipher macS kdfS streamS geom D.c.req D.o.1 hb hd) (some ls)
          none (W.of D.c D.o.2).1 (W.of D.c D.o.2).2) h1 h2).trans mid3.symm)).trans
        (backViewS1_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) :
            PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A)
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) u k hk hb).symm)
    exact propPayIdealRun_eq_strRun nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) _ (swapDraw nike cipher macS kdfS streamS geom hvalid hmactag
        h16 W) A (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
      (backPlain1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W) (backMS1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 W) (backPlainS1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          W)
      (backViewS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) iv km he seed D u v hM
          hplain hview

/-- **The keystream step for world 1 of SLU←.** -/
theorem backward1_pay_evalDistEq_prg (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) :
    (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) _
        (swapDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 W) A (backM1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W) (backPlain1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W) (backViewE1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        W)).exp cipher false
      =ᵈ PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
        (propStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W) A (propStrRun nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W names) A (backMS1 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W) (backPlainS1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 W) (backViewS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W))) :=
  propPay_exp_false_evalDistEq_prg nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) _ (swapDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
      W) A (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
    (backPlain1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W) (propStrRun nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
        kdfS streamS geom hvalid hmactag h16 W names) A (backMS1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W) (backPlainS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
        (backViewS1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W))
    (fun iv km he seed D u v => backPay1_ideal_eq nike cipher macS kdfS streamS geom hvalid hmactag
        h16 W names A iv km he seed D u v)

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
