/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLU

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

/-! # SLU← for NIKE Sphinx: the payload cipher step for world 1

As for world 0 (`backward0_macOnly_sub_pay_le`). At the exit the relay's payload key encrypts
the onion's block at the relay, which the adversary's first layer and the relay's own forward
layer both carry. On the backward path the world does not read that key. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

variable (W : Protocols.RSOR.BackSwap (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
  h16))

/-- Peeling up to the honest relay's place does not read its payload key. -/
theorem backPay_peels {names : Role → Name} {Oth : Type} {A : (Protocols.RSOR.backwardWith
    W).Adversary} (x : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
    (Protocols.RSOR.backwardWith W) .relay names Oth A) (kp : Vector UInt8 48) (i : ℕ)
    (hi : i ≤ (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2.2.2)) :
    peels nike cipher streamS geom (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names x kp) default) i = peels nike cipher
        streamS geom (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names x default) default) i := by
  unfold drawKeys
  exact peels_hopKeysWith nike cipher kdfS streamS geom _ _ _ (restKeys (propPayRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x
      kp).1 default)
    (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x default).1 default) rfl _ _ hi

/-- The bytes under the relay's tag do not read its payload key. -/
theorem backMsg1At_congr (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) (o :
    RSOR.Randomness nike geom × W.X)
    (a : ByteArray) (K K' : List HopKeys) (j : ℕ) (hK : ∀ m : ℕ, (K[m]?).map (fun k : HopKeys =>
        (k.headerMAC, k.headerEncryption, k.headerEncryptionIV, k.blindingFactor)) = (K'[m]?).map
        (fun k : HopKeys => (k.headerMAC, k.headerEncryption, k.headerEncryptionIV,
        k.blindingFactor)))
    (hne : ∀ i, i ≠ j → K.toArray[i]! = K'.toArray[i]!)
    (hjK : K.toArray[j]! = { K'.toArray[j]! with
      payloadEncryption := (K.toArray[j]!).payloadEncryption })
    (hjF : ch.c.pos.val = 0 → j < (RSOR.path nike ch.c.req.fwd [.recipient
        ch.c.req.receiver]).size) :
    backMsg1At nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o a K j =
        backMsg1At nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o a K' j := by
  unfold backMsg1At
  obtain hk | ⟨k, hk⟩ : ch.c.pos.val = 0 ∨ ∃ k, ch.c.pos.val = k + 1 := by
    cases h : ch.c.pos.val with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, rfl⟩
  · rw [hk]
    exact (onion_payloadKey nike cipher macS kdfS streamS geom 0 ch.c.req o.1 a K K' j .empty
      .empty (hjF hk) hne hjK rfl).2.1
  · rw [hk]
    exact backMsg_congr nike macS streamS geom ch.c.req o.1 a K K' j hK

/-- **At the exit, world 1 uses the relay's payload key for one encryption only**: of the
block `onionBlock`, which the first layer and the relay's own layer carry. -/
theorem backViewT1At_exit (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) (o :
    RSOR.Randomness nike geom × W.X)
    (a : ByteArray) (K K' : List HopKeys) (j : ℕ) (tag : ByteArray) (hp : ch.c.pos.val = 0)
    (hne : ∀ i, i ≠ j → K.toArray[i]! = K'.toArray[i]!)
    (hjK : K.toArray[j]! = { K'.toArray[j]! with
      payloadEncryption := (K.toArray[j]!).payloadEncryption })
    (hjp : j < (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
    (hpl : peels nike cipher streamS geom K (ch.c.req.fwd.hops.length - 1)
      = peels nike cipher streamS geom K' (ch.c.req.fwd.hops.length - 1)) :
    backViewT1At nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o a K j tag
      = Protocols.RSOR.BackwardChallenge.world1With ch.c
        (onionOfEnc nike cipher macS kdfS streamS geom 0 ch.c.req o.1 a K' j tag (cipher.encrypt
            (K.toArray[j]!).payloadEncryption.toArray (Util.Bytes.ofVector
            (K.toArray[j]!).headerEncryptionIV) (onionBlock nike cipher macS kdfS streamS geom
            ch.c.req o.1 K' j)))
        none
        (some (onionOfEnc nike cipher macS kdfS streamS geom (ch.c.req.fwd.hops.length - 1)
            ch.c.req o.1 a K' j tag (cipher.encrypt (K.toArray[j]!).payloadEncryption.toArray
            (Util.Bytes.ofVector (K.toArray[j]!).headerEncryptionIV) (onionBlock nike cipher macS
            kdfS streamS geom ch.c.req o.1 K' j))).1)
        (W.of ch.c o.2).1 (W.of ch.c o.2).2 := by
  have hpk0 := fun (tg e : ByteArray) => onion_payloadKey nike cipher macS kdfS streamS geom 0
    ch.c.req o.1 a K K' j tg e hjp hne hjK rfl
  have hpkL := fun (tg e : ByteArray) => onion_payloadKey nike cipher macS kdfS streamS geom
    (ch.c.req.fwd.hops.length - 1) ch.c.req o.1 a K K' j tg e hjp hne hjK hpl
  unfold backViewT1At
  rw [hp]
  dsimp only
  rw [ite_eq_left rfl, onionOfTag_enc nike cipher macS kdfS streamS geom 0 ch.c.req o.1 a K j tag
      hjp,
    onionOfTag_enc nike cipher macS kdfS streamS geom (ch.c.req.fwd.hops.length - 1) ch.c.req o.1
      a K j tag hjp,
    (hpk0 .empty .empty).2.2, (hpk0 tag _).1, (hpkL tag _).1]

include hvalid hmactag h16 in
/-- **On the backward path, world 1 does not read the relay's payload key.** -/
theorem backViewT1At_back (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) (o :
    RSOR.Randomness nike geom × W.X)
    (a : ByteArray) (K K' : List HopKeys) (j : ℕ) (tag : ByteArray) (k : ℕ)
    (hp : ch.c.pos.val = k + 1) (hK : ∀ m : ℕ, (K[m]?).map (fun k : HopKeys => (k.headerMAC,
        k.headerEncryption, k.headerEncryptionIV, k.blindingFactor)) = (K'[m]?).map (fun k :
        HopKeys => (k.headerMAC, k.headerEncryption, k.headerEncryptionIV, k.blindingFactor)))
    (hl : ch.c.req.back.hops.length ≤ K.length) (hl' : ch.c.req.back.hops.length ≤ K'.length)
    (ha : a.size = nike.publicKeySize) (ht : tag.size = macLength) :
    backViewT1At nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o a K j tag =
        backViewT1At nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o a K' j tag
        := by
  have hlt : ch.c.pos.val < ch.c.req.back.hops.length := ch.c.pos.isLt
  have hb : 0 < ch.c.req.back.hops.length := Nat.zero_lt_of_lt hlt
  have hkl : k ≤ ch.c.req.back.hops.length := by omega
  unfold backViewT1At
  rw [hp]
  dsimp only
  rw [ite_eq_right (Nat.succ_ne_zero k), ite_eq_right (Nat.succ_ne_zero k),
    backOnionOfTag_congr nike cipher macS kdfS streamS geom hvalid hmactag ch.c.req o.1 hb a K
      K' j tag hK ha ht,
    backLayerOfTag_fst_congr nike cipher macS streamS geom hvalid hmactag h16 k ch.c.req o.1 a K
      K' j tag hK (hkl.trans hl) (hkl.trans hl') hb ha ht]

/-- World 1 at the exit, from the encrypted block as bytes. -/
def backExitW1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropPayX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × W.X) A) (e : ByteArray) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1With x.2.2.2.2.c
    (onionOfEnc nike cipher macS kdfS streamS geom 0 x.2.2.2.2.c.req x.2.2.2.2.o.1 (groupElem nike
        (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names x.2.2.2.2) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names x default) default).toArray 0) (drawKeys
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x default) default) (drawPos nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2.2.2)
      (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.1) (backM1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x default)))) e)
    none
    (some (onionOfEnc nike cipher macS kdfS streamS geom (x.2.2.2.2.c.req.fwd.hops.length - 1)
      x.2.2.2.2.c.req x.2.2.2.2.o.1 (groupElem nike (drawKey nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2.2.2) (drawKeys nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names x default) default).toArray 0) (drawKeys
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names x default) default) (drawPos nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2.2.2)
          (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.1) (backM1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x default)))) e).1)
    (W.of x.2.2.2.2.c x.2.2.2.2.o.2).1 (W.of x.2.2.2.2.c x.2.2.2.2.o.2).2

/-- The block the sender encrypts under the honest relay's payload key in world 1: at the
exit the onion's block at the relay; on the backward path none. -/
def backPlain1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropPayX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × W.X) A) : Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength) :=
  match x.2.2.2.2.c.pos.val with
  | 0 => Util.Bytes.toVecN _ (onionBlock nike cipher macS kdfS streamS geom x.2.2.2.2.c.req
      x.2.2.2.2.o.1 (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names x default) default) (drawPos nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2.2.2))
  | _ + 1 => default

/-- World 1 from the encrypted block. On the backward path the world does not use it. -/
def backViewE1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropPayX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × W.X) A) (e : Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) : Protocols.RSOR.World 𝒮 :=
  match x.2.2.2.2.c.pos.val with
  | 0 => backExitW1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x (Util.Bytes.ofVector
      e)
  | _ + 1 => backViewT1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      x default) (macS.mac (Util.Bytes.ofVector x.2.1) (backM1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x default)))

theorem backPlain1_exit {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) (hp : x.2.2.2.2.c.pos.val = 0) :
    backPlain1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x = Util.Bytes.toVecN _
        (onionBlock nike cipher macS kdfS streamS geom x.2.2.2.2.c.req x.2.2.2.2.o.1 (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x default) default) (drawPos nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2.2.2)) := by
  unfold backPlain1
  rw [hp]

theorem backViewE1_exit {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) (e : Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) (hp : x.2.2.2.2.c.pos.val = 0) :
    backViewE1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x e = backExitW1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W x (Util.Bytes.ofVector e) := by
  unfold backViewE1
  rw [hp]

theorem backViewE1_back {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) (e : Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) (k : ℕ)
    (hp : x.2.2.2.2.c.pos.val = k + 1) :
    backViewE1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x e = backViewT1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x default) (macS.mac
        (Util.Bytes.ofVector x.2.1) (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x default))) := by
  unfold backViewE1
  rw [hp]

/-- The draws of world 1 on which its payload game is exact, as `backGoodP0`. -/
def backGoodP1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropPayX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × W.X) A) : Prop :=
  (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x
      default)).size = (2 + nike.publicKeySize + geom.routingInfoLength) ∧
    (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x
        default)).extract 2 (2 + nike.publicKeySize)
      = drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          x.2.2.2.2 ∧
    (x.2.2.2.2.c.pos.val = 0 → (onionBlock nike cipher macS kdfS streamS geom x.2.2.2.2.c.req
        x.2.2.2.2.o.1 (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names x default) default) (drawPos nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2.2.2)).size
        = (geom.payloadTagLength + geom.forwardPayloadLength))

set_option maxHeartbeats 4000000 in
/-- **The payload cipher step for world 1 of SLU←.** -/
theorem backward1_macOnly_sub_pay_le (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) :
    |(Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) _ (swapDraw nike cipher macS kdfS streamS geom hvalid hmactag
        h16 W) (backView1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A
        (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W))}[b = true]).toReal
      - (Pr{let b ← ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) _ (swapDraw nike cipher macS kdfS streamS geom hvalid
          hmactag h16 W) A (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
          (backPlain1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W)).exp cipher false)}[b = true]).toReal|
    ≤ (Pr{let z ← (propPayDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W) A)}[¬ backGoodP1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 W
        z.2]).toReal
      + |(Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _ (propPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) _ (swapDraw
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W) A (backM1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 W) (backPlain1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 W) (backViewE1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)).adv
            true)}[b = true]).toReal
          - (Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _ (propPay nike cipher macS
              kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) _ (swapDraw
              nike cipher macS kdfS streamS geom hvalid hmactag h16 W) A (backM1 nike cipher macS
              kdfS streamS geom hvalid hmactag h16 W) (backPlain1 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W) (backViewE1 nike cipher macS kdfS streamS geom hvalid
              hmactag h16 W)).adv
            false)}[b = true]).toReal| := by
  have hjF : ∀ x : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A,
      x.2.2.2.2.c.pos.val = 0 → (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2.2.2)
      < (RSOR.path nike x.2.2.2.2.c.req.fwd [.recipient x.2.2.2.2.c.req.receiver]).size := fun x hp
          =>
    lt_of_eq_of_lt (backPos_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W x.2.2.2.2
        hp) (lt_of_lt_of_eq
      (Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2 x.2.2.2.2.c.req.fwd_ne)))
      (RSOR.path_size nike _ _).symm)
  have hMkp : ∀ (x : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × W.X) A) (kp :
      Vector UInt8 48),
      backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x kp) =
          backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x
          default) := fun x kp => by
    obtain ⟨hG, hne, hjK⟩ := backPay_keys nike cipher macS kdfS streamS geom hvalid hmactag h16 W x
        kp
    unfold backM1
    exact backMsg1At_congr nike cipher macS kdfS streamS geom hvalid hmactag h16 W names _ _ _ _ _
        _ hG hne hjK (hjF x)
  refine macOnly_sub_propPay_le nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) _ _ (backView1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 W names) A (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
    (backPlain1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W) (backGoodP1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W) (fun D => backPos_lt nike cipher macS kdfS streamS geom hvalid
        hmactag h16 W D)
    (fun x hg => hg.1) (fun x hg => hg.2.1) (fun x kp _ => hMkp x kp) (fun x kp hg => ?_)
  obtain ⟨-, -, hblk⟩ := hg
  obtain ⟨hG, hne, hjK⟩ := backPay_keys nike cipher macS kdfS streamS geom hvalid hmactag h16 W x kp
  rw [backView1_draw_tag nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      x kp) x.2.1, hMkp x kp]
  obtain hk | ⟨k, hk⟩ : x.2.2.2.2.c.pos.val = 0 ∨ ∃ k, x.2.2.2.2.c.pos.val = k + 1 := by
    cases h : x.2.2.2.2.c.pos.val with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, rfl⟩
  · have hKj : (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names x kp) default).toArray[(drawPos nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2.2.2)]! =
      restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x kp).1 default := by
      unfold drawKeys
      exact toArray_getElem!_of_getElem? _ _ _
        (hopKeysWith_getElem nike kdfS _ _ _ _ _ (backPos_lt nike cipher macS kdfS streamS geom
            hvalid hmactag h16 W x.2.2.2.2))
    have heEq : cipher.encrypt ((drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names x kp) default).toArray[(drawPos nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        x.2.2.2.2)]!).payloadEncryption.toArray
          (Util.Bytes.ofVector ((drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x kp)
              default).toArray[(drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) x.2.2.2.2)]!).headerEncryptionIV) (onionBlock nike
              cipher macS kdfS streamS geom x.2.2.2.2.c.req x.2.2.2.2.o.1 (drawKeys nike cipher
              macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
              names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names x default) default) (drawPos nike cipher
              macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
              names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              x.2.2.2.2))
        = Util.Bytes.ofVector (Util.Bytes.toVecN (geom.payloadTagLength +
            geom.forwardPayloadLength) (cipher.encrypt kp.toArray (Util.Bytes.ofVector x.1)
            (Util.Bytes.ofVector (backPlain1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            W x)))) := by
      rw [hKj]
      show cipher.encrypt kp.toArray (Util.Bytes.ofVector x.1) (onionBlock nike cipher macS kdfS
          streamS geom x.2.2.2.2.c.req x.2.2.2.2.o.1 (drawKeys nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x default)
          default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2.2.2)) = _
      rw [backPlain1_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W x hk,
          Util.Bytes.ofVector_toVecN _ (hblk hk),
        Util.Bytes.ofVector_toVecN _ (by rw [cipher.encrypt_size]; exact hblk hk)]
    have hjl : x.2.2.2.2.c.req.fwd.hops.length - 1 ≤ (drawPos nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
        kdfS streamS geom hvalid hmactag h16 W names) x.2.2.2.2) := (backPos_exit nike cipher macS
        kdfS streamS geom hvalid hmactag h16 W x.2.2.2.2 hk).ge
    rw [backViewE1_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W x _ hk]
    unfold backViewT1
    exact (backViewT1At_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W names _ _ _ _
        (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names x default) default) _ _ hk hne hjK (hjF x
        hk)
      (backPay_peels nike cipher macS kdfS streamS geom hvalid hmactag h16 W x kp _ hjl)).trans
          (congrArg (backExitW1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x) heEq)
  · have hl : ∀ kp' : Vector UInt8 48,
        x.2.2.2.2.c.req.back.hops.length ≤ (drawKeys nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x kp')
            default).length := fun kp' => by
      unfold drawKeys
      rw [hopKeysWith_length]
      exact (backHops_size_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W x.2.2.2.2 k
          hk).ge
    rw [backViewE1_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W x _ k hk]
    unfold backViewT1
    exact backViewT1At_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W names _ _ _ _ _
        _ _ k hk hG (hl kp) (hl default)
      (Util.Bytes.size_ofVector _) ((Util.Bytes.size_ofVector _).trans hmactag)

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
