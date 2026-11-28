/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxProp

namespace Cryptlib.Protocols.Sphinx.NIKESphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.KEMSphinx (evalDistEq_pair_of_bijective
  prEvent_bind_toReal_sub_le_of_bad relayImpl)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Name Msg Onion split join stepOf replyOf)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.NIKE.NIKE (NIKE)
open Cryptlib.Protocols.RSOR (Role)

/-! # The payload cipher step, for any property of NIKE Sphinx

After the MAC step (`keyGame_false_sub_gameOnly_le`) the honest relay answers the element of
its place under one header only. If the world shown uses the relay's payload key for one
encryption only, that game is a payload game (`Protocols.RSOR.PayloadGame`), and the cipher
under the relay's payload key may be replaced by an ideal one. -/

section PropPay

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

variable (P : Protocols.RSOR.Property (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
    h16))
  (ρ : Role) (names : Role → Name)

/-- The draws besides the honest relay's payload key: its IV, MAC key, header key and
blinding seed, and the game's draws. -/
abbrev PropPayX (Oth : Type) (A : P.Adversary) :=
  Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 32 × PropDraw nike cipher macS
      kdfS streamS geom hvalid hmactag h16 P ρ names Oth A

/-- The draws of the MAC step, from those and a payload key. -/
def propPayRest {Oth : Type} {A : P.Adversary} (x : PropPayX nike cipher macS kdfS streamS geom
    hvalid hmactag h16 P ρ names Oth A) (kp : Vector UInt8 48) :
    Rest × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A :=
  (((kp, x.1, x.2.2.1), x.2.2.2.1), x.2.2.2.2)

/-- The honest relay's tag on the bytes `M`. -/
def propPayTag {Oth : Type} {A : P.Adversary} (M : Rest × PropDraw nike cipher macS kdfS streamS
    geom hvalid hmactag h16 P ρ names Oth A → ByteArray) (x : PropPayX nike cipher macS kdfS
    streamS geom hvalid hmactag h16 P ρ names Oth A) :
    Vector UInt8 macS.tagSize :=
  macS.mac (Util.Bytes.ofVector x.2.1) (macMsg nike cipher macS kdfS streamS geom hvalid hmactag
      h16 P ρ names M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
      x default))

/-- The one header the honest relay answers. -/
def propPayHeader {Oth : Type} {A : P.Adversary} (M : Rest × PropDraw nike cipher macS kdfS streamS
    geom hvalid hmactag h16 P ρ names Oth A → ByteArray) (x : PropPayX nike cipher macS kdfS
    streamS geom hvalid hmactag h16 P ρ names Oth A) :
    Vector UInt8 geom.headerLength :=
  Util.Bytes.toVecN _ ((macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names M
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names x default)) ++
      Util.Bytes.ofVector (propPayTag nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
      names M x))

/-- **The game after the MAC step, cut at the honest relay's payload key**: the sender's block
is `plain`, and the world from the encrypted block is `viewE`. -/
def propPay (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom hvalid
    hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth) (A : P.Adversary) (M : Rest × PropDraw nike cipher macS kdfS
        streamS geom hvalid hmactag h16 P ρ names Oth A → ByteArray)
    (plain : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (viewE : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → Protocols.RSOR.World 𝒮) :
    Protocols.RSOR.PayloadGame 𝒮 (geom.payloadTagLength + geom.forwardPayloadLength) where
  role := ρ
  X := PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A
  draw iv := do
    let km ← $ᵗ (Vector UInt8 32)
    let he ← $ᵗ (Vector UInt8 32)
    let seed ← $ᵗ (Vector UInt8 32)
    let D ← propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw A
    return (iv, km, he, seed, D)
  header := propPayHeader nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names M
  key o := o.2
  step x o y := stepOf geom (procD nike (Primitives.MAC.MAC.const (propPayTag nike cipher macS kdfS
      streamS geom hvalid hmactag h16 P ρ names M x)) streamS geom
    (fun _ => .ok (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names x default).1 default)) (fun _ _ => y) (join o))
  rep x msg o y := replyOf cipher geom msg (procD nike
    (Primitives.MAC.MAC.const (propPayTag nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names M x)) streamS geom
    (fun _ => .ok (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names x default).1 default)) (fun _ _ => y) (join o))
  proc x h o := if h = ρ then
      stepOf geom (noneAns nike cipher macS kdfS streamS geom x.2.2.2.2.k.2
        (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x.2.2.2.2)
            (join o))
    else RSOR.proc nike cipher macS kdfS streamS geom (x.2.2.2.2.keys h).2 o
  reply x h msg o := if h = ρ then
      replyOf cipher geom msg (noneAns nike cipher macS kdfS streamS geom x.2.2.2.2.k.2
        (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x.2.2.2.2)
            (join o))
    else RSOR.reply nike cipher macS kdfS streamS geom (x.2.2.2.2.keys h).2 msg o
  plain := plain
  log x := x.2.2.2.2.log
  patch x e := (viewE x e).patch
  rest x e := A.guess x.2.2.2.2.st (viewE x e).onion

set_option maxHeartbeats 2000000 in
/-- **The game after the MAC step is its payload game with the cipher, draw by draw**, when
the bytes under the relay's tag have a header's length, carry the element of its place and do
not read its payload key, and the world shown is `viewE` at the encryption of `plain`. -/
theorem propPay_run (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom
    hvalid hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth) (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS
        streamS geom hvalid hmactag h16 P ρ names pk → Oth → ByteArray → List HopKeys →
        Protocols.RSOR.World 𝒮) (A : P.Adversary) (M : Rest × PropDraw nike cipher macS kdfS
        streamS geom hvalid hmactag h16 P ρ names Oth A → ByteArray)
    (plain : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (viewE : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → Protocols.RSOR.World 𝒮)
    (x : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A) (kp :
        Vector UInt8 48)
    (hpos : drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x.2.2.2.2
        < (drawHops nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place
        x.2.2.2.2).size)
    (hM : (M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names x
        default)).size = (2 + nike.publicKeySize + geom.routingInfoLength))
    (hcar : (M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names x
        default)).extract 2 (2 + nike.publicKeySize) = (drawElem nike cipher macS kdfS streamS geom
        hvalid hmactag h16 P ρ names place x.2.2.2.2))
    (hMkp : M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names x kp) =
        M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names x default))
    (hview : drawView nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place view
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names x kp) x.2.1 =
        viewE x (Util.Bytes.toVecN _ (cipher.encrypt kp.toArray (Util.Bytes.ofVector x.1)
        (Util.Bytes.ofVector (plain x))))) :
    simulateQ (relayImpl (Relay.ansOf
      (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize) = drawElem nike cipher macS kdfS
          streamS geom hvalid hmactag h16 P ρ names place x.2))
      (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names x kp)
      (Relay.onlyT macS (2 + nike.publicKeySize + geom.routingInfoLength) (macMsg nike cipher macS
          kdfS streamS geom hvalid hmactag h16 P ρ names M)
        (fun x tag => procWith nike cipher (Primitives.MAC.MAC.const tag) streamS geom
          (fun _ => .ok (restKeys x.1 default)))
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names x kp)
        (macS.mac (Util.Bytes.ofVector x.2.1) (macMsg nike cipher macS kdfS streamS geom hvalid
            hmactag h16 P ρ names M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
            h16 P ρ names x kp))))))
    (drawRun nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place (propPayRest
        nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names x kp) (drawView nike cipher
        macS kdfS streamS geom hvalid hmactag h16 P ρ names place view (propPayRest nike cipher
        macS kdfS streamS geom hvalid hmactag h16 P ρ names x kp) x.2.1))
    = (simulateQ (Protocols.RSOR.withDec (S := 𝒮) (propPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).role ((propPay nike cipher
        macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).header
        x) (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw
        A M plain viewE).key
      ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
          plain viewE).step x) ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
          names place Oth draw A M plain viewE).rep x) ((propPay nike cipher macS kdfS streamS geom
          hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).proc x) ((propPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M plain
          viewE).reply x)
      (fun y => Util.Bytes.toVecN _ (cipher.decrypt kp.toArray (Util.Bytes.ofVector x.1)
        (Util.Bytes.ofVector y)))
      ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
          plain viewE).patch x (Util.Bytes.toVecN _ (cipher.encrypt kp.toArray (Util.Bytes.ofVector
          x.1) (Util.Bytes.ofVector ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          P ρ names place Oth draw A M plain viewE).plain x))))))
      ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
          plain viewE).rest x (Util.Bytes.toVecN _ (cipher.encrypt kp.toArray (Util.Bytes.ofVector
          x.1) (Util.Bytes.ofVector ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          P ρ names place Oth draw A M plain viewE).plain x)))))).run' ((propPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).log x) :=
          by
  obtain ⟨iv, km, he, seed, D⟩ := x
  have hmacEq : (macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names M
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((iv, km, he,
      seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A)
      kp)) = (macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names M (propPayRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((iv, km, he, seed, D) :
      PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A) default)) :=
      by
    unfold macMsg
    rw [hMkp]
  have hMeq : (macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names M
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((iv, km, he,
      seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A)
      default)) = M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
      ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
      names Oth A) default) := Util.Bytes.ofVector_toVecN _ hM
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have hH : Util.Bytes.ofVector (propPayHeader nike cipher macS kdfS streamS geom hvalid hmactag
      h16 P ρ names M ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid
      hmactag h16 P ρ names Oth A))
      = (macMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names M (propPayRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A) default))
          ++ Util.Bytes.ofVector (propPayTag nike cipher macS kdfS streamS geom hvalid hmactag h16
          P ρ names M ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid
          hmactag h16 P ρ names Oth A)) :=
    Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, hMeq, hM, Util.Bytes.size_ofVector, hmactag, hhdr]
      rfl)
  have hcar' : (Util.Bytes.ofVector (propPayHeader nike cipher macS kdfS streamS geom hvalid
      hmactag h16 P ρ names M ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom
      hvalid hmactag h16 P ρ names Oth A))).extract 2 (2 + nike.publicKeySize)
      = (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place D) := by
    rw [hH, hMeq, ← hcar]
    exact KEMSphinx.extract_of_prefix_eq (n := (M (propPayRest nike cipher macS kdfS streamS geom
        hvalid hmactag h16 P ρ names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS
        streamS geom hvalid hmactag h16 P ρ names Oth A) default)).size)
      (by rw [Util.Bytes.extract_append_left]; exact ByteArray.extract_zero_size.symm) 2
      (2 + nike.publicKeySize) (by rw [hM]; omega)
  have hsk : ((fun h => if h = ρ then D.k.2 else (D.keys h).2) ρ) = D.k.2 := ite_eq_left rfl
  have hans : (Relay.ansOf
      (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize) = drawElem nike cipher macS kdfS
          streamS geom hvalid hmactag h16 P ρ names place x.2))
      (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((iv, km, he,
          seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth
          A) kp)
      (Relay.onlyT macS (2 + nike.publicKeySize + geom.routingInfoLength) (macMsg nike cipher macS
          kdfS streamS geom hvalid hmactag h16 P ρ names M)
        (fun x tag => procWith nike cipher (Primitives.MAC.MAC.const tag) streamS geom
          (fun _ => .ok (restKeys x.1 default)))
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((iv, km, he,
            seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth
            A) kp)
        (macS.mac (Util.Bytes.ofVector ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS
            streamS geom hvalid hmactag h16 P ρ names Oth A).2.1) (macMsg nike cipher macS kdfS
            streamS geom hvalid hmactag h16 P ρ names M (propPayRest nike cipher macS kdfS streamS
            geom hvalid hmactag h16 P ρ names ((iv, km, he, seed, D) : PropPayX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 P ρ names Oth A) kp)))))
      = (onlyAns nike cipher macS kdfS streamS geom ((fun h => if h = ρ then D.k.2 else (D.keys
          h).2) ρ) (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place
          D) (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
          ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P
          ρ names Oth A) kp).1 default) (macMsg nike cipher macS kdfS streamS geom hvalid hmactag
          h16 P ρ names M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
          names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
          h16 P ρ names Oth A) default)) (propPayTag nike cipher macS kdfS streamS geom hvalid
          hmactag h16 P ρ names M ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS
          geom hvalid hmactag h16 P ρ names Oth A))) := by
    rw [hsk]
    funext pkt
    unfold Relay.ansOf Relay.onlyT onlyAns onlyAnsH propPayTag
    rw [hmacEq]
    by_cases he : pkt.extract 2 (2 + nike.publicKeySize) = (drawElem nike cipher macS kdfS streamS
        geom hvalid hmactag h16 P ρ names place D)
    · exact (ite_eq_left (decide_eq_true he)).trans (ite_eq_left he).symm
    · exact (ite_eq_right fun h => he (of_decide_eq_true h)).trans (ite_eq_right he).symm
  have hrun : ∀ w, drawRun nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((iv, km, he,
      seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A)
      kp) w
      = (simulateQ (viaOracle nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ (fun h =>
          (D.keys h).2) w.patch)
        (A.guess D.st w.onion)).run' D.log := fun w => ite_eq_left hpos
  rw [show simulateQ (relayImpl _) _
      = simulateQ (relayImpl (onlyAns nike cipher macS kdfS streamS geom ((fun h => if h = ρ then
          D.k.2 else (D.keys h).2) ρ) (drawElem nike cipher macS kdfS streamS geom hvalid hmactag
          h16 P ρ names place D) (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 P ρ names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS
          geom hvalid hmactag h16 P ρ names Oth A) kp).1 default) (macMsg nike cipher macS kdfS
          streamS geom hvalid hmactag h16 P ρ names M (propPayRest nike cipher macS kdfS streamS
          geom hvalid hmactag h16 P ρ names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS
          streamS geom hvalid hmactag h16 P ρ names Oth A) default)) (propPayTag nike cipher macS
          kdfS streamS geom hvalid hmactag h16 P ρ names M ((iv, km, he, seed, D) : PropPayX nike
          cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A)))) _ from
    congrArg (fun f => simulateQ (relayImpl f) _) hans]
  rw [hrun, viaOracle_congr nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ (fun h =>
      (D.keys h).2) (fun h => if h = ρ then D.k.2 else (D.keys h).2)
    (fun h hr => (ite_eq_right hr).symm)]
  refine (relayImpl_onlyAns_run nike cipher macS kdfS streamS geom hvalid hmactag h16 ρ (fun h =>
      if h = ρ then D.k.2 else (D.keys h).2) _ _ _ _ (propPayHeader nike cipher macS kdfS streamS
      geom hvalid hmactag h16 P ρ names M ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS
      streamS geom hvalid hmactag h16 P ρ names Oth A)) hH hcar' _ _ _).trans ?_
  have hs : (fun (o : Onion geom) (y : Vector UInt8 (geom.payloadTagLength +
      geom.forwardPayloadLength)) => stepOf geom (procD nike
        (Primitives.MAC.MAC.const (propPayTag nike cipher macS kdfS streamS geom hvalid hmactag h16
            P ρ names M ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid
            hmactag h16 P ρ names Oth A))) streamS geom
        (fun _ => .ok (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            P ρ names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid
            hmactag h16 P ρ names Oth A) kp).1 default)) (fun _ _ => y) (join o)))
      = (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
          plain viewE).step (iv, km, he, seed, D) := funext fun o => funext fun y =>
    congrArg (stepOf geom) (procD_payloadKey nike _ streamS geom
      (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((iv,
          km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
          names Oth A) default).1 default) kp (fun _ => y) (join o)).symm
  have hr : (fun (msg : Msg geom) (o : Onion geom) (y : Vector UInt8 (geom.payloadTagLength +
      geom.forwardPayloadLength)) =>
        replyOf cipher geom msg (procD nike
          (Primitives.MAC.MAC.const (propPayTag nike cipher macS kdfS streamS geom hvalid hmactag
              h16 P ρ names M ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom
              hvalid hmactag h16 P ρ names Oth A))) streamS geom
          (fun _ => .ok (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
              h16 P ρ names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom
              hvalid hmactag h16 P ρ names Oth A) kp).1 default)) (fun _ _ => y) (join o)))
      = (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
          plain viewE).rep (iv, km, he, seed, D) := funext fun msg => funext fun o => funext fun y
          =>
    congrArg (replyOf cipher geom msg) (procD_payloadKey nike _ streamS geom
      (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((iv,
          km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
          names Oth A) default).1 default) kp (fun _ => y) (join o)).symm
  have hp : (fun (h : Role) (o : Onion geom) => if h = ρ then
        stepOf geom (noneAns nike cipher macS kdfS streamS geom ((fun h => if h = ρ then D.k.2 else
            (D.keys h).2) ρ) (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
            names place D) (join o))
      else RSOR.proc nike cipher macS kdfS streamS geom ((fun h => if h = ρ then D.k.2 else (D.keys
          h).2) h) o)
      = (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
          plain viewE).proc (iv, km, he, seed, D) := funext fun h => funext fun o => by
    by_cases hh : h = ρ
    · rw [hsk]
      exact (ite_eq_left hh).trans (ite_eq_left hh).symm
    · exact (ite_eq_right hh).trans ((congrArg (fun k =>
        RSOR.proc nike cipher macS kdfS streamS geom k o) (ite_eq_right hh)).trans
        (ite_eq_right hh).symm)
  have hrp : (fun (h : Role) (msg : Msg geom) (o : Onion geom) => if h = ρ then
        replyOf cipher geom msg (noneAns nike cipher macS kdfS streamS geom ((fun h => if h = ρ
            then D.k.2 else (D.keys h).2) ρ)
          (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place D) (join
              o))
      else RSOR.reply nike cipher macS kdfS streamS geom ((fun h => if h = ρ then D.k.2 else
          (D.keys h).2) h) msg o)
      = (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
          plain viewE).reply (iv, km, he, seed, D) := funext fun h => funext fun msg => funext fun
          o => by
    by_cases hh : h = ρ
    · rw [hsk]
      exact (ite_eq_left hh).trans (ite_eq_left hh).symm
    · exact (ite_eq_right hh).trans ((congrArg (fun k =>
        RSOR.reply nike cipher macS kdfS streamS geom k msg o) (ite_eq_right hh)).trans
        (ite_eq_right hh).symm)
  have key : ∀ (impl impl' : QueryImpl (Protocols.RSOR.oracleSpec 𝒮)
      (StateT (Protocols.RSOR.Log 𝒮) ProbComp))
      (oa oa' : OracleComp (Protocols.RSOR.oracleSpec 𝒮) Bool) (log : Protocols.RSOR.Log 𝒮),
      impl = impl' → oa = oa' →
        (simulateQ impl oa).run' log = (simulateQ impl' oa').run' log := by
    rintro _ _ _ _ _ rfl rfl
    rfl
  refine key _ _ _ _ _
    (Protocols.RSOR.withDec_congr (S := 𝒮) (L := (geom.payloadTagLength +
        geom.forwardPayloadLength)) _ _ _ _ hs hr hp hrp
      (congrArg (fun w : Protocols.RSOR.World 𝒮 => w.patch) hview)) ?_
  exact congrArg (fun w : Protocols.RSOR.World 𝒮 => A.guess D.st w.onion) hview

/-- The draws after the MAC step, the honest relay's payload key first. -/
def propPayDraw (Oth : Type) (draw : ProbComp Oth) (A : P.Adversary) :
    ProbComp (Vector UInt8 48 × PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names Oth A) := do
  let kp ← $ᵗ (Vector UInt8 48)
  let iv ← $ᵗ (Vector UInt8 16)
  let km ← $ᵗ (Vector UInt8 32)
  let he ← $ᵗ (Vector UInt8 32)
  let seed ← $ᵗ (Vector UInt8 32)
  let D ← propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw A
  return (kp, iv, km, he, seed, D)

/-- The payload game with the cipher, as its draws and then its run. -/
theorem propPay_exp_true_evalDistEq (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS
    streamS geom hvalid hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth) (A : P.Adversary) (M : Rest × PropDraw nike cipher macS kdfS
        streamS geom hvalid hmactag h16 P ρ names Oth A → ByteArray)
    (plain : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (viewE : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → Protocols.RSOR.World 𝒮) :
    (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
        plain viewE).exp cipher true
      =ᵈ propPayDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw A >>=
          fun z =>
          (simulateQ (Protocols.RSOR.withDec (S := 𝒮) (propPay nike cipher macS kdfS streamS geom
              hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).role ((propPay nike
              cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M plain
              viewE).header z.2) (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
              names place Oth draw A M plain viewE).key
      ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
          plain viewE).step z.2) ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P
          ρ names place Oth draw A M plain viewE).rep z.2) ((propPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).proc z.2) ((propPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M plain
          viewE).reply z.2)
      (fun y => Util.Bytes.toVecN _ (cipher.decrypt z.1.toArray (Util.Bytes.ofVector z.2.1)
        (Util.Bytes.ofVector y)))
      ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
          plain viewE).patch z.2 (Util.Bytes.toVecN _ (cipher.encrypt z.1.toArray
          (Util.Bytes.ofVector z.2.1) (Util.Bytes.ofVector ((propPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).plain z.2))))))
      ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
          plain viewE).rest z.2 (Util.Bytes.toVecN _ (cipher.encrypt z.1.toArray
          (Util.Bytes.ofVector z.2.1) (Util.Bytes.ofVector ((propPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).plain z.2)))))).run'
          ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw
          A M plain viewE).log z.2) := by
  unfold Protocols.RSOR.PayloadGame.exp propPayDraw
  simp only [bind_assoc, pure_bind, ↓reduceIte]
  refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun iv => ?_
  show ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
      plain viewE).draw iv >>= fun x => _) =ᵈ _
  unfold propPay
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun he =>
    EvalDistEq.bind_right _ fun seed => EvalDistEq.bind_right _ fun D => ?_
  exact (OracleComp.EvalDistEq.bind_const _ _).trans (OracleComp.EvalDistEq.bind_const _ _)

/-- The game after the MAC step, as the same draws and then its run. -/
theorem macOnly_evalDistEq_propPayDraw (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS
    streamS geom hvalid hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth) (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS
        streamS geom hvalid hmactag h16 P ρ names pk → Oth → ByteArray → List HopKeys →
        Protocols.RSOR.World 𝒮) (A : P.Adversary) (M : Rest × PropDraw nike cipher macS kdfS
        streamS geom hvalid hmactag h16 P ρ names Oth A → ByteArray) :
    macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw view A M
      =ᵈ propPayDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw A >>=
          fun z =>
          simulateQ (relayImpl (Relay.ansOf
      (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize) = drawElem nike cipher macS kdfS
          streamS geom hvalid hmactag h16 P ρ names place x.2))
      (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names z.2 z.1)
      (Relay.onlyT macS (2 + nike.publicKeySize + geom.routingInfoLength) (macMsg nike cipher macS
          kdfS streamS geom hvalid hmactag h16 P ρ names M)
        (fun x tag => procWith nike cipher (Primitives.MAC.MAC.const tag) streamS geom
          (fun _ => .ok (restKeys x.1 default)))
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names z.2 z.1)
        (macS.mac (Util.Bytes.ofVector z.2.2.1) (macMsg nike cipher macS kdfS streamS geom hvalid
            hmactag h16 P ρ names M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
            h16 P ρ names z.2 z.1))))))
    (drawRun nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place (propPayRest
        nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names z.2 z.1) (drawView nike
        cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place view (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names z.2 z.1) z.2.2.1)) := by
  have hb : ∀ {α β : Type},
      Function.Bijective (Function.uncurry fun (a : α) (b : β) => (a, b)) :=
    fun {_ _} => Function.bijective_id
  let F : Vector UInt8 32 → Rest → PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P
      ρ names Oth A → ProbComp Bool := fun km r D =>
    simulateQ (relayImpl (Relay.ansOf
      (fun x pkt => decide (pkt.extract 2 (2 + nike.publicKeySize) = drawElem nike cipher macS kdfS
          streamS geom hvalid hmactag h16 P ρ names place x.2))
      (fun x => procWith nike cipher macS streamS geom (relayKeys nike kdfS x.2.k.2))
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((r.1.2.1, km,
          r.1.2.2, r.2, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
          names Oth A) r.1.1)
      (Relay.onlyT macS (2 + nike.publicKeySize + geom.routingInfoLength) (macMsg nike cipher macS
          kdfS streamS geom hvalid hmactag h16 P ρ names M)
        (fun x tag => procWith nike cipher (Primitives.MAC.MAC.const tag) streamS geom
          (fun _ => .ok (restKeys x.1 default)))
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((r.1.2.1, km,
            r.1.2.2, r.2, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
            names Oth A) r.1.1)
        (macS.mac (Util.Bytes.ofVector ((r.1.2.1, km, r.1.2.2, r.2, D) : PropPayX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 P ρ names Oth A).2.1) (macMsg nike cipher macS
            kdfS streamS geom hvalid hmactag h16 P ρ names M (propPayRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 P ρ names ((r.1.2.1, km, r.1.2.2, r.2, D) : PropPayX
            nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A) r.1.1))))))
    (drawRun nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place (propPayRest
        nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((r.1.2.1, km, r.1.2.2,
        r.2, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A)
        r.1.1) (drawView nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place view
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names ((r.1.2.1, km,
        r.1.2.2, r.2, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
        Oth A) r.1.1) ((r.1.2.1, km, r.1.2.2, r.2, D) : PropPayX nike cipher macS kdfS streamS geom
        hvalid hmactag h16 P ρ names Oth A).2.1))
  have h0 : macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw
      view A M
      = ($ᵗ (Vector UInt8 32)) >>= fun km => ($ᵗ Rest) >>= fun r =>
        propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw A >>=
            fun D => F km r D := by
    unfold macOnly Relay.gameOnly macDraw
    simp only [bind_assoc, pure_bind]
    rfl
  rw [h0]
  unfold propPayDraw
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective
    (g := fun (rk : KEMSphinx.RestKeys) (seed : Vector UInt8 32) => (rk, seed)) hb _).symm ?_
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective
    (g := fun (kp : Vector UInt8 48) (t : Vector UInt8 16 × Vector UInt8 32) => (kp, t)) hb
    _).symm ?_
  refine EvalDistEq.bind_right _ fun kp => ?_
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective
    (g := fun (iv : Vector UInt8 16) (he : Vector UInt8 32) => (iv, he)) hb _).symm ?_
  refine EvalDistEq.bind_right _ fun iv => ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun he =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- **The payload cipher step.** The game after the MAC step differs from its payload game
with an ideal cipher by the one-query advantage of `propPay`'s adversary against the payload
cipher, and the chance of a draw that is not `good`. -/
theorem macOnly_sub_propPay_le (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS
    geom hvalid hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth) (view : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS
        streamS geom hvalid hmactag h16 P ρ names pk → Oth → ByteArray → List HopKeys →
        Protocols.RSOR.World 𝒮) (A : P.Adversary) (M : Rest × PropDraw nike cipher macS kdfS
        streamS geom hvalid hmactag h16 P ρ names Oth A → ByteArray)
    (plain : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (viewE : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → Protocols.RSOR.World 𝒮)
    (good : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A → Prop)
    (hpos : ∀ D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A,
        drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place D < (drawHops
        nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place D).size)
    (hM : ∀ x, good x → (M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names x default)).size = (2 + nike.publicKeySize + geom.routingInfoLength))
    (hcar : ∀ x, good x → (M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names x default)).extract 2 (2 + nike.publicKeySize)
      = (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place x.2.2.2.2))
    (hMkp : ∀ x kp, good x → M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P
        ρ names x kp) = M (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names x default))
    (hview : ∀ x kp, good x → drawView nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names place view (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names x kp) x.2.1
      = viewE x (Util.Bytes.toVecN _ (cipher.encrypt kp.toArray (Util.Bytes.ofVector x.1)
          (Util.Bytes.ofVector (plain x))))) :
    |(Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth
        draw view A M)}[b = true]).toReal
      - (Pr{let b ← ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place
          Oth draw A M plain viewE).exp cipher false)}[b = true]).toReal|
    ≤ (Pr{let z ← (propPayDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth
        draw A)}[¬ good z.2]).toReal
      + |(Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _ (propPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).adv
            true)}[b = true]).toReal
          - (Pr{let b ← (Primitives.WideBlockCipher.oneQueryExp cipher _ (propPay nike cipher macS
              kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).adv
            false)}[b = true]).toReal| := by
  have hwf : ∀ iv, ∀ x ∈ support ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P
      ρ names place Oth draw A M plain viewE).draw iv), ((propPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).log x).WF := by
    intro iv (x : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A) hx
    change x ∈ support (($ᵗ (Vector UInt8 32)) >>= fun km => ($ᵗ (Vector UInt8 32)) >>= fun he =>
      ($ᵗ (Vector UInt8 32)) >>= fun seed => propDrawOf nike cipher macS kdfS streamS geom hvalid
          hmactag h16 P ρ names Oth draw A >>= fun D =>
        pure ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
            h16 P ρ names Oth A)) at hx
    obtain ⟨km, -, hx⟩ := (mem_support_bind_iff _ _ _).1 hx
    obtain ⟨he, -, hx⟩ := (mem_support_bind_iff _ _ _).1 hx
    obtain ⟨seed, -, hx⟩ := (mem_support_bind_iff _ _ _).1 hx
    obtain ⟨D, hD, hx⟩ := (mem_support_bind_iff _ _ _).1 hx
    obtain rfl : x = (iv, km, he, seed, D) := by
      rw [support_pure] at hx
      exact hx
    exact propDraw_log_wf nike cipher macS kdfS streamS geom hvalid hmactag h16 _ ρ names _ _ A D hD
  have h1 : |(Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
      place Oth draw view A M)}[b = true]).toReal
      - (Pr{let b ← ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place
          Oth draw A M plain viewE).exp cipher true)}[b = true]).toReal|
      ≤ (Pr{let z ← (propPayDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
          Oth draw A)}[¬ good z.2]).toReal := by
    rw [(macOnly_evalDistEq_propPayDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
        names place Oth draw view A M).prEvent_eq
        (fun b => b = true),
      (propPay_exp_true_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
          place Oth draw A M plain viewE).prEvent_eq
        (fun b => b = true)]
    exact prEvent_bind_toReal_sub_le_of_bad (propPayDraw nike cipher macS kdfS streamS geom hvalid
        hmactag h16 P ρ names Oth draw A) _ _
      (fun z => ¬ good z.2)
      (fun z hz => propPay_run nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
          place Oth draw view A M plain viewE z.2 z.1
        (hpos z.2.2.2.2.2) (hM z.2 (Classical.not_not.mp hz))
        (hcar z.2 (Classical.not_not.mp hz)) (hMkp z.2 z.1 (Classical.not_not.mp hz))
        (hview z.2 z.1 (Classical.not_not.mp hz))) (fun b => b = true)
  rw [← Protocols.RSOR.PayloadGame.exp_eq cipher (propPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 P ρ names place Oth draw A M plain viewE) hwf true,
    ← Protocols.RSOR.PayloadGame.exp_eq cipher (propPay nike cipher macS kdfS streamS geom hvalid
        hmactag h16 P ρ names place Oth draw A M plain viewE) hwf false]
  exact (abs_sub_le _ _ _).trans (add_le_add h1 le_rfl)

/-! ## The keystream step -/

/-- The draws besides the honest relay's header key and IV: its MAC key and blinding seed, and
the game's draws. -/
abbrev PropStrX (Oth : Type) (A : P.Adversary) :=
  Vector UInt8 32 × Vector UInt8 32 × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag
      h16 P ρ names Oth A

/-- The payload game with the ideal cipher, on its draws. -/
def propPayIdealRun (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom
    hvalid hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth) (A : P.Adversary) (M : Rest × PropDraw nike cipher macS kdfS
        streamS geom hvalid hmactag h16 P ρ names Oth A → ByteArray)
    (plain : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (viewE : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → Protocols.RSOR.World 𝒮)
    (x : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A) (u v :
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) : ProbComp Bool :=
  (simulateQ (Protocols.RSOR.withDec (S := 𝒮) (propPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 P ρ names place Oth draw A M plain viewE).role ((propPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).header x) (propPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M plain
      viewE).key
      ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
          plain viewE).step x) ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
          names place Oth draw A M plain viewE).rep x) ((propPay nike cipher macS kdfS streamS geom
          hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).proc x) ((propPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M plain
          viewE).reply x)
      (fun y => if y = u then (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ
          names place Oth draw A M plain viewE).plain x else v) ((propPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 P ρ names place Oth draw A M plain viewE).patch x u))
    ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
        plain viewE).rest x u)).run' ((propPay nike cipher macS kdfS streamS geom hvalid hmactag
        h16 P ρ names place Oth draw A M plain viewE).log x)

/-- **The adversary against the keystream generator**: it plays `run` from the keystream it
is given. -/
def propStreamAdv (Oth : Type) (draw : ProbComp Oth) (A : P.Adversary) (run : PropStrX nike cipher
    macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A → KEMSphinx.Keystream geom → Vector
    UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → Vector UInt8 (geom.payloadTagLength
    + geom.forwardPayloadLength) → ProbComp Bool) :
    PRGScheme.PRGAdversary (KEMSphinx.Keystream geom) := fun U => do
  let km ← $ᵗ (Vector UInt8 32)
  let seed ← $ᵗ (Vector UInt8 32)
  let D ← propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw A
  let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  run (km, seed, D) U u v

set_option maxHeartbeats 1000000 in
/-- **The keystream step.** If the payload game with the ideal cipher reads the honest
relay's header key and IV through its keystream only, as `run` on that keystream, it is the
real experiment of the keystream generator for `propStreamAdv`. -/
theorem propPay_exp_false_evalDistEq_prg (place : {pk : RSOR.Key nike} → PropCh nike cipher macS
    kdfS streamS geom hvalid hmactag h16 P ρ names pk → Array PathHop × ℕ)
    (Oth : Type) (draw : ProbComp Oth) (A : P.Adversary) (M : Rest × PropDraw nike cipher macS kdfS
        streamS geom hvalid hmactag h16 P ρ names Oth A → ByteArray)
    (plain : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (viewE : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → Protocols.RSOR.World 𝒮)
    (run : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth A →
        KEMSphinx.Keystream geom → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
        → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → ProbComp Bool)
    (hrun : ∀ (iv : Vector UInt8 16) (km he seed : Vector UInt8 32) (D : PropDraw nike cipher macS
        kdfS streamS geom hvalid hmactag h16 P ρ names Oth A)
      (u v : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)),
      (propPayIdealRun nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth
          draw A M plain viewE ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom
          hvalid hmactag h16 P ρ names Oth A) u v)
        = run (km, seed, D) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) u v) :
    (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A M
        plain viewE).exp cipher false
      =ᵈ PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom) (propStreamAdv nike
          cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names Oth draw A run) := by
  have hb : ∀ {α β : Type},
      Function.Bijective (Function.uncurry fun (a : α) (b : β) => (a, b)) :=
    fun {_ _} => Function.bijective_id
  have of_eq : ∀ {a b : ProbComp Bool}, a = b → a =ᵈ b := fun h => h ▸ EvalDistEq.rfl
  have h0 : (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw
      A M plain viewE).exp cipher false
      = ($ᵗ (Vector UInt8 48)) >>= fun _ => ($ᵗ (Vector UInt8 16)) >>= fun iv =>
        ($ᵗ (Vector UInt8 32)) >>= fun km => ($ᵗ (Vector UInt8 32)) >>= fun he =>
        ($ᵗ (Vector UInt8 32)) >>= fun seed => propDrawOf nike cipher macS kdfS streamS geom hvalid
            hmactag h16 P ρ names Oth draw A >>= fun D =>
        ($ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) >>= fun u => ($ᵗ
            (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) >>= fun v =>
          (propPayIdealRun nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place
              Oth draw A M plain viewE ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS
              streamS geom hvalid hmactag h16 P ρ names Oth A) u v) := by
    unfold Protocols.RSOR.PayloadGame.exp propPayIdealRun
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine bind_congr fun kp => bind_congr fun iv => ?_
    show ((propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names place Oth draw A
        M plain viewE).draw iv >>= fun x => _) = _
    unfold propPay
    simp only [bind_assoc, pure_bind]
  rw [h0]
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
  unfold PRGScheme.prgRealExperiment propStreamAdv
  refine EvalDistEq.trans ?_ (evalDistEq_pair_of_bijective
    (g := fun (he : Vector UInt8 32) (iv : Vector UInt8 16) => (he, iv)) hb _)
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun km =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun he => ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun iv => EvalDistEq.bind_right _ fun km =>
    EvalDistEq.bind_right _ fun seed => EvalDistEq.bind_right _ fun D =>
    EvalDistEq.bind_right _ fun u => EvalDistEq.bind_right _ fun v => of_eq ?_
  exact hrun iv km he seed D u v

end PropPay

end Cryptlib.Protocols.Sphinx.NIKESphinx
