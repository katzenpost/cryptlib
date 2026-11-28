/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLUSplit

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

/-! # SLU← for NIKE Sphinx: the two worlds against one relay

The games played from the honest relay's header keystream, against the relay in the closed
form of the TLU→ proof (`hdrRelay`, `fwdRelay`). -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- **A game played from the honest relay's header keystream is a game against `hdrRelay`.** -/
theorem propStrRun_eq_hdrRelay
    (P : Protocols.RSOR.Property (sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16))
    (names : Role → Name) (place : {pk : RSOR.Key nike} → PropCh nike cipher macS kdfS streamS geom
        hvalid hmactag h16 P .relay names pk → Array PathHop × ℕ)
    {Oth : Type} (A : P.Adversary) (MS : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag
        h16 P .relay names Oth A → KEMSphinx.Keystream geom → ByteArray)
    (plainS : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 P .relay names Oth A →
        KEMSphinx.Keystream geom → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (viewS : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 P .relay names Oth A →
        KEMSphinx.Keystream geom → Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)
        → Protocols.RSOR.World 𝒮)
    (x : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 P .relay names Oth A) (U :
        KEMSphinx.Keystream geom) (u v : Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) :
    propStrRun nike cipher macS kdfS streamS geom hvalid hmactag h16 P .relay names place A MS
        plainS viewS x U u v
      = (simulateQ (hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16
          (fun h o => if h = Role.relay then
              stepOf geom (noneAns nike cipher macS kdfS streamS geom x.2.2.k.2
                (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P .relay names
                    place x.2.2) (join o))
            else RSOR.proc nike cipher macS kdfS streamS geom (x.2.2.keys h).2 o)
          (fun h msg o => if h = Role.relay then
              replyOf cipher geom msg (noneAns nike cipher macS kdfS streamS geom x.2.2.k.2
                (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16 P .relay names
                    place x.2.2) (join o))
            else RSOR.reply nike cipher macS kdfS streamS geom (x.2.2.keys h).2 msg o)
          (propStrTag nike cipher macS kdfS streamS geom hvalid hmactag h16 P .relay names MS x U)
              (Util.Bytes.ofVector U)
          (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16 P .relay
              names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16 P .relay
              names x) default).1 default)
          (Util.Bytes.toVecN _ (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
              geom.routingInfoLength) (MS x U))
            ++ Util.Bytes.ofVector (propStrTag nike cipher macS kdfS streamS geom hvalid hmactag
                h16 P .relay names MS x U)))
          (fun y => if y = u then plainS x U else v) (viewS x U u).patch)
        (A.guess x.2.2.st (viewS x U u).onion)).run' x.2.2.log :=
  rfl

/-- **A sender that refuses one header is part of the relays' answers.** -/
theorem hdrRelay_refuse (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom)) {n : ℕ}
    (T : Vector UInt8 n) (U : ByteArray) (t : HopKeys) (Hv : Vector UInt8 geom.headerLength)
    (D : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength) → Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) (last : Vector UInt8
        geom.headerLength) :
    hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T U t Hv D
        { proc := fun (h : Role) (o : Onion geom) out =>
            if h = .sender ∧ o.1 = last then pure none else pure out }
      = hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16
        (fun h o => if h = .sender ∧ o.1 = last then none else procO h o) replyO T U t Hv D
        {} := by
  unfold hdrRelay Protocols.RSOR.withDec
  refine Protocols.RSOR.oracle_pure_patch (S := 𝒮) _ _ _ _ _ (fun h o => ?_) (fun h m o => rfl)
  by_cases hs : h = Role.sender ∧ o.1 = last
  · have hr : ¬ (h = Role.relay ∧ o.1 = Hv) := fun hc => by
      rw [hs.1] at hc
      exact absurd hc.1 (by decide)
    exact (ite_eq_left hs).trans
      (congrArg pure ((ite_eq_right hr).trans (ite_eq_left hs)).symm)
  · refine (ite_eq_right hs).trans (congrArg pure ?_)
    by_cases hr : h = Role.relay ∧ o.1 = Hv
    · exact (ite_eq_left hr).trans (ite_eq_left hr).symm
    · exact (ite_eq_right hr).trans ((ite_eq_right hr).trans (ite_eq_right hs)).symm

include hvalid hmactag in
/-- **The relay that answers a layer of a header function, in closed form**: with that layer's
keystream and tag given, it forwards the header of the next layer. -/
theorem hdrRelay_hdrFn (procO : Role → Onion geom → Option (Protocols.RSOR.Scheme.Step 𝒮))
    (replyO : Role → Msg geom → Onion geom → Option (Name × Onion geom))
    (ksf : ℕ → ByteArray) (tagf : ℕ → ByteArray → ByteArray) (gef : ℕ → ByteArray)
    (fil : ByteArray) (path : Array PathHop) (j : ℕ) (U : ByteArray)
    (T : Vector UInt8 macS.tagSize) (t : HopKeys) (D : Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength) → Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))
    (hj : j + 1 < path.size) (hn : path.size ≤ geom.nrHops)
    (hfill : fil.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hksf : ∀ k, (ksf k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (hU :
        U.size = (geom.routingInfoLength + geom.perHopRoutingInfoLength))
    (htagf : ∀ m x, (tagf m x).size = macLength) (hge : (gef j).size = nike.publicKeySize)
    (hcmd : path[j]!.commands = []) (hT : pathBuilds geom path (path.size - j))
    (hblind : nikeBlind nike (gef j) t.blindingFactor = gef (j + 1)) :
    hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T U t
        (Util.Bytes.toVecN _ (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
            geom.routingInfoLength)
          (hdrMsg geom (Function.update ksf j U) tagf gef fil path j)) ++ Util.Bytes.ofVector T))
        D {}
      = fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO
        (Util.Bytes.toVecN _ (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
            geom.routingInfoLength)
          (hdrMsg geom (Function.update ksf j U) tagf gef fil path j)) ++ Util.Bytes.ofVector T))
        path[j + 1]!.id
        (layerHdr geom (Function.update ksf j U)
          (Function.update tagf j fun _ => Util.Bytes.ofVector T) gef fil path (j + 1)) D := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hT' := fun (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) =>
    (nikeHdrTrace_isSome geom ks _ tag _ gef _ fil _ path (path.size - j)).trans hT
  have hks : ∀ k, ((Function.update ksf j U) k).size = (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) := fun k => by
    by_cases hk : k = j
    · rw [hk, Function.update_self]
      exact hU
    · rw [Function.update_of_ne hk]
      exact hksf k
  have hM : (hdrMsg geom (Function.update ksf j U) tagf gef fil path j).size = (2 +
      nike.publicKeySize + geom.routingInfoLength) :=
    hdrMsg_size nike geom _ _ _ _ _ j hj hnnh (by omega) hrouting hn hfill hks htagf hcmd
      (hT' _ _) hge
  rw [Util.Bytes.ofVector_toVecN _ hM]
  refine hdrRelay_eq_fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 procO replyO T
      U _ _ D _ _ _ _ _ j hj hn hfill hks
    (fun m x => ?_) hge hcmd (hT' _ _) (Function.update_self _ _ _)
    (by rw [Function.update_self]) hblind ?_
  · by_cases hm : m = j
    · rw [hm, Function.update_self]
      exact (Util.Bytes.size_ofVector _).trans hmactag
    · rw [Function.update_of_ne hm]
      exact htagf m x
  · rw [Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, hM, Util.Bytes.size_ofVector, hhdr, had, hmactag])]
    unfold layerHdr
    rw [hdrMsg_update_tag geom _ _ _ _ _ j (by omega), Function.update_self]

variable (W : Protocols.RSOR.BackSwap (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
  h16))

set_option maxHeartbeats 4000000 in
/-- **World 0 on the backward path, before its end, against the relay in closed form.** Under
the challenge header the relay forwards the header of the reply's next layer, with the block it
decrypts; the sender refuses the reply's last header. This holds when the reply's header builds
up to the relay's layer. -/
theorem backRun0_fwd {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A)
    (U : KEMSphinx.Keystream geom) (u v : Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength)) (k : ℕ) (hk : x.2.2.c.pos.val = k + 1)
    (hn : k + 1 < x.2.2.c.req.back.hops.length)
    (hT : pathBuilds geom (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2])
        ((RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]).size - (drawPos nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2))) :
    propStrRun nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A
        (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backPlainS0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W) (backViewS0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W) x U u v
      = (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 (fun h o => if h
          = Role.sender ∧ o.1 = (backHdrFn nike geom x.2.2.c.req x.2.2.o.1 (Function.update (keysKs
          geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
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
          (Util.Bytes.ofVector x.1) (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16
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
          default) default).toArray) (x.2.2.c.req.back.hops.length - 1)) then none else (fun h o =>
          if h = Role.relay then
          stepOf geom (noneAns nike cipher macS kdfS streamS geom x.2.2.k.2
            (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) x.2.2) (join o))
        else RSOR.proc nike cipher macS kdfS streamS geom (x.2.2.keys h).2 o) h o)
          (fun h msg o => if h = Role.relay then
          replyOf cipher geom msg (noneAns nike cipher macS kdfS streamS geom x.2.2.k.2
            (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) x.2.2) (join o))
        else RSOR.reply nike cipher macS kdfS streamS geom (x.2.2.keys h).2 msg o)
            (Util.Bytes.toVecN geom.headerLength ((backMS0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 W x U) ++ Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1)
            (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U)))) (RSOR.path
            nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2])[(drawPos nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
            nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) + 1]!.id
          (layerHdr geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
              default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
              h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U))
              (Function.update (keysTag macS (drawKeys nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
              kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (drawPos
              nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W
              names) x.2.2) fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1)
              (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U))) (blindElem
              nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
              default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
              kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray)
              (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2])
              x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2])
              ((drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) x.2.2) + 1)) (fun y => if y = u then x.2.2.o.2 else
              v))
        (A.guess x.2.2.st (backOnionOfHdr nike cipher macS kdfS streamS geom x.2.2.c.req x.2.2.o.1
          (Nat.zero_lt_of_lt x.2.2.c.pos.isLt)
          (backHdrBytes nike geom x.2.2.c.req x.2.2.o.1 (Function.update (keysKs geom streamS
              (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names x) default) default).toArray) (drawPos nike cipher macS kdfS streamS
              geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
              cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector
              U)) (Function.update (keysTag macS (drawKeys nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
              cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher
              macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
              names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (drawPos
              nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W
              names) x.2.2) fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1)
              (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U))) (blindElem
              nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
              default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
              kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray))))).run'
              x.2.2.log := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have hJ : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) = k := backPos_back nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W x.2.2 k hk
  have hb : 0 < x.2.2.c.req.back.hops.length := Nat.zero_lt_of_lt x.2.2.c.pos.isLt
  have hsz := RSOR.path_size nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]
  have hlen : x.2.2.c.req.back.hops.length ≤ geom.nrHops := x.2.2.c.req.back.length_le
  have hpn : (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]).size ≤ geom.nrHops := by
    rw [hsz]
    exact hlen
  have hJ1 : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) + 1 < x.2.2.c.req.back.hops.length := by
    rw [hJ]
    exact hn
  have hi : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) + 1 < (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]).size := by
    rw [hsz]
    exact hJ1
  have hmul : (geom.nrHops - (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]).size) *
      geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hfill : (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1).size = (geom.nrHops - (RSOR.path nike x.2.2.c.req.back
      [.surbReply x.2.2.o.1.2.2.2]).size) * geom.perHopRoutingInfoLength := by
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hksf : ∀ m, ((keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray) m).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) := fun m
      => streamS.keystream_size _ _ _
  have hU : (Util.Bytes.ofVector U).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)
      := Util.Bytes.size_ofVector _
  have hks : ∀ m, ((Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
      default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)) m).size = (geom.routingInfoLength
      + geom.perHopRoutingInfoLength) := fun m => by
    by_cases hm : m = (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2)
    · rw [hm, Function.update_self]
      exact hU
    · rw [Function.update_of_ne hm]
      exact hksf m
  have htagf : ∀ (m : ℕ) (y : ByteArray), ((keysTag macS (drawKeys nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
      default) default).toArray) m y).size = macLength := fun m y =>
    (Util.Bytes.size_ofVector _).trans hmactag
  have ha : (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
      default) default).toArray 0).size = nike.publicKeySize := Util.Bytes.size_ofVector _
  have hge : ((blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
      nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names x) default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2)).size = nike.publicKeySize := (blindElem_size nike _ _
      _).trans ha
  have hcmd : (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2])[(drawPos nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)]!.commands =
      [] := by
    have hJ0 : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) < x.2.2.c.req.back.hops.length := by omega
    rw [RSOR.path_getElem! nike _ _ (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) hJ0]
    exact ite_eq_right (by omega)
  have hT' := fun (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) =>
    (nikeHdrTrace_isSome geom ks _ tag _ (blindElem nike (groupElem nike (drawKey nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2)
        (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) _ (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply
        x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) _ (RSOR.path nike x.2.2.c.req.back [.surbReply
        x.2.2.o.1.2.2.2]) ((RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]).size -
        (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        x.2.2))).trans hT
  have hKj : (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray[(drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2)]! = (restKeys (propPayRest nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
      default).1 default) := by
    unfold drawKeys
    exact toArray_getElem!_of_getElem? _ _ _
      (hopKeysWith_getElem nike kdfS _ _ _ _ _ (backPos_lt nike cipher macS kdfS streamS geom
          hvalid hmactag h16 W x.2.2))
  have hblind : nikeBlind nike ((blindElem nike (groupElem nike (drawKey nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray 0) (drawKeys nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (drawPos nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)) (restKeys
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default).1
      default).blindingFactor = (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray 0) (drawKeys nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) ((drawPos nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) + 1) := by
    show _ = nikeBlind nike ((blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2)) ((drawKeys nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
        default) default).toArray[(drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2)]!).blindingFactor
    rw [hKj]
  have hMS : (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U) = hdrMsg geom
      (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
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
      hvalid hmactag h16 W names) x.2.2) :=
    backMS0_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U k hk
  have hM : (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U).size = (2 +
      nike.publicKeySize + geom.routingInfoLength) := by
    rw [hMS]
    exact hdrMsg_size nike geom _ _ _ _ _ (drawPos nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) x.2.2) hi hnnh (by omega) hrouting hpn hfill hks
        htagf
      hcmd (hT' _ _) hge
  have hTw : propStrTag nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backMS0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W) x U = (macS.mac (Util.Bytes.ofVector x.1) (backMS0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 W x U)) := by
    unfold propStrTag
    rw [Util.Bytes.ofVector_toVecN _ hM]
  have key := hdrRelay_hdrFn nike cipher macS kdfS streamS geom hvalid hmactag h16 (fun h o => if h
      = Role.sender ∧ o.1 = (backHdrFn nike geom x.2.2.c.req x.2.2.o.1 (Function.update (keysKs
      geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)) (Function.update (keysTag macS
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
      W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray)
      (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
      W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
      x.2.2) fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1) (backMS0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W x U))) (blindElem nike (groupElem nike (drawKey
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names x.2.2) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray) (x.2.2.c.req.back.hops.length - 1)) then none else (fun h o => if h =
      Role.relay then
          stepOf geom (noneAns nike cipher macS kdfS streamS geom x.2.2.k.2
            (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) x.2.2) (join o))
        else RSOR.proc nike cipher macS kdfS streamS geom (x.2.2.keys h).2 o) h o) (fun h msg o =>
            if h = Role.relay then
          replyOf cipher geom msg (noneAns nike cipher macS kdfS streamS geom x.2.2.k.2
            (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) x.2.2) (join o))
        else RSOR.reply nike cipher macS kdfS streamS geom (x.2.2.keys h).2 msg o) (keysKs geom
            streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
            default) default).toArray) (keysTag macS (drawKeys nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
            macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (blindElem
            nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
            nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray 0) (drawKeys
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
            default).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply
            x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply
            x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) x.2.2)
    (Util.Bytes.ofVector U) (macS.mac (Util.Bytes.ofVector x.1) (backMS0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W x U)) (restKeys (propPayRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names x) default).1 default) (fun y => if y = u then x.2.2.o.2 else v) hi hpn hfill
        hksf hU htagf hge hcmd hT hblind
  rw [← hMS, Util.Bytes.ofVector_toVecN _ hM] at key
  rw [propStrRun_eq_hdrRelay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) names (backPlace nike cipher macS kdfS streamS geom hvalid
      hmactag h16 W names) A _ _ _ x U u v,
    backViewS0_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U u k hk hb,
        backPlainS0_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U k hk, hTw,
    Util.Bytes.ofVector_toVecN _ hM]
  have cong : ∀ (impl impl' : QueryImpl (Protocols.RSOR.oracleSpec 𝒮)
      (StateT (Protocols.RSOR.Log 𝒮) ProbComp))
      (oa oa' : OracleComp (Protocols.RSOR.oracleSpec 𝒮) Bool) (log : Protocols.RSOR.Log 𝒮),
      impl = impl' → oa = oa' →
        (simulateQ impl oa).run' log = (simulateQ impl' oa').run' log := by
    rintro _ _ _ _ _ rfl rfl
    rfl
  exact cong _ _ _ _ _
    ((hdrRelay_refuse nike cipher macS kdfS streamS geom hvalid hmactag h16 (fun h o => if h =
        Role.relay then
          stepOf geom (noneAns nike cipher macS kdfS streamS geom x.2.2.k.2
            (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) x.2.2) (join o))
        else RSOR.proc nike cipher macS kdfS streamS geom (x.2.2.keys h).2 o) (fun h msg o => if h
            = Role.relay then
          replyOf cipher geom msg (noneAns nike cipher macS kdfS streamS geom x.2.2.k.2
            (drawElem nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W names) x.2.2) (join o))
        else RSOR.reply nike cipher macS kdfS streamS geom (x.2.2.keys h).2 msg o) (macS.mac
            (Util.Bytes.ofVector x.1) (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 W x U)) (Util.Bytes.ofVector U) (restKeys (propPayRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names x) default).1 default) (Util.Bytes.toVecN
            geom.headerLength ((backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x
            U) ++ Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1) (backMS0 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W x U)))) (fun y => if y = u then x.2.2.o.2 else v)
      (backHdrFn nike geom x.2.2.c.req x.2.2.o.1 (Function.update (keysKs geom streamS (drawKeys
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
          (Util.Bytes.ofVector x.1) (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16
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
          default) default).toArray) (x.2.2.c.req.back.hops.length - 1))).trans key) rfl

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
