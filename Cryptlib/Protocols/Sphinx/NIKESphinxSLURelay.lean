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

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
