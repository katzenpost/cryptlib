/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUBlind

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

/-! # The last comparison of TLU→ for NIKE Sphinx: world 1 from the hops' functions -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

set_option maxHeartbeats 4000000 in
/-- **World 1 on a draw, before the end of the path, from the hops' functions.** The relay's
header is the replacement's layer at the relay, the layer forwarded is the original's next
layer from its own keys and the keystream `x.1`, and the other answers are world 0's. -/
theorem finRun_layerFn (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary)
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A)
    (hn : (x.2.p.c.pos : ℕ) + 1 < x.2.p.c.req.fwd.hops.length)
    (hT' : pathBuilds geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) (RSOR.path nike
        ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]).size)
    (hb' : (RSOR.body nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.o)).size = geom.forwardPayloadLength)
    (hMsz : (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem nike (drawKey nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S :=
        𝒮)) .relay names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
        (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos).size = 2 +
        nike.publicKeySize + geom.routingInfoLength)
    (hrep : finNoReply nike cipher macS kdfS streamS geom hvalid hmactag h16 x) :
    finOwnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A x
      =ᵈ $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) >>= fun g =>
        (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 ((forwardPay
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (A := A) (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2)))) ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, default, (toDraw0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom
            hvalid hmactag h16 x.2).2.2)))) (layerFn nike macS kdfS streamS geom ((fwd1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o)
            ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) (Function.update (keysKs
            geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
            x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (Function.update (keysTag macS (forwardKeys0
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos fun _ =>
            Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector
            (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom
            (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
            default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem
            nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
            default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
            hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
            [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
            (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
            h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
            ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).receiver]) x.2.p.c.pos))))) (Function.update (keysEnc cipher (forwardKeys0
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos fun _ =>
            Util.Bytes.ofVector x.2.u) (blindElem nike (groupElem nike (drawKey nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
            names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
            (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos).1 (RSOR.path nike
            x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])[(x.2.p.c.pos : ℕ) + 1]!.id
          (Util.Bytes.ofVector (layerFn nike macS kdfS streamS geom x.2.p.c.req x.2.o.1
              (Function.update (keysKs geom streamS (nextKeysI nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) x.2.p.c.pos
              (Util.Bytes.ofVector x.1)) (keysTag macS (nextKeysI nike cipher macS kdfS streamS
              geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) (keysEnc cipher
              (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default
              x.2.y, x.2.p)).toArray) (blindElem nike (groupElem nike ((nike.decodePrivateKey
              x.2.p.d0).getD default) (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag
              h16 (keys4 default x.2.y, x.2.p)).toArray 0) (nextKeysI nike cipher macS kdfS streamS
              geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) (x.2.p.c.pos + 1)).1)
              (fun y => if y = (layerFn nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
              geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
              hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd
              (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o)
              (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
              h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U))
              (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
              names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
              h16 x.2)) default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac
              (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
              nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs
              geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
              default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS
              (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
              nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
              (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike
              cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom
              (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
              names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
              (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
              nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
              ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X
              nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
              cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
              geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom
              hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid
              hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
              hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
              h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
              (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
              [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
              (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
              (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS
              kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos)))))
              (Function.update (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
              names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
              h16 x.2)) default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector x.2.u)
              (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike
              cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos).2 then (layerFn
              nike macS kdfS streamS geom x.2.p.c.req x.2.o.1 (Function.update (keysKs geom streamS
              (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default
              x.2.y, x.2.p)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.1)) (keysTag macS
              (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default
              x.2.y, x.2.p)).toArray) (keysEnc cipher (nextKeysI nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) (blindElem nike (groupElem
              nike ((nike.decodePrivateKey x.2.p.d0).getD default) (nextKeysI nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray 0) (nextKeysI
              nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y,
              x.2.p)).toArray) (x.2.p.c.pos + 1)).2 else g))
          (A.guess x.2.p.st (layerFn nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
              geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
              hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd
              (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o)
              (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
              h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U))
              (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
              names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
              h16 x.2)) default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac
              (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
              nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs
              geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
              default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS
              (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
              nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
              (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike
              cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom
              (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
              names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
              (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
              nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
              ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X
              nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
              cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
              geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom
              hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid
              hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
              hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
              h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
              (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
              [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
              (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
              (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS
              kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos)))))
              (Function.update (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
              names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
              h16 x.2)) default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector x.2.u)
              (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike
              cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
              (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2)) default)).toArray) 0))).run' x.2.p.log := by
  have hpos : (x.2.p.c.pos : ℕ) < x.2.p.c.req.fwd.hops.length := x.2.p.c.pos.isLt
  have hposP : (x.2.p.c.pos : ℕ) < (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size := lt_of_lt_of_eq hpos (RSOR.path_size nike _ _).symm
  have hlen1 : (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length = x.2.p.c.pos + 1 := by
    show (List.take ((x.2.p.c.pos : ℕ) + 1) x.2.p.c.req.fwd.hops).length = x.2.p.c.pos + 1
    rw [List.length_take]
    omega
  have hszP1 : (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]).size = x.2.p.c.pos + 1 := (RSOR.path_size nike
      _ _).trans hlen1
  have hlt := fwd_hops_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2
  have hjk : (x.2.p.c.pos : ℕ) ≤ (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).length :=
    le_of_lt (lt_of_lt_of_eq hlt (hopKeysWith_length nike kdfS _ _ _ _ _).symm)
  have hMINE : finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x = (layerFn nike macS
      kdfS streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) (Function.update (keysKs
      geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U))
      (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector
      (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom
      (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem
      nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos)))))
      (Function.update (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      fun _ => Util.Bytes.ofVector x.2.u) (blindElem nike (groupElem nike (drawKey nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos) :=
    onionOfStream_eq_layerFn nike cipher macS kdfS streamS geom x.2.p.c.pos ((fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
        geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
        hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.o) (groupElem nike (drawKey nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)) x.2.p.c.pos
      (Util.Bytes.ofVector x.2.U) (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km)
          (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
          (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike
          (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
          (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).receiver]) x.2.p.c.pos))))) (Util.Bytes.ofVector x.2.u) hvalid
      hmactag le_rfl (by rw [hszP1]; omega) hjk (Util.Bytes.size_ofVector _)
      ((Util.Bytes.size_ofVector _).trans hmactag) (by rw [Util.Bytes.size_ofVector]; exact h16)
      (Util.Bytes.size_ofVector _)
  have hSHOWN : strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2) x.2.U x.2.u 0 = (layerFn nike macS kdfS streamS geom ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.o) (Function.update (keysKs geom streamS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (Function.update (keysTag macS
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac
      (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize
      + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
      names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler
      nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))))) (Function.update (keysEnc
      cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector
      x.2.u) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) 0) :=
    onionOfStream_eq_layerFn nike cipher macS kdfS streamS geom 0 ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.o) (groupElem nike (drawKey nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)) x.2.p.c.pos
      (Util.Bytes.ofVector x.2.U) (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km)
          (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
          (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike
          (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
          (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).receiver]) x.2.p.c.pos))))) (Util.Bytes.ofVector x.2.u) hvalid
      hmactag (Nat.zero_le _) (by rw [hszP1]; omega) hjk (Util.Bytes.size_ofVector _)
      ((Util.Bytes.size_ofVector _).trans hmactag) (by rw [Util.Bytes.size_ofVector]; exact h16)
      (Util.Bytes.size_ofVector _)
  have hNEXT : finNext nike cipher macS kdfS streamS geom hvalid hmactag h16 x = (layerFn nike macS
      kdfS streamS geom x.2.p.c.req x.2.o.1 (Function.update (keysKs geom streamS (nextKeysI nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector x.1)) (keysTag macS (nextKeysI nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) (keysEnc cipher (nextKeysI
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray)
      (blindElem nike (groupElem nike ((nike.decodePrivateKey x.2.p.d0).getD default) (nextKeysI
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray
      0) (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y,
      x.2.p)).toArray) (x.2.p.c.pos + 1)) := by
    unfold finNext next4Nxt
    rw [ite_eq_left hn]
    exact nextOfStream_eq_layerFn nike cipher macS kdfS streamS geom x.2.p.c.req x.2.o.1 (groupElem
        nike ((nike.decodePrivateKey x.2.p.d0).getD default) (nextKeysI nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray 0) (nextKeysI nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)) x.2.p.c.pos
      (Util.Bytes.ofVector x.1) hvalid hmactag (by rw [RSOR.path_size]; exact hn)
      (lt_of_lt_of_eq hposP (hopKeysWith_length nike kdfS _ _ _ _ _).symm)
      (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _)
  have hlast := layerFn_last nike macS kdfS streamS geom hvalid ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o) (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
    (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector
        (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
        nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom
        streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
        (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
        (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path
        nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
        (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))))) x.2.u hszP1.symm
        hb' hT' hMsz
    ((Util.Bytes.size_ofVector _).trans hmactag)
  have hmineHdr : (finMine nike cipher macS kdfS streamS geom hvalid hmactag h16 x).1 =
      Util.Bytes.toVecN _ (strMsg nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2) x.2.U
      ++ Util.Bytes.ofVector (strTag nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2) x.2.U)) := by
    rw [hMINE, hlast]
    show Util.Bytes.toVecN _ ((hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem nike
        (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path
        nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
        (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos) ++ Util.Bytes.ofVector
        (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
        nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom
        streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
        (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
        (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path
        nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
        (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos)))))
      = Util.Bytes.toVecN _ (Util.Bytes.ofVector (Util.Bytes.toVecN _ (hdrMsg geom (Function.update
          (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
          x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
          .relay names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path nike
          ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))
        ++ Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector
            (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom
            (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
            default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem
            nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
            default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
            hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
            [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
            (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
            h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
            ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).receiver]) x.2.p.c.pos)))))
    rw [Util.Bytes.ofVector_toVecN _ hMsz]
  have hPO : ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))) =
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (A := A) (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))) := by
    funext h o
    show (if h = Role.relay then stepOf geom (noneAns nike cipher macS kdfS streamS geom
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.2 (drawElem nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S
            := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16
            names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)) (next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
        (join o)) else _) = _
    rw [drawElem_fwd1]
    rfl
  have hRO : ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))) =
      ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (A := A) (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))) := by
    funext h m o
    show (if h = Role.relay then replyOf cipher geom m (noneAns nike cipher macS kdfS streamS geom
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.2 (drawElem nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S
            := 𝒮)) .relay names (forwardPlace nike cipher macS kdfS streamS geom hvalid hmactag h16
            names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)) (next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
        (join o)) else _) = _
    rw [drawElem_fwd1]
    rfl
  have hname : x.2.p.c.req.fwd.hops[(x.2.p.c.pos : ℕ) + 1].name = (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver])[(x.2.p.c.pos : ℕ) + 1]!.id :=
    (congrArg PathHop.id (RSOR.path_getElem! nike _ _ _ hn)).symm
  have hG : strGuess nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) A (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2) x.2.U x.2.u = A.guess x.2.p.st (layerFn nike macS kdfS streamS geom
      ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o)
      ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) (Function.update (keysKs geom streamS
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U))
      (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector
      (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom
      (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem
      nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray 0)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos)))))
      (Function.update (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      fun _ => Util.Bytes.ofVector x.2.u) (blindElem nike (groupElem nike (drawKey nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) 0) := by
    unfold strGuess
    rw [ite_eq_left hlt]
    exact congrArg (A.guess _) hSHOWN
  refine (finOwnRun_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 names A x hn
      hmineHdr hrep).trans ?_
  rw [hPO, hRO, hMINE, hNEXT, hG, hname]

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
