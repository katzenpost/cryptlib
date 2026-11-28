/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUWorld1

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

/-! # The last comparison of TLU→ for NIKE Sphinx: the joined keystream on a draw

On the keystream that joins a draw of world 1, the blinding adversary plays world 1's run. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- Before the end of a path whose header builds, the blinding adversary plays the game from
the hops' functions. -/
theorem blindPost_fn (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) (s : KEMSphinx.Keystream geom × Vector UInt8 32 ×
    (PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
    (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS kdfS streamS
    geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)))
    (tail : ByteArray × List HopKeys)
    (hj : (s.2.2.1.c.pos : ℕ) + 1 < s.2.2.1.c.req.fwd.hops.length)
    (hT : pathBuilds geom (RSOR.path nike s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver])
        ((RSOR.path nike s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver]).size -
        s.2.2.1.c.pos)) :
    blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E s tail
      = fnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 A ((forwardPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A
          := A) (s.2.1, default, s.2.2.1)))
        ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (A := A) (s.2.1, default, s.2.2.1)))
        s.2.2.1.st s.2.2.1.log s.2.2.1.c.req s.2.2.1.o s.2.2.1.c.pos s.2.1 s.2.2.2.1 s.2.2.2.2
        (spliceAt s.2.2.1.c.pos (Function.update (keysKs geom streamS (hopKeysWith nike kdfS
            ((nike.decodePrivateKey s.2.2.1.d).getD default) (RSOR.path nike s.2.2.1.c.req.fwd
            [.recipient s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys ((default, default,
            default), default) default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]).size).toArray)
          s.2.2.1.c.pos (Util.Bytes.ofVector s.1)) (keysKs geom streamS tail.2.toArray))
        (spliceAt s.2.2.1.c.pos (keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey
            s.2.2.1.d).getD default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys ((default, default, default), default)
            default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]).size).toArray) (keysTag macS tail.2.toArray))
        (spliceAt s.2.2.1.c.pos (keysEnc cipher (hopKeysWith nike kdfS ((nike.decodePrivateKey
            s.2.2.1.d).getD default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys ((default, default, default), default)
            default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient
            s.2.2.1.c.req.receiver]).size).toArray) (keysEnc cipher tail.2.toArray))
        (spliceAt s.2.2.1.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey
            s.2.2.1.d).getD default) (hopKeysWith nike kdfS ((nike.decodePrivateKey s.2.2.1.d).getD
            default) (RSOR.path nike s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver])
            s.2.2.1.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
            s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver]).size).toArray 0) (hopKeysWith
            nike kdfS ((nike.decodePrivateKey s.2.2.1.d).getD default) (RSOR.path nike
            s.2.2.1.c.req.fwd [.recipient s.2.2.1.c.req.receiver]) s.2.2.1.c.pos (restKeys
            ((default, default, default), default) default) (RSOR.path nike s.2.2.1.c.req.fwd
            [.recipient s.2.2.1.c.req.receiver]).size).toArray)
          (blindElem nike tail.1 tail.2.toArray)) := by
  unfold blindPost
  rw [ite_eq_left hj, ite_eq_left hT]

/-- **The keystream of world 0's relay that joins a draw of world 1**: `combStream` on the
replacement's keystream `x.2.U` and the keystream `x.1` of the original's next layer. -/
def finComb {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) : KEMSphinx.Keystream geom :=
  Util.Bytes.toVecN _ (combStream nike geom (spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith
      nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default),
      default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (Function.update (keysKs geom
      streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default
      x.2.y, x.2.p)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.1)) x.2.p.c.pos ((Function.update
      (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      (Util.Bytes.ofVector x.2.U)) x.2.p.c.pos) ((lastFrag geom (RSOR.path nike ((fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos) ++
      (if geom.nrHops > (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]).size then (RSOR.filler nike geom (RSOR.path
      nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
      [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1) else
      ByteArray.empty)) (spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike kdfS
      ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (keysTag
      macS (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray))
      (spliceAt x.2.p.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey x.2.d').getD
      default) (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default,
      default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS ((nike.decodePrivateKey
      x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem nike (tailOf
      nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (RSOR.filler nike geom (RSOR.path
      nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]))

set_option maxHeartbeats 16000000 in
/-- **On the joined keystream, the blinding adversary plays world 1.** Take a draw of world 1's
last game before the end of the path. The bytes under the relay's tag in the replacement
have their length, and handed the tail of the original's path from the
original's own secret, with the joined keystream for the relay and the block `g` for a changed
payload, the blinding adversary plays the game `finRun_layerFn` gives for world 1. -/
theorem blindPost_comb (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool)
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) (g : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    (hn : (x.2.p.c.pos : ℕ) + 1 < x.2.p.c.req.fwd.hops.length)
    (hT : pathBuilds geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
        (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size) (hT' : pathBuilds
        geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) (RSOR.path nike ((fwd1
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
        geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]).size)
    (hb : (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1).size =
        geom.forwardPayloadLength)
    (hb' : (RSOR.body nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.o)).size = geom.forwardPayloadLength) :
    (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
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
        nike.publicKeySize + geom.routingInfoLength
      ∧ blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (finComb nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x, x.2.km, (toDraw0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2), x.2.u, g) (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD
          default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos
          x.2.y.2.2)
      = (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 ((forwardPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (A := A) (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))))
          ((forwardPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (A := A) (x.2.km, default, (toDraw0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2)))) (layerFn nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.o) (Function.update (keysKs geom streamS (forwardKeys0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U))
          (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac
          (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
          nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom
          streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
          (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
          (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
          (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos)))))
          (Function.update (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector x.2.u) (blindElem nike
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
          x.2.p.c.pos).1 (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver])[(x.2.p.c.pos : ℕ) + 1]!.id
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
        (A.guess x.2.p.st (layerFn nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
            h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.o) (Function.update (keysKs geom streamS
            (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
            (Util.Bytes.ofVector x.2.U)) (Function.update (keysTag macS (forwardKeys0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos fun _ =>
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
            streamS geom hvalid hmactag h16 x.2)) default)).toArray) 0))).run' x.2.p.log := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have hpos : (x.2.p.c.pos : ℕ) < x.2.p.c.req.fwd.hops.length := x.2.p.c.pos.isLt
  have hszP := RSOR.path_size nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]
  have hposP : (x.2.p.c.pos : ℕ) < (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size := lt_of_lt_of_eq hpos hszP.symm
  have hjP : (x.2.p.c.pos : ℕ) + 1 < (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size := lt_of_lt_of_eq hn hszP.symm
  have hnP : (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size ≤ geom.nrHops
      := le_of_eq_of_le hszP x.2.p.c.req.fwd.length_le
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
  have hszP1e : (RSOR.path nike (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)) []).size = x.2.p.c.pos + 1
      := (RSOR.path_size nike _ _).trans hlen1
  have hP1 : (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) = (RSOR.path nike (x.2.p.c.req.fwd.take
      (x.2.p.c.pos + 1)) [.recipient x.2.o.2.2.1]) := rfl
  have hjp : ((x.2.p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting]
    exact (Nat.mul_comm _ _).le.trans (Nat.mul_le_mul_left _ (by omega))
  have hfillOf : ∀ (pth : Array PathHop) (rr : RSOR.Randomness nike geom),
      (RSOR.filler nike geom pth rr.1).size
        = (geom.nrHops - pth.size) * geom.perHopRoutingInfoLength := fun pth rr => by
    have hmul : (geom.nrHops - pth.size) * geom.perHopRoutingInfoLength
        ≤ geom.routingInfoLength := by
      rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hTj : pathBuilds geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      ((RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size - x.2.p.c.pos) :=
    nikeHdrTrace_isSome_of_le geom _ _ _ _ (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) ((RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]).size - x.2.p.c.pos) x.2.p.c.pos (by
      rw [Nat.sub_add_cancel (le_of_lt hposP)]
      exact hT)
  have hT1' : pathBuilds geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) 1 :=
    nikeHdrTrace_isSome_of_le geom _ _ _ _ (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
        hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.o).receiver]) 1 x.2.p.c.pos (by
      rw [show 1 + (x.2.p.c.pos : ℕ) = (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).receiver]).size by omega]
      exact hT')
  have hTail : (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2) = (groupElem nike
      ((nike.decodePrivateKey x.2.p.d0).getD default) (nextKeysI nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray (x.2.p.c.pos + 1), (nextKeysI nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).drop
      (x.2.p.c.pos + 1)) :=
    tailOf_hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2 (keysOfDraw (keys4
        default x.2.y))
      hposP rfl
  have hdrop : ∀ i, (x.2.p.c.pos : ℕ) < i →
      ((nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y,
          x.2.p)).drop (x.2.p.c.pos + 1)).toArray[i - (x.2.p.c.pos + 1)]! = (nextKeysI nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray[i]! :=
          fun i hi => by
    rw [toArray_drop_getElem!, show (x.2.p.c.pos : ℕ) + 1 + (i - (x.2.p.c.pos + 1)) = i by omega]
  have hpub : ∀ m, m < (x.2.p.c.pos : ℕ) + 1 → (RSOR.path nike (x.2.p.c.req.fwd.take (x.2.p.c.pos +
      1)) [])[m]!.publicKey = (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver])[m]!.publicKey := fun m hm => by
    have hb1 : m < (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length := lt_of_lt_of_eq hm
        hlen1.symm
    have hb2 : m < x.2.p.c.req.fwd.hops.length := by omega
    rw [RSOR.path_getElem! nike _ _ m hb1, RSOR.path_getElem! nike _ _ m hb2]
    exact congrArg (fun h : Protocols.RSOR.Hop Name (RSOR.Key nike) =>
      Util.Bytes.ofVector (nike.encodePublicKey h.key.1)) List.getElem_take
  have hkeys : ∀ i, i < (x.2.p.c.pos : ℕ) → (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray[i]! =
      (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default,
      default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray[i]! := fun i hi => by
    have hle1 : (RSOR.path nike (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)) []).size ≤ (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size := by
      rw [hszP1e]
      omega
    have hi1 : i < (RSOR.path nike (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)) []).size := by
      rw [hszP1e]
      omega
    rw [fwd1_keys nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2)]
    exact (hopKeysWith_cut nike kdfS _ (RSOR.path nike (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)) [])
        (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos _ _
        (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size hle1
      (fun m hm => hpub m (lt_of_lt_of_eq hm hszP1e)) i hi1).trans
      (hopKeysWith_getElem!_lt nike kdfS _ _ x.2.p.c.pos _ (restKeys ((default, default, default),
          default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size
          i hi hposP.le)
  have hks0 : ∀ k, ((spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS
      ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (keysKs
      geom streamS (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path
      nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray))
      k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) := fun k => by
    by_cases hk : k ≤ (x.2.p.c.pos : ℕ)
    · rw [spliceAt_le _ _ _ k hk]
      exact streamS.keystream_size _ _ _
    · rw [spliceAt_gt _ _ _ k (by omega)]
      exact streamS.keystream_size _ _ _
  have hksI : ∀ k, ((Function.update (keysKs geom streamS (nextKeysI nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) x.2.p.c.pos
      (Util.Bytes.ofVector x.1)) k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength)
      := fun k => by
    by_cases hk : k = (x.2.p.c.pos : ℕ)
    · rw [hk, Function.update_self]
      exact Util.Bytes.size_ofVector _
    · rw [Function.update_of_ne hk]
      exact streamS.keystream_size _ _ _
  have hks1 : ∀ k, ((Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) k).size = (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) := fun k => by
    by_cases hk : k = (x.2.p.c.pos : ℕ)
    · rw [hk, Function.update_self]
      exact Util.Bytes.size_ofVector _
    · rw [Function.update_of_ne hk]
      exact streamS.keystream_size _ _ _
  have htag0 : ∀ i m, ((spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike kdfS
      ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (keysTag
      macS (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) i
      m).size = macLength := fun i m => by
    by_cases hk : i ≤ (x.2.p.c.pos : ℕ)
    · rw [spliceAt_le _ _ _ i hk]
      exact (Util.Bytes.size_ofVector _).trans hmactag
    · rw [spliceAt_gt _ _ _ i (by omega)]
      exact (Util.Bytes.size_ofVector _).trans hmactag
  have htag1 : ∀ i m, ((keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) i m).size =
      macLength := fun i m =>
    (Util.Bytes.size_ofVector _).trans hmactag
  have hT1sz : (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1.size =
      nike.publicKeySize := by
    rw [hTail]
    show (groupElem nike ((nike.decodePrivateKey x.2.p.d0).getD default) (nextKeysI nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray
        (x.2.p.c.pos + 1)).size = _
    rw [groupElem_eq_blindElem nike ((nike.decodePrivateKey x.2.p.d0).getD default) (nextKeysI nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray
        (x.2.p.c.pos + 1), blindElem_size]
    exact Util.Bytes.size_ofVector _
  have hge0 : ∀ i, ((spliceAt x.2.p.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey
      x.2.d').getD default) (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default)
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys
      ((default, default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS ((nike.decodePrivateKey
      x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem nike (tailOf
      nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) i).size = nike.publicKeySize := fun
      i => by
    by_cases hk : i ≤ (x.2.p.c.pos : ℕ)
    · rw [spliceAt_le _ _ _ i hk]
      exact (blindElem_size nike _ _ _).trans (Util.Bytes.size_ofVector _)
    · rw [spliceAt_gt _ _ _ i (by omega)]
      exact (blindElem_size nike _ _ _).trans hT1sz
  have hge1p : ((blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
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
      hmactag h16 x.2)) default)).toArray) x.2.p.c.pos).size = nike.publicKeySize :=
    (blindElem_size nike _ _ _).trans (Util.Bytes.size_ofVector _)
  obtain ⟨F0, hF0⟩ := pathBuilds_fragment geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) hT1'
  rw [show (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).receiver]).size - 1 = (x.2.p.c.pos : ℕ) by omega] at hF0
  have hFr : nikeFragment geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) ByteArray.empty x.2.p.c.pos = .ok (lastFrag
      geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos) := by
    unfold lastFrag
    rw [hF0]
  have hX' : ((lastFrag geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos) ++ (if geom.nrHops > (RSOR.path
      nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
      [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).receiver]).size then (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.o).1) else ByteArray.empty)).size =
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - ((x.2.p.c.pos : ℕ) + 1) *
      geom.perHopRoutingInfoLength) := by
    have hfs : (if geom.nrHops > (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size then
        (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS
        geom hvalid hmactag h16 x.2).2.2.o).1) else ByteArray.empty).size
        = (geom.nrHops - (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
            ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).receiver]).size) * geom.perHopRoutingInfoLength := by
      by_cases hg : geom.nrHops > (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size
      · rw [ite_eq_left hg]
        exact hfillOf _ _
      · rw [ite_eq_right hg, show geom.nrHops - (RSOR.path nike ((fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).receiver]).size = 0 by omega, Nat.zero_mul]
        rfl
    rw [ByteArray.size_append, nikeFragment_size geom (RSOR.path nike ((fwd1 nike cipher macS kdfS
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
        x.2).2.2.o).receiver]) _ x.2.p.c.pos hnnh (by omega) _ hFr, hfs,
      hszP1, hrouting]
    obtain ⟨k, hk⟩ : ∃ k, geom.nrHops = (x.2.p.c.pos : ℕ) + 1 + k :=
      ⟨geom.nrHops - ((x.2.p.c.pos : ℕ) + 1), by omega⟩
    rw [hk, Nat.add_sub_cancel_left, Nat.mul_add,
      Nat.mul_comm geom.perHopRoutingInfoLength ((x.2.p.c.pos : ℕ) + 1),
      Nat.mul_comm geom.perHopRoutingInfoLength k]
    omega
  have hcsz := combStream_size nike geom (spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith
      nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default),
      default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (Function.update (keysKs geom
      streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default
      x.2.y, x.2.p)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.1)) hksI x.2.p.c.pos hjp
      ((Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      (Util.Bytes.ofVector x.2.U)) x.2.p.c.pos) ((lastFrag geom (RSOR.path nike ((fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos) ++
      (if geom.nrHops > (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]).size then (RSOR.filler nike geom (RSOR.path
      nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
      [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1) else
      ByteArray.empty))
    (hks1 x.2.p.c.pos) (spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike kdfS
        ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default)
        default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray)
        (keysTag macS (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path
        nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray))
        (spliceAt x.2.p.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey x.2.d').getD
        default) (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path
        nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
        default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS ((nike.decodePrivateKey
        x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
        x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem nike (tailOf
        nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
        [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
        ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (RSOR.filler nike geom (RSOR.path
        nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
  have hksC : ∀ k, ((Function.update (spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith nike
      kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default),
      default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) x.2.p.c.pos (combStream nike geom
      (spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey
      x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS
      (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray))
      (Function.update (keysKs geom streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.1))
      x.2.p.c.pos ((Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) x.2.p.c.pos) ((lastFrag geom (RSOR.path nike ((fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
      ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).receiver]) x.2.p.c.pos) ++ (if geom.nrHops > (RSOR.path nike ((fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size then
      (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).1) else ByteArray.empty)) (spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike
      kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default),
      default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike kdfS ((nike.decodePrivateKey
      x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos x.2.y.2.2).2.toArray)) (spliceAt x.2.p.c.pos (blindElem nike (groupElem nike
      ((nike.decodePrivateKey x.2.d').getD default) (hopKeysWith nike kdfS ((nike.decodePrivateKey
      x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS
      ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem
      nike (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (RSOR.filler nike geom (RSOR.path
      nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]))) k).size = (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) := fun k => by
    by_cases hk : k = (x.2.p.c.pos : ℕ)
    · rw [hk, Function.update_self]
      exact hcsz
    · rw [Function.update_of_ne hk]
      exact hks0 k
  have hcmd : (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])[(x.2.p.c.pos :
      ℕ)]!.commands = [] := by
    rw [RSOR.path_getElem! nike _ _ _ hpos]
    exact ite_eq_right (by omega)
  have hgeEq : ∀ i, i ≤ (x.2.p.c.pos : ℕ) → (spliceAt x.2.p.c.pos (blindElem nike (groupElem nike
      ((nike.decodePrivateKey x.2.d').getD default) (hopKeysWith nike kdfS ((nike.decodePrivateKey
      x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS
      ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem
      nike (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) i = (blindElem nike (groupElem nike
      (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
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
      hmactag h16 x.2)) default)).toArray) i := fun i hi => by
    rw [spliceAt_le _ _ _ i hi]
    exact blindElem_congr_lt nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey
        ((nike.decodePrivateKey x.2.d').getD default)))) _ _ i fun n hn =>
      congrArg HopKeys.blindingFactor (hkeys n (by omega)).symm
  have hksF : ∀ m, m < (x.2.p.c.pos : ℕ) → (spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith
      nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default),
      default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) m = (Function.update (keysKs geom
      streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) m
      := fun m hm => by
    rw [spliceAt_le _ _ _ m (by omega), Function.update_of_ne (by omega)]
    unfold keysKs
    rw [hkeys m hm]
  have hM := hdrMsg_comb nike geom (spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith nike
      kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default),
      default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (Function.update (keysKs geom
      streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default
      x.2.y, x.2.p)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.1)) (Function.update (keysKs geom
      streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U))
      (spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey
      x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike
      kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (keysTag macS
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) default)).toArray) (spliceAt x.2.p.c.pos (blindElem nike (groupElem nike
      ((nike.decodePrivateKey x.2.d').getD default) (hopKeysWith nike kdfS ((nike.decodePrivateKey
      x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS
      ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem
      nike (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (blindElem nike (groupElem nike
      (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
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
      hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.filler nike geom (RSOR.path nike ((fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
      ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) (RSOR.path nike ((fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
      ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).receiver])
    x.2.p.c.pos hjP hnnh (by omega) hrouting hnP (hfillOf _ _) hks0 hksI hks1 htag0 hcmd hTj
    (hge0 ((x.2.p.c.pos : ℕ) + 1)) hszP1.symm (lastFrag geom (RSOR.path nike ((fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]) x.2.p.c.pos) hFr hX' (hgeEq _ le_rfl) hksF
  have hfront : ∀ i < (x.2.p.c.pos : ℕ), (Function.update (spliceAt x.2.p.c.pos (keysKs geom
      streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default,
      default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) x.2.p.c.pos (combStream nike geom
      (spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey
      x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS
      (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray))
      (Function.update (keysKs geom streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.1))
      x.2.p.c.pos ((Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) x.2.p.c.pos) ((lastFrag geom (RSOR.path nike ((fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
      ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).receiver]) x.2.p.c.pos) ++ (if geom.nrHops > (RSOR.path nike ((fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size then
      (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).1) else ByteArray.empty)) (spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike
      kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default),
      default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike kdfS ((nike.decodePrivateKey
      x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos x.2.y.2.2).2.toArray)) (spliceAt x.2.p.c.pos (blindElem nike (groupElem nike
      ((nike.decodePrivateKey x.2.d').getD default) (hopKeysWith nike kdfS ((nike.decodePrivateKey
      x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS
      ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem
      nike (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (RSOR.filler nike geom (RSOR.path
      nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]))) i = (Function.update (keysKs geom
      streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) i
      ∧ (spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey
          x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
          x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
          x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (keysTag macS (tailOf
          nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) i = (keysTag macS
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) i ∧ (spliceAt
          x.2.p.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey x.2.d').getD default)
          (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike
          x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
          default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS ((nike.decodePrivateKey
          x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
          x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
          x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem nike (tailOf
          nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
          ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) i = (blindElem nike
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
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) i
          ∧ (spliceAt x.2.p.c.pos (keysEnc cipher (hopKeysWith nike kdfS ((nike.decodePrivateKey
          x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
          x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
          x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (keysEnc cipher (tailOf
          nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) i = (keysEnc cipher
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) i
      ∧ (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])[i]!.commands =
          (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
          (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver])[i]!.commands ∧ (RSOR.path
          nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])[i + 1]!.id = (RSOR.path nike
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
          hvalid hmactag h16 x.2).2.2.o).receiver])[i + 1]!.id := fun i hi => by
    have hb1 : i < (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length :=
      lt_of_lt_of_eq (Nat.lt_succ_of_lt hi) hlen1.symm
    have hb2 : i < x.2.p.c.req.fwd.hops.length := by omega
    have hb3 : i + 1 < (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length :=
      lt_of_lt_of_eq (Nat.succ_lt_succ hi) hlen1.symm
    have hb4 : i + 1 < x.2.p.c.req.fwd.hops.length := by omega
    refine ⟨?_, ?_, hgeEq i (by omega), ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega)]
      exact hksF i hi
    · rw [spliceAt_le _ _ _ i (by omega)]
      funext m
      unfold keysTag
      rw [hkeys i hi]
    · rw [spliceAt_le _ _ _ i (by omega)]
      funext m
      unfold keysEnc
      rw [hkeys i hi]
    · rw [hP1, RSOR.path_getElem! nike _ _ i hb2, RSOR.path_getElem! nike _ _ i hb1]
      have hne : ¬ i + 1 = (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length := by
        rw [hlen1]
        omega
      exact (ite_eq_right (by omega)).trans (ite_eq_right hne).symm
    · rw [hP1, RSOR.path_getElem! nike _ _ (i + 1) hb4, RSOR.path_getElem! nike _ _ (i + 1) hb3]
      exact congrArg (fun h : Protocols.RSOR.Hop Name (RSOR.Key nike) => h.name)
        List.getElem_take.symm
  have htail : ∀ i, (x.2.p.c.pos : ℕ) < i → (Function.update (keysKs geom streamS (nextKeysI nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector x.1)) i = (Function.update (spliceAt x.2.p.c.pos (keysKs
      geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path
      nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
      default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) x.2.p.c.pos (combStream nike geom
      (spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey
      x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS
      (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray))
      (Function.update (keysKs geom streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.1))
      x.2.p.c.pos ((Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) x.2.p.c.pos) ((lastFrag geom (RSOR.path nike ((fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
      ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).receiver]) x.2.p.c.pos) ++ (if geom.nrHops > (RSOR.path nike ((fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size then
      (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).1) else ByteArray.empty)) (spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike
      kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default),
      default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike kdfS ((nike.decodePrivateKey
      x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos x.2.y.2.2).2.toArray)) (spliceAt x.2.p.c.pos (blindElem nike (groupElem nike
      ((nike.decodePrivateKey x.2.d').getD default) (hopKeysWith nike kdfS ((nike.decodePrivateKey
      x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS
      ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem
      nike (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (RSOR.filler nike geom (RSOR.path
      nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]))) i
      ∧ (keysTag macS (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4
          default x.2.y, x.2.p)).toArray) i = (spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike
          kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default),
          default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike kdfS
          ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) i ∧ (blindElem nike
          (groupElem nike ((nike.decodePrivateKey x.2.p.d0).getD default) (nextKeysI nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray 0)
          (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y,
          x.2.p)).toArray) i = (spliceAt x.2.p.c.pos (blindElem nike (groupElem nike
          ((nike.decodePrivateKey x.2.d').getD default) (hopKeysWith nike kdfS
          ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default)
          default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray
          0) (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike
          x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
          default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]).size).toArray) (blindElem nike (tailOf nike kdfS
          ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
          ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) i ∧ (keysEnc cipher
          (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y,
          x.2.p)).toArray) i = (spliceAt x.2.p.c.pos (keysEnc cipher (hopKeysWith nike kdfS
          ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default)
          default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]).size).toArray) (keysEnc cipher (tailOf nike kdfS
          ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) i := fun i hi => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        spliceAt_gt _ _ _ i hi, hTail]
      dsimp only
      unfold keysKs
      rw [hdrop i hi]
    · rw [spliceAt_gt _ _ _ i hi, hTail]
      dsimp only
      funext m
      unfold keysTag
      rw [hdrop i hi]
    · rw [spliceAt_gt _ _ _ i hi, hTail]
      dsimp only
      rw [groupElem_eq_blindElem nike ((nike.decodePrivateKey x.2.p.d0).getD default) (nextKeysI
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y,
          x.2.p)).toArray (x.2.p.c.pos + 1), blindElem_drop,
        show (x.2.p.c.pos : ℕ) + 1 + (i - (x.2.p.c.pos + 1)) = i by omega]
    · rw [spliceAt_gt _ _ _ i hi, hTail]
      dsimp only
      funext m
      unfold keysEnc
      rw [hdrop i hi]
  have hpad := (padAt_combStream nike geom (spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith
      nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default),
      default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
      ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (Function.update (keysKs geom
      streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default
      x.2.y, x.2.p)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.1)) hks0 hksI x.2.p.c.pos hjp
      ((Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
      (Util.Bytes.ofVector x.2.U)) x.2.p.c.pos) ((lastFrag geom (RSOR.path nike ((fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos) ++
      (if geom.nrHops > (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]).size then (RSOR.filler nike geom (RSOR.path
      nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
      [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1) else
      ByteArray.empty))
    (hks1 x.2.p.c.pos) (spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike kdfS
        ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default)
        default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray)
        (keysTag macS (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path
        nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray))
        (spliceAt x.2.p.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey x.2.d').getD
        default) (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path
        nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
        default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS ((nike.decodePrivateKey
        x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
        x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem nike (tailOf
        nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
        [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
        ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (RSOR.filler nike geom (RSOR.path
        nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])).symm
  have e : spliceAt x.2.p.c.pos (Function.update (keysKs geom streamS (hopKeysWith nike kdfS
      ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) x.2.p.c.pos
      (Util.Bytes.ofVector (finComb nike cipher macS kdfS streamS geom hvalid hmactag h16 x)))
          (keysKs geom streamS (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default)
          (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos
          x.2.y.2.2).2.toArray)
      = Function.update (spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS
          ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default)
          default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
          ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) x.2.p.c.pos
          (combStream nike geom (spliceAt x.2.p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS
          ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default)
          default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
          ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (Function.update
          (keysKs geom streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16
          (keys4 default x.2.y, x.2.p)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.1)) x.2.p.c.pos
          ((Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
          default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) x.2.p.c.pos) ((lastFrag geom
          (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
          (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos) ++ (if
          geom.nrHops > (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
          h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size then
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
          streamS geom hvalid hmactag h16 x.2).2.2.o).1) else ByteArray.empty)) (spliceAt
          x.2.p.c.pos (keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD
          default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos
          (restKeys ((default, default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike kdfS
          ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (spliceAt
          x.2.p.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey x.2.d').getD default)
          (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike
          x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
          default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS ((nike.decodePrivateKey
          x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
          x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
          x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem nike (tailOf
          nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
          ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (RSOR.filler nike
          geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1)
          (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])) := by
    rw [spliceAt_update]
    unfold finComb
    rw [Util.Bytes.ofVector_toVecN _ hcsz]
  refine ⟨by
    rw [← hM]
    exact hdrMsg_size nike geom _ (spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike kdfS
        ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default)
        default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray)
        (keysTag macS (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path
        nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray))
        (spliceAt x.2.p.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey x.2.d').getD
        default) (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path
        nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
        default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS ((nike.decodePrivateKey
        x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
        x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem nike (tailOf
        nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
        [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
        ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) _ _ x.2.p.c.pos hjP hnnh (by
        omega) hrouting hnP
      (hfillOf _ _) hksC htag0 hcmd ((nikeHdrTrace_isSome geom _ _ _ _ _ _ _ _ (RSOR.path nike
          x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) _).trans hTj)
      (hge0 x.2.p.c.pos), ?_⟩
  rw [blindPost_fn nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E _ _ hn hTj]
  show fnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 A ((forwardPay nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km,
      default, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))) ((forwardPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) A).reply (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, default,
      (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2)))) x.2.p.st x.2.p.log x.2.p.c.req x.2.o.1
      x.2.p.c.pos x.2.km x.2.u g
    (spliceAt x.2.p.c.pos (Function.update (keysKs geom streamS (hopKeysWith nike kdfS
        ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default)
        default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray)
        x.2.p.c.pos
      (Util.Bytes.ofVector (finComb nike cipher macS kdfS streamS geom hvalid hmactag h16 x)))
          (keysKs geom streamS (tailOf nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default)
          (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos
          x.2.y.2.2).2.toArray))
    (spliceAt x.2.p.c.pos (keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD
        default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos
        (restKeys ((default, default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd
        [.recipient x.2.p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike kdfS
        ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (spliceAt x.2.p.c.pos (keysEnc
        cipher (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
        default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]).size).toArray) (keysEnc cipher (tailOf nike kdfS
        ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (spliceAt x.2.p.c.pos (blindElem
        nike (groupElem nike ((nike.decodePrivateKey x.2.d').getD default) (hopKeysWith nike kdfS
        ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default, default, default), default)
        default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray
        0) (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
        default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]).size).toArray) (blindElem nike (tailOf nike kdfS
        ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS ((nike.decodePrivateKey
        x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
        x.2.p.c.pos x.2.y.2.2).2.toArray)) = _
  rw [e]
  exact fnRun_eq_short nike cipher macS kdfS streamS geom hvalid hmactag h16 A ((forwardPay nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
      (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))) ((forwardPay nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) A).reply (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km,
      default, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))) x.2.p.st x.2.p.log x.2.p.c.req ((fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) x.2.o.1 ((fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2.o) x.2.p.c.pos x.2.km x.2.u g
    _ (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
        x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (Function.update (keysKs geom streamS (nextKeysI
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y,
        x.2.p)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.1)) (spliceAt x.2.p.c.pos (keysTag macS
        (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
        default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike kdfS
        ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (keysTag macS (forwardKeys0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2)) default)).toArray) (keysTag macS (nextKeysI nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) (spliceAt x.2.p.c.pos (keysEnc
        cipher (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
        default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]).size).toArray) (keysEnc cipher (tailOf nike kdfS
        ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (keysEnc cipher (forwardKeys0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2)) default)).toArray) (keysEnc cipher (nextKeysI nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) (spliceAt
        x.2.p.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey x.2.d').getD default)
        (hopKeysWith nike kdfS ((nike.decodePrivateKey x.2.d').getD default) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos (restKeys ((default,
        default, default), default) default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS ((nike.decodePrivateKey
        x.2.d').getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
        x.2.p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size).toArray) (blindElem nike (tailOf
        nike kdfS ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd
        [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).1 (tailOf nike kdfS
        ((nike.decodePrivateKey x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2).2.toArray)) (blindElem nike (groupElem nike
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
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike (groupElem nike
        ((nike.decodePrivateKey x.2.p.d0).getD default) (nextKeysI nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray 0) (nextKeysI nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (keys4 default x.2.y, x.2.p)).toArray) hjP
        hszP1.symm hnP
    hT hT' hb hb' hksC htag0 htag1 hge0 hge1p hfront
    (by rw [spliceAt_le _ _ _ 0 (Nat.zero_le _)]; rfl) hM htail hpad hcmd

/-- **World 1 on a draw is the blinding adversary's game on the joined keystream**, before
the end of the path: with a block `g` drawn for a changed payload. This holds when both paths
build, both bodies have a payload's length, and the relay would not reply to the
replacement. -/
theorem finOwnRun_blindPost (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool)
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A)
    (hn : (x.2.p.c.pos : ℕ) + 1 < x.2.p.c.req.fwd.hops.length)
    (hT : pathBuilds geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
        (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size) (hT' : pathBuilds
        geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) (RSOR.path nike ((fwd1
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
        geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd
        [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o).receiver]).size)
    (hb : (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1).size =
        geom.forwardPayloadLength)
    (hb' : (RSOR.body nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.o)).size = geom.forwardPayloadLength) (hrep : finNoReply nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x) :
    finOwnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A x
      =ᵈ $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) >>= fun g =>
        blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (finComb nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x, x.2.km, (toDraw0 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2), x.2.u, g) (tailOf nike kdfS ((nike.decodePrivateKey
            x.2.p.d0).getD default) (RSOR.path nike x.2.p.c.req.fwd [.recipient
            x.2.p.c.req.receiver]) x.2.p.c.pos x.2.y.2.2) := by
  have h := fun g => blindPost_comb nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E
      x g hn hT hT' hb hb'
  refine (finRun_layerFn nike cipher macS kdfS streamS geom hvalid hmactag h16 names A x hn hT' hb'
      (h default).1 hrep).trans ?_
  exact EvalDistEq.bind_right _ fun g => by
    rw [(h g).2]

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
