/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUDraws

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

/-! # The last comparison of the two worlds of TLU→, for NIKE Sphinx

After the steps of `NIKESphinxTLU.lean` and `NIKESphinxTLUNext.lean` each world is played from
uniform keystreams. Here the two are compared; the lemmas are in `NIKESphinxTLUFn.lean`,
`NIKESphinxTLURelay.lean`, `NIKESphinxTLUBlind.lean`, `NIKESphinxTLUWorld1.lean`,
`NIKESphinxTLUJoin.lean` and `NIKESphinxTLUDraws.lean`. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

set_option maxHeartbeats 16000000 in
/-- **World 1's relay does not reply to the replacement**, before the end of the path: the
replacement has no reply block, and a changed payload is decrypted to the block `x.2.v`, which
the relay refuses unless it begins with the zero tag. -/
theorem finNoReply_of (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names A)
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
    (hv : ¬ ((Util.Bytes.ofVector x.2.v).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
        : finNoReply nike cipher macS kdfS streamS geom hvalid hmactag h16 x := by
  intro m o ho
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hpos : (x.2.p.c.pos : ℕ) < x.2.p.c.req.fwd.hops.length := x.2.p.c.pos.isLt
  have hlen1 : (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length = x.2.p.c.pos + 1 := by
    show (List.take ((x.2.p.c.pos : ℕ) + 1) x.2.p.c.req.fwd.hops).length = x.2.p.c.pos + 1
    rw [List.length_take]
    omega
  have hpos1 : (x.2.p.c.pos : ℕ) < (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length :=
    lt_of_lt_of_eq (Nat.lt_succ_self _) hlen1.symm
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
  have hnP1 : (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]).size ≤ geom.nrHops := by
    have h2 : x.2.p.c.req.fwd.hops.length ≤ geom.nrHops := x.2.p.c.req.fwd.length_le
    omega
  have hfill : (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
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
      x.2).2.2.o).1).size = (geom.nrHops - (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size) *
      geom.perHopRoutingInfoLength := by
    have hmul : (geom.nrHops - (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size) *
        geom.perHopRoutingInfoLength
        ≤ geom.routingInfoLength := by
      rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
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
  have htg1 : ∀ i m, ((Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km)
      (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
      (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
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
      i m).size = macLength := fun i m => by
    by_cases hi : i = (x.2.p.c.pos : ℕ)
    · rw [hi, Function.update_self]
      exact (Util.Bytes.size_ofVector _).trans hmactag
    · rw [Function.update_of_ne hi]
      exact (Util.Bytes.size_ofVector _).trans hmactag
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
  have hcmds : (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver])[(x.2.p.c.pos : ℕ)]!.commands =
      [RoutingCommand.recipient x.2.o.2.2.1] := by
    rw [hP1, RSOR.path_getElem! nike _ _ _ hpos1]
    exact ite_eq_left hlen1.symm
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
  have hL : layerHdr geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (Function.update (keysTag macS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector
      x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
      geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom
      (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1)
      (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))))) (blindElem nike (groupElem nike (drawKey
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S :=
      𝒮)) .relay names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
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
      geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos
      = (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
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
          x.2).2.2.o).receiver]) x.2.p.c.pos) ++ Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector
          x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
          geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U))
          (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike
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
          x.2).2.2.o).receiver]) x.2.p.c.pos)))) := by
    unfold layerHdr
    rw [hdrMsg_update_tag geom _ _ _ _ _ x.2.p.c.pos (by rw [hszP1]; omega), Function.update_self]
  have ho' : Util.Bytes.ofVector o.1 = layerHdr geom (Function.update (keysKs geom streamS
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
      (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (next4X nike cipher macS kdfS
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
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos := by
    rw [ho, hMINE, hlast, hL]
    exact Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, hMsz, Util.Bytes.size_ofVector, hhdr, had, hmactag])
  have hproc := procD_join_last nike geom (strTag nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2) x.2.U) (Util.Bytes.ofVector x.2.U)
      (restKeys (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default).1
      default) ((fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).plain
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) else x.2.v) o.2)
    (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
        x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (Function.update (keysTag macS (forwardKeys0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2)) default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac
        (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
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
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))))) (blindElem nike
        (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
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
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos o hszP1.symm hnnh (by
        omega) hrouting hnP1 hfill hks1 htg1
    hge1p F0 hF0
    (by
      rw [hcmds]
      intro c hc
      rw [List.mem_singleton] at hc
      rw [hc]
      intro hcon
      cases hcon)
    (by rw [hcmds]; rfl) (by rw [hcmds]; rfl) (Function.update_self _ _ _)
    (by rw [Function.update_self]; rfl) ho' (by omega)
  rw [hproc, hcmds]
  by_cases hu : o.2 = x.2.u
  · have hz : ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)).size =
      geom.payloadTagLength := Array.size_replicate
    have hD : (fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        A).plain (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) else x.2.v) o.2 = Util.Bytes.toVecN _
        (((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)) ++ (RSOR.body nike macS kdfS
        streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
        (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o))) := by
      show (if o.2 = x.2.u then Util.Bytes.toVecN _ (encTrace (keysEnc cipher (forwardKeys0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.path nike ((fwd1 nike cipher macS
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
          x.2).2.2.o).receiver]).size
        (((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)) ++ (RSOR.body nike macS kdfS
            streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
            (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o))) ((RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
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
            x.2).2.2.o).receiver]).size - 1 - x.2.p.c.pos)) else x.2.v) = _
      rw [ite_eq_left hu, show (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size - 1 -
          (x.2.p.c.pos : ℕ) = 0 by omega]
      rfl
    have hpl := Util.Bytes.extract_append_right ((⟨Array.replicate geom.payloadTagLength 0⟩ :
        ByteArray)) (RSOR.body nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
        hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid
        hmactag h16 x.2).2.2.o))
    rw [hz, hb'] at hpl
    rw [hD, Util.Bytes.ofVector_toVecN _ (by rw [ByteArray.size_append, hz, hb']), hpl]
    split
    · unfold replyOf
      exact ite_eq_right fun hc => absurd hc.2 (by
        rw [body_get_zero nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
            h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.o) rfl]
        decide)
    · rfl
  · have hD : (fun y => if y = x.2.u then (forwardPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A).plain
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2)) else x.2.v) o.2 = x.2.v := ite_eq_right hu
    rw [hD, ite_eq_right hv]
    rfl

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
