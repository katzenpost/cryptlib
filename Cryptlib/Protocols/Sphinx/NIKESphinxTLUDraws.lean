/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUJoin

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

/-! # The last comparison of TLU→ for NIKE Sphinx: the two worlds over their draws

For fixed game draws before the end of the path, world 1 is world 0 with the hops after the
relay from an independent secret. -/

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

/-! ## The two worlds for fixed game draws, before the end of the path -/

/-- The draws of world 1's last game after the game's own: the keystream of the original's
next layer, the relay's other draws for the original, the replacement's keystream, MAC key and
blinding seed, the challenger's draws, the replacement's secret, and the cipher's two blocks. -/
abbrev FinRest (names : Role → Name) : Type :=
  KEMSphinx.Keystream geom × (Vector UInt8 48 × Vector UInt8 32 × Vector UInt8 32) ×
      KEMSphinx.Keystream geom × Vector UInt8 32 × Vector UInt8 32 × (fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).Oth × Vector UInt8 nike.privateKeySize × (Vector UInt8
      (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
      geom.forwardPayloadLength))

/-- The draw of `FinRest`. -/
def finRest (names : Role → Name) : ProbComp (FinRest nike cipher macS kdfS streamS geom hvalid
    hmactag h16 names) := do
  let W ← $ᵗ (KEMSphinx.Keystream geom)
  let y ← $ᵗ (Vector UInt8 48 × Vector UInt8 32 × Vector UInt8 32)
  let U ← $ᵗ (KEMSphinx.Keystream geom)
  let km ← $ᵗ (Vector UInt8 32)
  let seed ← $ᵗ (Vector UInt8 32)
  let o ← shortDraw nike geom
  let d' ← $ᵗ (Vector UInt8 nike.privateKeySize)
  let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  return (W, y, U, km, seed, o, d', u, v)

/-- A draw of world 1's last game, from the game's draws and the rest. -/
def finX {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (p : NextPre nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) (r : FinRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) : KEMSphinx.Keystream geom × Next4
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names A :=
  (r.1, ⟨default, r.2.1, p, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1,
    r.2.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.2⟩)

/-- **World 1's last game draws the game's draws first.** -/
theorem finDraw_bind {δ : Type} (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary)
    (F : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A → ProbComp δ) :
    (finDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 names A >>= F)
      =ᵈ (nextPre nike cipher macS kdfS streamS geom hvalid hmactag h16 names A >>= fun p =>
        finRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names >>= fun r => F (finX
            nike cipher macS kdfS streamS geom hvalid hmactag h16 p r)) := by
  unfold finDraw next4Rest finRest
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun W =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- The draws of world 1's last game on which the last comparison is exact before the end of
the path: both paths build, both bodies have a payload's length, and the block a changed
payload is decrypted to does not begin with the zero tag. -/
def finGood {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) : Prop :=
  pathBuilds geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) (RSOR.path
      nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size ∧ pathBuilds geom (RSOR.path
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
      x.2).2.2.o).receiver]) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2.o).receiver]).size
    ∧ (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1).size = geom.forwardPayloadLength
        ∧ (RSOR.body nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.o)).size = geom.forwardPayloadLength
    ∧ ¬ ((Util.Bytes.ofVector x.2.v).extract 0 geom.payloadTagLength).data.all (· == 0) = true

/-- **For fixed game draws before the end of the path, world 1 is the blinding adversary's
game on the joined keystream**, off the draws that are not good. -/
theorem finRest_sub_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) (p : NextPre nike cipher macS kdfS streamS geom
    hvalid hmactag h16 names A)
    (hn : (p.c.pos : ℕ) + 1 < p.c.req.fwd.hops.length) :
    |(Pr{let b ← (finRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names >>= fun r =>
        finOwnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (finX nike cipher
        macS kdfS streamS geom hvalid hmactag h16 p r))}[b =
        true]).toReal
      - (Pr{let b ← (finRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names >>= fun r
          => $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) >>= fun g =>
          blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (finComb nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (finX nike cipher macS kdfS streamS
              geom hvalid hmactag h16 p r), (finX nike cipher macS kdfS streamS geom hvalid hmactag
              h16 p r).2.km, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X
              nike cipher macS kdfS streamS geom hvalid hmactag h16 (finX nike cipher macS kdfS
              streamS geom hvalid hmactag h16 p r).2).2.2),
            (finX nike cipher macS kdfS streamS geom hvalid hmactag h16 p r).2.u, g) (tailOf nike
                kdfS ((nike.decodePrivateKey (finX nike cipher macS kdfS streamS geom hvalid
                hmactag h16 p r).2.p.d0).getD default) (RSOR.path nike (finX nike cipher macS kdfS
                streamS geom hvalid hmactag h16 p r).2.p.c.req.fwd [.recipient (finX nike cipher
                macS kdfS streamS geom hvalid hmactag h16 p r).2.p.c.req.receiver]) (finX nike
                cipher macS kdfS streamS geom hvalid hmactag h16 p r).2.p.c.pos (finX nike cipher
                macS kdfS streamS geom hvalid hmactag h16 p r).2.y.2.2))}[b = true]).toReal|
    ≤ (Pr{let r ← (finRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names)}[¬ finGood
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (finX nike cipher macS kdfS streamS
        geom hvalid hmactag h16 p r)]).toReal :=
  KEMSphinx.abs_prEvent_bind_sub_le_bad_dist _ _ _ (fun r => ¬ finGood nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (finX nike cipher macS kdfS streamS geom hvalid hmactag h16 p
      r))
    fun r hr => by
      obtain ⟨hT, hT', hb, hb', hv⟩ := not_not.mp hr
      exact finOwnRun_blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E
          (finX nike cipher macS kdfS streamS geom hvalid hmactag h16 p r) hn hT hT' hb hb'
        (finNoReply_of nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (finX nike
            cipher macS kdfS streamS geom hvalid hmactag h16 p r) hn hT' hb'
          (blindPost_comb nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (finX
              nike cipher macS kdfS streamS geom hvalid hmactag h16 p r) default hn hT hT' hb
              hb').1 hv)

set_option maxHeartbeats 4000000 in
/-- **The joined keystream reads the two keystreams through one pad**: the head of the
replacement's keystream under a mask of the tail of the other, and that tail under a fixed
mask. -/
theorem finComb_eq (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (p : NextPre nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) (W :
    KEMSphinx.Keystream geom)
    (y : Vector UInt8 48 × Vector UInt8 32 × Vector UInt8 32) (U1 : KEMSphinx.Keystream geom)
    (km seed1 : Vector UInt8 32) (o : (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).Oth) (d' : Vector UInt8 nike.privateKeySize)
    (u v1 : Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) :
    finComb nike cipher macS kdfS streamS geom hvalid hmactag h16 (finX nike cipher macS kdfS
        streamS geom hvalid hmactag h16 p (W, y, U1, km, seed1, o, d', u, v1))
      = Util.Bytes.toVecN _
        (xorBytes ((Util.Bytes.ofVector U1).extract 0 ((geom.routingInfoLength +
            geom.perHopRoutingInfoLength) - ((p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength))
            (xorBytes ((lastFrag geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
                hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS
                streamS geom hvalid hmactag h16 names p.k.1) o).fwd [.recipient ((fwd1 nike cipher
                macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names p.k.1) o).receiver])
                p.c.pos) ++ (if geom.nrHops > (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS
                geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS
                streamS geom hvalid hmactag h16 names p.k.1) o).fwd [.recipient ((fwd1 nike cipher
                macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names p.k.1)
                o).receiver]).size then (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher
                macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh
                nike cipher macS kdfS streamS geom hvalid hmactag h16 names p.k.1) o).fwd
                [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
                (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
                names p.k.1) o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
                h16 names).rnd o).1) else ByteArray.empty)) (hopContent nike geom (Function.update
                (spliceAt p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS
                ((nike.decodePrivateKey d').getD default) (RSOR.path nike p.c.req.fwd [.recipient
                p.c.req.receiver]) p.c.pos (restKeys ((default, default, default), default)
                default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]).size).toArray)
                (keysKs geom streamS (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default)
                (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos
                y.2.2).2.toArray)) p.c.pos
              (KEMSphinx.zeroBytes ((geom.routingInfoLength + geom.perHopRoutingInfoLength) -
                  ((p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength)
                ++ xorBytes ((Util.Bytes.ofVector W).extract ((geom.routingInfoLength +
                    geom.perHopRoutingInfoLength) - ((p.c.pos : ℕ) + 1) *
                    geom.perHopRoutingInfoLength) (geom.routingInfoLength +
                    geom.perHopRoutingInfoLength)) (padMask geom (spliceAt p.c.pos (keysKs geom
                    streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey d').getD default)
                    (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos (restKeys
                    ((default, default, default), default) default) (RSOR.path nike p.c.req.fwd
                    [.recipient p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike
                    kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                    [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (keysKs geom streamS
                    (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default
                    y, p)).toArray) p.c.pos)))
              (spliceAt p.c.pos (keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey
                  d').getD default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver])
                  p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
                  p.c.req.fwd [.recipient p.c.req.receiver]).size).toArray) (keysTag macS (tailOf
                  nike kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (spliceAt p.c.pos
                  (blindElem nike (groupElem nike ((nike.decodePrivateKey d').getD default)
                  (hopKeysWith nike kdfS ((nike.decodePrivateKey d').getD default) (RSOR.path nike
                  p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default, default,
                  default), default) default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS
                  ((nike.decodePrivateKey d').getD default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]) p.c.pos (restKeys ((default, default, default), default)
                  default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]).size).toArray) (blindElem nike (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).1 (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (RSOR.filler nike geom
                  (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) o.1.1) (RSOR.path nike
                  p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos))
          ++ xorBytes ((Util.Bytes.ofVector W).extract ((geom.routingInfoLength +
              geom.perHopRoutingInfoLength) - ((p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength)
              (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (padMask geom (spliceAt
              p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey d').getD
              default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos (restKeys
              ((default, default, default), default) default) (RSOR.path nike p.c.req.fwd
              [.recipient p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
              ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd [.recipient
              p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (keysKs geom streamS (nextKeysI nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default y, p)).toArray)
              p.c.pos)) := by
  have hm : padMask geom (spliceAt p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS
      ((nike.decodePrivateKey d').getD default) (RSOR.path nike p.c.req.fwd [.recipient
      p.c.req.receiver]) p.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]).size).toArray) (keysKs geom
      streamS (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike
      p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (Function.update
      (keysKs geom streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4
      default y, p)).toArray) p.c.pos (Util.Bytes.ofVector W)) p.c.pos = (padMask geom (spliceAt
      p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey d').getD default)
      (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default,
      default, default), default) default) (RSOR.path nike p.c.req.fwd [.recipient
      p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
      ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd [.recipient
      p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (keysKs geom streamS (nextKeysI nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (keys4 default y, p)).toArray) p.c.pos) :=
    padMask_congr geom _ _ _ (fun k => by
      by_cases hk : k = (p.c.pos : ℕ)
      · rw [hk, Function.update_self]
        exact Util.Bytes.size_ofVector _
      · rw [Function.update_of_ne hk]
        exact streamS.keystream_size _ _ _) (fun k => streamS.keystream_size _ _ _) p.c.pos
      (fun i hi => Function.update_of_ne (by omega) _ _)
  show Util.Bytes.toVecN _ (combStream nike geom (spliceAt p.c.pos (keysKs geom streamS
      (hopKeysWith nike kdfS ((nike.decodePrivateKey d').getD default) (RSOR.path nike p.c.req.fwd
      [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default, default, default), default)
      default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]).size).toArray) (keysKs
      geom streamS (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike
      p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (Function.update
      (keysKs geom streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4
      default y, p)).toArray) p.c.pos (Util.Bytes.ofVector W)) p.c.pos ((Function.update (keysKs
      geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) ((km, seed1, (⟨p.k, p.keys, p.c,
      p.st, p.log, o, d'⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names).Oth A)) : StrX nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) A))
      default)).toArray) p.c.pos (Util.Bytes.ofVector U1)) p.c.pos) ((lastFrag geom (RSOR.path nike
      ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names p.k.1) o).fwd
      [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys,
      p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names p.k.1)
      o).receiver]) p.c.pos) ++ (if geom.nrHops > (RSOR.path nike ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names p.k.1) o).fwd [.recipient ((fwd1 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names p.k.1) o).receiver]).size then (RSOR.filler nike geom
      (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names p.k.1)
      o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
      (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names p.k.1)
      o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd o).1)
      else ByteArray.empty))
    (spliceAt p.c.pos (keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey d').getD
        default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos (restKeys
        ((default, default, default), default) default) (RSOR.path nike p.c.req.fwd [.recipient
        p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike kdfS ((nike.decodePrivateKey
        p.d0).getD default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos
        y.2.2).2.toArray)) (spliceAt p.c.pos (blindElem nike (groupElem nike
        ((nike.decodePrivateKey d').getD default) (hopKeysWith nike kdfS ((nike.decodePrivateKey
        d').getD default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos
        (restKeys ((default, default, default), default) default) (RSOR.path nike p.c.req.fwd
        [.recipient p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS
        ((nike.decodePrivateKey d').getD default) (RSOR.path nike p.c.req.fwd [.recipient
        p.c.req.receiver]) p.c.pos (restKeys ((default, default, default), default) default)
        (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]).size).toArray) (blindElem nike
        (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
        [.recipient p.c.req.receiver]) p.c.pos y.2.2).1 (tailOf nike kdfS ((nike.decodePrivateKey
        p.d0).getD default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos
        y.2.2).2.toArray)) (RSOR.filler nike geom (RSOR.path nike p.c.req.fwd [.recipient
        p.c.req.receiver]) o.1.1) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver])) = _
  unfold combStream
  rw [hm, Function.update_self, Function.update_self, Util.Bytes.size_ofVector]

/-- The draws of `FinRest` after the two keystreams and the relay's draws for the original. -/
def finTail (names : Role → Name) : ProbComp (Vector UInt8 32 × Vector UInt8 32 × (fwd1 nike cipher
    macS kdfS streamS geom hvalid hmactag h16 names).Oth × Vector UInt8 nike.privateKeySize ×
    (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength))) := do
  let km ← $ᵗ (Vector UInt8 32)
  let seed ← $ᵗ (Vector UInt8 32)
  let o ← shortDraw nike geom
  let d' ← $ᵗ (Vector UInt8 nike.privateKeySize)
  let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  return (km, seed, o, d', u, v)

set_option maxHeartbeats 16000000 in
/-- **The joined keystream is uniform.** For fixed game draws, the blinding adversary's game
on the joined keystream of world 1's draws is its game on one uniform keystream, with the
original's randomness, the replacement's secret, and the blinding seed of the original's
relay for those of world 0. The draws it does not read drop out. -/
theorem finRest_comb_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool)
    (p : NextPre nike cipher macS kdfS streamS geom hvalid hmactag h16 names A) :
    (finRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names >>= fun r => $ᵗ (Vector
        UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) >>= fun g =>
        blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (finComb nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (finX nike cipher macS kdfS streamS
            geom hvalid hmactag h16 p r), (finX nike cipher macS kdfS streamS geom hvalid hmactag
            h16 p r).2.km, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (finX nike cipher macS kdfS
            streamS geom hvalid hmactag h16 p r).2).2.2),
          (finX nike cipher macS kdfS streamS geom hvalid hmactag h16 p r).2.u, g) (tailOf nike
              kdfS ((nike.decodePrivateKey (finX nike cipher macS kdfS streamS geom hvalid hmactag
              h16 p r).2.p.d0).getD default) (RSOR.path nike (finX nike cipher macS kdfS streamS
              geom hvalid hmactag h16 p r).2.p.c.req.fwd [.recipient (finX nike cipher macS kdfS
              streamS geom hvalid hmactag h16 p r).2.p.c.req.receiver]) (finX nike cipher macS kdfS
              streamS geom hvalid hmactag h16 p r).2.p.c.pos (finX nike cipher macS kdfS streamS
              geom hvalid hmactag h16 p r).2.y.2.2))
      =ᵈ (do
        let r0 ← $ᵗ (RSOR.Randomness nike geom)
        let d ← $ᵗ (Vector UInt8 nike.privateKeySize)
        let U ← $ᵗ (KEMSphinx.Keystream geom)
        let km ← $ᵗ (Vector UInt8 32)
        let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        let seed ← $ᵗ (Vector UInt8 32)
        blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U, km, (⟨p.k,
            p.keys, p.c, p.st, p.log, r0, d⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names).Oth A), u, v) (tailOf nike kdfS
            ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd [.recipient
            p.c.req.receiver]) p.c.pos seed)) := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have hjp : ((p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    have h1 : (p.c.pos : ℕ) < p.c.req.fwd.hops.length := p.c.pos.isLt
    have h2 : p.c.req.fwd.hops.length ≤ geom.nrHops := p.c.req.fwd.length_le
    rw [hrouting]
    exact (Nat.mul_comm _ _).le.trans (Nat.mul_le_mul_left _ (by omega))
  have hLN : ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - ((p.c.pos : ℕ) + 1) *
      geom.perHopRoutingInfoLength) + ((p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength =
      (geom.routingInfoLength + geom.perHopRoutingInfoLength) := by omega
  have hbody : ∀ (W : KEMSphinx.Keystream geom)
      (y : Vector UInt8 48 × Vector UInt8 32 × Vector UInt8 32) (U1 : KEMSphinx.Keystream geom)
      (t : Vector UInt8 32 × Vector UInt8 32 × (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).Oth × Vector UInt8 nike.privateKeySize × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) (g : Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength)),
      blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E
          (finComb nike cipher macS kdfS streamS geom hvalid hmactag h16 (finX nike cipher macS
              kdfS streamS geom hvalid hmactag h16 p (W, y, U1, t.1, t.2.1, t.2.2.1, t.2.2.2.1,
              t.2.2.2.2.1,
            t.2.2.2.2.2)), t.1, (⟨p.k, p.keys, p.c, p.st, p.log, t.2.2.1.1, t.2.2.2.1⟩ : PropDraw
                nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS
                kdfS streamS geom hvalid hmactag h16 names).Oth A), t.2.2.2.2.1, g) (tailOf nike
                kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                [.recipient p.c.req.receiver]) p.c.pos y.2.2)
        = (fun U => blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U,
            t.1, (⟨p.k, p.keys, p.c, p.st, p.log, t.2.2.1.1, t.2.2.2.1⟩ : PropDraw nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
            names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A),
            t.2.2.2.2.1, g) (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default)
            (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos y.2.2))
            (Util.Bytes.toVecN _
          (xorBytes ((Util.Bytes.ofVector U1).extract 0 ((geom.routingInfoLength +
              geom.perHopRoutingInfoLength) - ((p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength))
              ((fun yb => xorBytes ((lastFrag geom (RSOR.path nike ((fwd1 nike cipher macS kdfS
                  streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names p.k.1) t.2.2.1).fwd [.recipient
                  ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys,
                  p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
                  p.k.1) t.2.2.1).receiver]) p.c.pos) ++ (if geom.nrHops > (RSOR.path nike ((fwd1
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ :
                  ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names p.k.1)
                  t.2.2.1).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
                  h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
                  hvalid hmactag h16 names p.k.1) t.2.2.1).receiver]).size then (RSOR.filler nike
                  geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
                  names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
                  hmactag h16 names p.k.1) t.2.2.1).fwd [.recipient ((fwd1 nike cipher macS kdfS
                  streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names p.k.1) t.2.2.1).receiver]) ((fwd1
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd t.2.2.1).1) else
                  ByteArray.empty)) (hopContent nike geom (Function.update (spliceAt p.c.pos
                  (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey
                  t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]) p.c.pos (restKeys ((default, default, default), default)
                  default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) p.c.pos
                  (KEMSphinx.zeroBytes ((geom.routingInfoLength + geom.perHopRoutingInfoLength) -
                  ((p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength) ++ xorBytes yb (padMask geom
                  (spliceAt p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS
                  ((nike.decodePrivateKey t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default, default, default),
                  default) default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (keysKs geom streamS
                  (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default
                  y, p)).toArray) p.c.pos))) (spliceAt p.c.pos (keysTag macS (hopKeysWith nike kdfS
                  ((nike.decodePrivateKey t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default, default, default),
                  default) default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (spliceAt p.c.pos
                  (blindElem nike (groupElem nike ((nike.decodePrivateKey t.2.2.2.1).getD default)
                  (hopKeysWith nike kdfS ((nike.decodePrivateKey t.2.2.2.1).getD default)
                  (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos (restKeys
                  ((default, default, default), default) default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS
                  ((nike.decodePrivateKey t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default, default, default),
                  default) default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]).size).toArray) (blindElem nike (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).1 (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (RSOR.filler nike geom
                  (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) t.2.2.1.1.1)
                  (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos))
                  ((Util.Bytes.ofVector W).extract ((geom.routingInfoLength +
                  geom.perHopRoutingInfoLength) - ((p.c.pos : ℕ) + 1) *
                  geom.perHopRoutingInfoLength) (geom.routingInfoLength +
                  geom.perHopRoutingInfoLength)))
            ++ xorBytes ((Util.Bytes.ofVector W).extract ((geom.routingInfoLength +
                geom.perHopRoutingInfoLength) - ((p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength)
                (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (padMask geom (spliceAt
                p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey
                t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver])
                p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
                p.c.req.fwd [.recipient p.c.req.receiver]).size).toArray) (keysKs geom streamS
                (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike
                p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (keysKs geom
                streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4
                default y, p)).toArray) p.c.pos))) := fun W y U1 t g => by
    rw [finComb_eq]
  have h1 : (finRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names >>= fun r => $ᵗ
      (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)) >>= fun g =>
        blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (finComb nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (finX nike cipher macS kdfS streamS
            geom hvalid hmactag h16 p r), (finX nike cipher macS kdfS streamS geom hvalid hmactag
            h16 p r).2.km, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (finX nike cipher macS kdfS
            streamS geom hvalid hmactag h16 p r).2).2.2),
          (finX nike cipher macS kdfS streamS geom hvalid hmactag h16 p r).2.u, g) (tailOf nike
              kdfS ((nike.decodePrivateKey (finX nike cipher macS kdfS streamS geom hvalid hmactag
              h16 p r).2.p.d0).getD default) (RSOR.path nike (finX nike cipher macS kdfS streamS
              geom hvalid hmactag h16 p r).2.p.c.req.fwd [.recipient (finX nike cipher macS kdfS
              streamS geom hvalid hmactag h16 p r).2.p.c.req.receiver]) (finX nike cipher macS kdfS
              streamS geom hvalid hmactag h16 p r).2.p.c.pos (finX nike cipher macS kdfS streamS
              geom hvalid hmactag h16 p r).2.y.2.2))
      = (do
        let W ← $ᵗ (KEMSphinx.Keystream geom)
        let y ← $ᵗ (Vector UInt8 48 × Vector UInt8 32 × Vector UInt8 32)
        let U1 ← $ᵗ (KEMSphinx.Keystream geom)
        let t ← finTail nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        let g ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
        (fun U => blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U,
            t.1, (⟨p.k, p.keys, p.c, p.st, p.log, t.2.2.1.1, t.2.2.2.1⟩ : PropDraw nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
            names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A),
            t.2.2.2.2.1, g) (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default)
            (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos y.2.2))
            (Util.Bytes.toVecN _
          (xorBytes ((Util.Bytes.ofVector U1).extract 0 ((geom.routingInfoLength +
              geom.perHopRoutingInfoLength) - ((p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength))
              ((fun yb => xorBytes ((lastFrag geom (RSOR.path nike ((fwd1 nike cipher macS kdfS
                  streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names p.k.1) t.2.2.1).fwd [.recipient
                  ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys,
                  p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
                  p.k.1) t.2.2.1).receiver]) p.c.pos) ++ (if geom.nrHops > (RSOR.path nike ((fwd1
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ :
                  ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names p.k.1)
                  t.2.2.1).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
                  h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom
                  hvalid hmactag h16 names p.k.1) t.2.2.1).receiver]).size then (RSOR.filler nike
                  geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
                  names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
                  hmactag h16 names p.k.1) t.2.2.1).fwd [.recipient ((fwd1 nike cipher macS kdfS
                  streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher
                  macS kdfS streamS geom hvalid hmactag h16 names p.k.1) t.2.2.1).receiver]) ((fwd1
                  nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd t.2.2.1).1) else
                  ByteArray.empty)) (hopContent nike geom (Function.update (spliceAt p.c.pos
                  (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey
                  t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]) p.c.pos (restKeys ((default, default, default), default)
                  default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) p.c.pos
                  (KEMSphinx.zeroBytes ((geom.routingInfoLength + geom.perHopRoutingInfoLength) -
                  ((p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength) ++ xorBytes yb (padMask geom
                  (spliceAt p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS
                  ((nike.decodePrivateKey t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default, default, default),
                  default) default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (keysKs geom streamS
                  (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default
                  y, p)).toArray) p.c.pos))) (spliceAt p.c.pos (keysTag macS (hopKeysWith nike kdfS
                  ((nike.decodePrivateKey t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default, default, default),
                  default) default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (spliceAt p.c.pos
                  (blindElem nike (groupElem nike ((nike.decodePrivateKey t.2.2.2.1).getD default)
                  (hopKeysWith nike kdfS ((nike.decodePrivateKey t.2.2.2.1).getD default)
                  (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos (restKeys
                  ((default, default, default), default) default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS
                  ((nike.decodePrivateKey t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default, default, default),
                  default) default) (RSOR.path nike p.c.req.fwd [.recipient
                  p.c.req.receiver]).size).toArray) (blindElem nike (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).1 (tailOf nike kdfS
                  ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
                  [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (RSOR.filler nike geom
                  (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) t.2.2.1.1.1)
                  (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos))
                  ((Util.Bytes.ofVector W).extract ((geom.routingInfoLength +
                  geom.perHopRoutingInfoLength) - ((p.c.pos : ℕ) + 1) *
                  geom.perHopRoutingInfoLength) (geom.routingInfoLength +
                  geom.perHopRoutingInfoLength)))
            ++ xorBytes ((Util.Bytes.ofVector W).extract ((geom.routingInfoLength +
                geom.perHopRoutingInfoLength) - ((p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength)
                (geom.routingInfoLength + geom.perHopRoutingInfoLength)) (padMask geom (spliceAt
                p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey
                t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver])
                p.c.pos (restKeys ((default, default, default), default) default) (RSOR.path nike
                p.c.req.fwd [.recipient p.c.req.receiver]).size).toArray) (keysKs geom streamS
                (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike
                p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (keysKs geom
                streamS (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4
                default y, p)).toArray) p.c.pos)))) := by
    simp only [← hbody]
    unfold finRest finTail
    simp only [bind_assoc, pure_bind]
    rfl
  rw [h1]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun W => EvalDistEq.bind_right _ fun y =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun W => EvalDistEq.bind_right _ fun y =>
      EvalDistEq.bind_right _ fun t => OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y => OracleComp.EvalDistEq.bind_bind_swap _
      _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y => EvalDistEq.bind_right _ fun t =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y => EvalDistEq.bind_right _ fun t =>
      EvalDistEq.bind_right _ fun g => OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y => EvalDistEq.bind_right _ fun t =>
      EvalDistEq.bind_right _ fun g => KEMSphinx.evalDistEq_headTail hLN (fun yb => xorBytes
      ((lastFrag geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      names p.k.1) t.2.2.1).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names p.k.1) t.2.2.1).receiver]) p.c.pos) ++ (if geom.nrHops > (RSOR.path nike
      ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ :
      ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names p.k.1) t.2.2.1).fwd
      [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys,
      p.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names p.k.1)
      t.2.2.1).receiver]).size then (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names p.k.1) t.2.2.1).fwd [.recipient ((fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).req (⟨p.keys, p.c⟩ : ForwardCh nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names p.k.1) t.2.2.1).receiver]) ((fwd1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names).rnd t.2.2.1).1) else ByteArray.empty))
      (hopContent nike geom (Function.update (spliceAt p.c.pos (keysKs geom streamS (hopKeysWith
      nike kdfS ((nike.decodePrivateKey t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd
      [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default, default, default), default)
      default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]).size).toArray) (keysKs
      geom streamS (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike
      p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) p.c.pos
      (KEMSphinx.zeroBytes ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - ((p.c.pos :
      ℕ) + 1) * geom.perHopRoutingInfoLength) ++ xorBytes yb (padMask geom (spliceAt p.c.pos
      (keysKs geom streamS (hopKeysWith nike kdfS ((nike.decodePrivateKey t.2.2.2.1).getD default)
      (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default,
      default, default), default) default) (RSOR.path nike p.c.req.fwd [.recipient
      p.c.req.receiver]).size).toArray) (keysKs geom streamS (tailOf nike kdfS
      ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd [.recipient
      p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (keysKs geom streamS (nextKeysI nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (keys4 default y, p)).toArray) p.c.pos))) (spliceAt
      p.c.pos (keysTag macS (hopKeysWith nike kdfS ((nike.decodePrivateKey t.2.2.2.1).getD default)
      (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos (restKeys ((default,
      default, default), default) default) (RSOR.path nike p.c.req.fwd [.recipient
      p.c.req.receiver]).size).toArray) (keysTag macS (tailOf nike kdfS ((nike.decodePrivateKey
      p.d0).getD default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos
      y.2.2).2.toArray)) (spliceAt p.c.pos (blindElem nike (groupElem nike ((nike.decodePrivateKey
      t.2.2.2.1).getD default) (hopKeysWith nike kdfS ((nike.decodePrivateKey t.2.2.2.1).getD
      default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos (restKeys
      ((default, default, default), default) default) (RSOR.path nike p.c.req.fwd [.recipient
      p.c.req.receiver]).size).toArray 0) (hopKeysWith nike kdfS ((nike.decodePrivateKey
      t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos
      (restKeys ((default, default, default), default) default) (RSOR.path nike p.c.req.fwd
      [.recipient p.c.req.receiver]).size).toArray) (blindElem nike (tailOf nike kdfS
      ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd [.recipient
      p.c.req.receiver]) p.c.pos y.2.2).1 (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD
      default) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos
      y.2.2).2.toArray)) (RSOR.filler nike geom (RSOR.path nike p.c.req.fwd [.recipient
      p.c.req.receiver]) t.2.2.1.1.1) (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver])
      p.c.pos)) (padMask geom (spliceAt p.c.pos (keysKs geom streamS (hopKeysWith nike kdfS
      ((nike.decodePrivateKey t.2.2.2.1).getD default) (RSOR.path nike p.c.req.fwd [.recipient
      p.c.req.receiver]) p.c.pos (restKeys ((default, default, default), default) default)
      (RSOR.path nike p.c.req.fwd [.recipient p.c.req.receiver]).size).toArray) (keysKs geom
      streamS (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike
      p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos y.2.2).2.toArray)) (keysKs geom streamS
      (nextKeysI nike cipher macS kdfS streamS geom hvalid hmactag h16 (keys4 default y,
      p)).toArray) p.c.pos) (fun U => blindPost nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names A E (U, t.1, (⟨p.k, p.keys, p.c, p.st, p.log, t.2.2.1.1, t.2.2.2.1⟩ : PropDraw nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
      .relay names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A),
      t.2.2.2.2.1, g) (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike
      p.c.req.fwd [.recipient p.c.req.receiver]) p.c.pos y.2.2))) ?_
  unfold finTail shortDraw
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y => EvalDistEq.bind_right _ fun km =>
      OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y => EvalDistEq.bind_right _ fun km =>
      EvalDistEq.bind_right _ fun r0 => OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y => EvalDistEq.bind_right _ fun km =>
      EvalDistEq.bind_right _ fun r0 => OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y => EvalDistEq.bind_right _ fun km =>
      EvalDistEq.bind_right _ fun r0 => OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun y => EvalDistEq.bind_right _ fun km =>
      EvalDistEq.bind_right _ fun r0 => EvalDistEq.bind_right _ fun d => EvalDistEq.bind_right _
      fun u => OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (KEMSphinx.evalDistEq_snd (fun y2 : Vector UInt8 32 × Vector UInt8 32 =>
      do
    let km ← $ᵗ (Vector UInt8 32)
    let r0 ← $ᵗ (RSOR.Randomness nike geom)
    let d ← $ᵗ (Vector UInt8 nike.privateKeySize)
    let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let g ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let U ← $ᵗ (KEMSphinx.Keystream geom)
    blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U, km, (⟨p.k,
        p.keys, p.c, p.st, p.log, r0, d⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names).Oth A), u, g) (tailOf nike kdfS
        ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd [.recipient
        p.c.req.receiver]) p.c.pos y2.2))) ?_
  refine EvalDistEq.trans (KEMSphinx.evalDistEq_snd (fun seed : Vector UInt8 32 => do
    let km ← $ᵗ (Vector UInt8 32)
    let r0 ← $ᵗ (RSOR.Randomness nike geom)
    let d ← $ᵗ (Vector UInt8 nike.privateKeySize)
    let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let g ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
    let U ← $ᵗ (KEMSphinx.Keystream geom)
    blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U, km, (⟨p.k,
        p.keys, p.c, p.st, p.log, r0, d⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names).Oth A), u, g) (tailOf nike kdfS
        ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd [.recipient
        p.c.req.receiver]) p.c.pos seed))) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun km => OracleComp.EvalDistEq.bind_bind_swap _
      _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun r0 =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun r0 =>
      EvalDistEq.bind_right _ fun d => OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun r0 =>
      EvalDistEq.bind_right _ fun d => EvalDistEq.bind_right _ fun u =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun r0 =>
      EvalDistEq.bind_right _ fun d => EvalDistEq.bind_right _ fun u => EvalDistEq.bind_right _ fun
      g => OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun r0 => OracleComp.EvalDistEq.bind_bind_swap _
      _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun r0 => EvalDistEq.bind_right _ fun d =>
      EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun u =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun r0 => EvalDistEq.bind_right _ fun d =>
      EvalDistEq.bind_right _ fun km => OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun r0 => EvalDistEq.bind_right _ fun d =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact EvalDistEq.rfl

/-- **World 0 with the hops after the relay from an independent secret, for fixed game
draws**: the original's randomness, the sender's secret, the relay's keystream and MAC key, the
two blocks and the relay's blinding seed, and the blinding adversary's game on the tail of the
path from the secret `p.d0`. -/
def world0P (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) (E :
    KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS kdfS streamS geom
    hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher
    macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8 (geom.payloadTagLength
    + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) (p : NextPre nike cipher macS kdfS streamS geom
    hvalid hmactag h16 names A) :
    ProbComp Bool := do
  let r0 ← $ᵗ (RSOR.Randomness nike geom)
  let d ← $ᵗ (Vector UInt8 nike.privateKeySize)
  let U ← $ᵗ (KEMSphinx.Keystream geom)
  let km ← $ᵗ (Vector UInt8 32)
  let u ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  let v ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  let seed ← $ᵗ (Vector UInt8 32)
  blindPost nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E (U, km, (⟨p.k, p.keys,
      p.c, p.st, p.log, r0, d⟩ : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (fwd0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names).Oth A), u, v)
    (tailOf nike kdfS ((nike.decodePrivateKey p.d0).getD default) (RSOR.path nike p.c.req.fwd
        [.recipient p.c.req.receiver]) p.c.pos seed)

set_option maxHeartbeats 4000000 in
/-- `world0B` draws the game's draws and the independent secret first. -/
theorem world0B_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) :
    world0B nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E =ᵈ (nextPre nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names A >>= world0P nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names A E) := by
  unfold world0B nextPre world0P forwardDraw propDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
      EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => EvalDistEq.bind_right _
      fun o => EvalDistEq.bind_right _ fun d => EvalDistEq.bind_right _ fun U =>
      EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun u => EvalDistEq.bind_right _
      fun v => OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
      EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => EvalDistEq.bind_right _
      fun o => EvalDistEq.bind_right _ fun d => EvalDistEq.bind_right _ fun U =>
      EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun u =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
      EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => EvalDistEq.bind_right _
      fun o => EvalDistEq.bind_right _ fun d => EvalDistEq.bind_right _ fun U =>
      EvalDistEq.bind_right _ fun km => OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
      EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => EvalDistEq.bind_right _
      fun o => EvalDistEq.bind_right _ fun d => EvalDistEq.bind_right _ fun U =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
      EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => EvalDistEq.bind_right _
      fun o => EvalDistEq.bind_right _ fun d => OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
      EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => EvalDistEq.bind_right _
      fun o => OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
      EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out =>
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact EvalDistEq.rfl

/-- **For fixed game draws before the end of the path, world 1 is world 0 with the hops after
the relay from an independent secret**, off the draws that are not good. -/
theorem fin_fixed_fwd_le (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary) (E : KEMSphinx.Keystream geom × Vector UInt8 32 × (PropDraw nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
    (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).Oth A) × (Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength)) → ProbComp Bool) (p : NextPre nike cipher macS kdfS streamS geom
    hvalid hmactag h16 names A)
    (hn : (p.c.pos : ℕ) + 1 < p.c.req.fwd.hops.length) :
    |(Pr{let b ← (finRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names >>= fun r =>
        finOwnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (finX nike cipher
        macS kdfS streamS geom hvalid hmactag h16 p r))}[b =
        true]).toReal
      - (Pr{let b ← (world0P nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E p)}[b
          = true]).toReal|
    ≤ (Pr{let r ← (finRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names)}[¬ finGood
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (finX nike cipher macS kdfS streamS
        geom hvalid hmactag h16 p r)]).toReal := by
  have h1 := finRest_sub_le nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E p hn
  rw [(finRest_comb_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 names A E p)
      (fun b => b = true)] at h1
  exact h1

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
