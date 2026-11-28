/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUExit

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

/-! # The last comparison of TLU→ for NIKE Sphinx: the end of the path, on the draws

At the end of the path, world 1's run on a draw is world 0's run with the head of the relay's
keystream shifted by a constant. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- **What the last hop's keystream masks has one length**: the hop's fragment and the
filler. -/
theorem lastContent_size (filler : ByteArray) (path : Array PathHop) (i : ℕ) (F : ByteArray)
    (hi : i + 1 = path.size) (hnnh : geom.nextNodeHopLength = nextNodeHopLength)
    (hle : geom.nextNodeHopLength ≤ geom.perHopRoutingInfoLength)
    (hrouting : geom.routingInfoLength = geom.perHopRoutingInfoLength * geom.nrHops)
    (hn : path.size ≤ geom.nrHops)
    (hfill : filler.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (hF : nikeFragment geom path ByteArray.empty i = .ok F) :
    (F ++ (if geom.nrHops > path.size then filler else ByteArray.empty)).size =
        ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - (i + 1) *
        geom.perHopRoutingInfoLength) := by
  obtain ⟨k, hk⟩ : ∃ k, geom.nrHops = i + 1 + k := ⟨geom.nrHops - (i + 1), by omega⟩
  have e1 : geom.routingInfoLength = (i + 1) * geom.perHopRoutingInfoLength
      + k * geom.perHopRoutingInfoLength := by
    rw [hrouting, hk, Nat.mul_comm, Nat.add_mul]
  have hFs : F.size = geom.perHopRoutingInfoLength :=
    nikeFragment_size geom path _ i hnnh hle F hF
  have hB : (if geom.nrHops > path.size then filler else ByteArray.empty).size
      = k * geom.perHopRoutingInfoLength := by
    by_cases hg : geom.nrHops > path.size
    · rw [ite_eq_left hg, hfill, show geom.nrHops - path.size = k by omega]
    · rw [ite_eq_right hg, show k = 0 by omega, Nat.zero_mul]
      rfl
  rw [ByteArray.size_append, hFs, hB]
  omega

/-- **The keystream of world 0's relay that matches a draw of world 1 at the end of the path**:
the replacement's keystream with its head shifted by the difference of what the two last hops
mask. -/
def finShift {names : Role → Name} {A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary}
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) : KEMSphinx.Keystream geom :=
  Util.Bytes.toVecN _
    (xorBytes ((Util.Bytes.ofVector x.2.U).extract 0 ((geom.routingInfoLength +
        geom.perHopRoutingInfoLength) - ((x.2.p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength))
        (xorBytes ((lastFrag geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos) ++ (if
        geom.nrHops > (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size then (RSOR.filler
        nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.o).1) else ByteArray.empty)) (lastFrag geom (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos ++ (if geom.nrHops >
        (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size then (RSOR.filler
        nike geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1)
        else ByteArray.empty)))
      ++ (Util.Bytes.ofVector x.2.U).extract ((geom.routingInfoLength +
          geom.perHopRoutingInfoLength) - ((x.2.p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength))

set_option maxHeartbeats 16000000 in
/-- **At the end of the path, world 1 on a draw is world 0 on the shifted keystream**, whatever
blinding seed `sd` world 0's relay has. This holds when both paths build, both bodies have a
payload's length, the original's two paths build, and the block a changed payload is decrypted
to does not begin with the zero tag. -/
theorem finOwnRun_eq_fwd0_last (names : Role → Name) (A : (Protocols.RSOR.forwardUnlinkable (S :=
    𝒮)).Adversary)
    (x : KEMSphinx.Keystream geom × Next4 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names A) (sd : Vector UInt8 32)
    (hlast : (x.2.p.c.pos : ℕ) + 1 = x.2.p.c.req.fwd.hops.length)
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
        x.2).2.2.o)).size = geom.forwardPayloadLength)
    (hr : RSOR.Reliable nike cipher macS kdfS streamS geom x.2.p.c.req x.2.o.1)
    (hv : ¬ ((Util.Bytes.ofVector x.2.v).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
        :
    finOwnRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names A x
      = strRun nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) A (x.2.km, sd, (toDraw0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2)) (finShift nike cipher macS kdfS streamS geom hvalid hmactag h16 x) x.2.u
          x.2.v := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  have hpos : (x.2.p.c.pos : ℕ) < x.2.p.c.req.fwd.hops.length := x.2.p.c.pos.isLt
  have hszP := RSOR.path_size nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]
  have hposP : (x.2.p.c.pos : ℕ) < (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size := lt_of_lt_of_eq hpos hszP.symm
  have hjP : (x.2.p.c.pos : ℕ) + 1 = (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size := hlast.trans hszP.symm
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
      geom hvalid hmactag h16 x.2).2.2.o).receiver]).size ≤ geom.nrHops := by omega
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
  have hT1 : pathBuilds geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) 1 :=
    nikeHdrTrace_isSome_of_le geom _ _ _ _ (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) 1 x.2.p.c.pos (by
      rw [show 1 + (x.2.p.c.pos : ℕ) = (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]).size by omega]
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
  obtain ⟨Fa, hFa⟩ := pathBuilds_fragment geom (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) hT1
  rw [show (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size - 1 =
      (x.2.p.c.pos : ℕ) by omega] at hFa
  have hF : nikeFragment geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      ByteArray.empty x.2.p.c.pos = .ok (lastFrag geom (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]) x.2.p.c.pos) := by
    unfold lastFrag
    rw [hFa]
  obtain ⟨Fb, hFb⟩ := pathBuilds_fragment geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS
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
      hmactag h16 x.2).2.2.o).receiver]).size - 1 = (x.2.p.c.pos : ℕ) by omega] at hFb
  have hF' : nikeFragment geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
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
    rw [hFb]
  have hX : (lastFrag geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos ++ (if geom.nrHops > (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size then (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) else ByteArray.empty)).size =
      ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - ((x.2.p.c.pos : ℕ) + 1) *
      geom.perHopRoutingInfoLength) :=
    lastContent_size geom _ _ _ _ hjP hnnh (by omega) hrouting hnP (hfillOf _ _) hF
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
      geom.perHopRoutingInfoLength) :=
    lastContent_size geom _ _ _ _ hszP1.symm hnnh (by omega) hrouting hnP1 (hfillOf _ _) hF'
  have hjp : ((x.2.p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting]
    exact (Nat.mul_comm _ _).le.trans (Nat.mul_le_mul_left _ (by omega))
  have hUs : (Util.Bytes.ofVector x.2.U).size = (geom.routingInfoLength +
      geom.perHopRoutingInfoLength) := Util.Bytes.size_ofVector _
  have hHD : (xorBytes ((Util.Bytes.ofVector x.2.U).extract 0 ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - ((x.2.p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength))
      (xorBytes ((lastFrag geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
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
      streamS geom hvalid hmactag h16 x.2).2.2.o).1) else ByteArray.empty)) (lastFrag geom
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos ++ (if
      geom.nrHops > (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size then
      (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.o.1.1) else ByteArray.empty)))).size
      = ((geom.routingInfoLength + geom.perHopRoutingInfoLength) - ((x.2.p.c.pos : ℕ) + 1) *
          geom.perHopRoutingInfoLength) := by
    rw [Cryptlib.Protocols.Sphinx.Common.size_xorBytes, ByteArray.size_extract, hUs]
    omega
  have hSh : (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS geom hvalid hmactag h16
      x)) = xorBytes ((Util.Bytes.ofVector x.2.U).extract 0 ((geom.routingInfoLength +
      geom.perHopRoutingInfoLength) - ((x.2.p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength))
      (xorBytes ((lastFrag geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
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
      streamS geom hvalid hmactag h16 x.2).2.2.o).1) else ByteArray.empty)) (lastFrag geom
      (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos ++ (if
      geom.nrHops > (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size then
      (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.o.1.1) else ByteArray.empty)))
      ++ (Util.Bytes.ofVector x.2.U).extract ((geom.routingInfoLength +
          geom.perHopRoutingInfoLength) - ((x.2.p.c.pos : ℕ) + 1) * geom.perHopRoutingInfoLength)
          (geom.routingInfoLength + geom.perHopRoutingInfoLength) := by
    unfold finShift
    exact Util.Bytes.ofVector_toVecN _ (by
      rw [ByteArray.size_append, hHD, ByteArray.size_extract, hUs]
      omega)
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
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2))) default)).toArray[i]! := fun i hi => by
    have hle1 : (RSOR.path nike (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)) []).size ≤ (RSOR.path nike
        x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size := by
      rw [hszP1e]
      omega
    have hi1 : i < (RSOR.path nike (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)) []).size := by
      rw [hszP1e]
      omega
    rw [fwd1_keys nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2), fwd0_keys nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names A (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))]
    exact (hopKeysWith_cut nike kdfS _ (RSOR.path nike (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)) [])
        (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos _ _
        (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size hle1
      (fun m hm => hpub m (lt_of_lt_of_eq hm hszP1e)) i hi1).trans
      (hopKeysWith_getElem!_lt nike kdfS _ _ x.2.p.c.pos _ _ (RSOR.path nike x.2.p.c.req.fwd
          [.recipient x.2.p.c.req.receiver]).size i hi hposP.le)
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
  have hksA : ∀ k, ((Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x))) k).size = (geom.routingInfoLength + geom.perHopRoutingInfoLength) := fun k => by
    by_cases hk : k = (x.2.p.c.pos : ℕ)
    · rw [hk, Function.update_self]
      exact Util.Bytes.size_ofVector _
    · rw [Function.update_of_ne hk]
      exact streamS.keystream_size _ _ _
  have hgeEq : ∀ i, i ≤ (x.2.p.c.pos : ℕ) → (blindElem nike (groupElem nike (drawKey nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
      names (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray 0)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2))) default)).toArray) i = (blindElem nike (groupElem nike (drawKey nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
      .relay names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
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
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) i := fun i hi
      =>
    blindElem_congr_lt nike (Util.Bytes.ofVector (nike.encodePublicKey (nike.derivePublicKey
        ((nike.decodePrivateKey x.2.d').getD default)))) _ _ i fun n hn =>
      congrArg HopKeys.blindingFactor (hkeys n (by omega)).symm
  have hksF : ∀ m, m < (x.2.p.c.pos : ℕ) → (Function.update (keysKs geom streamS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
      default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x))) m = (Function.update (keysKs geom streamS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
      default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) m := fun m hm => by
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    unfold keysKs
    rw [hkeys m hm]
  have hM01 : (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
      default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x))) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
      (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray) (blindElem
      nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (toDraw0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2))) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray)
      (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.o.1.1) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos) =
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
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos) :=
    hdrMsg_shift_last geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
        default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS
        geom hvalid hmactag h16 x))) (Function.update (keysKs geom streamS (forwardKeys0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U)) (keysTag macS
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2))) default)).toArray) (keysTag macS (forwardKeys0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2)) default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
        (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
        default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
        (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray) (blindElem
        nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
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
        nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.filler nike geom
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
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid
        hmactag h16 x.2).2.2.o).1) (RSOR.path nike x.2.p.c.req.fwd [.recipient
        x.2.p.c.req.receiver]) (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ :
        ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos hjP
      hszP1.symm _ _ hF hF' hX hX' hks1 (hgeEq _ le_rfl) hksF (by
        rw [Function.update_self, Function.update_self, hSh]
        have e := Util.Bytes.extract_append_left
          (xorBytes ((Util.Bytes.ofVector x.2.U).extract 0 ((geom.routingInfoLength +
              geom.perHopRoutingInfoLength) - ((x.2.p.c.pos : ℕ) + 1) *
              geom.perHopRoutingInfoLength)) (xorBytes ((lastFrag geom (RSOR.path nike ((fwd1 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
              macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
              kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom
              hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid
              hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid
              hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag
              h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
              (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver])
              x.2.p.c.pos) ++ (if geom.nrHops > (RSOR.path nike ((fwd1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
              geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
              hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
              x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
              (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
              nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]).size
              then (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom
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
              streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom
              hvalid hmactag h16 x.2).2.2.o).1) else ByteArray.empty)) (lastFrag geom (RSOR.path
              nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos ++ (if
              geom.nrHops > (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size
              then (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd [.recipient
              x.2.p.c.req.receiver]) x.2.o.1.1) else ByteArray.empty))))
          ((Util.Bytes.ofVector x.2.U).extract ((geom.routingInfoLength +
              geom.perHopRoutingInfoLength) - ((x.2.p.c.pos : ℕ) + 1) *
              geom.perHopRoutingInfoLength) (geom.routingInfoLength + geom.perHopRoutingInfoLength))
        rw [hHD] at e
        exact e)
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
  have hgeAp : ((blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (toDraw0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd,
      (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray 0) (forwardKeys0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
      default)).toArray) x.2.p.c.pos).size = nike.publicKeySize :=
    (blindElem_size nike _ _ _).trans (Util.Bytes.size_ofVector _)
  have hMsz : (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS
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
      hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos).size = 2 + nike.publicKeySize +
      geom.routingInfoLength :=
    hdrMsg_size_last nike geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
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
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos hszP1.symm hnnh (by
        omega)
      hrouting hnP1 (hfillOf _ _) hks1 hge1p _ hF'
  have hlt1 := fwd_hops_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2
  have hlt0 := fwd_hops_pos nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (toDraw0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2)
  have hjk1 : (x.2.p.c.pos : ℕ) ≤ (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
      macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).length :=
    le_of_lt (lt_of_lt_of_eq hlt1 (hopKeysWith_length nike kdfS _ _ _ _ _).symm)
  have hjk0 : (x.2.p.c.pos : ℕ) ≤ (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km,
      sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS
      kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).length :=
    le_of_lt (lt_of_lt_of_eq hlt0 (hopKeysWith_length nike kdfS _ _ _ _ _).symm)
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
      hmactag le_rfl (by rw [hszP1]; omega) hjk1 (Util.Bytes.size_ofVector _)
      ((Util.Bytes.size_ofVector _).trans hmactag) (by rw [Util.Bytes.size_ofVector]; exact h16)
      (Util.Bytes.size_ofVector _)
  have hlastL := layerFn_last nike macS kdfS streamS geom hvalid ((fwd1 nike cipher macS kdfS
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
  have hH : Util.Bytes.toVecN _ (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
      geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
      default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x))) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
      (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray) (blindElem
      nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (toDraw0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2))) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray)
      (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.o.1.1) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos))
      ++ Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector
          (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom
          (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2))) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x))) (keysTag macS (forwardKeys0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2))) default)).toArray) (blindElem nike (groupElem nike (drawKey nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S :=
          𝒮)) .relay names (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)) (forwardKeys0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2))) default)).toArray 0) (forwardKeys0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2))) default)).toArray) (RSOR.filler nike geom (RSOR.path nike
          x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike
          x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos))))) = (finMine nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x).1 := by
    rw [hMINE, hlastL, hM01, Util.Bytes.ofVector_toVecN _ hMsz]
  have hD : (fun y => if y = x.2.u then Util.Bytes.toVecN _ (encTrace (keysEnc cipher (forwardKeys0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2))) default)).toArray) (RSOR.path nike x.2.p.c.req.fwd [.recipient
      x.2.p.c.req.receiver]).size (((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)) ++
      (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1)) ((RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]).size - 1 - x.2.p.c.pos)) else x.2.v) = (fun y => if y =
      x.2.u then Util.Bytes.toVecN _ (((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)) ++
      (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1)) else x.2.v) := by
    funext y
    rw [show (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size - 1 -
        (x.2.p.c.pos : ℕ) = 0 by omega]
    rfl
  have htagA : ∀ i m, ((Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray)
      x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km)
      (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
      (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray)
      x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS geom hvalid hmactag
      h16 x))) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
      (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd,
      (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray) (blindElem nike (groupElem
      nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (toDraw0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2))) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray)
      (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.o.1.1) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
      x.2.p.c.pos))))) i m).size = macLength := fun i m => by
    by_cases hi : i = (x.2.p.c.pos : ℕ)
    · rw [hi, Function.update_self]
      exact (Util.Bytes.size_ofVector _).trans hmactag
    · rw [Function.update_of_ne hi]
      exact (Util.Bytes.size_ofVector _).trans hmactag
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
  have hT01 : (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
      nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom
      streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom
      hvalid hmactag h16 x.2).2.2))) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector (finShift
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x))) (keysTag macS (forwardKeys0 nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
      default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (toDraw0
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS
      geom hvalid hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
      (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray 0)
      (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2))) default)).toArray) (RSOR.filler nike geom (RSOR.path nike
      x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike x.2.p.c.req.fwd
      [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos)))) = (macS.mac (Util.Bytes.ofVector x.2.km)
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
      nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))))
      := by rw [hM01]
  have hOn : strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) (x.2.km, sd, (toDraw0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
      x.2).2.2)) (finShift nike cipher macS kdfS streamS geom hvalid hmactag h16 x) x.2.u 0
      = strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2) x.2.U x.2.u 0 := by
    have e0 : strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (x.2.km, sd, (toDraw0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
        hmactag h16 x.2).2.2)) (finShift nike cipher macS kdfS streamS geom hvalid hmactag h16 x)
        x.2.u 0
        = layerFn nike macS kdfS streamS geom x.2.p.c.req x.2.o.1 (Function.update (keysKs geom
            streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
            (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray)
            x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x))) (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2))) default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector
            (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
            nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom
            streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
            (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray)
            x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x))) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
            default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
            names (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2))) default)).toArray 0) (forwardKeys0 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2))) default)).toArray) (RSOR.filler nike geom (RSOR.path nike
            x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike
            x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos))))) (Function.update
            (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
            default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector x.2.u) (blindElem nike
            (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (toDraw0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
            default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
            default)).toArray) 0 :=
      onionOfStream_eq_layerFn nike cipher macS kdfS streamS geom 0 x.2.p.c.req x.2.o.1 (groupElem
          nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (toDraw0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
          (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray 0)
          (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd,
          (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)) x.2.p.c.pos
        (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS geom hvalid hmactag h16 x))
            (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector
            (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom
            (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2))) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x))) (keysTag macS (forwardKeys0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2))) default)).toArray) (blindElem nike (groupElem nike
            (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (toDraw0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
            default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
            default)).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd [.recipient
            x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike x.2.p.c.req.fwd [.recipient
            x.2.p.c.req.receiver]) x.2.p.c.pos))))) (Util.Bytes.ofVector x.2.u) hvalid hmactag
        (Nat.zero_le _) hposP hjk0 (Util.Bytes.size_ofVector _)
        ((Util.Bytes.size_ofVector _).trans hmactag)
        (by rw [Util.Bytes.size_ofVector]; exact h16) (Util.Bytes.size_ofVector _)
    have e1 : strOnion nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2) x.2.U x.2.u 0 = (layerFn nike macS kdfS streamS geom
        ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o)
        ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) (Function.update (keysKs geom streamS
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector
        x.2.U)) (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray)
        x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km)
        (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength)
        (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS
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
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))))) (Function.update
        (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos fun _
        => Util.Bytes.ofVector x.2.u) (blindElem nike (groupElem nike (drawKey nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
        names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default)).toArray) 0) :=
      onionOfStream_eq_layerFn nike cipher macS kdfS streamS geom 0 ((fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.o) (groupElem nike (drawKey nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2) (forwardKeys0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2)) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2)) default)) x.2.p.c.pos
        (Util.Bytes.ofVector x.2.U) (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km)
            (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
            geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom streamS
            (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
            (Util.Bytes.ofVector x.2.U)) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2)) default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
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
            streamS geom hvalid hmactag h16 x.2)) default)).toArray) (RSOR.filler nike geom
            (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
            (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
            hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver])
            ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
            h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver])
            x.2.p.c.pos))))) (Util.Bytes.ofVector x.2.u) hvalid
        hmactag (Nat.zero_le _) (by rw [hszP1]; omega) hjk1 (Util.Bytes.size_ofVector _)
        ((Util.Bytes.size_ofVector _).trans hmactag)
        (by rw [Util.Bytes.size_ofVector]; exact h16) (Util.Bytes.size_ofVector _)
    have iso : ∀ (k : ℕ → ByteArray) (tg : ℕ → ByteArray → ByteArray) (g : ℕ → ByteArray),
        (nikeHdrTrace geom k tg g (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd
            [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike x.2.p.c.req.fwd
            [.recipient x.2.p.c.req.receiver]) ((RSOR.path nike x.2.p.c.req.fwd [.recipient
            x.2.p.c.req.receiver]).size - x.2.p.c.pos)).isSome := fun k tg g =>
      nikeHdrTrace_isSome_of_le geom k tg g _ _ ((RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]).size - x.2.p.c.pos) x.2.p.c.pos (by
        rw [Nat.sub_add_cancel (le_of_lt hposP)]
        exact (nikeHdrTrace_isSome geom k _ tg _ g _ (RSOR.filler nike geom (RSOR.path nike
            x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) _ (RSOR.path nike
            x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) _).trans hT)
    have iso' : ∀ (k : ℕ → ByteArray) (tg : ℕ → ByteArray → ByteArray) (g : ℕ → ByteArray),
        (nikeHdrTrace geom k tg g (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom
            hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1) (RSOR.path nike ((fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
            kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
            h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver])
            ((RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient
            ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).receiver]).size - x.2.p.c.pos)).isSome := fun k tg g =>
      nikeHdrTrace_isSome_of_le geom k tg g _ _ ((RSOR.path nike ((fwd1 nike cipher macS kdfS
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
          x.2).2.2.o).receiver]).size - x.2.p.c.pos) x.2.p.c.pos (by
        rw [Nat.sub_add_cancel (by omega)]
        exact (nikeHdrTrace_isSome geom k _ tg _ g _ (RSOR.filler nike geom (RSOR.path nike ((fwd1
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
            h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names).rnd (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).1) _ (RSOR.path nike ((fwd1 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
            kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag
            h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) _).trans
            hT')
    have hfront : ∀ i < (x.2.p.c.pos : ℕ), (Function.update (keysKs geom streamS (forwardKeys0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2))) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x))) i = (Function.update (keysKs geom streamS
        (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS
        streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector
        x.2.U)) i ∧ (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
        default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector
        x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
        geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
        hmactag h16 x.2).2.2))) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector (finShift nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x))) (keysTag macS (forwardKeys0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2))) default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
        names (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher
        macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
        default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
        (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray)
        (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
        x.2.o.1.1) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
        x.2.p.c.pos))))) i = (Function.update (keysTag macS (forwardKeys0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
        default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector
        x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
        geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom streamS (forwardKeys0
        nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
        (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS geom
        hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector x.2.U))
        (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
        cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) (blindElem nike
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
        streamS geom hvalid hmactag h16 x.2).2.2.o).receiver]) x.2.p.c.pos))))) i ∧ (blindElem nike
        (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (toDraw0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag
        h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names
        (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km,
        sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray 0) (forwardKeys0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
        x.2).2.2))) default)).toArray) i = (blindElem nike (groupElem nike (drawKey nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮))
        .relay names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)
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
        default)).toArray) i
        ∧ (Function.update (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
            default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector x.2.u) i = (Function.update
            (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2))
            default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector x.2.u) i ∧ (RSOR.path nike
            x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])[i]!.commands = (RSOR.path nike
            ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o).receiver])[i]!.commands
        ∧ (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])[i + 1]!.id =
            (RSOR.path nike ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
            (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom
            hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1)
            (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver])[i
            + 1]!.id := fun i hi => by
      have hb1 : i < (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length :=
        lt_of_lt_of_eq (Nat.lt_succ_of_lt hi) hlen1.symm
      have hb2 : i < x.2.p.c.req.fwd.hops.length := by omega
      have hb3 : i + 1 < (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length :=
        lt_of_lt_of_eq (Nat.succ_lt_succ hi) hlen1.symm
      have hb4 : i + 1 < x.2.p.c.req.fwd.hops.length := by omega
      refine ⟨hksF i hi, ?_, hgeEq i (by omega), ?_, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        funext m
        unfold keysTag
        rw [hkeys i hi]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        funext m
        unfold keysEnc
        rw [hkeys i hi]
      · have hne : ¬ i + 1 = (x.2.p.c.req.fwd.take (x.2.p.c.pos + 1)).hops.length := by
          rw [hlen1]
          omega
        rw [hP1, RSOR.path_getElem! nike _ _ i hb2, RSOR.path_getElem! nike _ _ i hb1]
        exact (ite_eq_right (by omega)).trans (ite_eq_right hne).symm
      · rw [hP1, RSOR.path_getElem! nike _ _ (i + 1) hb4, RSOR.path_getElem! nike _ _ (i + 1) hb3]
        exact congrArg (fun h : Protocols.RSOR.Hop Name (RSOR.Key nike) => h.name)
          List.getElem_take.symm
    rw [e0, e1, layerFn_zero nike macS kdfS streamS geom x.2.p.c.req x.2.o.1 _ _ _ _ (by omega),
      layerFn_zero nike macS kdfS streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.keys, (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩
          : ForwardCh nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2.o) _ _ _ _ (by omega),
      nikePktFn_shift nike geom (Function.update (keysKs geom streamS (forwardKeys0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2))) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector (finShift
          nike cipher macS kdfS streamS geom hvalid hmactag h16 x))) (Function.update (keysKs geom
          streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos
          (Util.Bytes.ofVector x.2.U)) (Function.update (keysTag macS (forwardKeys0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x.2).2.2))) default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector
          (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
          nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom
          streamS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
          (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray)
          x.2.p.c.pos (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS geom hvalid
          hmactag h16 x))) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
          default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (toDraw0
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2))) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
          default)).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]) x.2.p.c.pos))))) (Function.update (keysTag macS (forwardKeys0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector
          (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector (Util.Bytes.toVecN (2 +
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
          hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
          default)).toArray) x.2.p.c.pos fun _ => Util.Bytes.ofVector x.2.u) (Function.update
          (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          names (fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (next4X nike
          cipher macS kdfS streamS geom hvalid hmactag h16 x.2)) default)).toArray) x.2.p.c.pos fun
          _ => Util.Bytes.ofVector x.2.u) (blindElem nike (groupElem nike (drawKey nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
          names (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher
          macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names
          (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2))) default)).toArray 0) (forwardKeys0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
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
          default)).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.p.c.req.fwd [.recipient
          x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.filler nike geom (RSOR.path nike ((fwd1 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 names).req (⟨(next4X nike cipher macS
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X nike cipher macS kdfS streamS
          geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike cipher macS kdfS streamS geom hvalid
          hmactag h16 names (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
          x.2).2.2.o).fwd [.recipient ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16
          names).req (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys,
          (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh
          nike cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
          streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2).2.2.o).receiver]) ((fwd1 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2.o).1) (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver])
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
          kdfS streamS geom hvalid hmactag h16 x.2).2.2.o).receiver])
        (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1) (RSOR.body nike macS kdfS
            streamS geom ((fwd1 nike cipher macS kdfS streamS geom hvalid hmactag h16 names).req
            (⟨(next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.keys, (next4X
            nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2.c⟩ : ForwardCh nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (next4X nike cipher macS kdfS
            streamS geom hvalid hmactag h16 x.2).2.2.k.1) (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2.o) ((fwd1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names).rnd (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16
            x.2).2.2.o)) x.2.p.c.pos hposP (by omega) hfront (hgeEq 0 (Nat.zero_le _)) (by
          rw [hdrMsg_update_tag geom _ _ _ _ _ x.2.p.c.pos hposP,
            hdrMsg_update_tag geom _ _ _ _ _ x.2.p.c.pos (by omega)]
          exact hM01) (by rw [Function.update_self, Function.update_self, hT01]) (iso _ _ _)
        (iso' _ _ _) hnnh (by omega) hnP hnP1 (hfillOf _ _) (hfillOf _ _) htagA htg1 hgeAp hge1p
        (Util.Bytes.ofVector x.2.u) (fun b => by rw [Function.update_self])
        (fun b => by rw [Function.update_self]) hb hb']
  have hG : strGuess nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 names) A (x.2.km, sd, (toDraw0 nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
      hmactag h16 x.2).2.2)) (finShift nike cipher macS kdfS streamS geom hvalid hmactag h16 x)
      x.2.u
      = strGuess nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) A (next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2) x.2.U x.2.u := by
    unfold strGuess
    rw [ite_eq_left hlt0, ite_eq_left hlt1]
    exact congrArg (A.guess x.2.p.st) hOn
  rw [finOwnRun_last nike cipher macS kdfS streamS geom hvalid hmactag h16 names A x hlast hT' hb
      hb' hr hv,
    strRun_fwd0_last nike cipher macS kdfS streamS geom hvalid hmactag h16 names A (x.2.km, sd,
        (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS
        kdfS streamS geom hvalid hmactag h16 x.2).2.2)) (finShift nike cipher macS kdfS streamS
        geom hvalid hmactag h16 x) x.2.u x.2.v hlast hT1]
  show (simulateQ (lastRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 ((forwardPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
      streamS geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (A := A) (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16
      (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))) ((forwardPay nike
      cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 names) A).reply (strPay nike cipher macS kdfS streamS geom hvalid
      hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
      (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike
      cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))) (finMine nike cipher macS kdfS
      streamS geom hvalid hmactag h16 x).1 x.2.p.c.req.receiver (fun y => if y = x.2.u then
      Util.Bytes.toVecN _ (((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)) ++ (RSOR.body
      nike macS kdfS streamS geom x.2.p.c.req x.2.o.1)) else x.2.v))
      (strGuess nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd1 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) A (next4X nike cipher macS kdfS streamS geom
          hvalid hmactag h16 x.2) x.2.U x.2.u)).run' x.2.p.log
    = (simulateQ (lastRelay nike cipher macS kdfS streamS geom hvalid hmactag h16 ((forwardPay nike
        cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 names) A).proc (strPay nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A :=
        A) (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))) ((forwardPay nike cipher
        macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 names) A).reply (strPay nike cipher macS kdfS streamS geom hvalid
        hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A :=
        A) (x.2.km, default, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X
        nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))))
        (Util.Bytes.toVecN _ (Util.Bytes.ofVector (Util.Bytes.toVecN (2 + nike.publicKeySize +
            geom.routingInfoLength) (hdrMsg geom (Function.update (keysKs geom streamS
            (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names
            (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km,
            sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher
            macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray) x.2.p.c.pos
            (Util.Bytes.ofVector (finShift nike cipher macS kdfS streamS geom hvalid hmactag h16
            x))) (keysTag macS (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike
            cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16
            names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag
            h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
            default)).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay
            names (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike
            cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS
            geom hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (strPay nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS
            geom hvalid hmactag h16 x.2).2.2))) default)).toArray 0) (forwardKeys0 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
            h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
            nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
            hmactag h16 x.2).2.2))) default)).toArray) (RSOR.filler nike geom (RSOR.path nike
            x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1) (RSOR.path nike
            x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos))
          ++ Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.2.km) (Util.Bytes.ofVector
              (Util.Bytes.toVecN (2 + nike.publicKeySize + geom.routingInfoLength) (hdrMsg geom
              (Function.update (keysKs geom streamS (forwardKeys0 nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid
              hmactag h16 x.2).2.2))) default)).toArray) x.2.p.c.pos (Util.Bytes.ofVector (finShift
              nike cipher macS kdfS streamS geom hvalid hmactag h16 x))) (keysTag macS
              (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (A := A)
              (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid hmactag h16 (next4X
              nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray)
              (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.forwardUnlinkable (S := 𝒮)) .relay names (toDraw0 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2).2.2)) (forwardKeys0 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid
              hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay nike
              cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom
              hvalid hmactag h16 x.2).2.2))) default)).toArray 0) (forwardKeys0 nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom
              hvalid hmactag h16 names) (payRest nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (strPay
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names) (A := A) (x.2.km, sd, (toDraw0 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS
              streamS geom hvalid hmactag h16 x.2).2.2))) default)).toArray) (RSOR.filler nike geom
              (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.o.1.1)
              (RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]) x.2.p.c.pos))))))
              x.2.p.c.req.receiver (fun y => if y = x.2.u then Util.Bytes.toVecN _ (encTrace
              (keysEnc cipher (forwardKeys0 nike cipher macS kdfS streamS geom hvalid hmactag h16
              names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag h16 names) (payRest
              nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
              kdfS streamS geom hvalid hmactag h16 names) (strPay nike cipher macS kdfS streamS
              geom hvalid hmactag h16 names (fwd0 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 names) (A := A) (x.2.km, sd, (toDraw0 nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2).2.2)))
              default)).toArray) (RSOR.path nike x.2.p.c.req.fwd [.recipient
              x.2.p.c.req.receiver]).size (((⟨Array.replicate geom.payloadTagLength 0⟩ :
              ByteArray)) ++ (RSOR.body nike macS kdfS streamS geom x.2.p.c.req x.2.o.1))
              ((RSOR.path nike x.2.p.c.req.fwd [.recipient x.2.p.c.req.receiver]).size - 1 -
              x.2.p.c.pos)) else x.2.v))
      (strGuess nike cipher macS kdfS streamS geom hvalid hmactag h16 names (fwd0 nike cipher macS
          kdfS streamS geom hvalid hmactag h16 names) A (x.2.km, sd, (toDraw0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (next4X nike cipher macS kdfS streamS geom hvalid hmactag
          h16 x.2).2.2)) (finShift nike cipher macS kdfS streamS geom hvalid hmactag h16 x)
          x.2.u)).run' x.2.p.log
  rw [hH, hD, hG]

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
