/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLURelay

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

/-! # SLU← for NIKE Sphinx: world 0 on the backward path, on the hops' functions

Before the end of the backward path, world 0 played from a uniform keystream at the honest
relay is a game on the keystreams, tagging functions and group elements of the backward path's
hops. That is the form in which the hops after the relay can be replaced. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

omit nike cipher macS kdfS streamS hvalid hmactag h16 in
/-- The bytes under a tag read the tagging functions through the header built so far. -/
theorem hdrMsg_congr_trace (ks : ℕ → ByteArray) (tag tag' : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (fil : ByteArray) (path : Array PathHop) (i : ℕ)
    (h : nikeHdrTrace geom ks tag ge fil path (path.size - 1 - i)
      = nikeHdrTrace geom ks tag' ge fil path (path.size - 1 - i)) :
    hdrMsg geom ks tag ge fil path i = hdrMsg geom ks tag' ge fil path i := by
  unfold hdrMsg
  rw [h]

omit nike cipher macS kdfS streamS hvalid hmactag h16 in
/-- **A layer's header uses a hop's tagging function once**, on the bytes under that hop's
tag. -/
theorem layerHdr_tagAt (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (fil : ByteArray) (path : Array PathHop) (j : ℕ) (hj : j < path.size)
    (f : ByteArray → ByteArray) (i : ℕ) :
    layerHdr geom ks (Function.update tag j f) ge fil path i
      = layerHdr geom ks (Function.update tag j fun _ => f (hdrMsg geom ks tag ge fil path j))
        ge fil path i := by
  have hm := hdrMsg_congr_trace geom ks (Function.update tag j f)
    (Function.update tag j fun _ => f (hdrMsg geom ks tag ge fil path j)) ge fil path i
    (nikeHdrTrace_tagAt geom ks tag ge fil path j hj f (path.size - 1 - i) (by omega))
  unfold layerHdr
  rw [hm]
  by_cases hi : i = j
  · rw [hi, Function.update_self, Function.update_self,
      hdrMsg_update_tag geom _ _ _ _ _ j hj]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

omit cipher macS kdfS streamS hvalid hmactag h16 in
theorem backHdrFn_tagAt (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (ks : ℕ →
    ByteArray)
    (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) (j : ℕ)
    (hj : j < (RSOR.path nike q.back [.surbReply r.2.2.2]).size) (f : ByteArray → ByteArray) (i :
        ℕ) :
    backHdrFn nike geom q r ks (Function.update tag j f) ge i
      = backHdrFn nike geom q r ks (Function.update tag j fun _ =>
          f (hdrMsg geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply
              r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) j)) ge i := by
  unfold backHdrFn
  rw [nikeHdrTrace_tagAt geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply
      r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) j hj f _ le_rfl,
    layerHdr_tagAt geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply
        r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) j hj f i]

omit cipher macS kdfS streamS hvalid hmactag h16 in
theorem backHdrBytes_tagAt (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (ks : ℕ →
    ByteArray)
    (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) (j : ℕ)
    (hj : j < (RSOR.path nike q.back [.surbReply r.2.2.2]).size) (f : ByteArray → ByteArray) :
    backHdrBytes nike geom q r ks (Function.update tag j f) ge
      = backHdrBytes nike geom q r ks (Function.update tag j fun _ =>
          f (hdrMsg geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply
              r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) j)) ge := by
  unfold backHdrBytes
  rw [nikeHdrTrace_tagAt geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply
      r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) j hj f _ le_rfl,
    layerHdr_tagAt geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply
        r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) j hj f 0]

variable (W : Protocols.RSOR.BackSwap (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
  h16))

/-- **World 0 on the backward path, from the hops' functions.** The adversary's onion carries
the header of the reply's first layer; under the header of the layer at the honest relay the
relay forwards the header of the next layer with the block it decrypts; and the sender refuses
the header of the last layer. -/
def backFnRun0 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropStrX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (u v : Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) :
    ProbComp Bool :=
  (simulateQ (fwdRelay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (fun (h : Role) (o : Onion geom) =>
        if h = Role.sender ∧ o.1 = backHdrFn nike geom x.2.2.c.req x.2.2.o.1 ks tag ge
            (x.2.2.c.req.back.hops.length - 1) then none
        else (fun h o => if h = Role.relay then
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
      (Util.Bytes.toVecN geom.headerLength (layerHdr geom ks tag ge (RSOR.filler nike geom
          (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path
          nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)))
      (RSOR.path nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2])[(drawPos nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) + 1]!.id (layerHdr
          geom ks tag ge (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply
          x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply
          x.2.2.o.1.2.2.2]) ((drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) + 1)) (fun y => if y = u then x.2.2.o.2 else v))
    (A.guess x.2.2.st (backOnionOfHdr nike cipher macS kdfS streamS geom x.2.2.c.req x.2.2.o.1
      (Nat.zero_lt_of_lt x.2.2.c.pos.isLt)
      (backHdrBytes nike geom x.2.2.c.req x.2.2.o.1 ks tag ge)))).run' x.2.2.log

/-- **World 0 before the end of the backward path is that game** on the hops' keystreams, the
honest relay's replaced by the uniform one; their tags, the relay's replaced by its tag; and
their elements. -/
theorem backRun0_fn {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
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
      = backFnRun0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x u v (Function.update
          (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
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
          default) default).toArray) := by
  have hJ : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) = k := backPos_back nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W x.2.2 k hk
  have hsz := RSOR.path_size nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]
  have hJs : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) < (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]).size := by
    rw [hsz, hJ]
    exact lt_trans (Nat.lt_succ_self k) hn
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
  have hL : layerHdr geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
      cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      x) default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
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
      default).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2)
      = (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U) ++
          Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1) (backMS0 nike cipher macS kdfS
          streamS geom hvalid hmactag h16 W x U)) := by
    unfold layerHdr
    rw [hdrMsg_update_tag geom _ _ _ _ _ (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W names) x.2.2) hJs, Function.update_self, ← hMS]
  rw [backRun0_fwd nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U u v k hk hn hT]
  unfold backFnRun0
  rw [hL]

/-- **The same, with the honest relay's tag as its MAC** on whatever the header puts under
it. -/
theorem backRun0_fnMac {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
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
      = backFnRun0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x u v (Function.update
          (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
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
          geom hvalid hmactag h16 W names) x.2.2) (fun m => Util.Bytes.ofVector (macS.mac
          (Util.Bytes.ofVector x.1) m))) (blindElem nike (groupElem nike (drawKey nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2)
          (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray) := by
  have hJ : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) = k := backPos_back nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W x.2.2 k hk
  have hsz := RSOR.path_size nike x.2.2.c.req.back [.surbReply x.2.2.o.1.2.2.2]
  have hJs : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2.2) < (RSOR.path nike x.2.2.c.req.back [.surbReply
      x.2.2.o.1.2.2.2]).size := by
    rw [hsz, hJ]
    exact lt_trans (Nat.lt_succ_self k) hn
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
  rw [backRun0_fn nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U u v k hk hn hT]
  unfold backFnRun0
  rw [backHdrFn_tagAt nike geom x.2.2.c.req x.2.2.o.1 (Function.update (keysKs geom streamS
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
      W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
      (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray)
      (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
      W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
      x.2.2) (Util.Bytes.ofVector U)) (keysTag macS (drawKeys nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
      kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray 0) (drawKeys nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (drawPos nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2) hJs (fun m
      => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector x.1) m)),
    backHdrBytes_tagAt nike geom x.2.2.c.req x.2.2.o.1 (Function.update (keysKs geom streamS
        (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)) (keysTag macS (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS
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
        hvalid hmactag h16 W names) x.2.2) hJs (fun m => Util.Bytes.ofVector (macS.mac
        (Util.Bytes.ofVector x.1) m)),
    layerHdr_tagAt geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
        nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (drawPos nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)
        (Util.Bytes.ofVector U)) (keysTag macS (drawKeys nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
        default) default).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2)
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
        default).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply
        x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply
        x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) hJs (fun m => Util.Bytes.ofVector (macS.mac
        (Util.Bytes.ofVector x.1) m)) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W names) x.2.2),
    layerHdr_tagAt geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
        nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (drawPos nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)
        (Util.Bytes.ofVector U)) (keysTag macS (drawKeys nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
        default) default).toArray) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2)
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
        default).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back [.surbReply
        x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply
        x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) hJs (fun m => Util.Bytes.ofVector (macS.mac
        (Util.Bytes.ofVector x.1) m)) ((drawPos nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W names) x.2.2) + 1), ← hMS]

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
