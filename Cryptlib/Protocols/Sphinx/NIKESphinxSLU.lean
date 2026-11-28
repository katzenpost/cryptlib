/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxTLUFinal
import Cryptlib.Protocols.Sphinx.KEMSphinxSLU

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

/-! # Backward layer unlinkability (SLU←) for NIKE Sphinx

A reply's layers are the layers of a packet over the backward path, with the payload as the
relays before left it (`RSOR.formBack`), and the reply block in the sender's payload is the
header of the first of them. So the honest relay's layer of a reply is keyed as its layer of a
forward onion is. The games of SLU← with any onion sent on in world 1 (`backwardWith`) are those
of `KEMSphinxSLU.lean`, which are stated for any scheme. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

include hvalid hmactag in
/-- **The reply block is the header of the first layer on the backward path**, then the first
relay's name and the reply's payload key. -/
theorem surb_fst (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (payload x0 : ByteArray) (hb : 0 < q.back.hops.length)
    (hx0 : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike q.back [.surbReply
        r.2.2.2]) r.2.1 payload 0 = .ok x0) :
    (RSOR.surb nike macS kdfS streamS geom q r).1
      = x0.extract 0 geom.headerLength ++ Util.Bytes.ofVector (q.back.hops[0]'hb).name
        ++ Util.Bytes.ofVector r.2.2.1 := by
  obtain ⟨p, hp, hfold⟩ := (RSOR.layer_ok nike cipher macS kdfS streamS geom _ _ _ 0 x0).1 hx0
  obtain rfl : p = x0 := hfold
  obtain ⟨-, hdr, keys, t, hcreate, -, -, hx⟩ :=
    newNIKEPacket_unfold nike cipher macS kdfS streamS geom _ _ _ _ _ hp
  have hh := createHeader_hdr_size nike macS kdfS streamS geom _ _ _ hdr keys hvalid hmactag
    hcreate
  have hxh : p.extract 0 geom.headerLength = hdr := by
    rw [hx, ← hh]
    exact Util.Bytes.extract_append_left hdr _
  unfold RSOR.surb
  dsimp only
  rw [RSOR.newNIKESURB_eq nike macS kdfS streamS geom _ _ _ _ _ _ hcreate,
    RSOR.path_getElem! nike _ _ 0 hb, hxh]

/-- **A reply layer has the header of the layer on the backward path.** -/
theorem formBack_fst (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (m : Msg geom)
    (j : Fin q.back.hops.length) (pkt : ByteArray)
    (h : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike q.back [.surbReply r.2.2.2])
        r.2.1
      ⟨Array.replicate geom.forwardPayloadLength 0⟩ j = .ok pkt)
    (hsz : geom.headerLength ≤ pkt.size) :
    (RSOR.formBack nike cipher macS kdfS streamS geom q r m j).1 = (split geom pkt).1 := by
  have hA : (pkt.extract 0 geom.headerLength).size = geom.headerLength := by
    rw [ByteArray.size_extract]
    omega
  unfold RSOR.formBack
  dsimp only
  rw [h]
  dsimp only
  rw [split_append_bytes geom _ _ hA]
  unfold split
  rfl

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
