/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLUDrop

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

/-! # SLU← for NIKE Sphinx: the onion built like a reply layer, in closed form

The header of a layer of a sender's header-only packet is `layerHdr` on the sender's hop keys.
So the onion built like a reply layer (`replySwap`) and the header that goes with it are the
first and the last layer header of a packet over the rest of the backward path. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

include hvalid hmactag h16 in
set_option maxHeartbeats 1000000 in
/-- **The header of a layer of a sender's packet, in closed form**, when the packet builds. -/
theorem layer_fst_closed (R : Protocols.RSOR.Route geom.nrHops Name (RSOR.Key nike))
    (last : List RoutingCommand) (d : RSOR.Draw nike geom) (i : ℕ) (hi : i < R.hops.length)
    (x0 : ByteArray) (hx0 : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike R last) d
        (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) 0 = .ok x0) :
    (match RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike R last) d
        (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) i with
      | .ok pkt => (split geom pkt).1
      | .error _ => (default : Onion geom).1)
      = Util.Bytes.toVecN geom.headerLength (layerHdr geom (keysKs geom streamS (RSOR.hopKeys nike
          kdfS (RSOR.clientKey nike geom d) (RSOR.path nike R last) (RSOR.path nike R
          last).size).toArray) (keysTag macS (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d)
          (RSOR.path nike R last) (RSOR.path nike R last).size).toArray) (groupElem nike
          (RSOR.clientKey nike geom d) (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d)
          (RSOR.path nike R last) (RSOR.path nike R last).size).toArray) (RSOR.filler nike geom
          (RSOR.path nike R last) d) (RSOR.path nike R last) i) := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have hsz := RSOR.path_size nike R last
  have hpn : (RSOR.path nike R last).size ≤ geom.nrHops := by
    rw [hsz]
    exact R.length_le
  have hpos : 0 < (RSOR.path nike R last).size := by
    rw [hsz]
    exact Nat.zero_lt_of_lt hi
  have hi' : i < (RSOR.path nike R last).size := by
    rw [hsz]
    exact hi
  have hmul : (geom.nrHops - (RSOR.path nike R last).size) * geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hfill : (RSOR.filler nike geom (RSOR.path nike R last) d).size = (geom.nrHops - (RSOR.path
      nike R last).size) * geom.perHopRoutingInfoLength := by
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have hks : ∀ m, ((keysKs geom streamS (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d)
      (RSOR.path nike R last) (RSOR.path nike R last).size).toArray) m).size =
      (geom.routingInfoLength + geom.perHopRoutingInfoLength) := fun m => streamS.keystream_size _
      _ _
  have htag : ∀ (m : ℕ) (y : ByteArray), ((keysTag macS (RSOR.hopKeys nike kdfS (RSOR.clientKey
      nike geom d) (RSOR.path nike R last) (RSOR.path nike R last).size).toArray) m y).size =
      macLength := fun m y =>
    (Util.Bytes.size_ofVector _).trans hmactag
  have hge : ((groupElem nike (RSOR.clientKey nike geom d) (RSOR.hopKeys nike kdfS (RSOR.clientKey
      nike geom d) (RSOR.path nike R last) (RSOR.path nike R last).size).toArray) 0).size =
      nike.publicKeySize := Util.Bytes.size_ofVector _
  have hcmd : ∀ m, m + 1 < (RSOR.path nike R last).size → (RSOR.path nike R last)[m]!.commands = []
      := fun m hm => by
    have hm1 : m + 1 < R.hops.length := by
      rw [hsz] at hm
      exact hm
    have hm0 : m < R.hops.length := by omega
    rw [RSOR.path_getElem! nike _ _ m hm0]
    exact ite_eq_right (by omega)
  have hz : (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray).size =
      geom.forwardPayloadLength := Array.size_replicate
  have hzt : (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray).size = geom.payloadTagLength
      := Array.size_replicate
  have hK : i ≤ (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d) (RSOR.path nike R last)
      (RSOR.path nike R last).size).length := by
    rw [← hopKeysWith_hopKey nike kdfS (RSOR.clientKey nike geom d) (RSOR.path nike R last) 0
        (RSOR.path nike R last).size, hopKeysWith_length]
    exact le_of_lt hi'
  have hp := layer_zero_pktFn nike cipher macS kdfS streamS geom (RSOR.path nike R last) d
      (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) x0 hx0
    (RSOR.path_keys nike R last)
  rw [layer_peels nike cipher macS kdfS streamS geom _ _ _ i (RSOR.path nike R last).size (le_of_lt
      hi'), hx0]
  show (split geom (peels nike cipher streamS geom (RSOR.hopKeys nike kdfS (RSOR.clientKey nike
      geom d) (RSOR.path nike R last) (RSOR.path nike R last).size) i x0)).1 = _
  unfold nikePktFn at hp
  rw [ite_eq_left hz] at hp
  cases hs : nikeHdrTrace geom (keysKs geom streamS (RSOR.hopKeys nike kdfS (RSOR.clientKey nike
      geom d) (RSOR.path nike R last) (RSOR.path nike R last).size).toArray) (keysTag macS
      (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d) (RSOR.path nike R last) (RSOR.path nike
      R last).size).toArray) (groupElem nike (RSOR.clientKey nike geom d) (RSOR.hopKeys nike kdfS
      (RSOR.clientKey nike geom d) (RSOR.path nike R last) (RSOR.path nike R last).size).toArray)
      (RSOR.filler nike geom (RSOR.path nike R last) d) (RSOR.path nike R last) (RSOR.path nike R
      last).size with
  | none =>
    rw [hs] at hp
    cases hp
  | some s =>
    rw [hs] at hp
    have hH := hdr_size geom nike.publicKeySize _ _ _ _ _ hnnh (by omega) hrouting hpn hpos hfill
      htag hge s hs
    have hE : 0 < ((List.range' 0 (RSOR.path nike R last).size).foldl
        (fun b iRev => keysEnc cipher (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d)
            (RSOR.path nike R last) (RSOR.path nike R last).size).toArray ((RSOR.path nike R
            last).size - 1 - iRev) b)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ (⟨Array.replicate
            geom.forwardPayloadLength 0⟩ : ByteArray))).size := by
      have e := encTrace_keysEnc_size cipher (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d)
          (RSOR.path nike R last) (RSOR.path nike R last).size).toArray (RSOR.path nike R
          last).size ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ (⟨Array.replicate
          geom.forwardPayloadLength 0⟩ : ByteArray)) (RSOR.path nike R last).size
      unfold encTrace at e
      rw [e, ByteArray.size_append, hzt, hz]
      omega
    obtain ⟨P1, -, e1, s1⟩ := peels_append_hdr nike cipher streamS geom (RSOR.hopKeys nike kdfS
        (RSOR.clientKey nike geom d) (RSOR.path nike R last) (RSOR.path nike R last).size) _ _ hH
        hE i hK
    have hL := (hdrPeels_layerHdr nike geom streamS (RSOR.hopKeys nike kdfS (RSOR.clientKey nike
        geom d) (RSOR.path nike R last) (RSOR.path nike R last).size) (keysKs geom streamS
        (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d) (RSOR.path nike R last) (RSOR.path
        nike R last).size).toArray) (keysTag macS (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom
        d) (RSOR.path nike R last) (RSOR.path nike R last).size).toArray) (groupElem nike
        (RSOR.clientKey nike geom d) (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d)
        (RSOR.path nike R last) (RSOR.path nike R last).size).toArray) (RSOR.filler nike geom
        (RSOR.path nike R last) d) (RSOR.path nike R last) hnnh
      (by omega) hrouting hpn hfill hks htag hge hcmd (by rw [hs]; rfl) i hi' hK
      (fun _ _ => rfl) (fun _ _ => rfl)).1
    rw [← Option.some.inj hp]
    refine Eq.trans (congrArg (fun p => (split geom p).1) e1) ?_
    rw [layerHdr_zero geom _ _ _ _ _ s hpos hs] at s1 ⊢
    rw [hL] at s1 ⊢
    have := Util.Bytes.extract_append_left (layerHdr geom (keysKs geom streamS (RSOR.hopKeys nike
        kdfS (RSOR.clientKey nike geom d) (RSOR.path nike R last) (RSOR.path nike R
        last).size).toArray) (keysTag macS (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d)
        (RSOR.path nike R last) (RSOR.path nike R last).size).toArray) (groupElem nike
        (RSOR.clientKey nike geom d) (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom d)
        (RSOR.path nike R last) (RSOR.path nike R last).size).toArray) (RSOR.filler nike geom
        (RSOR.path nike R last) d) (RSOR.path nike R last) i) P1
    rw [s1.trans hhdr.symm] at this
    exact congrArg (Util.Bytes.toVecN _) this

include hvalid hmactag h16 in
/-- **The onion built like a reply layer, in closed form**: the header of the first layer of a
packet over the rest of the backward path, and the block drawn with it. -/
theorem replySwap_fst {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.BackwardChallenge hon) (x : RSOR.Randomness nike geom × Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) (x0 : ByteArray)
    (hx0 : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike (c.req.back.drop c.pos)
        [.surbReply x.1.2.2.2]) x.1.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) 0
        = .ok x0) :
    ((replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16).of c x).1 =
        ((Util.Bytes.toVecN geom.headerLength (layerHdr geom (keysKs geom streamS (RSOR.hopKeys
        nike kdfS (RSOR.clientKey nike geom x.1.1) (RSOR.path nike (c.req.back.drop c.pos)
        [.surbReply x.1.2.2.2]) (RSOR.path nike (c.req.back.drop c.pos) [.surbReply
        x.1.2.2.2]).size).toArray) (keysTag macS (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom
        x.1.1) (RSOR.path nike (c.req.back.drop c.pos) [.surbReply x.1.2.2.2]) (RSOR.path nike
        (c.req.back.drop c.pos) [.surbReply x.1.2.2.2]).size).toArray) (groupElem nike
        (RSOR.clientKey nike geom x.1.1) (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom x.1.1)
        (RSOR.path nike (c.req.back.drop c.pos) [.surbReply x.1.2.2.2]) (RSOR.path nike
        (c.req.back.drop c.pos) [.surbReply x.1.2.2.2]).size).toArray) (RSOR.filler nike geom
        (RSOR.path nike (c.req.back.drop c.pos) [.surbReply x.1.2.2.2]) x.1.1) (RSOR.path nike
        (c.req.back.drop c.pos) [.surbReply x.1.2.2.2]) 0)), x.2) := by
  have hlen : 0 < (c.req.back.drop c.pos).hops.length := by
    show 0 < (c.req.back.hops.drop c.pos).length
    rw [List.length_drop]
    exact Nat.sub_pos_of_lt c.pos.isLt
  have h := layer_fst_closed nike cipher macS kdfS streamS geom hvalid hmactag h16 (c.req.back.drop
      c.pos)
    [.surbReply x.1.2.2.2] x.1.1 0 hlen x0 hx0
  rw [hx0] at h
  show (match RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike (c.req.back.drop c.pos)
      [.surbReply x.1.2.2.2]) x.1.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) 0
      with
    | .ok pkt => ((split geom pkt).1, x.2)
    | .error _ => (default : Onion geom)) = _
  rw [hx0]
  exact Prod.ext h rfl

include hvalid hmactag h16 in
/-- **The header that goes with it**: the header of that packet's last layer. -/
theorem replySwap_snd {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.BackwardChallenge hon) (x : RSOR.Randomness nike geom × Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) (x0 : ByteArray)
    (hx0 : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike (c.req.back.drop c.pos)
        [.surbReply x.1.2.2.2]) x.1.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) 0
        = .ok x0) :
    ((replySwap nike cipher macS kdfS streamS geom hvalid hmactag h16).of c x).2 =
        (Util.Bytes.toVecN geom.headerLength (layerHdr geom (keysKs geom streamS (RSOR.hopKeys nike
        kdfS (RSOR.clientKey nike geom x.1.1) (RSOR.path nike (c.req.back.drop c.pos) [.surbReply
        x.1.2.2.2]) (RSOR.path nike (c.req.back.drop c.pos) [.surbReply x.1.2.2.2]).size).toArray)
        (keysTag macS (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom x.1.1) (RSOR.path nike
        (c.req.back.drop c.pos) [.surbReply x.1.2.2.2]) (RSOR.path nike (c.req.back.drop c.pos)
        [.surbReply x.1.2.2.2]).size).toArray) (groupElem nike (RSOR.clientKey nike geom x.1.1)
        (RSOR.hopKeys nike kdfS (RSOR.clientKey nike geom x.1.1) (RSOR.path nike (c.req.back.drop
        c.pos) [.surbReply x.1.2.2.2]) (RSOR.path nike (c.req.back.drop c.pos) [.surbReply
        x.1.2.2.2]).size).toArray) (RSOR.filler nike geom (RSOR.path nike (c.req.back.drop c.pos)
        [.surbReply x.1.2.2.2]) x.1.1) (RSOR.path nike (c.req.back.drop c.pos) [.surbReply
        x.1.2.2.2]) ((c.req.back.drop c.pos).hops.length - 1))) := by
  have hlen : 0 < (c.req.back.drop c.pos).hops.length := by
    show 0 < (c.req.back.hops.drop c.pos).length
    rw [List.length_drop]
    exact Nat.sub_pos_of_lt c.pos.isLt
  exact layer_fst_closed nike cipher macS kdfS streamS geom hvalid hmactag h16 (c.req.back.drop
      c.pos)
    [.surbReply x.1.2.2.2] x.1.1 ((c.req.back.drop c.pos).hops.length - 1)
    (Nat.sub_one_lt (Nat.ne_of_gt hlen)) x0 hx0

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
