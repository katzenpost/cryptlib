/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.NIKESphinxSLUPay

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

/-! # SLU← for NIKE Sphinx: the reply's headers in closed form

The header of each layer of the reply's packet over the backward path is `layerHdr` on the
hops' keystreams, tags and group elements. So a hop's keystream may be replaced in it by
substitution. -/

section Final

variable (nike : NIKE) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry) (hvalid : geom.ValidForNIKE nike)
  (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx nike cipher macS kdfS streamS geom hvalid hmactag h16

/-- The header of layer `i` of the reply's packet over the backward path, from the hops'
keystreams, tagging functions and group elements. -/
def backHdrFn (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (ks : ℕ → ByteArray)
    (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) (i : ℕ) :
    Vector UInt8 geom.headerLength :=
  match nikeHdrTrace geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply
      r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) (RSOR.path nike q.back
      [.surbReply r.2.2.2]).size with
  | some _ => Util.Bytes.toVecN _ (layerHdr geom ks tag ge (RSOR.filler nike geom (RSOR.path nike
      q.back [.surbReply r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) i)
  | none => default

/-- The header of its first layer as bytes, empty when the header does not build. -/
def backHdrBytes (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (ks : ℕ → ByteArray)
    (tag : ℕ → ByteArray → ByteArray) (ge : ℕ → ByteArray) : ByteArray :=
  match nikeHdrTrace geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply
      r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) (RSOR.path nike q.back
      [.surbReply r.2.2.2]).size with
  | some _ => layerHdr geom ks tag ge (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply
      r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) 0
  | none => ByteArray.empty

include hvalid hmactag in
/-- **The reply block's header is the first layer's, in closed form.** -/
theorem backHdrOfTag_eq (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (K : List HopKeys) (j : ℕ) (tag : ByteArray) (hb : 0 < q.back.hops.length)
    (ha : a.size = nike.publicKeySize) (ht : tag.size = macLength) :
    backHdrOfTag nike cipher macS streamS geom q r a K j tag
      = backHdrBytes nike geom q r (keysKs geom streamS K.toArray) (Function.update (keysTag macS
          K.toArray) j fun _ => tag) (blindElem nike a K.toArray) := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have hsz := RSOR.path_size nike q.back [.surbReply r.2.2.2]
  have hlen : q.back.hops.length ≤ geom.nrHops := q.back.length_le
  have hn : (RSOR.path nike q.back [.surbReply r.2.2.2]).size ≤ geom.nrHops := by
    rw [hsz]
    exact hlen
  have hpos : 0 < (RSOR.path nike q.back [.surbReply r.2.2.2]).size := by
    rw [hsz]
    exact hb
  have hmul : (geom.nrHops - (RSOR.path nike q.back [.surbReply r.2.2.2]).size) *
      geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hfill : (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply r.2.2.2]) r.2.1).size =
      (geom.nrHops - (RSOR.path nike q.back [.surbReply r.2.2.2]).size) *
      geom.perHopRoutingInfoLength := by
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have htag : ∀ (m : ℕ) (x : ByteArray), ((Function.update (keysTag macS K.toArray) j fun _ => tag)
      m x).size = macLength := fun m x => by
    by_cases hm : m = j
    · rw [hm, Function.update_self]
      exact ht
    · rw [Function.update_of_ne hm]
      exact (Util.Bytes.size_ofVector _).trans hmactag
  have hz : (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray).size =
      geom.forwardPayloadLength := Array.size_replicate
  unfold backHdrOfTag backHdrBytes nikePktFn
  rw [ite_eq_left hz]
  cases hs : nikeHdrTrace geom (keysKs geom streamS K.toArray) (Function.update (keysTag macS
      K.toArray) j fun _ => tag) (blindElem nike a K.toArray) (RSOR.filler nike geom (RSOR.path
      nike q.back [.surbReply r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2])
      (RSOR.path nike q.back [.surbReply r.2.2.2]).size with
  | none => rfl
  | some s =>
    have hH := hdr_size geom nike.publicKeySize _ _ _ _ _ hnnh (by omega) hrouting hn hpos hfill
      htag ha s hs
    have hx : ∀ B : ByteArray,
        (v0AD ++ (blindElem nike a K.toArray) 0 ++ s.1 ++ s.2 ++ B).extract 0 geom.headerLength
          = v0AD ++ (blindElem nike a K.toArray) 0 ++ s.1 ++ s.2 := fun B => by
      have := Util.Bytes.extract_append_left (v0AD ++ (blindElem nike a K.toArray) 0 ++ s.1 ++ s.2)
          B
      rwa [hH.trans hhdr.symm] at this
    exact (hx _).trans (layerHdr_zero geom _ _ _ _ _ s hpos hs)

include hvalid hmactag h16 in
/-- **The header of each layer of the reply's packet, in closed form.** -/
theorem backLayerOfTag_fst (i : ℕ) (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a
    : ByteArray)
    (K : List HopKeys) (j : ℕ) (tag : ByteArray) (hi : i < q.back.hops.length)
    (hiK : i ≤ K.length) (ha : a.size = nike.publicKeySize) (ht : tag.size = macLength) :
    (backLayerOfTag nike cipher macS streamS geom i q r a K j tag).1
      = backHdrFn nike geom q r (keysKs geom streamS K.toArray) (Function.update (keysTag macS
          K.toArray) j fun _ => tag) (blindElem nike a K.toArray) i := by
  have hb : 0 < q.back.hops.length := Nat.zero_lt_of_lt hi
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  have hsz := RSOR.path_size nike q.back [.surbReply r.2.2.2]
  have hlen : q.back.hops.length ≤ geom.nrHops := q.back.length_le
  have hn : (RSOR.path nike q.back [.surbReply r.2.2.2]).size ≤ geom.nrHops := by
    rw [hsz]
    exact hlen
  have hpos : 0 < (RSOR.path nike q.back [.surbReply r.2.2.2]).size := by
    rw [hsz]
    exact hb
  have hmul : (geom.nrHops - (RSOR.path nike q.back [.surbReply r.2.2.2]).size) *
      geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hfill : (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply r.2.2.2]) r.2.1).size =
      (geom.nrHops - (RSOR.path nike q.back [.surbReply r.2.2.2]).size) *
      geom.perHopRoutingInfoLength := by
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have htag : ∀ (m : ℕ) (x : ByteArray), ((Function.update (keysTag macS K.toArray) j fun _ => tag)
      m x).size = macLength := fun m x => by
    by_cases hm : m = j
    · rw [hm, Function.update_self]
      exact ht
    · rw [Function.update_of_ne hm]
      exact (Util.Bytes.size_ofVector _).trans hmactag
  have hz : (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray).size =
      geom.forwardPayloadLength := Array.size_replicate
  have hks : ∀ k, ((keysKs geom streamS K.toArray) k).size = geom.routingInfoLength +
      geom.perHopRoutingInfoLength :=
    fun k => streamS.keystream_size _ _ _
  have hcmd : ∀ m, m + 1 < (RSOR.path nike q.back [.surbReply r.2.2.2]).size → (RSOR.path nike
      q.back [.surbReply r.2.2.2])[m]!.commands = [] := fun m hm => by
    have hm1 : m + 1 < q.back.hops.length := by
      rw [hsz] at hm
      exact hm
    have hm0 : m < q.back.hops.length := by omega
    rw [RSOR.path_getElem! nike _ _ m hm0]
    exact ite_eq_right (by omega)
  have hi' : i < (RSOR.path nike q.back [.surbReply r.2.2.2]).size := by
    rw [hsz]
    exact hi
  unfold backLayerOfTag backHdrFn nikePktFn
  rw [ite_eq_left hz]
  cases hs : nikeHdrTrace geom (keysKs geom streamS K.toArray) (Function.update (keysTag macS
      K.toArray) j fun _ => tag) (blindElem nike a K.toArray) (RSOR.filler nike geom (RSOR.path
      nike q.back [.surbReply r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2])
      (RSOR.path nike q.back [.surbReply r.2.2.2]).size with
  | none => rfl
  | some s =>
    have hH := hdr_size geom nike.publicKeySize _ _ _ _ _ hnnh (by omega) hrouting hn hpos hfill
      htag ha s hs
    have hzt : (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray).size = geom.payloadTagLength
        := Array.size_replicate
    have hE : 0 < ((List.range' 0 (RSOR.path nike q.back [.surbReply r.2.2.2]).size).foldl
        (fun b iRev => keysEnc cipher K.toArray ((RSOR.path nike q.back [.surbReply r.2.2.2]).size
            - 1 - iRev) b)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ (⟨Array.replicate
            geom.forwardPayloadLength 0⟩ : ByteArray))).size := by
      have e := encTrace_keysEnc_size cipher K.toArray (RSOR.path nike q.back [.surbReply
          r.2.2.2]).size ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++
          (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)) (RSOR.path nike q.back
          [.surbReply r.2.2.2]).size
      unfold encTrace at e
      rw [e, ByteArray.size_append, hzt, hz]
      omega
    obtain ⟨P1, -, e1, s1⟩ := peels_append_hdr nike cipher streamS geom K _ _ hH hE i hiK
    have hL := (hdrPeels_layerHdr nike geom streamS K (keysKs geom streamS K.toArray)
        (Function.update (keysTag macS K.toArray) j fun _ => tag) (blindElem nike a K.toArray)
        (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply r.2.2.2]) r.2.1) (RSOR.path nike
        q.back [.surbReply r.2.2.2]) hnnh
      (by omega) hrouting hn hfill hks htag ha hcmd (by rw [hs]; rfl) i hi' hiK
      (fun _ _ => rfl) (fun _ _ => rfl)).1
    refine Eq.trans (congrArg (fun p => (split geom p).1) e1) ?_
    rw [layerHdr_zero geom _ _ _ _ _ s hpos hs] at s1 ⊢
    rw [hL] at s1 ⊢
    show (split geom _).1 = _
    have := Util.Bytes.extract_append_left
      (layerHdr geom (keysKs geom streamS K.toArray) (Function.update (keysTag macS K.toArray) j
          fun _ => tag) (blindElem nike a K.toArray) (RSOR.filler nike geom (RSOR.path nike q.back
          [.surbReply r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) i) P1
    rw [s1.trans hhdr.symm] at this
    exact congrArg (Util.Bytes.toVecN _) this

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
