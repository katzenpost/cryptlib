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


/-! ## Replacing a hop's header key and IV -/

omit cipher hvalid hmactag h16 in
/-- **Replacing a hop's header key and IV changes the hops' keys in those only**, and of the
functions a packet reads, in that hop's keystream only. -/
theorem hopKeysWith_streamKey (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ)
    (t t' : HopKeys) (ht : (fun k : HopKeys => (k.headerMAC, k.payloadEncryption,
        k.blindingFactor)) t = (fun k : HopKeys => (k.headerMAC, k.payloadEncryption,
        k.blindingFactor)) t') (n : ℕ) (hj : j < n) :
    (∀ i, i ≠ j → (hopKeysWith nike kdfS c hops j t n).toArray[i]! = (hopKeysWith nike kdfS c hops
        j t' n).toArray[i]!)
      ∧ (hopKeysWith nike kdfS c hops j t n).toArray[j]! = { (hopKeysWith nike kdfS c hops j t'
          n).toArray[j]! with
        headerEncryption := ((hopKeysWith nike kdfS c hops j t n).toArray[j]!).headerEncryption
        headerEncryptionIV := ((hopKeysWith nike kdfS c hops j t n).toArray[j]!).headerEncryptionIV
            }
      ∧ keysKs geom streamS (hopKeysWith nike kdfS c hops j t n).toArray
        = Function.update (keysKs geom streamS (hopKeysWith nike kdfS c hops j t' n).toArray) j
          (keysKs geom streamS (hopKeysWith nike kdfS c hops j t n).toArray j)
      ∧ keysTag macS (hopKeysWith nike kdfS c hops j t n).toArray = keysTag macS (hopKeysWith nike
          kdfS c hops j t' n).toArray
      ∧ ∀ a, blindElem nike a (hopKeysWith nike kdfS c hops j t n).toArray = blindElem nike a
          (hopKeysWith nike kdfS c hops j t' n).toArray := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := t
  obtain ⟨b1, b2, b3, b4, b5⟩ := t'
  simp only [Prod.mk.injEq] at ht
  obtain ⟨rfl, rfl, rfl⟩ := ht
  have hc := hopKeysWith_congr nike kdfS c hops j (⟨a1, a2, a3, a4, a5⟩ : HopKeys)
    (⟨a1, b2, b3, a4, a5⟩ : HopKeys) rfl n
  have h1 := toArray_getElem!_of_getElem? _ _ _
    (hopKeysWith_getElem nike kdfS c hops j (⟨a1, a2, a3, a4, a5⟩ : HopKeys) n hj)
  have h2 := toArray_getElem!_of_getElem? _ _ _
    (hopKeysWith_getElem nike kdfS c hops j (⟨a1, b2, b3, a4, a5⟩ : HopKeys) n hj)
  have hne : ∀ i, i ≠ j → (hopKeysWith nike kdfS c hops j (⟨a1, a2, a3, a4, a5⟩ : HopKeys)
      n).toArray[i]! = (hopKeysWith nike kdfS c hops j (⟨a1, b2, b3, a4, a5⟩ : HopKeys)
      n).toArray[i]! := fun i hi => toArray_getElem!_congr _ _ i (hc.2 i hi)
  refine ⟨hne, ?_, funext fun i => ?_, funext fun i => ?_, fun a => funext fun i => ?_⟩
  · rw [h1, h2]
  · by_cases hi : i = j
    · rw [hi, Function.update_self]
    · rw [Function.update_of_ne hi]
      unfold keysKs
      rw [hne i hi]
  · unfold keysTag
    by_cases hi : i = j
    · rw [hi, h1, h2]
    · rw [hne i hi]
  · refine blindElem_congr nike a _ _ (fun m => ?_) i
    by_cases hm : m = j
    · rw [hm, h1, h2]
    · rw [hne m hm]

/-! ## World 0 from the honest relay's header keystream -/

/-- The adversary's first layer, from the reply block's header. -/
def backOnionOfHdr (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (hb : 0 <
    q.back.hops.length)
    (hdr : ByteArray) : Onion geom :=
  match RSOR.layer nike cipher macS kdfS streamS geom
      (RSOR.path nike q.fwd [.recipient q.receiver]) r.1 (bodyH nike geom q r hb hdr) 0 with
  | .ok pkt => split geom pkt
  | .error _ => default

/-- World 0 on the backward path, from the reply block's header and the header the sender
refuses. -/
def backW0Of (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (hb : 0 <
    q.back.hops.length)
    (hdr : ByteArray) (last : Vector UInt8 geom.headerLength) : Protocols.RSOR.World 𝒮 :=
  { onion := backOnionOfHdr nike cipher macS kdfS streamS geom q r hb hdr
    patch :=
      { proc := fun (h : Role) (o : Onion geom) out =>
          if h = .sender ∧ o.1 = last then pure none else pure out } }

variable (W : Protocols.RSOR.BackSwap (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
  h16))

/-- World 0 on the backward path, in that form. -/
theorem backViewTAt_back_form (names : Role → Name) {pk : RSOR.Key nike}
    (ch : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names pk) (ow : RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength
        + geom.forwardPayloadLength))) (a : ByteArray) (K : List HopKeys) (j : ℕ)
    (tag : ByteArray) (k : ℕ) (hp : ch.c.pos.val = k + 1)
    (hb : 0 < ch.c.req.back.hops.length) :
    backViewTAt nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch ow a K j tag
      = backW0Of nike cipher macS kdfS streamS geom hvalid hmactag h16 ch.c.req ow.1 hb
        (backHdrOfTag nike cipher macS streamS geom ch.c.req ow.1 a K j tag)
        (backLayerOfTag nike cipher macS streamS geom (ch.c.req.back.hops.length - 1) ch.c.req
          ow.1 a K j tag).1 := by
  unfold backViewTAt
  rw [hp]
  rfl

theorem backM0_exit {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : Rest
    × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
    W) .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (hp : x.2.c.pos.val = 0) :
    backM0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x = onionMsg nike macS streamS
        geom x.2.c.req x.2.o.1
      (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names x.2) (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) x default).toArray 0)
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          x default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2) := by
  unfold backM0 backMsgAt
  dsimp only
  rw [hp]

theorem backM0_back {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : Rest
    × PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
    W) .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (k : ℕ) (hp : x.2.c.pos.val = k + 1) :
    backM0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x = backMsg nike macS streamS
        geom x.2.c.req x.2.o.1
      (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names x.2) (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) x default).toArray 0)
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          x default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2) := by
  unfold backM0 backMsgAt
  dsimp only
  rw [hp]

theorem backPlain0_back {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (k : ℕ) (hp : x.2.2.2.2.c.pos.val = k + 1) :
    backPlain0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x = x.2.2.2.2.o.2 := by
  unfold backPlain0
  rw [hp]

/-- The bytes under the honest relay's tag in world 0, from its header keystream. -/
def backMS0 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropStrX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (U : KEMSphinx.Keystream geom) : ByteArray :=
  match x.2.2.c.pos.val with
  | 0 => onionMsgStream nike macS streamS geom x.2.2.c.req x.2.2.o.1 (groupElem nike (drawKey nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      x.2.2) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
      default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default) default)
      (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          x.2.2) (Util.Bytes.ofVector U)
  | _ + 1 => hdrMsg geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
      cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      x) default) default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
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
      hvalid hmactag h16 W names) x.2.2)

/-- The sender's block in world 0; it does not read the keystream. -/
def backPlainS0 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropStrX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (_U : KEMSphinx.Keystream geom) : Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength) :=
  match x.2.2.c.pos.val with
  | 0 => Util.Bytes.toVecN _ (onionBlock nike cipher macS kdfS streamS geom x.2.2.c.req
      x.2.2.o.1 (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2))
  | _ + 1 => x.2.2.o.2

/-- World 0 at the exit, from the honest relay's header keystream and the encrypted block. -/
def backStrExitW0 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (U : KEMSphinx.Keystream geom) (e : ByteArray) :
    Protocols.RSOR.World 𝒮 :=
  { onion := onionOfStream nike cipher macS kdfS streamS geom 0 x.2.2.c.req x.2.2.o.1 (groupElem
      nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS
      geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
      default) default).toArray 0)
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default) default)
          (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U) (Util.Bytes.ofVector
          (macS.mac (Util.Bytes.ofVector x.1) (backMS0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 W x U))) e
    patch := (Protocols.RSOR.BackwardChallenge.world0 x.2.2.c x.2.2.o.1).patch }

/-- World 0 on the backward path, from the honest relay's header keystream. -/
def backStrW0 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropStrX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (U : KEMSphinx.Keystream geom) (hb : 0 <
    x.2.2.c.req.back.hops.length) :
    Protocols.RSOR.World 𝒮 :=
  backW0Of nike cipher macS kdfS streamS geom hvalid hmactag h16 x.2.2.c.req x.2.2.o.1 hb
    (backHdrBytes nike geom x.2.2.c.req x.2.2.o.1 (Function.update (keysKs geom streamS (drawKeys
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)) (Function.update (keysTag macS
        (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) fun _ => Util.Bytes.ofVector (macS.mac
        (Util.Bytes.ofVector x.1) (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W
        x U))) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray 0) (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray))
    (backHdrFn nike geom x.2.2.c.req x.2.2.o.1 (Function.update (keysKs geom streamS (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U)) (Function.update (keysTag macS
        (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) x.2.2) fun _ => Util.Bytes.ofVector (macS.mac
        (Util.Bytes.ofVector x.1) (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W
        x U))) (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray 0) (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray)
      (x.2.2.c.req.back.hops.length - 1))

/-- **World 0 from the honest relay's header keystream.** -/
def backViewS0 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : PropStrX
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (U : KEMSphinx.Keystream geom) (e : Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) : Protocols.RSOR.World 𝒮 :=
  match x.2.2.c.pos.val with
  | 0 => backStrExitW0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U
      (Util.Bytes.ofVector e)
  | _ + 1 => backStrW0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U
      (Nat.zero_lt_of_lt x.2.2.c.pos.isLt)

theorem backMS0_exit {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (U : KEMSphinx.Keystream geom) (hp : x.2.2.c.pos.val = 0) :
    backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U = onionMsgStream nike macS
        streamS geom x.2.2.c.req x.2.2.o.1 (groupElem nike (drawKey nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2.2) (drawKeys nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default)
        default).toArray 0)
      (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
          W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x) default) default)
          (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) (Util.Bytes.ofVector U) := by
  unfold backMS0
  rw [hp]

theorem backMS0_back {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (U : KEMSphinx.Keystream geom) (k : ℕ)
    (hp : x.2.2.c.pos.val = k + 1) :
    backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U
      = hdrMsg geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names x) default) default).toArray) (drawPos nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2.2)
          (Util.Bytes.ofVector U)) (keysTag macS (drawKeys nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names x) default) default).toArray) (blindElem nike (groupElem nike (drawKey nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names x.2.2) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default).toArray) (RSOR.filler nike geom (RSOR.path nike x.2.2.c.req.back
          [.surbReply x.2.2.o.1.2.2.2]) x.2.2.o.1.2.1) (RSOR.path nike x.2.2.c.req.back [.surbReply
          x.2.2.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2) := by
  unfold backMS0
  rw [hp]

theorem backPlainS0_exit {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (U : KEMSphinx.Keystream geom) (hp : x.2.2.c.pos.val = 0) :
    backPlainS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U = Util.Bytes.toVecN _
        (onionBlock nike cipher macS kdfS streamS geom
      x.2.2.c.req x.2.2.o.1 (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x)
          default) default) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2.2)) := by
  unfold backPlainS0
  rw [hp]

theorem backPlainS0_back {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (U : KEMSphinx.Keystream geom) (k : ℕ)
    (hp : x.2.2.c.pos.val = k + 1) :
    backPlainS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U = x.2.2.o.2 := by
  unfold backPlainS0
  rw [hp]

theorem backViewS0_exit {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (U : KEMSphinx.Keystream geom) (e : Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength))
    (hp : x.2.2.c.pos.val = 0) :
    backViewS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U e = backStrExitW0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 W x U (Util.Bytes.ofVector e) := by
  unfold backViewS0
  rw [hp]

theorem backViewS0_back {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x :
    PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) (U : KEMSphinx.Keystream geom) (e : Vector UInt8
    (geom.payloadTagLength + geom.forwardPayloadLength)) (k : ℕ)
    (hp : x.2.2.c.pos.val = k + 1) (hb : 0 < x.2.2.c.req.back.hops.length) :
    backViewS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x U e = backStrW0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 W x U hb := by
  unfold backViewS0
  rw [hp]

set_option maxHeartbeats 4000000 in
/-- **World 0's payload game with the ideal cipher reads the honest relay's header key and IV
through its keystream only.** -/
theorem backPay0_ideal_eq (names : Role → Name) (A : (Protocols.RSOR.backwardWith W).Adversary) (iv
    : Vector UInt8 16)
    (km he seed : Vector UInt8 32) (D : PropDraw nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) (u v : Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength)) :
    propPayIdealRun nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) _ (backDraw0 nike geom) A (backM0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W) (backPlain0 nike cipher macS kdfS streamS geom hvalid hmactag
        h16 W)
        (backViewE0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) ((iv, km, he, seed, D)
            : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) u v
      = (propStrRun nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) A (backMS0 nike cipher macS kdfS streamS geom hvalid
          hmactag h16 W) (backPlainS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
          (backViewS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)) ((km, seed, D) :
          PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS
          geom).gen (he, iv)) u v := by
  have hposD := backPos_lt nike cipher macS kdfS streamS geom hvalid hmactag h16 W D
  have hall : (∀ i, i ≠ (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) D) → (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
      geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
      geom.forwardPayloadLength))) A) default) default).toArray[i]! = (drawKeys nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace
      nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
      kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
      (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default) default).toArray[i]!)
      ∧ (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default)
          default).toArray[(drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) D)]! = { (drawKeys nike cipher macS kdfS streamS geom
          hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
          streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay
          nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
          .relay names ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
          UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default)
          default).toArray[(drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) D)]! with
        headerEncryption := ((drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
            PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) default)
            default).toArray[(drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) D)]!).headerEncryption
        headerEncryptionIV := ((drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
            PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) default)
            default).toArray[(drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) D)]!).headerEncryptionIV }
      ∧ keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray
        = Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
            kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A)) default) default).toArray) (drawPos nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
          (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
              D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A) default)
              default).toArray (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) D))
      ∧ keysTag macS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray =
          keysTag macS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
          seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default) default).toArray
      ∧ ∀ a, blindElem nike a (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray =
          blindElem nike a (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
          seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default) default).toArray := by
    unfold drawKeys
    exact hopKeysWith_streamKey nike macS kdfS streamS geom _ _ _ (restKeys (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) default).1 default)
      (restKeys (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) :
          PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default).1 default) rfl _ hposD
  obtain ⟨hne, hK, hks, htg, hge⟩ := hall
  have hU : Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))
      = streamS.keystream (Util.Bytes.ofVector he) (Util.Bytes.ofVector iv)
        (geom.routingInfoLength + geom.perHopRoutingInfoLength) :=
    Util.Bytes.ofVector_toVecN _ (streamS.keystream_size _ _ _)
  have hKj : (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
      geom.forwardPayloadLength))) A) default) default).toArray[(drawPos nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
      cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)]! = restKeys (propPayRest nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
      (geom.payloadTagLength + geom.forwardPayloadLength))) A) default).1 default := by
    unfold drawKeys
    exact toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS _ _ _ _ _ hposD)
  have hKS : keysKs geom streamS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
      h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
      cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
      geom.forwardPayloadLength))) A) default) default).toArray (drawPos nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
      cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) = Util.Bytes.ofVector
      ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) := by
    unfold keysKs
    rw [hKj]
    exact hU.symm
  obtain hk | ⟨k, hk⟩ : D.c.pos.val = 0 ∨ ∃ k, D.c.pos.val = k + 1 := by
    cases h : D.c.pos.val with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, rfl⟩
  · have hjp : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) D) < (RSOR.path nike D.c.req.fwd [.recipient
      D.c.req.receiver]).size :=
      lt_of_eq_of_lt (backPos_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W D hk)
          (lt_of_lt_of_eq
        (Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2 D.c.req.fwd_ne)))
        (RSOR.path_size nike _ _).symm)
    have hsk := fun (a tag e : ByteArray) => onion_streamKey nike cipher macS kdfS streamS geom 0
      D.c.req D.o.1 a (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default) (drawKeys nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
          (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) :
          PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default) default) (drawPos nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) tag e
          hjp hne hK rfl
    have hM : backM0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) = backMS0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) :=
      (backM0_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) hk).trans (((hsk
          (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv,
          km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray 0)
          .empty .empty).2.1).trans
        (by rw [hKS]; exact (backMS0_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W
            ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG
            streamS geom).gen (he, iv)) hk).symm))
    have hplain : backPlain0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) = backPlainS0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) :=
      (backPlain0_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he, seed,
          D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) hk).trans ((congrArg
          (Util.Bytes.toVecN _)
        (hsk .empty .empty .empty).2.2).trans (backPlainS0_exit nike cipher macS kdfS streamS geom
            hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike
            geom × (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)
            ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) hk).symm)
    have hon : onionOfEnc nike cipher macS kdfS streamS geom 0 D.c.req D.o.1 (groupElem nike
        (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names D) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) default) default).toArray 0) (drawKeys nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default) (drawPos nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
          (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM0 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
              D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A) default))))
              (Util.Bytes.ofVector u)
        = onionOfStream nike cipher macS kdfS streamS geom 0 D.c.req D.o.1 (groupElem nike (drawKey
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names D) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
            PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray 0)
            (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
            seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default) default) (drawPos
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            D)
          (Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))
              (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backMS0 nike cipher macS
              kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS
              kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
              geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he,
              iv))))) (Util.Bytes.ofVector u) :=
      ((hsk (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv,
          km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray 0) _
          _).1).trans (by rw [hKS, hM])
    have hview : backViewE0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) u = backViewS0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) u :=
      (backViewE0_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he, seed,
          D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) u hk).trans ((congrArg (fun on =>
        Protocols.RSOR.World.mk (S := 𝒮) on
          (Protocols.RSOR.BackwardChallenge.world0 D.c D.o.1).patch) hon).trans
        (backViewS0_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) :
            PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG
            streamS geom).gen (he, iv)) u hk).symm)
    exact propPayIdealRun_eq_strRun nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) _ (backDraw0 nike geom) A (backM0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W)
      (backPlain0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W) (backMS0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 W) (backPlainS0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          W)
      (backViewS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) iv km he seed D u v hM
          hplain hview
  · have hlt : D.c.pos.val < D.c.req.back.hops.length := D.c.pos.isLt
    have hb : 0 < D.c.req.back.hops.length := Nat.zero_lt_of_lt hlt
    have hA : (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray 0) =
        (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default) default).toArray 0) :=
        rfl
    have hM : backM0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) = backMS0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) :=
      (backM0_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher
          macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
          ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) k hk).trans ((show
          backMsg nike macS streamS geom D.c.req D.o.1
          (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
              geom.forwardPayloadLength))) A) default) default).toArray 0) (drawKeys nike cipher
              macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
              names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
              geom.forwardPayloadLength))) A) default) default) (drawPos nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
        = hdrMsg geom (Function.update (keysKs geom streamS (drawKeys nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A)) default) default).toArray) (drawPos nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
            (Util.Bytes.ofVector ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))) (keysTag
            macS (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
            seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default) default).toArray)
            (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A)) default) default).toArray 0) (drawKeys nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A)) default) default).toArray) (RSOR.filler nike geom
            (RSOR.path nike D.c.req.back [.surbReply D.o.1.2.2.2]) D.o.1.2.1) (RSOR.path nike
            D.c.req.back [.surbReply D.o.1.2.2.2]) (drawPos nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
            macS kdfS streamS geom hvalid hmactag h16 W names) D) from by
          unfold backMsg
          rw [hks, hKS, htg, hge (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher
              macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
              names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
              geom.forwardPayloadLength))) A) default) default).toArray 0), hA]).trans
              (backMS0_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D)
              : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)
              ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) k hk).symm)
    have hplain : backPlain0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) = backPlainS0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) :=
      (backPlain0_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he, seed,
          D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) k hk).trans (backPlainS0_back
          nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
          geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) k
          hk).symm
    have ha : (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
        geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray 0).size
        = nike.publicKeySize := Util.Bytes.size_ofVector _
    have ht : (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM0 nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) default)))).size = macLength :=
      (Util.Bytes.size_ofVector _).trans hmactag
    have hlK : D.c.req.back.hops.length ≤ (drawKeys nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
        PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) default) default).length := by
      unfold drawKeys
      rw [hopKeysWith_length]
      exact (backHops_size_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W D k hk).ge
    have h1 : backHdrOfTag nike cipher macS streamS geom D.c.req D.o.1 (groupElem nike (drawKey
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names D) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) default) default).toArray 0) (drawKeys nike cipher macS
        kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag
        h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default) (drawPos nike
        cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
        names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
          (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM0 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
              D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A) default))))
        = backHdrBytes nike geom D.c.req D.o.1 (Function.update (keysKs geom streamS (drawKeys nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) :
            PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default) default).toArray)
            (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector ((KEMSphinx.keystreamPRG
            streamS geom).gen (he, iv)))) (Function.update (keysTag macS (drawKeys nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A)) default) default).toArray) (drawPos nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) fun _ =>
            Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backMS0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))))
            (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A)) default) default).toArray 0) (drawKeys nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A)) default) default).toArray) :=
      (backHdrOfTag_eq nike cipher macS streamS geom hvalid hmactag D.c.req D.o.1 (groupElem nike
          (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
          geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
          kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv,
          km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray 0)
          (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default)
        (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
            W) .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W
            names) D) (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM0 nike cipher
            macS kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he,
            seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) default)))) hb ha ht).trans
            (by rw [hks, hKS, htg, hge (groupElem nike (drawKey nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A) default) default).toArray 0), hM, hA])
    have h2 : (backLayerOfTag nike cipher macS streamS geom (D.c.req.back.hops.length - 1)
          D.c.req D.o.1 (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag
              h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
              geom.forwardPayloadLength))) A) default) default).toArray 0) (drawKeys nike cipher
              macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
              names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
              geom.forwardPayloadLength))) A) default) default) (drawPos nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
              (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM0 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
              D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A) default))))).1
        = backHdrFn nike geom D.c.req D.o.1 (Function.update (keysKs geom streamS (drawKeys nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) :
            PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default) default).toArray)
            (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector ((KEMSphinx.keystreamPRG
            streamS geom).gen (he, iv)))) (Function.update (keysTag macS (drawKeys nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A)) default) default).toArray) (drawPos nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D) fun _ =>
            Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backMS0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)))))
            (blindElem nike (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A)) default) default).toArray 0) (drawKeys nike cipher
            macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names (propStrPay nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names ((km, seed, D) : PropStrX nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
            (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
            geom.forwardPayloadLength))) A)) default) default).toArray)
          (D.c.req.back.hops.length - 1) :=
      (backLayerOfTag_fst nike cipher macS streamS geom hvalid hmactag h16
        (D.c.req.back.hops.length - 1) D.c.req D.o.1 (groupElem nike (drawKey nike cipher macS kdfS
            streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names D)
            (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
            PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray 0)
            (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
            hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
            PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default) (drawPos
            nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
            .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
            D)
        (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D)
            : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) default)))) (Nat.sub_one_lt
            (Nat.ne_of_gt hb))
        ((Nat.sub_le _ _).trans hlK) ha ht).trans (by rw [hks, hKS, htg, hge (groupElem nike
            (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS streamS
            geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W names) (propPayRest nike cipher macS
            kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv,
            km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray 0),
            hM, hA])
    have mid1 : backViewT0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W (propPayRest
        nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names ((iv, km, he, seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom ×
        (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) (macS.mac
        (Util.Bytes.ofVector km) (backM0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W
        (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike cipher
        macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) default)))
        = backW0Of nike cipher macS kdfS streamS geom hvalid hmactag h16 D.c.req D.o.1 hb
          (backHdrOfTag nike cipher macS streamS geom D.c.req D.o.1 (groupElem nike (drawKey nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names D) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
              D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A) default)
              default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
              D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default)
              (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) D)
            (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM0 nike cipher macS kdfS
                streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
                hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed,
                D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
                UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A) default)))))
          (backLayerOfTag nike cipher macS streamS geom (D.c.req.back.hops.length - 1) D.c.req
            D.o.1 (groupElem nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS
                streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
                (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
                (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
                cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
                .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
                geom.forwardPayloadLength))) A) default) default).toArray 0) (drawKeys nike cipher
                macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
                names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
                (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) : PropPayX nike
                cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
                .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
                geom.forwardPayloadLength))) A) default) default) (drawPos nike cipher macS kdfS
                streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
                (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
                (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM0 nike cipher macS
                kdfS streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS
                geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he,
                seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
                (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
                UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A) default))))).1 :=
      backViewTAt_back_form nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨D.keys,
          D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names D.k.1) D.o (groupElem nike (drawKey nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names D) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default).toArray 0)
          (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom hvalid
          hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D) :
          PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) default) default) (drawPos nike
          cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
          names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) D)
        (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) (backM0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W (propPayRest nike cipher macS kdfS streamS geom
            hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((iv, km, he, seed, D)
            : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
            (geom.payloadTagLength + geom.forwardPayloadLength))) A) default)))) k hk hb
    have mid3 : backStrW0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) :
        PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith
        W) .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) hb
        = backW0Of nike cipher macS kdfS streamS geom hvalid hmactag h16 D.c.req D.o.1 hb
          (backHdrBytes nike geom D.c.req D.o.1 (Function.update (keysKs geom streamS (drawKeys
              nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W
              names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
              seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default)
              default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector ((KEMSphinx.keystreamPRG
              streamS geom).gen (he, iv)))) (Function.update (keysTag macS (drawKeys nike cipher
              macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
              names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
              seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default)
              default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) D) fun _ => Util.Bytes.ofVector (macS.mac
              (Util.Bytes.ofVector km) (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)
              ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))))) (blindElem nike (groupElem
              nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
              seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default)
              default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom ×
              (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default)
              default).toArray))
          (backHdrFn nike geom D.c.req D.o.1 (Function.update (keysKs geom streamS (drawKeys nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W
              names) (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
              seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default)
              default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) D) (Util.Bytes.ofVector ((KEMSphinx.keystreamPRG
              streamS geom).gen (he, iv)))) (Function.update (keysTag macS (drawKeys nike cipher
              macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
              names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
              seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default)
              default).toArray) (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) D) fun _ => Util.Bytes.ofVector (macS.mac
              (Util.Bytes.ofVector km) (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag
              h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)
              ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv))))) (blindElem nike (groupElem
              nike (drawKey nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names D) (drawKeys nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
              (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names)
              (propPayRest nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike cipher macS kdfS
              streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names ((km,
              seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default)
              default).toArray 0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
              geom hvalid hmactag h16 W names) (propPayRest nike cipher macS kdfS streamS geom
              hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (propStrPay nike
              cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
              .relay names ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid
              hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom ×
              (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)) default)
              default).toArray)
            (D.c.req.back.hops.length - 1)) := rfl
    have hview : backViewE0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he,
        seed, D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
        (geom.payloadTagLength + geom.forwardPayloadLength))) A) u = backViewS0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 W ((km, seed, D) : PropStrX nike cipher macS kdfS
        streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
        (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) A) ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) u :=
      (backViewE0_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W ((iv, km, he, seed,
          D) : PropPayX nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector UInt8
          (geom.payloadTagLength + geom.forwardPayloadLength))) A) u k hk).trans ((mid1.trans
        ((congrArg₂ (fun hd ls => backW0Of nike cipher macS kdfS streamS geom hvalid hmactag h16
            D.c.req D.o.1 hb hd ls) h1 h2).trans
          mid3.symm)).trans (backViewS0_back nike cipher macS kdfS streamS geom hvalid hmactag h16
              W ((km, seed, D) : PropStrX nike cipher macS kdfS streamS geom hvalid hmactag h16
              (Protocols.RSOR.backwardWith W) .relay names (RSOR.Randomness nike geom × (Vector
              UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))) A)
              ((KEMSphinx.keystreamPRG streamS geom).gen (he, iv)) u k hk hb).symm)
    exact propPayIdealRun_eq_strRun nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W names) _ (backDraw0 nike geom) A (backM0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W)
      (backPlain0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE0 nike cipher
          macS kdfS streamS geom hvalid hmactag h16 W) (backMS0 nike cipher macS kdfS streamS geom
          hvalid hmactag h16 W) (backPlainS0 nike cipher macS kdfS streamS geom hvalid hmactag h16
          W)
      (backViewS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) iv km he seed D u v hM
          hplain hview

/-- **The keystream step for world 0 of SLU←.** Its payload game with the ideal cipher is the
real experiment of the keystream generator, for the adversary that plays world 0 from the
keystream it is given. -/
theorem backward0_pay_evalDistEq_prg (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) :
    (propPay nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
        .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) _
        (backDraw0 nike geom) A (backM0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
        (backPlain0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 W)).exp cipher false
      =ᵈ PRGScheme.prgRealExperiment (KEMSphinx.keystreamPRG streamS geom)
        (propStreamAdv nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A (propStrRun nike
            cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
            names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A
            (backMS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backPlainS0 nike
            cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewS0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W))) :=
  propPay_exp_false_evalDistEq_prg nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) _ (backDraw0 nike geom) A (backM0 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 W)
    (backPlain0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewE0 nike cipher
        macS kdfS streamS geom hvalid hmactag h16 W) (propStrRun nike cipher macS kdfS streamS geom
        hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS
        kdfS streamS geom hvalid hmactag h16 W names) A (backMS0 nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W) (backPlainS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
        (backViewS0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W))
    (fun iv km he seed D u v => backPay0_ideal_eq nike cipher macS kdfS streamS geom hvalid hmactag
        h16 W names A iv km he seed D u v)

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
