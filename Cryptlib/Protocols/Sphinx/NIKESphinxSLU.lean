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

/-! ## The two worlds as their draws -/

variable {nike geom} in
/-- The challenger's randomness with the secret of the honest relay's path replaced: the
forward path's when the relay is the exit relay, the backward path's otherwise. -/
def relayKey (pos : ℕ) (r : RSOR.Randomness nike geom) (d : Vector UInt8 nike.privateKeySize) :
    RSOR.Randomness nike geom :=
  match pos with
  | 0 => setKey r d
  | _ + 1 => (r.1, (d, r.2.1.2), r.2.2)

omit cipher macS kdfS streamS hvalid hmactag h16 in
/-- Drawing the challenger's randomness and a secret, and putting the secret on the relay's
path, is drawing the randomness. -/
theorem evalDistEq_relayKey {δ : Type} (pos : ℕ) (K : RSOR.Randomness nike geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness nike geom)
      let d ← $ᵗ (Vector UInt8 nike.privateKeySize)
      K (relayKey pos r d)) =ᵈ ($ᵗ (RSOR.Randomness nike geom) >>= K) := by
  cases pos with
  | zero => exact evalDistEq_setKey nike geom K
  | succ k =>
    have hg : Function.Bijective (Function.uncurry
        fun (r : RSOR.Randomness nike geom) (d : Vector UInt8 nike.privateKeySize) =>
          (relayKey (k + 1) r d, r.2.1.1)) := by
      refine Function.bijective_iff_has_inverse.2
        ⟨fun p => (relayKey (k + 1) p.1 p.2, p.1.2.1.1), ?_, ?_⟩ <;>
      · rintro ⟨r, d⟩
        rfl
    have hp := KEMSphinx.evalDistEq_pair_of_bijective
      (g := fun (r : RSOR.Randomness nike geom) (d : Vector UInt8 nike.privateKeySize) => (r, d))
      ⟨fun ⟨_, _⟩ ⟨_, _⟩ h => h, fun p => ⟨p, rfl⟩⟩ (fun p => K p.1)
    exact ((KEMSphinx.evalDistEq_pair_of_bijective hg
      (fun p : RSOR.Randomness nike geom × Vector UInt8 nike.privateKeySize => K p.1)).trans
          hp.symm).trans
      (EvalDistEq.bind_right _ fun r =>
        OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 nike.privateKeySize)) (K r))

/-! ## The first layer, from the backward path's hop keys -/

/-- The sender's payload with `hdr` as the header of the reply's first layer. -/
def bodyH (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (hb : 0 < q.back.hops.length)
    (hdr : ByteArray) : ByteArray :=
  ⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩
    ++ (hdr ++ Util.Bytes.ofVector (q.back.hops[0]'hb).name ++ Util.Bytes.ofVector r.2.2.1)
    ++ Util.Bytes.ofVector q.msg

include hvalid hmactag in
/-- The sender's payload, with the header of the reply's first layer written out. -/
theorem body_eq (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (payload x0 :
    ByteArray)
    (hb : 0 < q.back.hops.length)
    (hx0 : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike q.back [.surbReply
        r.2.2.2]) r.2.1 payload 0 = .ok x0) :
    RSOR.body nike macS kdfS streamS geom q r
      = bodyH nike geom q r hb (x0.extract 0 geom.headerLength) := by
  unfold RSOR.body bodyH
  rw [surb_fst nike cipher macS kdfS streamS geom hvalid hmactag q r payload x0 hb hx0]

/-- The header of the reply's first layer, from the backward path's first group element and
its hops' keys. -/
def backHdrOfKeys (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray) (ks
    : List HopKeys) :
    ByteArray :=
  match nikePktFn geom (keysKs geom streamS ks.toArray) (keysTag macS ks.toArray)
      (keysEnc cipher ks.toArray) (blindElem nike a ks.toArray)
      (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply r.2.2.2]) r.2.1) (RSOR.path nike
          q.back [.surbReply r.2.2.2]) (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
          with
  | some pkt => pkt.extract 0 geom.headerLength
  | none => ByteArray.empty

/-- The first layer of `q`'s onion, from the backward path's first group element and its
hops' keys: they enter through the reply block in the sender's payload. -/
def backOnionOfKeys (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (hb : 0 <
    q.back.hops.length)
    (a : ByteArray) (ks : List HopKeys) : Onion geom :=
  match RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike q.fwd [.recipient
      q.receiver]) r.1
      (bodyH nike geom q r hb (backHdrOfKeys nike cipher macS streamS geom q r a ks)) 0 with
  | .ok pkt => split geom pkt
  | .error _ => default

include hvalid hmactag in
/-- **On the sender's own keys it is the sender's onion**, when the reply's first layer
builds. -/
theorem backOnionOfKeys_real (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (d : Vector UInt8 nike.privateKeySize) (k : ℕ) (hb : 0 < q.back.hops.length)
    (x0 : ByteArray)
    (hx0 : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike q.back [.surbReply
        r.2.2.2]) (relayKey (k + 1) r d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
        ByteArray) 0
      = .ok x0) :
    backOnionOfKeys nike cipher macS kdfS streamS geom q r hb
        (groupElem nike ((nike.decodePrivateKey d).getD default) (RSOR.hopKeys nike kdfS
            ((nike.decodePrivateKey d).getD default) (RSOR.path nike q.back [.surbReply r.2.2.2])
            (RSOR.path nike q.back [.surbReply r.2.2.2]).size).toArray 0) (RSOR.hopKeys nike kdfS
            ((nike.decodePrivateKey d).getD default) (RSOR.path nike q.back [.surbReply r.2.2.2])
            (RSOR.path nike q.back [.surbReply r.2.2.2]).size)
      = RSOR.form nike cipher macS kdfS streamS geom q (relayKey (k + 1) r d) q.first := by
  have hp := layer_zero_pktFn nike cipher macS kdfS streamS geom (RSOR.path nike q.back [.surbReply
      r.2.2.2]) (relayKey (k + 1) r d).2.1
    (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) x0 hx0 (RSOR.path_keys nike q.back
        [.surbReply r.2.2.2])
  have hbody := body_eq nike cipher macS kdfS streamS geom hvalid hmactag q (relayKey (k + 1) r d)
    (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) x0 hb hx0
  unfold backOnionOfKeys backHdrOfKeys
  rw [show blindElem nike (groupElem nike ((nike.decodePrivateKey d).getD default) (RSOR.hopKeys
      nike kdfS ((nike.decodePrivateKey d).getD default) (RSOR.path nike q.back [.surbReply
      r.2.2.2]) (RSOR.path nike q.back [.surbReply r.2.2.2]).size).toArray 0) (RSOR.hopKeys nike
      kdfS ((nike.decodePrivateKey d).getD default) (RSOR.path nike q.back [.surbReply r.2.2.2])
      (RSOR.path nike q.back [.surbReply r.2.2.2]).size).toArray
      = groupElem nike ((nike.decodePrivateKey d).getD default) (RSOR.hopKeys nike kdfS
          ((nike.decodePrivateKey d).getD default) (RSOR.path nike q.back [.surbReply r.2.2.2])
          (RSOR.path nike q.back [.surbReply r.2.2.2]).size).toArray from
    funext fun i => (groupElem_eq_blindElem nike _ _ i).symm]
  dsimp only [relayKey, RSOR.clientKey, RSOR.filler] at hp ⊢
  rw [hp]
  dsimp only
  unfold RSOR.form
  dsimp only [relayKey] at hbody ⊢
  rw [hbody]
  rfl

/-- Layer `i` of the reply's packet over the backward path, from the path's first group element
and its hops' keys. -/
def backLayerOfKeys (i : ℕ) (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a :
    ByteArray)
    (ks : List HopKeys) : Onion geom :=
  match nikePktFn geom (keysKs geom streamS ks.toArray) (keysTag macS ks.toArray)
      (keysEnc cipher ks.toArray) (blindElem nike a ks.toArray)
      (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply r.2.2.2]) r.2.1) (RSOR.path nike
          q.back [.surbReply r.2.2.2]) (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
          with
  | some pkt => split geom (peels nike cipher streamS geom ks i pkt)
  | none => default

/-- **On the sender's own keys it is the layer of the packet over the backward path**, when
that packet builds. -/
theorem backLayerOfKeys_real (i : ℕ) (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (d : Vector UInt8 nike.privateKeySize) (k : ℕ) (x0 : ByteArray) (hi : i ≤ (RSOR.path nike
        q.back [.surbReply r.2.2.2]).size)
    (hx0 : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike q.back [.surbReply
        r.2.2.2]) (relayKey (k + 1) r d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
        ByteArray) 0
      = .ok x0) :
    backLayerOfKeys nike cipher macS streamS geom i q r (groupElem nike ((nike.decodePrivateKey
        d).getD default) (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
        (RSOR.path nike q.back [.surbReply r.2.2.2]) (RSOR.path nike q.back [.surbReply
        r.2.2.2]).size).toArray 0) (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default)
        (RSOR.path nike q.back [.surbReply r.2.2.2]) (RSOR.path nike q.back [.surbReply
        r.2.2.2]).size)
      = (match RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike q.back [.surbReply
          r.2.2.2]) (relayKey (k + 1) r d).2.1
          (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) i with
        | .ok pkt => split geom pkt
        | .error _ => default) := by
  have hp := layer_zero_pktFn nike cipher macS kdfS streamS geom (RSOR.path nike q.back [.surbReply
      r.2.2.2]) (relayKey (k + 1) r d).2.1
    (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) x0 hx0 (RSOR.path_keys nike q.back
        [.surbReply r.2.2.2])
  rw [layer_peels nike cipher macS kdfS streamS geom _ _ _ i (RSOR.path nike q.back [.surbReply
      r.2.2.2]).size hi, hx0]
  unfold backLayerOfKeys
  rw [show blindElem nike (groupElem nike ((nike.decodePrivateKey d).getD default) (RSOR.hopKeys
      nike kdfS ((nike.decodePrivateKey d).getD default) (RSOR.path nike q.back [.surbReply
      r.2.2.2]) (RSOR.path nike q.back [.surbReply r.2.2.2]).size).toArray 0) (RSOR.hopKeys nike
      kdfS ((nike.decodePrivateKey d).getD default) (RSOR.path nike q.back [.surbReply r.2.2.2])
      (RSOR.path nike q.back [.surbReply r.2.2.2]).size).toArray
      = groupElem nike ((nike.decodePrivateKey d).getD default) (RSOR.hopKeys nike kdfS
          ((nike.decodePrivateKey d).getD default) (RSOR.path nike q.back [.surbReply r.2.2.2])
          (RSOR.path nike q.back [.surbReply r.2.2.2]).size).toArray from
    funext fun i => (groupElem_eq_blindElem nike _ _ i).symm]
  dsimp only [relayKey, RSOR.clientKey, RSOR.filler] at hp ⊢
  rw [hp]
  rfl

/-! ## The replaced hop's MAC key, on any path -/

/-- **Peeling does not read a hop's MAC key.** -/
theorem peels_restKeys (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (x : Rest)
    (km : Vector UInt8 32) (n : ℕ) (hj : j < n) (i : ℕ) :
    peels nike cipher streamS geom (hopKeysWith nike kdfS c hops j (restKeys x km) n) i = peels
        nike cipher streamS geom (hopKeysWith nike kdfS c hops j (restKeys x default) n) i := by
  have hmap : (hopKeysWith nike kdfS c hops j (restKeys x km) n).map (RSOR.peel nike cipher streamS
      geom)
      = (hopKeysWith nike kdfS c hops j (restKeys x default) n).map (RSOR.peel nike cipher streamS
          geom) := by
    refine List.ext_getElem? fun m => ?_
    rw [List.getElem?_map, List.getElem?_map]
    by_cases hm : m = j
    · rw [hm, hopKeysWith_getElem nike kdfS c hops j _ n hj,
        hopKeysWith_getElem nike kdfS c hops j _ n hj]
      rfl
    · rw [(hopKeysWith_congr nike kdfS c hops j (restKeys x km) (restKeys x default) rfl n).2 m
        hm]
  have e : ∀ (l : List HopKeys) (pkt : ByteArray),
      l.foldl (fun p k => RSOR.peel nike cipher streamS geom k p) pkt
        = (l.map (RSOR.peel nike cipher streamS geom)).foldl (fun p g => g p) pkt :=
    fun l pkt => by rw [List.foldl_map]
  funext pkt
  unfold peels
  rw [e, e, List.map_take, List.map_take, hmap]

/-- **A packet uses the replaced hop's MAC key for one tag only**, whatever its path, filler
and payload: the tag of `hdrMsg` at that hop. -/
theorem nikePktFn_restKeys (a : ByteArray) (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ)
    (x : Rest) (km : Vector UInt8 32) (n : ℕ) (hj : j < n) (fil : ByteArray)
    (path : Array PathHop) (payload : ByteArray) (hjp : j < path.size) :
    nikePktFn geom (keysKs geom streamS (hopKeysWith nike kdfS c hops j (restKeys x km) n).toArray)
        (keysTag macS (hopKeysWith nike kdfS c hops j (restKeys x km) n).toArray)
        (keysEnc cipher (hopKeysWith nike kdfS c hops j (restKeys x km) n).toArray) (blindElem nike
            a (hopKeysWith nike kdfS c hops j (restKeys x km) n).toArray) fil path payload
      = nikePktFn geom (keysKs geom streamS (hopKeysWith nike kdfS c hops j (restKeys x default)
          n).toArray)
        (Function.update (keysTag macS (hopKeysWith nike kdfS c hops j (restKeys x default)
            n).toArray) j fun _ =>
          Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
            (hdrMsg geom (keysKs geom streamS (hopKeysWith nike kdfS c hops j (restKeys x default)
                n).toArray) (keysTag macS (hopKeysWith nike kdfS c hops j (restKeys x default)
                n).toArray)
              (blindElem nike a (hopKeysWith nike kdfS c hops j (restKeys x default) n).toArray)
                  fil path j)))
        (keysEnc cipher (hopKeysWith nike kdfS c hops j (restKeys x default) n).toArray) (blindElem
            nike a (hopKeysWith nike kdfS c hops j (restKeys x default) n).toArray) fil path
            payload := by
  have hne : ∀ i, i ≠ j → (hopKeysWith nike kdfS c hops j (restKeys x km) n).toArray[i]! =
      (hopKeysWith nike kdfS c hops j (restKeys x default) n).toArray[i]! := fun i hi =>
    toArray_getElem!_congr _ _ i ((hopKeysWith_congr nike kdfS c hops j (restKeys x km)
      (restKeys x default) rfl n).2 i hi)
  have hj1 : (hopKeysWith nike kdfS c hops j (restKeys x km) n).toArray[j]! = restKeys x km :=
    toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS c hops j _ n hj)
  have hj0 : (hopKeysWith nike kdfS c hops j (restKeys x default) n).toArray[j]! = restKeys x
      default :=
    toArray_getElem!_of_getElem? _ _ _ (hopKeysWith_getElem nike kdfS c hops j _ n hj)
  have hks : keysKs geom streamS (hopKeysWith nike kdfS c hops j (restKeys x km) n).toArray =
      keysKs geom streamS (hopKeysWith nike kdfS c hops j (restKeys x default) n).toArray := by
    funext i
    unfold keysKs
    by_cases hi : i = j
    · rw [hi, hj1, hj0]; rfl
    · rw [hne i hi]
  have henc : keysEnc cipher (hopKeysWith nike kdfS c hops j (restKeys x km) n).toArray = keysEnc
      cipher (hopKeysWith nike kdfS c hops j (restKeys x default) n).toArray := by
    funext i
    unfold keysEnc
    by_cases hi : i = j
    · rw [hi, hj1, hj0]; rfl
    · rw [hne i hi]
  have hge : blindElem nike a (hopKeysWith nike kdfS c hops j (restKeys x km) n).toArray =
      blindElem nike a (hopKeysWith nike kdfS c hops j (restKeys x default) n).toArray := by
    funext i
    refine blindElem_congr nike a _ _ (fun m => ?_) i
    by_cases hm : m = j
    · rw [hm, hj1, hj0]; rfl
    · rw [hne m hm]
  have htag : keysTag macS (hopKeysWith nike kdfS c hops j (restKeys x km) n).toArray
      = Function.update (keysTag macS (hopKeysWith nike kdfS c hops j (restKeys x default)
          n).toArray) j
        (fun m => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) m)) := by
    funext i
    by_cases hi : i = j
    · rw [hi, Function.update_self]
      unfold keysTag
      rw [hj1]
      rfl
    · rw [Function.update_of_ne hi]
      unfold keysTag
      rw [hne i hi]
  rw [hks, henc, hge, htag, nikePktFn_tagAt geom _ _ _ _ _ _ _ j hjp
    (fun m => Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km) m))]

/-! ## A peeled packet's header -/

/-- **Peeling a header and a payload peels the header, whatever the payload**: after `i`
relays the packet is the header peeled `i` times and a payload of the same length. -/
theorem peels_append_hdr (ks : List HopKeys) (H P : ByteArray) (hH : H.size = 2 +
    nike.publicKeySize + geom.routingInfoLength + macLength)
    (hP : 0 < P.size) (i : ℕ) (hik : i ≤ ks.length) :
    ∃ P' : ByteArray, P'.size = P.size
      ∧ peels nike cipher streamS geom ks i (H ++ P) = hdrPeels nike streamS geom ks i H ++ P'
      ∧ (hdrPeels nike streamS geom ks i H).size = 2 + nike.publicKeySize + geom.routingInfoLength
          + macLength := by
  induction i with
  | zero => exact ⟨P, rfl, rfl, hH⟩
  | succ i ih =>
    obtain ⟨P', hP', ihp, ihs⟩ := ih (by omega)
    have hi : i < ks.length := hik
    have hs : peels nike cipher streamS geom ks (i + 1) (H ++ P)
        = RSOR.peel nike cipher streamS geom ks[i] (peels nike cipher streamS geom ks i
          (H ++ P)) := by
      unfold peels
      rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
      rfl
    have hh : hdrPeels nike streamS geom ks (i + 1) H
        = peelHdr nike geom (streamS.keystream (Util.Bytes.ofVector ks[i].headerEncryption)
            (Util.Bytes.ofVector ks[i].headerEncryptionIV) (geom.routingInfoLength +
            geom.perHopRoutingInfoLength)) ks[i].blindingFactor
          (hdrPeels nike streamS geom ks i H) := by
      unfold hdrPeels
      rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
      rfl
    refine ⟨cipher.decrypt ks[i].payloadEncryption.toArray
      (Util.Bytes.ofVector ks[i].headerEncryptionIV) P', ?_, ?_, ?_⟩
    · rw [cipher.decrypt_size, hP']
    · rw [hs, ihp, peel_append nike cipher streamS geom _ _ _ ihs (by omega), hh]
    · rw [hh]
      exact peelHdr_size nike geom _ _ _ ihs

/-- **Peeling a header reads the hops' header keys, IVs and blinding factors only.** -/
theorem hdrPeels_congr (ks ks' : List HopKeys) (i : ℕ) (H : ByteArray)
    (h : ∀ m : ℕ, (ks[m]?).map (fun k : HopKeys => (k.headerEncryption, k.headerEncryptionIV,
        k.blindingFactor))
      = (ks'[m]?).map (fun k : HopKeys => (k.headerEncryption, k.headerEncryptionIV,
          k.blindingFactor))) :
    hdrPeels nike streamS geom ks i H = hdrPeels nike streamS geom ks' i H := by
  have hmap : ks.map (fun k : HopKeys => (k.headerEncryption, k.headerEncryptionIV,
      k.blindingFactor))
      = ks'.map (fun k : HopKeys => (k.headerEncryption, k.headerEncryptionIV, k.blindingFactor)) :=
    List.ext_getElem? fun m => by rw [List.getElem?_map, List.getElem?_map, h m]
  have e : ∀ l : List HopKeys,
      l.foldl (fun h (k : HopKeys) => peelHdr nike geom (streamS.keystream (Util.Bytes.ofVector
          k.headerEncryption) (Util.Bytes.ofVector k.headerEncryptionIV) (geom.routingInfoLength +
          geom.perHopRoutingInfoLength)) k.blindingFactor h) H
        = (l.map (fun k : HopKeys => (k.headerEncryption, k.headerEncryptionIV,
            k.blindingFactor))).foldl
          (fun h (t : Vector UInt8 32 × Vector UInt8 16 × ByteArray) => peelHdr nike geom
            (streamS.keystream (Util.Bytes.ofVector t.1) (Util.Bytes.ofVector t.2.1)
              (geom.routingInfoLength + geom.perHopRoutingInfoLength)) t.2.2 h) H :=
    fun l => by rw [List.foldl_map]
  unfold hdrPeels
  rw [e, e, List.map_take, List.map_take, hmap]

include hvalid in
/-- **A packet's header does not read the hops' encryptions.** -/
theorem nikePktFn_hdr_enc (ks : ℕ → ByteArray) (tag enc enc' : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (fil : ByteArray) (path : Array PathHop) (payload : ByteArray)
    (hn : path.size ≤ geom.nrHops) (hpos : 0 < path.size)
    (hfill : fil.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (htag : ∀ m x, (tag m x).size = macLength) (hge : (ge 0).size = nike.publicKeySize) :
    (match nikePktFn geom ks tag enc ge fil path payload with
      | some pkt => pkt.extract 0 geom.headerLength
      | none => ByteArray.empty)
      = (match nikePktFn geom ks tag enc' ge fil path payload with
        | some pkt => pkt.extract 0 geom.headerLength
        | none => ByteArray.empty) := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  unfold nikePktFn
  by_cases hb : payload.size = geom.forwardPayloadLength
  · rw [ite_eq_left hb, ite_eq_left hb]
    cases hs : nikeHdrTrace geom ks tag ge fil path path.size with
    | none => rfl
    | some s =>
      have hH := hdr_size geom nike.publicKeySize ks tag ge fil path hnnh (by omega) hrouting hn
          hpos
        hfill htag hge s hs
      have hsz : (v0AD ++ ge 0 ++ s.1 ++ s.2).size = geom.headerLength := by
        rw [hH]
        exact hhdr.symm
      have hx : ∀ B : ByteArray,
          (v0AD ++ ge 0 ++ s.1 ++ s.2 ++ B).extract 0 geom.headerLength
            = v0AD ++ ge 0 ++ s.1 ++ s.2 := fun B => by
        have := Util.Bytes.extract_append_left (v0AD ++ ge 0 ++ s.1 ++ s.2) B
        rwa [hsz] at this
      exact (hx _).trans (hx _).symm
  · rw [ite_eq_right hb, ite_eq_right hb]

include hvalid h16 in
/-- **A later layer's header does not read the hops' payload keys.** -/
theorem nikePktFn_peels_fst (K K' : List HopKeys) (i : ℕ) (hi : i ≤ K.length)
    (hi' : i ≤ K'.length)
    (hK : ∀ m : ℕ, (K[m]?).map (fun k : HopKeys => (k.headerEncryption, k.headerEncryptionIV,
        k.blindingFactor)) = (K'[m]?).map (fun k : HopKeys => (k.headerEncryption,
        k.headerEncryptionIV, k.blindingFactor)))
    (ks : ℕ → ByteArray) (tag : ℕ → ByteArray → ByteArray)
    (ge : ℕ → ByteArray) (fil : ByteArray) (path : Array PathHop) (payload : ByteArray)
    (hn : path.size ≤ geom.nrHops) (hpos : 0 < path.size)
    (hfill : fil.size = (geom.nrHops - path.size) * geom.perHopRoutingInfoLength)
    (htag : ∀ m x, (tag m x).size = macLength) (hge : (ge 0).size = nike.publicKeySize) :
    (match nikePktFn geom ks tag (keysEnc cipher K.toArray) ge fil path payload with
      | some pkt => split geom (peels nike cipher streamS geom K i pkt)
      | none => default).1
      = (match nikePktFn geom ks tag (keysEnc cipher K'.toArray) ge fil path payload with
        | some pkt => split geom (peels nike cipher streamS geom K' i pkt)
        | none => default).1 := by
  obtain ⟨hnnh, hper, hrouting, hhdr, -⟩ := id hvalid
  unfold nikePktFn
  by_cases hb : payload.size = geom.forwardPayloadLength
  · rw [ite_eq_left hb, ite_eq_left hb]
    cases hs : nikeHdrTrace geom ks tag ge fil path path.size with
    | none => rfl
    | some s =>
      have hH := hdr_size geom nike.publicKeySize ks tag ge fil path hnnh (by omega) hrouting hn
          hpos
        hfill htag hge s hs
      have hz : (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray).size =
          geom.payloadTagLength := Array.size_replicate
      have hE : ∀ K₀ : List HopKeys, 0 < ((List.range' 0 path.size).foldl
          (fun b iRev => keysEnc cipher K₀.toArray (path.size - 1 - iRev) b)
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ payload)).size := fun K₀ => by
        have e := encTrace_keysEnc_size cipher K₀.toArray path.size ((⟨Array.replicate
            geom.payloadTagLength 0⟩ : ByteArray) ++ payload) path.size
        unfold encTrace at e
        rw [e, ByteArray.size_append, hz, hb]
        omega
      obtain ⟨P1, -, e1, s1⟩ := peels_append_hdr nike cipher streamS geom K _ _ hH (hE K) i hi
      obtain ⟨P2, -, e2, s2⟩ := peels_append_hdr nike cipher streamS geom K' _ _ hH (hE K') i hi'
      have hsz : (hdrPeels nike streamS geom K' i (v0AD ++ ge 0 ++ s.1 ++ s.2)).size
          = geom.headerLength := by
        rw [s2]
        exact hhdr.symm
      have hsp : ∀ B : ByteArray,
          (split geom (hdrPeels nike streamS geom K' i (v0AD ++ ge 0 ++ s.1 ++ s.2) ++ B)).1
            = Util.Bytes.toVecN _ (hdrPeels nike streamS geom K' i
              (v0AD ++ ge 0 ++ s.1 ++ s.2)) := fun B => by
        have := Util.Bytes.extract_append_left
          (hdrPeels nike streamS geom K' i (v0AD ++ ge 0 ++ s.1 ++ s.2)) B
        rw [hsz] at this
        exact congrArg (Util.Bytes.toVecN _) this
      show (split geom (peels nike cipher streamS geom K i _)).1
        = (split geom (peels nike cipher streamS geom K' i _)).1
      rw [e1, e2, hdrPeels_congr nike streamS geom K K' i _ hK]
      exact (hsp _).trans (hsp _).symm
  · rw [ite_eq_right hb, ite_eq_right hb]

/-! ## The reply's packet, with one hop's tag given -/

/-- The bytes of the reply's packet over the backward path that hop `j`'s tag covers. -/
def backMsg (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray) (ks : List
    HopKeys)
    (j : ℕ) : ByteArray :=
  hdrMsg geom (keysKs geom streamS ks.toArray) (keysTag macS ks.toArray)
    (blindElem nike a ks.toArray) (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply
        r.2.2.2]) r.2.1) (RSOR.path nike q.back [.surbReply r.2.2.2]) j

/-- `backHdrOfKeys`, with the tag of hop `j` given. -/
def backHdrOfTag (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray) (ks :
    List HopKeys)
    (j : ℕ) (tag : ByteArray) : ByteArray :=
  match nikePktFn geom (keysKs geom streamS ks.toArray)
      (Function.update (keysTag macS ks.toArray) j fun _ => tag)
      (keysEnc cipher ks.toArray) (blindElem nike a ks.toArray)
      (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply r.2.2.2]) r.2.1) (RSOR.path nike
          q.back [.surbReply r.2.2.2]) (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
          with
  | some pkt => pkt.extract 0 geom.headerLength
  | none => ByteArray.empty

/-- `backOnionOfKeys`, with the tag of hop `j` of the backward path given. -/
def backOnionOfTag (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (hb : 0 <
    q.back.hops.length)
    (a : ByteArray) (ks : List HopKeys) (j : ℕ) (tag : ByteArray) : Onion geom :=
  match RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike q.fwd [.recipient
      q.receiver]) r.1
      (bodyH nike geom q r hb (backHdrOfTag nike cipher macS streamS geom q r a ks j tag)) 0 with
  | .ok pkt => split geom pkt
  | .error _ => default

/-- `backLayerOfKeys`, with the tag of hop `j` given. -/
def backLayerOfTag (i : ℕ) (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a :
    ByteArray)
    (ks : List HopKeys) (j : ℕ) (tag : ByteArray) : Onion geom :=
  match nikePktFn geom (keysKs geom streamS ks.toArray)
      (Function.update (keysTag macS ks.toArray) j fun _ => tag)
      (keysEnc cipher ks.toArray) (blindElem nike a ks.toArray)
      (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply r.2.2.2]) r.2.1) (RSOR.path nike
          q.back [.surbReply r.2.2.2]) (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
          with
  | some pkt => split geom (peels nike cipher streamS geom ks i pkt)
  | none => default

/-- **The reply block uses the replaced hop's MAC key for one tag only.** -/
theorem backHdrOfKeys_tag (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a :
    ByteArray)
    (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (x : Rest) (km : Vector UInt8 32)
    (n : ℕ) (hj : j < n) (hjp : j < (RSOR.path nike q.back [.surbReply r.2.2.2]).size) :
    backHdrOfKeys nike cipher macS streamS geom q r a (hopKeysWith nike kdfS c hops j (restKeys x
        km) n)
      = backHdrOfTag nike cipher macS streamS geom q r a (hopKeysWith nike kdfS c hops j (restKeys
          x default) n) j
        (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
          (backMsg nike macS streamS geom q r a (hopKeysWith nike kdfS c hops j (restKeys x
              default) n) j))) := by
  unfold backHdrOfKeys backHdrOfTag backMsg
  rw [nikePktFn_restKeys nike cipher macS kdfS streamS geom a c hops j x km n hj _ _ _ hjp]

/-- **The adversary's first layer uses the replaced backward hop's MAC key for one tag
only.** -/
theorem backOnionOfKeys_tag (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom)
    (hb : 0 < q.back.hops.length) (a : ByteArray) (c : nike.PrivateKey) (hops : Array PathHop)
    (j : ℕ) (x : Rest) (km : Vector UInt8 32) (n : ℕ) (hj : j < n) (hjp : j < (RSOR.path nike
        q.back [.surbReply r.2.2.2]).size) :
    backOnionOfKeys nike cipher macS kdfS streamS geom q r hb a (hopKeysWith nike kdfS c hops j
        (restKeys x km) n)
      = backOnionOfTag nike cipher macS kdfS streamS geom q r hb a (hopKeysWith nike kdfS c hops j
          (restKeys x default) n) j
        (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
          (backMsg nike macS streamS geom q r a (hopKeysWith nike kdfS c hops j (restKeys x
              default) n) j))) := by
  unfold backOnionOfKeys backOnionOfTag
  rw [backHdrOfKeys_tag nike cipher macS kdfS streamS geom q r a c hops j x km n hj hjp]

/-- **So does each layer of the reply's packet.** -/
theorem backLayerOfKeys_tag (i : ℕ) (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a
    : ByteArray)
    (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (x : Rest) (km : Vector UInt8 32)
    (n : ℕ) (hj : j < n) (hjp : j < (RSOR.path nike q.back [.surbReply r.2.2.2]).size) :
    backLayerOfKeys nike cipher macS streamS geom i q r a (hopKeysWith nike kdfS c hops j (restKeys
        x km) n)
      = backLayerOfTag nike cipher macS streamS geom i q r a (hopKeysWith nike kdfS c hops j
          (restKeys x default) n) j
        (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
          (backMsg nike macS streamS geom q r a (hopKeysWith nike kdfS c hops j (restKeys x
              default) n) j))) := by
  unfold backLayerOfKeys backLayerOfTag backMsg
  rw [nikePktFn_restKeys nike cipher macS kdfS streamS geom a c hops j x km n hj _ _ _ hjp,
    peels_restKeys nike cipher kdfS streamS geom c hops j x km n hj i]

/-! ## Two lists of hop keys that differ in payload keys only -/

omit cipher kdfS hvalid hmactag h16 in
/-- Their keystreams, tagging functions and blinded elements are the same. -/
theorem keyFns_congr (K K' : List HopKeys) (hK : ∀ m : ℕ, (K[m]?).map (fun k : HopKeys =>
    (k.headerMAC, k.headerEncryption, k.headerEncryptionIV, k.blindingFactor)) = (K'[m]?).map (fun
    k : HopKeys => (k.headerMAC, k.headerEncryption, k.headerEncryptionIV, k.blindingFactor))) :
    keysKs geom streamS K.toArray = keysKs geom streamS K'.toArray
      ∧ keysTag macS K.toArray = keysTag macS K'.toArray
      ∧ ∀ a, blindElem nike a K.toArray = blindElem nike a K'.toArray := by
  have hfld : ∀ m : ℕ, (fun k : HopKeys => (k.headerMAC, k.headerEncryption, k.headerEncryptionIV,
      k.blindingFactor)) (K.toArray[m]!) = (fun k : HopKeys => (k.headerMAC, k.headerEncryption,
      k.headerEncryptionIV, k.blindingFactor)) (K'.toArray[m]!) := fun m => by
    have h := hK m
    have e : ∀ (L : List HopKeys), L.toArray[m]! = (L[m]?).getD default := fun L => by
      simp only [getElem!_def, List.getElem?_toArray]
      cases L[m]? <;> rfl
    rw [e, e]
    cases h1 : K[m]? <;> cases h2 : K'[m]? <;> rw [h1, h2] at h
    · cases h
    · cases h
    · exact Option.some.inj h
  refine ⟨funext fun i => ?_, funext fun i => ?_, fun a => funext fun i => ?_⟩
  · have h := hfld i
    simp only [Prod.mk.injEq] at h
    unfold keysKs
    rw [h.2.1, h.2.2.1]
  · have h := hfld i
    simp only [Prod.mk.injEq] at h
    unfold keysTag
    rw [h.1]
  · refine blindElem_congr nike a _ _ (fun m => ?_) i
    have h := hfld m
    simp only [Prod.mk.injEq] at h
    exact h.2.2.2

omit cipher kdfS hvalid hmactag h16 in
/-- The bytes a hop's tag covers in the reply's packet are the same. -/
theorem backMsg_congr (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a : ByteArray)
    (K K' : List HopKeys) (j : ℕ) (hK : ∀ m : ℕ, (K[m]?).map (fun k : HopKeys => (k.headerMAC,
        k.headerEncryption, k.headerEncryptionIV, k.blindingFactor)) = (K'[m]?).map (fun k :
        HopKeys => (k.headerMAC, k.headerEncryption, k.headerEncryptionIV, k.blindingFactor))) :
    backMsg nike macS streamS geom q r a K j = backMsg nike macS streamS geom q r a K' j := by
  obtain ⟨hks, htg, hge⟩ := keyFns_congr nike macS streamS geom K K' hK
  unfold backMsg
  rw [hks, htg, hge a]

include hvalid hmactag in
/-- The header of the reply's first layer is the same. -/
theorem backHdrOfTag_congr (q : RSOR.Request nike geom) (r : RSOR.Randomness nike geom) (a :
    ByteArray)
    (K K' : List HopKeys) (j : ℕ) (tag : ByteArray) (hK : ∀ m : ℕ, (K[m]?).map (fun k : HopKeys =>
        (k.headerMAC, k.headerEncryption, k.headerEncryptionIV, k.blindingFactor)) = (K'[m]?).map
        (fun k : HopKeys => (k.headerMAC, k.headerEncryption, k.headerEncryptionIV,
        k.blindingFactor)))
    (hb : 0 < q.back.hops.length) (ha : a.size = nike.publicKeySize)
    (ht : tag.size = macLength) :
    backHdrOfTag nike cipher macS streamS geom q r a K j tag
      = backHdrOfTag nike cipher macS streamS geom q r a K' j tag := by
  obtain ⟨hks, htg, hge⟩ := keyFns_congr nike macS streamS geom K K' hK
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hsz := RSOR.path_size nike q.back [.surbReply r.2.2.2]
  have hlen : q.back.hops.length ≤ geom.nrHops := q.back.length_le
  have hmul : (geom.nrHops - (RSOR.path nike q.back [.surbReply r.2.2.2]).size) *
      geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hfill : (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply r.2.2.2]) r.2.1).size
      = (geom.nrHops - (RSOR.path nike q.back [.surbReply r.2.2.2]).size) *
          geom.perHopRoutingInfoLength := by
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have htag : ∀ (m : ℕ) (x : ByteArray),
      ((Function.update (keysTag macS K'.toArray) j fun _ => tag) m x).size = macLength :=
    fun m x => by
      by_cases hm : m = j
      · rw [hm, Function.update_self]
        exact ht
      · rw [Function.update_of_ne hm]
        exact (Util.Bytes.size_ofVector _).trans hmactag
  unfold backHdrOfTag
  rw [hks, htg, hge a]
  exact nikePktFn_hdr_enc nike geom hvalid _ _ _ _ _ _ _ _ (by rw [hsz]; exact hlen)
    (by rw [hsz]; exact hb) hfill htag ha

include hvalid hmactag h16 in
/-- The header of each layer of the reply's packet is the same. -/
theorem backLayerOfTag_fst_congr (i : ℕ) (q : RSOR.Request nike geom) (r : RSOR.Randomness nike
    geom)
    (a : ByteArray) (K K' : List HopKeys) (j : ℕ) (tag : ByteArray) (hK : ∀ m : ℕ, (K[m]?).map (fun
        k : HopKeys => (k.headerMAC, k.headerEncryption, k.headerEncryptionIV, k.blindingFactor)) =
        (K'[m]?).map (fun k : HopKeys => (k.headerMAC, k.headerEncryption, k.headerEncryptionIV,
        k.blindingFactor)))
    (hi : i ≤ K.length) (hi' : i ≤ K'.length)
    (hb : 0 < q.back.hops.length) (ha : a.size = nike.publicKeySize)
    (ht : tag.size = macLength) :
    (backLayerOfTag nike cipher macS streamS geom i q r a K j tag).1
      = (backLayerOfTag nike cipher macS streamS geom i q r a K' j tag).1 := by
  obtain ⟨hks, htg, hge⟩ := keyFns_congr nike macS streamS geom K K' hK
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hsz := RSOR.path_size nike q.back [.surbReply r.2.2.2]
  have hlen : q.back.hops.length ≤ geom.nrHops := q.back.length_le
  have hmul : (geom.nrHops - (RSOR.path nike q.back [.surbReply r.2.2.2]).size) *
      geom.perHopRoutingInfoLength
      ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hfill : (RSOR.filler nike geom (RSOR.path nike q.back [.surbReply r.2.2.2]) r.2.1).size
      = (geom.nrHops - (RSOR.path nike q.back [.surbReply r.2.2.2]).size) *
          geom.perHopRoutingInfoLength := by
    unfold RSOR.filler
    rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
    omega
  have htag : ∀ (m : ℕ) (x : ByteArray),
      ((Function.update (keysTag macS K'.toArray) j fun _ => tag) m x).size = macLength :=
    fun m x => by
      by_cases hm : m = j
      · rw [hm, Function.update_self]
        exact ht
      · rw [Function.update_of_ne hm]
        exact (Util.Bytes.size_ofVector _).trans hmactag
  have hF : ∀ m : ℕ,
      (K[m]?).map (fun k : HopKeys => (k.headerEncryption, k.headerEncryptionIV, k.blindingFactor))
        = (K'[m]?).map
          (fun k : HopKeys => (k.headerEncryption, k.headerEncryptionIV, k.blindingFactor)) :=
    fun m => by
      have h := congrArg (Option.map
        fun g : Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 16 × ByteArray => g.2) (hK m)
      rw [Option.map_map, Option.map_map] at h
      exact h
  unfold backLayerOfTag
  rw [hks, htg, hge a]
  exact nikePktFn_peels_fst nike cipher streamS geom hvalid h16 K K' i hi hi' hF _ _ _ _ _ _
    (by rw [hsz]; exact hlen) (by rw [hsz]; exact hb) hfill htag ha

variable (W : Protocols.RSOR.BackSwap (sphinx nike cipher macS kdfS streamS geom hvalid hmactag
    h16))

/-- The challenger's draws in world 1: its randomness, and the draws for the onion sent on. -/
def swapDraw : ProbComp (RSOR.Randomness nike geom × W.X) := do
  let r ← $ᵗ (RSOR.Randomness nike geom)
  let x ← W.draw
  return (r, x)

/-- The challenger's draws in world 0: its randomness, and a block for the ideal cipher to
decrypt to when the sender has encrypted nothing under the relay's payload key. -/
def backDraw0 : ProbComp (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) := do
  let r ← $ᵗ (RSOR.Randomness nike geom)
  let w ← $ᵗ (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength))
  return (r, w)

/-- **World 0 of SLU← as its draws**, with the secret of the honest relay's path drawn apart,
and then the adversary's guess against the honest relays. -/
theorem backward_play_false_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) :
    Protocols.RSOR.Property.play names A false
      =ᵈ propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A >>= fun D =>
        (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid hmactag
            h16 .relay names D.k.1 D.keys)
            (fun h => if h = .relay then D.k.2 else (D.keys h).2)
                (Protocols.RSOR.BackwardChallenge.world0 D.c (relayKey D.c.pos D.o.1 D.d)).patch)
          (A.guess D.st (Protocols.RSOR.BackwardChallenge.world0 D.c (relayKey D.c.pos D.o.1
              D.d)).onion)).run' D.log := by
  refine (play_evalDistEq_honAt nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names A false).trans ?_
  unfold Protocols.RSOR.Property.playFrom propDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
    EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => ?_
  have hcong : ∀ (m m' : ProbComp (Protocols.RSOR.World 𝒮))
      (F : Protocols.RSOR.World 𝒮 → ProbComp Bool), m = m' → m >>= F =ᵈ m' >>= F :=
    fun _ _ _ h => h ▸ EvalDistEq.rfl
  refine (hcong _ _ _ (Protocols.RSOR.backwardWith_world_false W out.1.1)).trans ?_
  simp only [backDraw0, bind_assoc, pure_bind]
  refine EvalDistEq.symm ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ =>
    OracleComp.EvalDistEq.bind_const _ _) ?_
  exact evalDistEq_relayKey nike geom out.1.1.pos fun r =>
    (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid hmactag h16
        .relay names k.1 (keysOf nike .relay k₁ k₂))
        (fun h => if h = .relay then k.2 else ((keysOf nike .relay k₁ k₂) h).2)
        (Protocols.RSOR.BackwardChallenge.world0 out.1.1 r).patch)
      (A.guess out.1.2 (Protocols.RSOR.BackwardChallenge.world0 out.1.1 r).onion)).run' out.2

/-- **World 1 of SLU← as its draws**, with the secret of the honest relay's path drawn apart,
and then the adversary's guess against the honest relays. -/
theorem backward_play_true_evalDistEq (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) :
    Protocols.RSOR.Property.play names A true
      =ᵈ propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W) A >>= fun D =>
        (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid hmactag
            h16 .relay names D.k.1 D.keys)
            (fun h => if h = .relay then D.k.2 else (D.keys h).2)
                (Protocols.RSOR.BackwardChallenge.world1Of W D.c (relayKey D.c.pos D.o.1 D.d)
                D.o.2).patch)
          (A.guess D.st (Protocols.RSOR.BackwardChallenge.world1Of W D.c (relayKey D.c.pos D.o.1
              D.d) D.o.2).onion)).run' D.log := by
  refine (play_evalDistEq_honAt nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names A true).trans ?_
  unfold Protocols.RSOR.Property.playFrom propDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
    EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => ?_
  have hcong : ∀ (m m' : ProbComp (Protocols.RSOR.World 𝒮))
      (F : Protocols.RSOR.World 𝒮 → ProbComp Bool), m = m' → m >>= F =ᵈ m' >>= F :=
    fun _ _ _ h => h ▸ EvalDistEq.rfl
  refine (hcong _ _ _ (Protocols.RSOR.backwardWith_world_true W out.1.1)).trans ?_
  simp only [swapDraw, bind_assoc, pure_bind]
  refine EvalDistEq.symm ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact evalDistEq_relayKey nike geom out.1.1.pos fun r =>
    W.draw >>= fun x =>
      (simulateQ (Protocols.RSOR.honest (honAt nike cipher macS kdfS streamS geom hvalid hmactag
          h16 .relay names k.1 (keysOf nike .relay k₁ k₂))
          (fun h => if h = .relay then k.2 else ((keysOf nike .relay k₁ k₂) h).2)
          (Protocols.RSOR.BackwardChallenge.world1Of W out.1.1 r x).patch)
        (A.guess out.1.2
          (Protocols.RSOR.BackwardChallenge.world1Of W out.1.1 r x).onion)).run' out.2

/-! ## World 0 around the honest relay's keys -/

/-- The path whose keys the key game replaces for SLU←, and the honest relay's place on it: the
forward path and its last hop when the relay is the exit relay, the backward path and the hop
before the challenge position otherwise. -/
def backPlace (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS kdfS streamS
    geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) : Array PathHop × ℕ :=
  match ch.c.pos.val with
  | 0 => (RSOR.path nike ch.c.req.fwd [], ch.c.req.fwd.hops.length - 1)
  | k + 1 => (RSOR.path nike ch.c.req.back [], k)

/-- **World 0 of SLU← around the honest relay's keys.** At the exit the relay's layer is the
last of the forward path. On the backward path its keys enter the adversary's onion through the
reply block, and the header the sender refuses through the reply's last layer. -/
def backView0 (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS kdfS streamS
    geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk)
    (ow : RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) (a : ByteArray) (ks : List HopKeys) : Protocols.RSOR.World 𝒮 :=
  match ch.c.pos.val with
  | 0 =>
    { onion := onionOfKeys nike cipher macS kdfS streamS geom 0 ch.c.req ow.1 a ks
      patch := (Protocols.RSOR.BackwardChallenge.world0 ch.c ow.1).patch }
  | _ + 1 =>
    { onion := backOnionOfKeys nike cipher macS kdfS streamS geom ch.c.req ow.1
        (Nat.zero_lt_of_lt ch.c.pos.isLt) a ks
      patch :=
        { proc := fun (h : Role) (o : Onion geom) out =>
            if h = .sender ∧ o.1 = (backLayerOfKeys nike cipher macS streamS geom
                (ch.c.req.back.hops.length - 1) ch.c.req ow.1 a ks).1 then pure none
            else pure out } }

/-- The adversary on the key game for world 0 of SLU←. -/
abbrev backAdv0 (names : Role → Name) (A : (Protocols.RSOR.backwardWith W).Adversary) :
    KeyAdversary nike :=
  propAdvOf nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
      .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) _
      (backDraw0 nike geom)
    (backView0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A

include hvalid hmactag in
/-- **On the backward path, the view on the sender's own keys is world 0**, from the randomness
with the backward path's secret replaced, when the reply's packet builds and its last layer has
at least a header's length. -/
theorem backView0_real_back (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher
    macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk)
    (ow : RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) (k : ℕ) (hp : ch.c.pos.val = k + 1)
    (d : Vector UInt8 nike.privateKeySize) (x0 : ByteArray)
    (hx0 : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike ch.c.req.back [.surbReply
        ow.1.2.2.2]) (relayKey (k + 1) ow.1 d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
        ByteArray)
      0 = .ok x0)
    (hsz : ∀ pkt, RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike ch.c.req.back
        [.surbReply ow.1.2.2.2])
      (relayKey (k + 1) ow.1 d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
          (ch.c.req.back.hops.length - 1) = .ok pkt →
        geom.headerLength ≤ pkt.size) :
    backView0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch ow (groupElem nike
        ((nike.decodePrivateKey d).getD default) (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey
        d).getD default) (RSOR.path nike ch.c.req.back [.surbReply ow.1.2.2.2]) (RSOR.path nike
        ch.c.req.back [.surbReply ow.1.2.2.2]).size).toArray 0) (RSOR.hopKeys nike kdfS
        ((nike.decodePrivateKey d).getD default) (RSOR.path nike ch.c.req.back [.surbReply
        ow.1.2.2.2]) (RSOR.path nike ch.c.req.back [.surbReply ow.1.2.2.2]).size)
      = Protocols.RSOR.BackwardChallenge.world0 ch.c (relayKey (k + 1) ow.1 d) := by
  have hlt : ch.c.pos.val < ch.c.req.back.hops.length := ch.c.pos.isLt
  have honion := backOnionOfKeys_real nike cipher macS kdfS streamS geom hvalid hmactag ch.c.req
    ow.1 d k (Nat.zero_lt_of_lt hlt) x0 hx0
  have hhdr : (RSOR.formBack nike cipher macS kdfS streamS geom ch.c.req (relayKey (k + 1) ow.1 d)
      ch.c.req.msg ⟨ch.c.req.back.hops.length - 1,
        Nat.sub_one_lt (Nat.ne_of_gt (Nat.zero_lt_of_lt hlt))⟩).1
      = (backLayerOfKeys nike cipher macS streamS geom (ch.c.req.back.hops.length - 1) ch.c.req
        ow.1 (groupElem nike ((nike.decodePrivateKey d).getD default) (RSOR.hopKeys nike kdfS
            ((nike.decodePrivateKey d).getD default) (RSOR.path nike ch.c.req.back [.surbReply
            ow.1.2.2.2]) (RSOR.path nike ch.c.req.back [.surbReply ow.1.2.2.2]).size).toArray 0)
            (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default) (RSOR.path nike
            ch.c.req.back [.surbReply ow.1.2.2.2]) (RSOR.path nike ch.c.req.back [.surbReply
            ow.1.2.2.2]).size)).1 := by
    rw [backLayerOfKeys_real nike cipher macS kdfS streamS geom (ch.c.req.back.hops.length - 1)
      ch.c.req ow.1 d k x0 (by rw [RSOR.path_size]; exact Nat.sub_le _ _) hx0]
    cases hl : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike ch.c.req.back
        [.surbReply ow.1.2.2.2]) (relayKey (k + 1) ow.1 d).2.1
        (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) (ch.c.req.back.hops.length - 1)
            with
    | error err =>
      have hl' : RSOR.layer nike cipher macS kdfS streamS geom
          (RSOR.path nike ch.c.req.back [.surbReply (relayKey (k + 1) ow.1 d).2.2.2])
          (relayKey (k + 1) ow.1 d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
          (ch.c.req.back.hops.length - 1) = .error err := hl
      unfold RSOR.formBack
      dsimp only
      rw [hl']
    | ok pkt =>
      exact formBack_fst nike cipher macS kdfS streamS geom ch.c.req (relayKey (k + 1) ow.1 d)
        ch.c.req.msg _ pkt hl (hsz pkt hl)
  unfold backView0
  rw [hp]
  exact congrArg₂ (fun on (hd : Vector UInt8 geom.headerLength) =>
    ({ onion := on
       patch := { proc := fun (h : Role) (o : Onion geom) out =>
        if h = .sender ∧ o.1 = hd then pure none else pure out } } : Protocols.RSOR.World 𝒮))
    honion hhdr.symm

/-- **At the exit, the view on the sender's own keys is world 0**, from the randomness with the
forward path's secret replaced, when the adversary's onion builds. -/
theorem backView0_real_exit (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher
    macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk)
    (ow : RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
        geom.forwardPayloadLength))) (hp : ch.c.pos.val = 0) (d : Vector UInt8 nike.privateKeySize)
    (pkt : ByteArray)
    (hpkt : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike ch.c.req.fwd [.recipient
        ch.c.req.receiver]) (setKey ow.1 d).1
      (RSOR.body nike macS kdfS streamS geom ch.c.req (setKey ow.1 d)) 0 = .ok pkt) :
    backView0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch ow (groupElem nike
        ((nike.decodePrivateKey d).getD default) (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey
        d).getD default) (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]) (RSOR.path
        nike ch.c.req.fwd [.recipient ch.c.req.receiver]).size).toArray 0) (RSOR.hopKeys nike kdfS
        ((nike.decodePrivateKey d).getD default) (RSOR.path nike ch.c.req.fwd [.recipient
        ch.c.req.receiver]) (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
      = Protocols.RSOR.BackwardChallenge.world0 ch.c (setKey ow.1 d) := by
  have honion := onionOfKeys_real nike cipher macS kdfS streamS geom ch.c.req ow.1 d pkt
    ch.c.req.first hpkt
  unfold backView0
  rw [hp]
  exact congrArg₂ (fun on pt => ({ onion := on, patch := pt } : Protocols.RSOR.World 𝒮))
    honion rfl

/-- The draws of world 0 that the exact step does not cover. At the exit: the adversary's onion
cannot be built. On the backward path: the reply's packet cannot be built, or its last layer
is shorter than a header. -/
def backBad0 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (D : PropDraw
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) : Prop :=
  ¬ (match D.c.pos.val with
    | 0 => ∃ pkt, RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike D.c.req.fwd
        [.recipient D.c.req.receiver]) (setKey D.o.1 D.d).1
        (RSOR.body nike macS kdfS streamS geom D.c.req (setKey D.o.1 D.d)) 0 = .ok pkt
    | k + 1 => (∃ x0, RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike D.c.req.back
        [.surbReply D.o.1.2.2.2])
          (relayKey (k + 1) D.o.1 D.d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
              ByteArray) 0 = .ok x0)
        ∧ ∀ pkt, RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike D.c.req.back
            [.surbReply D.o.1.2.2.2])
          (relayKey (k + 1) D.o.1 D.d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
              ByteArray) (D.c.req.back.hops.length - 1) = .ok pkt →
            geom.headerLength ≤ pkt.size)

set_option maxHeartbeats 4000000 in
/-- **World 0 of SLU← is the key game's real world, off the bad draws.** -/
theorem backward_false_sub_keyGame_le (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
      - (Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv0 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names A)
          true)}[x = true]).toReal|
    ≤ (Pr{let D ← (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A)}[backBad0 nike
        cipher macS kdfS streamS geom hvalid hmactag h16 W
        D]).toReal := by
  rw [(backward_play_false_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 W names
      A).prEvent_eq (fun x => x = true),
    (keyGame_true_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names _ _ _ _ A).prEvent_eq (fun x => x = true)]
  refine KEMSphinx.prEvent_bind_toReal_sub_le_of_bad _ _ _ (backBad0 nike cipher macS kdfS streamS
      geom
      hvalid hmactag h16 W) (fun D hD => ?_)
    (fun x => x = true)
  have hgood := Classical.not_not.mp hD
  obtain hk | ⟨k, hk⟩ : D.c.pos.val = 0 ∨ ∃ k, D.c.pos.val = k + 1 := by
    cases h : D.c.pos.val with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, rfl⟩
  · rw [hk] at hgood
    obtain ⟨pkt, hpkt⟩ := hgood
    have hlen : 0 < D.c.req.fwd.hops.length := List.length_pos_iff.2 D.c.req.fwd_ne
    have hlast : D.c.req.fwd.hops.length - 1 < D.c.req.fwd.hops.length := Nat.sub_one_lt (by omega)
    have hrel := D.c.relay
    rw [hk] at hrel
    have hkey : (D.c.req.fwd.hops[D.c.req.fwd.hops.length - 1]'hlast).key = D.k.1 := by
      have h1 : D.c.req.fwd.hops[D.c.req.fwd.hops.length - 1]'hlast
          = honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay names D.k.1 D.keys
              .relay :=
        Option.some.inj ((List.getElem?_eq_getElem hlast).symm.trans
          (List.getLast?_eq_getElem?.symm.trans hrel))
      rw [h1]
      rfl
    have hsz := RSOR.path_size nike D.c.req.fwd ([] : List RoutingCommand)
    have hmod := modify_publicKey_self (RSOR.path nike D.c.req.fwd []) (D.c.req.fwd.hops.length -
        1) (Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1))
      (lt_of_lt_of_eq hlast hsz.symm) (by
        rw [RSOR.path_getElem! nike _ _ _ hlast]
        exact congrArg (fun key : RSOR.Key nike =>
          Util.Bytes.ofVector (nike.encodePublicKey key.1)) hkey)
    have hK : RSOR.hopKeys nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
        D.c.req.fwd []) (RSOR.path nike D.c.req.fwd []).size
        = RSOR.hopKeys nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
            D.c.req.fwd [.recipient D.c.req.receiver]) (RSOR.path nike D.c.req.fwd [.recipient
            D.c.req.receiver]).size := by
      rw [hsz, RSOR.path_size nike D.c.req.fwd [.recipient D.c.req.receiver]]
      exact hopKeys_congr_pub nike kdfS _ _ _ _ fun i hi => by
        rw [RSOR.path_getElem! nike _ _ i hi, RSOR.path_getElem! nike _ _ i hi]
    have hpl : backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨D.keys,
        D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D.k.1) = ((RSOR.path nike D.c.req.fwd []),
        D.c.req.fwd.hops.length - 1) := by
      unfold backPlace
      rw [hk]
    have hrk : relayKey (D.c.pos : ℕ) D.o.1 D.d = setKey D.o.1 D.d := by
      rw [hk]
      rfl
    unfold propRealOf
    simp only [hpl]
    rw [hmod, hK, hrk]
    refine Eq.trans ?_ (ite_eq_left (lt_of_lt_of_eq hlast hsz.symm)).symm
    rw [backView0_real_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨D.keys,
        D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D.k.1) D.o hk D.d pkt hpkt]
  · rw [hk] at hgood
    obtain ⟨⟨x0, hx0⟩, hszL⟩ := hgood
    have hlt : D.c.pos.val < D.c.req.back.hops.length := D.c.pos.isLt
    have hkl : k < D.c.req.back.hops.length := by omega
    have hrel := D.c.relay
    rw [hk] at hrel
    have hkey : (D.c.req.back.hops[k]'hkl).key = D.k.1 := by
      have h1 : D.c.req.back.hops[k]'hkl = honAt nike cipher macS kdfS streamS geom hvalid hmactag
          h16 .relay names D.k.1 D.keys .relay :=
        Option.some.inj ((List.getElem?_eq_getElem hkl).symm.trans hrel)
      rw [h1]
      rfl
    have hsz := RSOR.path_size nike D.c.req.back ([] : List RoutingCommand)
    have hmod := modify_publicKey_self (RSOR.path nike D.c.req.back []) k (Util.Bytes.ofVector
        (nike.encodePublicKey D.k.1.1)) (lt_of_lt_of_eq hkl hsz.symm) (by
      rw [RSOR.path_getElem! nike _ _ _ hkl]
      exact congrArg (fun key : RSOR.Key nike =>
        Util.Bytes.ofVector (nike.encodePublicKey key.1)) hkey)
    have hK : RSOR.hopKeys nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
        D.c.req.back []) (RSOR.path nike D.c.req.back []).size
        = RSOR.hopKeys nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
            D.c.req.back [.surbReply D.o.1.2.2.2]) (RSOR.path nike D.c.req.back [.surbReply
            D.o.1.2.2.2]).size := by
      rw [hsz, RSOR.path_size nike D.c.req.back [.surbReply D.o.1.2.2.2]]
      exact hopKeys_congr_pub nike kdfS _ _ _ _ fun i hi => by
        rw [RSOR.path_getElem! nike _ _ i hi, RSOR.path_getElem! nike _ _ i hi]
    have hpl : backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨D.keys,
        D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D.k.1) = ((RSOR.path nike D.c.req.back []), k)
        := by
      unfold backPlace
      rw [hk]
    have hrk : relayKey (D.c.pos : ℕ) D.o.1 D.d = relayKey (k + 1) D.o.1 D.d := by rw [hk]
    unfold propRealOf
    simp only [hpl]
    rw [hmod, hK, hrk]
    refine Eq.trans ?_ (ite_eq_left (lt_of_lt_of_eq hkl hsz.symm)).symm
    rw [backView0_real_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨D.keys,
        D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D.k.1) D.o k hk D.d x0 hx0 hszL]

/-! ## World 1 around the honest relay's keys -/

/-- **World 1 of SLU← around the honest relay's keys**: the adversary's first layer, the header
of the relay's own reply layer and the header of the relay's own forward layer, each from the
keys of the relay's path. -/
def backView1 (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS kdfS streamS
    geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) (o : RSOR.Randomness
    nike geom × W.X)
    (a : ByteArray) (ks : List HopKeys) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1With ch.c
    (match ch.c.pos.val with
      | 0 => onionOfKeys nike cipher macS kdfS streamS geom 0 ch.c.req o.1 a ks
      | _ + 1 => backOnionOfKeys nike cipher macS kdfS streamS geom ch.c.req o.1
          (Nat.zero_lt_of_lt ch.c.pos.isLt) a ks)
    (match ch.c.pos.val with
      | 0 => none
      | k + 1 => if k < ch.c.req.back.hops.length then
          some (backLayerOfKeys nike cipher macS streamS geom k ch.c.req o.1 a ks).1
        else none)
    (if ch.c.pos.val = 0 then
        some (onionOfKeys nike cipher macS kdfS streamS geom (ch.c.req.fwd.hops.length - 1)
          ch.c.req o.1 a ks).1
      else none)
    (W.of ch.c o.2).1 (W.of ch.c o.2).2

/-- The adversary on the key game for world 1 of SLU←. -/
abbrev backAdv1 (names : Role → Name) (A : (Protocols.RSOR.backwardWith W).Adversary) :
    KeyAdversary nike :=
  propAdvOf nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
      .relay names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) _
      (swapDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
    (backView1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A

include hvalid hmactag in
/-- **On the backward path, the view on the sender's own keys is world 1**, when the reply's
packet builds and its layer at the relay has at least a header's length. -/
theorem backView1_real_back (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher
    macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk)
    (o : RSOR.Randomness nike geom × W.X) (k : ℕ) (hp : ch.c.pos.val = k + 1)
    (d : Vector UInt8 nike.privateKeySize) (x0 : ByteArray)
    (hx0 : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike ch.c.req.back [.surbReply
        o.1.2.2.2]) (relayKey (k + 1) o.1 d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
        ByteArray)
      0 = .ok x0)
    (hsz : ∀ pkt, RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike ch.c.req.back
        [.surbReply o.1.2.2.2])
      (relayKey (k + 1) o.1 d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) k =
          .ok pkt → geom.headerLength ≤ pkt.size) :
    backView1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o (groupElem nike
        ((nike.decodePrivateKey d).getD default) (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey
        d).getD default) (RSOR.path nike ch.c.req.back [.surbReply o.1.2.2.2]) (RSOR.path nike
        ch.c.req.back [.surbReply o.1.2.2.2]).size).toArray 0) (RSOR.hopKeys nike kdfS
        ((nike.decodePrivateKey d).getD default) (RSOR.path nike ch.c.req.back [.surbReply
        o.1.2.2.2]) (RSOR.path nike ch.c.req.back [.surbReply o.1.2.2.2]).size)
      = Protocols.RSOR.BackwardChallenge.world1Of W ch.c (relayKey (k + 1) o.1 d) o.2 := by
  have hlt : ch.c.pos.val < ch.c.req.back.hops.length := ch.c.pos.isLt
  have hk : k < ch.c.req.back.hops.length := by omega
  have honion := backOnionOfKeys_real nike cipher macS kdfS streamS geom hvalid hmactag ch.c.req
    o.1 d k (Nat.zero_lt_of_lt hlt) x0 hx0
  have hhdr : (RSOR.formBack nike cipher macS kdfS streamS geom ch.c.req (relayKey (k + 1) o.1 d)
      ch.c.req.msg ⟨k, hk⟩).1
      = (backLayerOfKeys nike cipher macS streamS geom k ch.c.req o.1
        (groupElem nike ((nike.decodePrivateKey d).getD default) (RSOR.hopKeys nike kdfS
            ((nike.decodePrivateKey d).getD default) (RSOR.path nike ch.c.req.back [.surbReply
            o.1.2.2.2]) (RSOR.path nike ch.c.req.back [.surbReply o.1.2.2.2]).size).toArray 0)
            (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey d).getD default) (RSOR.path nike
            ch.c.req.back [.surbReply o.1.2.2.2]) (RSOR.path nike ch.c.req.back [.surbReply
            o.1.2.2.2]).size)).1 := by
    rw [backLayerOfKeys_real nike cipher macS kdfS streamS geom k ch.c.req o.1 d k x0
      (by rw [RSOR.path_size]; exact le_of_lt hk) hx0]
    cases hl : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike ch.c.req.back
        [.surbReply o.1.2.2.2]) (relayKey (k + 1) o.1 d).2.1
        (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) k with
    | error err =>
      have hl' : RSOR.layer nike cipher macS kdfS streamS geom
          (RSOR.path nike ch.c.req.back [.surbReply (relayKey (k + 1) o.1 d).2.2.2])
          (relayKey (k + 1) o.1 d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray)
              k = .error err := hl
      unfold RSOR.formBack
      dsimp only
      rw [hl']
    | ok pkt =>
      exact formBack_fst nike cipher macS kdfS streamS geom ch.c.req (relayKey (k + 1) o.1 d)
        ch.c.req.msg _ pkt hl (hsz pkt hl)
  unfold backView1 Protocols.RSOR.BackwardChallenge.world1Of
    Protocols.RSOR.BackwardChallenge.ownAt Protocols.RSOR.BackwardChallenge.exitAt
  rw [hp]
  dsimp only
  rw [ite_eq_left hk, dite_eq_left hk, ite_eq_right (Nat.succ_ne_zero k),
    ite_eq_right (Nat.succ_ne_zero k)]
  exact congrArg₂ (fun (on : Onion geom) (hd : Vector UInt8 geom.headerLength) =>
    Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) ch.c on (some hd) none (W.of ch.c o.2).1
      (W.of ch.c o.2).2) honion hhdr.symm

/-- **At the exit, the view on the sender's own keys is world 1**, when the adversary's onion
builds. -/
theorem backView1_real_exit (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher
    macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk)
    (o : RSOR.Randomness nike geom × W.X) (hp : ch.c.pos.val = 0) (d : Vector UInt8
        nike.privateKeySize)
    (pkt : ByteArray)
    (hpkt : RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike ch.c.req.fwd [.recipient
        ch.c.req.receiver]) (setKey o.1 d).1
      (RSOR.body nike macS kdfS streamS geom ch.c.req (setKey o.1 d)) 0 = .ok pkt) :
    backView1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o (groupElem nike
        ((nike.decodePrivateKey d).getD default) (RSOR.hopKeys nike kdfS ((nike.decodePrivateKey
        d).getD default) (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]) (RSOR.path
        nike ch.c.req.fwd [.recipient ch.c.req.receiver]).size).toArray 0) (RSOR.hopKeys nike kdfS
        ((nike.decodePrivateKey d).getD default) (RSOR.path nike ch.c.req.fwd [.recipient
        ch.c.req.receiver]) (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
      = Protocols.RSOR.BackwardChallenge.world1Of W ch.c (setKey o.1 d) o.2 := by
  have honion := onionOfKeys_real nike cipher macS kdfS streamS geom ch.c.req o.1 d pkt
    ch.c.req.first hpkt
  have hlast := onionOfKeys_real nike cipher macS kdfS streamS geom ch.c.req o.1 d pkt
    ch.c.req.last hpkt
  unfold backView1 Protocols.RSOR.BackwardChallenge.world1Of
    Protocols.RSOR.BackwardChallenge.ownAt Protocols.RSOR.BackwardChallenge.exitAt
  rw [hp]
  dsimp only
  rw [ite_eq_left rfl, ite_eq_left rfl]
  exact congrArg₂ (fun (on : Onion geom) (ex : Vector UInt8 geom.headerLength) =>
    Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) ch.c on none (some ex) (W.of ch.c o.2).1
      (W.of ch.c o.2).2) honion (congrArg Prod.fst hlast)

/-- The draws of world 1 that the exact step does not cover. At the exit: the adversary's onion
cannot be built. On the backward path: the reply's packet cannot be built, or its layer at the
relay is shorter than a header. -/
def backBad1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (D : PropDraw
    nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
    names (RSOR.Randomness nike geom × W.X) A) : Prop :=
  ¬ (match D.c.pos.val with
    | 0 => ∃ pkt, RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike D.c.req.fwd
        [.recipient D.c.req.receiver]) (setKey D.o.1 D.d).1
        (RSOR.body nike macS kdfS streamS geom D.c.req (setKey D.o.1 D.d)) 0 = .ok pkt
    | k + 1 => (∃ x0, RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike D.c.req.back
        [.surbReply D.o.1.2.2.2])
          (relayKey (k + 1) D.o.1 D.d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
              ByteArray) 0 = .ok x0)
        ∧ ∀ pkt, RSOR.layer nike cipher macS kdfS streamS geom (RSOR.path nike D.c.req.back
            [.surbReply D.o.1.2.2.2])
          (relayKey (k + 1) D.o.1 D.d).2.1 (⟨Array.replicate geom.forwardPayloadLength 0⟩ :
              ByteArray) k = .ok pkt → geom.headerLength ≤ pkt.size)

set_option maxHeartbeats 4000000 in
/-- **World 1 of SLU← is the key game's real world, off the bad draws.** -/
theorem backward_true_sub_keyGame_le (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A true}[x = true]).toReal
      - (Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv1 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names A)
          true)}[x = true]).toReal|
    ≤ (Pr{let D ← (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike cipher macS kdfS streamS geom
        hvalid hmactag h16 W) A)}[backBad1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W
        D]).toReal := by
  rw [(backward_play_true_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16 W names
      A).prEvent_eq (fun x => x = true),
    (keyGame_true_evalDistEq nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names _ _ _ _ A).prEvent_eq (fun x => x = true)]
  refine KEMSphinx.prEvent_bind_toReal_sub_le_of_bad _ _ _ (backBad1 nike cipher macS kdfS streamS
      geom hvalid hmactag h16 W) (fun D hD => ?_)
    (fun x => x = true)
  have hgood := Classical.not_not.mp hD
  obtain hk | ⟨k, hk⟩ : D.c.pos.val = 0 ∨ ∃ k, D.c.pos.val = k + 1 := by
    cases h : D.c.pos.val with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, rfl⟩
  · rw [hk] at hgood
    obtain ⟨pkt, hpkt⟩ := hgood
    have hlen : 0 < D.c.req.fwd.hops.length := List.length_pos_iff.2 D.c.req.fwd_ne
    have hlast : D.c.req.fwd.hops.length - 1 < D.c.req.fwd.hops.length := Nat.sub_one_lt (by omega)
    have hrel := D.c.relay
    rw [hk] at hrel
    have hkey : (D.c.req.fwd.hops[D.c.req.fwd.hops.length - 1]'hlast).key = D.k.1 := by
      have h1 : D.c.req.fwd.hops[D.c.req.fwd.hops.length - 1]'hlast
          = honAt nike cipher macS kdfS streamS geom hvalid hmactag h16 .relay names D.k.1 D.keys
              .relay :=
        Option.some.inj ((List.getElem?_eq_getElem hlast).symm.trans
          (List.getLast?_eq_getElem?.symm.trans hrel))
      rw [h1]
      rfl
    have hsz := RSOR.path_size nike D.c.req.fwd ([] : List RoutingCommand)
    have hmod := modify_publicKey_self (RSOR.path nike D.c.req.fwd []) (D.c.req.fwd.hops.length -
        1) (Util.Bytes.ofVector (nike.encodePublicKey D.k.1.1))
      (lt_of_lt_of_eq hlast hsz.symm) (by
        rw [RSOR.path_getElem! nike _ _ _ hlast]
        exact congrArg (fun key : RSOR.Key nike =>
          Util.Bytes.ofVector (nike.encodePublicKey key.1)) hkey)
    have hK : RSOR.hopKeys nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
        D.c.req.fwd []) (RSOR.path nike D.c.req.fwd []).size
        = RSOR.hopKeys nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
            D.c.req.fwd [.recipient D.c.req.receiver]) (RSOR.path nike D.c.req.fwd [.recipient
            D.c.req.receiver]).size := by
      rw [hsz, RSOR.path_size nike D.c.req.fwd [.recipient D.c.req.receiver]]
      exact hopKeys_congr_pub nike kdfS _ _ _ _ fun i hi => by
        rw [RSOR.path_getElem! nike _ _ i hi, RSOR.path_getElem! nike _ _ i hi]
    have hpl : backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨D.keys,
        D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D.k.1) = ((RSOR.path nike D.c.req.fwd []),
        D.c.req.fwd.hops.length - 1) := by
      unfold backPlace
      rw [hk]
    have hrk : relayKey (D.c.pos : ℕ) D.o.1 D.d = setKey D.o.1 D.d := by
      rw [hk]
      rfl
    unfold propRealOf
    simp only [hpl]
    rw [hmod, hK, hrk]
    refine Eq.trans ?_ (ite_eq_left (lt_of_lt_of_eq hlast hsz.symm)).symm
    rw [backView1_real_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨D.keys,
        D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D.k.1) D.o hk D.d pkt hpkt]
  · rw [hk] at hgood
    obtain ⟨⟨x0, hx0⟩, hszL⟩ := hgood
    have hlt : D.c.pos.val < D.c.req.back.hops.length := D.c.pos.isLt
    have hkl : k < D.c.req.back.hops.length := by omega
    have hrel := D.c.relay
    rw [hk] at hrel
    have hkey : (D.c.req.back.hops[k]'hkl).key = D.k.1 := by
      have h1 : D.c.req.back.hops[k]'hkl = honAt nike cipher macS kdfS streamS geom hvalid hmactag
          h16 .relay names D.k.1 D.keys .relay :=
        Option.some.inj ((List.getElem?_eq_getElem hkl).symm.trans hrel)
      rw [h1]
      rfl
    have hsz := RSOR.path_size nike D.c.req.back ([] : List RoutingCommand)
    have hmod := modify_publicKey_self (RSOR.path nike D.c.req.back []) k (Util.Bytes.ofVector
        (nike.encodePublicKey D.k.1.1)) (lt_of_lt_of_eq hkl hsz.symm) (by
      rw [RSOR.path_getElem! nike _ _ _ hkl]
      exact congrArg (fun key : RSOR.Key nike =>
        Util.Bytes.ofVector (nike.encodePublicKey key.1)) hkey)
    have hK : RSOR.hopKeys nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
        D.c.req.back []) (RSOR.path nike D.c.req.back []).size
        = RSOR.hopKeys nike kdfS ((nike.decodePrivateKey D.d).getD default) (RSOR.path nike
            D.c.req.back [.surbReply D.o.1.2.2.2]) (RSOR.path nike D.c.req.back [.surbReply
            D.o.1.2.2.2]).size := by
      rw [hsz, RSOR.path_size nike D.c.req.back [.surbReply D.o.1.2.2.2]]
      exact hopKeys_congr_pub nike kdfS _ _ _ _ fun i hi => by
        rw [RSOR.path_getElem! nike _ _ i hi, RSOR.path_getElem! nike _ _ i hi]
    have hpl : backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨D.keys,
        D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D.k.1) = ((RSOR.path nike D.c.req.back []), k)
        := by
      unfold backPlace
      rw [hk]
    have hrk : relayKey (D.c.pos : ℕ) D.o.1 D.d = relayKey (k + 1) D.o.1 D.d := by rw [hk]
    unfold propRealOf
    simp only [hpl]
    rw [hmod, hK, hrk]
    refine Eq.trans ?_ (ite_eq_left (lt_of_lt_of_eq hkl hsz.symm)).symm
    rw [backView1_real_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨D.keys,
        D.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names D.k.1) D.o k hk D.d x0 hx0 hszL]

/-! ## Both worlds with the honest relay's keys replaced -/

/-- **SLU← with the honest relay's keys replaced.** The advantage is at most the chance of a
bad draw in each world, the advantage of each world's adversary in the key game, and the
distance between the two key games with the relay's keys replaced. -/
theorem backwardUnlinkable_le_keyGame (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) :
    ((Protocols.RSOR.backwardWith W).advantage names A).toReal
      ≤ (Pr{let D ← (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A)}[backBad0 nike
          cipher macS kdfS streamS geom hvalid hmactag h16 W
          D]).toReal
        + (Pr{let D ← (propDrawOf nike cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike cipher macS kdfS streamS
            geom hvalid hmactag h16 W) A)}[backBad1 nike cipher macS kdfS streamS geom hvalid
            hmactag h16 W
          D]).toReal
        + keyAdvantage cipher macS kdfS streamS geom (backAdv0 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 W names A)
        + keyAdvantage cipher macS kdfS streamS geom (backAdv1 nike cipher macS kdfS streamS geom
            hvalid hmactag h16 W names A)
        + |(Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W names A) false)}[x = true]).toReal
          - (Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv0 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W names A) false)}[x = true]).toReal| := by
  refine (Protocols.RSOR.Property.advantage_toReal (P := (Protocols.RSOR.backwardWith W)) names
      A).le.trans ?_
  have h0 := backward_false_sub_keyGame_le nike cipher macS kdfS streamS geom hvalid hmactag h16 W
      names A
  have h1 := backward_true_sub_keyGame_le nike cipher macS kdfS streamS geom hvalid hmactag h16 W
      names A
  have k0 : keyAdvantage cipher macS kdfS streamS geom (backAdv0 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names A)
      = |(Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv0 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names A) true)}[x = true]).toReal
        - (Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv0 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W names A) false)}[x = true]).toReal| := rfl
  have k1 : keyAdvantage cipher macS kdfS streamS geom (backAdv1 nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names A)
      = |(Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv1 nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names A) true)}[x = true]).toReal
        - (Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv1 nike cipher macS kdfS
            streamS geom hvalid hmactag h16 W names A) false)}[x = true]).toReal| := rfl
  have t1 := abs_sub_le ((Pr{let x ← Protocols.RSOR.Property.play names A true}[x = true]).toReal)
    ((Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W names A) true)}[x = true]).toReal)
    ((Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal)
  have t2 := abs_sub_le ((Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W names A) true)}[x = true]).toReal)
    ((Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W names A) false)}[x = true]).toReal)
    ((Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal)
  have t3 := abs_sub_le ((Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv1 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W names A) false)}[x = true]).toReal)
    ((Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W names A) false)}[x = true]).toReal)
    ((Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal)
  have t4 := abs_sub_le ((Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv0 nike cipher
      macS kdfS streamS geom hvalid hmactag h16 W names A) false)}[x = true]).toReal)
    ((Pr{let x ← (keyGame cipher macS kdfS streamS geom (backAdv0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W names A) true)}[x = true]).toReal)
    ((Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal)
  rw [abs_sub_comm] at h0
  rw [abs_sub_comm] at k0
  linarith

/-! ## The MAC step for world 0 -/

theorem backPlace_exit (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk)
    (hp : ch.c.pos.val = 0) :
    backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch = (RSOR.path nike
        ch.c.req.fwd [], ch.c.req.fwd.hops.length - 1) := by
  unfold backPlace
  rw [hp]

theorem backPlace_back (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS
    kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) (k : ℕ)
    (hp : ch.c.pos.val = k + 1) :
    backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch = (RSOR.path nike
        ch.c.req.back [], k) := by
  unfold backPlace
  rw [hp]

/-- The bytes that the tag of hop `j` of the honest relay's path covers: of the adversary's
onion at the exit, of the reply's packet on the backward path. -/
def backMsgAt (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS kdfS streamS
    geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) (ow : RSOR.Randomness
    nike geom × (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)))
    (a : ByteArray) (ks : List HopKeys) (j : ℕ) : ByteArray :=
  match ch.c.pos.val with
  | 0 => onionMsg nike macS streamS geom ch.c.req ow.1 a ks j
  | _ + 1 => backMsg nike macS streamS geom ch.c.req ow.1 a ks j

/-- `backView0`, with the tag of hop `j` of the honest relay's path given. -/
def backViewTAt (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS kdfS
    streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) (ow :
    RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)))
    (a : ByteArray) (ks : List HopKeys) (j : ℕ) (tag : ByteArray) : Protocols.RSOR.World 𝒮 :=
  match ch.c.pos.val with
  | 0 =>
    { onion := onionOfTag nike cipher macS kdfS streamS geom 0 ch.c.req ow.1 a ks j tag
      patch := (Protocols.RSOR.BackwardChallenge.world0 ch.c ow.1).patch }
  | _ + 1 =>
    { onion := backOnionOfTag nike cipher macS kdfS streamS geom ch.c.req ow.1
        (Nat.zero_lt_of_lt ch.c.pos.isLt) a ks j tag
      patch :=
        { proc := fun (h : Role) (o : Onion geom) out =>
            if h = .sender ∧ o.1 = (backLayerOfTag nike cipher macS streamS geom
                (ch.c.req.back.hops.length - 1) ch.c.req ow.1 a ks j tag).1 then pure none
            else pure out } }

/-- **World 0 uses the replaced hop's MAC key for one tag only.** -/
theorem backView0_tag (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS kdfS
    streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) (ow :
    RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength + geom.forwardPayloadLength)))
    (a : ByteArray) (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (x : Rest)
    (km : Vector UInt8 32) (n : ℕ) (hj : j < n)
    (hjF : ch.c.pos.val = 0 → j < (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]).size)
    (hjB : ∀ k, ch.c.pos.val = k + 1 → j < (RSOR.path nike ch.c.req.back [.surbReply
        ow.1.2.2.2]).size) :
    backView0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch ow a (hopKeysWith
        nike kdfS c hops j (restKeys x km) n)
      = backViewTAt nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch ow a
          (hopKeysWith nike kdfS c hops j (restKeys x default) n) j
        (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
          (backMsgAt nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch ow a
              (hopKeysWith nike kdfS c hops j (restKeys x default) n) j))) := by
  unfold backView0 backViewTAt backMsgAt
  obtain hk | ⟨k, hk⟩ : ch.c.pos.val = 0 ∨ ∃ k, ch.c.pos.val = k + 1 := by
    cases h : ch.c.pos.val with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, rfl⟩
  · rw [hk]
    dsimp only
    rw [onionOfKeys_tag nike cipher macS kdfS streamS geom 0 ch.c.req ow.1 a c hops j x km n hj
      (hjF hk) (Nat.zero_le j)]
  · rw [hk]
    dsimp only
    rw [backOnionOfKeys_tag nike cipher macS kdfS streamS geom ch.c.req ow.1 _ a c hops j x km n
        hj (hjB k hk),
      backLayerOfKeys_tag nike cipher macS kdfS streamS geom (ch.c.req.back.hops.length - 1)
        ch.c.req ow.1 a c hops j x km n hj (hjB k hk)]

/-- The bytes of world 0 that the honest relay's tag covers. -/
def backM0 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : Rest ×
    PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A) : ByteArray :=
  backMsgAt nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys, x.2.c⟩ :
      PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
      .relay names x.2.k.1) x.2.o (groupElem nike (drawKey nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2) (drawKeys nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x default).toArray
      0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x default) (drawPos nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) x.2)

/-- World 0 from the honest relay's tag. -/
def backViewT0 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : Rest ×
    PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × (Vector UInt8 (geom.payloadTagLength +
    geom.forwardPayloadLength))) A)
    (tag : Vector UInt8 macS.tagSize) : Protocols.RSOR.World 𝒮 :=
  backViewTAt nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys, x.2.c⟩ :
      PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
      .relay names x.2.k.1) x.2.o (groupElem nike (drawKey nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2) (drawKeys nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x default).toArray
      0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x default) (drawPos nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) x.2) (Util.Bytes.ofVector tag)

/-- **The MAC step for world 0 of SLU←.** With the honest relay's keys replaced, the relay may
answer the element of its place under the challenge's header only, at the cost of a forgery
against the MAC and the chance that the bytes its tag covers do not have a header's length. -/
theorem backward0_keyGame_sub_macOnly_le (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) :
    |(Pr{let b ← (keyGame cipher macS kdfS streamS geom (backAdv0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W names A)
          false)}[b = true]).toReal
      - (Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) _ (backDraw0 nike geom)
          (backView0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A (backM0 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 W))}[b = true]).toReal|
    ≤ (Pr{let b ← (Primitives.MAC.forgeExp macS (macForge nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) _
          (backDraw0 nike geom) A (backM0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)
              (backViewT0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W)))}[b =
              true]).toReal
      + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 nike geom) A)}[¬
          (backM0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x).size = (2 +
              nike.publicKeySize + geom.routingInfoLength)]).toReal := by
  refine keyGame_false_sub_gameOnly_le nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) _ _ (backView0 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 W names) A
    (backM0 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewT0 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 W) (fun x => (backM0 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W x).size = (2 + nike.publicKeySize + geom.routingInfoLength)) (fun
        x hg => hg)
    (fun x km _ => ?_)
  have hcases : x.2.c.pos.val = 0 ∨ ∃ k, x.2.c.pos.val = k + 1 := by
    cases h : x.2.c.pos.val with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, rfl⟩
  have hlenF : 0 < x.2.c.req.fwd.hops.length := List.length_pos_iff.2 x.2.c.req.fwd_ne
  have hposB : x.2.c.pos.val < x.2.c.req.back.hops.length := x.2.c.pos.isLt
  have hjF : x.2.c.pos.val = 0 → (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2)
      < (RSOR.path nike x.2.c.req.fwd [.recipient x.2.c.req.receiver]).size := fun hp => by
    unfold drawPos
    beta_reduce
    rw [backPlace_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys,
        x.2.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x.2.k.1) hp]
    exact lt_of_lt_of_eq (Nat.sub_one_lt (Nat.ne_of_gt hlenF))
      (RSOR.path_size nike _ _).symm
  have hjB : ∀ k, x.2.c.pos.val = k + 1 → (drawPos nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) x.2)
      < (RSOR.path nike x.2.c.req.back [.surbReply x.2.o.1.2.2.2]).size := fun k hp => by
    unfold drawPos
    beta_reduce
    rw [backPlace_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys,
        x.2.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x.2.k.1) k hp]
    exact lt_of_lt_of_eq (show k < x.2.c.req.back.hops.length by omega)
      (RSOR.path_size nike _ _).symm
  have hj : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2) < (drawHops nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) x.2).size := by
    unfold drawPos drawHops
    beta_reduce
    rw [Array.size_modify]
    obtain hk | ⟨k, hk⟩ := hcases
    · rw [backPlace_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys,
        x.2.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x.2.k.1) hk]
      exact lt_of_lt_of_eq (Nat.sub_one_lt (Nat.ne_of_gt hlenF))
        (RSOR.path_size nike _ _).symm
    · rw [backPlace_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys,
        x.2.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x.2.k.1) k hk]
      exact lt_of_lt_of_eq (show k < x.2.c.req.back.hops.length by omega)
        (RSOR.path_size nike _ _).symm
  unfold drawView backViewT0 backM0
  exact backView0_tag nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys,
      x.2.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x.2.k.1) x.2.o _ (drawKey nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2) (drawHops
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2) (drawPos
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2) x.1 km _
      hj hjF hjB

/-! ## The MAC step for world 1 -/

/-- As `backMsgAt`, for world 1's draws. -/
def backMsg1At (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS kdfS
    streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) (o :
    RSOR.Randomness nike geom × W.X)
    (a : ByteArray) (ks : List HopKeys) (j : ℕ) : ByteArray :=
  match ch.c.pos.val with
  | 0 => onionMsg nike macS streamS geom ch.c.req o.1 a ks j
  | _ + 1 => backMsg nike macS streamS geom ch.c.req o.1 a ks j

/-- `backView1`, with the tag of hop `j` of the honest relay's path given. -/
def backViewT1At (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS kdfS
    streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) (o :
    RSOR.Randomness nike geom × W.X)
    (a : ByteArray) (ks : List HopKeys) (j : ℕ) (tag : ByteArray) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1With ch.c
    (match ch.c.pos.val with
      | 0 => onionOfTag nike cipher macS kdfS streamS geom 0 ch.c.req o.1 a ks j tag
      | _ + 1 => backOnionOfTag nike cipher macS kdfS streamS geom ch.c.req o.1
          (Nat.zero_lt_of_lt ch.c.pos.isLt) a ks j tag)
    (match ch.c.pos.val with
      | 0 => none
      | k + 1 => if k < ch.c.req.back.hops.length then
          some (backLayerOfTag nike cipher macS streamS geom k ch.c.req o.1 a ks j tag).1
        else none)
    (if ch.c.pos.val = 0 then
        some (onionOfTag nike cipher macS kdfS streamS geom (ch.c.req.fwd.hops.length - 1)
          ch.c.req o.1 a ks j tag).1
      else none)
    (W.of ch.c o.2).1 (W.of ch.c o.2).2

/-- **World 1 uses the replaced hop's MAC key for one tag only**, when that hop is the last of
the forward path at the exit. -/
theorem backView1_tag (names : Role → Name) {pk : RSOR.Key nike} (ch : PropCh nike cipher macS kdfS
    streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names pk) (o :
    RSOR.Randomness nike geom × W.X)
    (a : ByteArray) (c : nike.PrivateKey) (hops : Array PathHop) (j : ℕ) (x : Rest)
    (km : Vector UInt8 32) (n : ℕ) (hj : j < n)
    (hjF : ch.c.pos.val = 0 → j < (RSOR.path nike ch.c.req.fwd [.recipient ch.c.req.receiver]).size
        ∧ ch.c.req.fwd.hops.length - 1 ≤ j)
    (hjB : ∀ k, ch.c.pos.val = k + 1 → j < (RSOR.path nike ch.c.req.back [.surbReply
        o.1.2.2.2]).size) :
    backView1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o a (hopKeysWith
        nike kdfS c hops j (restKeys x km) n)
      = backViewT1At nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o a
          (hopKeysWith nike kdfS c hops j (restKeys x default) n) j
        (Util.Bytes.ofVector (macS.mac (Util.Bytes.ofVector km)
          (backMsg1At nike cipher macS kdfS streamS geom hvalid hmactag h16 W names ch o a
              (hopKeysWith nike kdfS c hops j (restKeys x default) n) j))) := by
  unfold backView1 backViewT1At backMsg1At
  obtain hk | ⟨k, hk⟩ : ch.c.pos.val = 0 ∨ ∃ k, ch.c.pos.val = k + 1 := by
    cases h : ch.c.pos.val with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, rfl⟩
  · rw [hk]
    dsimp only
    rw [onionOfKeys_tag nike cipher macS kdfS streamS geom 0 ch.c.req o.1 a c hops j x km n hj
        (hjF hk).1 (Nat.zero_le j),
      onionOfKeys_tag nike cipher macS kdfS streamS geom (ch.c.req.fwd.hops.length - 1) ch.c.req
        o.1 a c hops j x km n hj (hjF hk).1 (hjF hk).2]
  · rw [hk]
    dsimp only
    rw [ite_eq_right (Nat.succ_ne_zero k), ite_eq_right (Nat.succ_ne_zero k),
      backOnionOfKeys_tag nike cipher macS kdfS streamS geom ch.c.req o.1 _ a c hops j x km n
        hj (hjB k hk),
      backLayerOfKeys_tag nike cipher macS kdfS streamS geom k ch.c.req o.1 a c hops j x km n hj
        (hjB k hk)]

/-- The bytes of world 1 that the honest relay's tag covers. -/
def backM1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : Rest ×
    PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A) : ByteArray :=
  backMsg1At nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys, x.2.c⟩ :
      PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
      .relay names x.2.k.1) x.2.o (groupElem nike (drawKey nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2) (drawKeys nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x default).toArray
      0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x default) (drawPos nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) x.2)

/-- World 1 from the honest relay's tag. -/
def backViewT1 {names : Role → Name} {A : (Protocols.RSOR.backwardWith W).Adversary} (x : Rest ×
    PropDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
    .relay names (RSOR.Randomness nike geom × W.X) A)
    (tag : Vector UInt8 macS.tagSize) : Protocols.RSOR.World 𝒮 :=
  backViewT1At nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys, x.2.c⟩ :
      PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W)
      .relay names x.2.k.1) x.2.o (groupElem nike (drawKey nike cipher macS kdfS streamS geom
      hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2) (drawKeys nike cipher
      macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names
      (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x default).toArray
      0) (drawKeys nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x default) (drawPos nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) x.2) (Util.Bytes.ofVector tag)

/-- **The MAC step for world 1 of SLU←**, as for world 0. -/
theorem backward1_keyGame_sub_macOnly_le (names : Role → Name) (A : (Protocols.RSOR.backwardWith
    W).Adversary) :
    |(Pr{let b ← (keyGame cipher macS kdfS streamS geom (backAdv1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W names A)
          false)}[b = true]).toReal
      - (Pr{let b ← (macOnly nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) _ (swapDraw nike cipher macS kdfS streamS geom hvalid
          hmactag h16 W)
          (backView1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) A (backM1 nike
              cipher macS kdfS streamS geom hvalid hmactag h16 W))}[b = true]).toReal|
    ≤ (Pr{let b ← (Primitives.MAC.forgeExp macS (macForge nike cipher macS kdfS streamS geom hvalid
        hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
        streamS geom hvalid hmactag h16 W names) _
          (swapDraw nike cipher macS kdfS streamS geom hvalid hmactag h16 W) A (backM1 nike cipher
              macS kdfS streamS geom hvalid hmactag h16 W) (backViewT1 nike cipher macS kdfS
              streamS geom hvalid hmactag h16 W)))}[b = true]).toReal
      + (Pr{let x ← (macDraw nike cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names _ (swapDraw nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W) A)}[¬
          (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W x).size = (2 +
              nike.publicKeySize + geom.routingInfoLength)]).toReal := by
  refine keyGame_false_sub_gameOnly_le nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) _ _ (backView1 nike cipher macS kdfS streamS geom hvalid hmactag
      h16 W names) A
    (backM1 nike cipher macS kdfS streamS geom hvalid hmactag h16 W) (backViewT1 nike cipher macS
        kdfS streamS geom hvalid hmactag h16 W) (fun x => (backM1 nike cipher macS kdfS streamS
        geom hvalid hmactag h16 W x).size = (2 + nike.publicKeySize + geom.routingInfoLength)) (fun
        x hg => hg)
    (fun x km _ => ?_)
  have hcases : x.2.c.pos.val = 0 ∨ ∃ k, x.2.c.pos.val = k + 1 := by
    cases h : x.2.c.pos.val with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, rfl⟩
  have hlenF : 0 < x.2.c.req.fwd.hops.length := List.length_pos_iff.2 x.2.c.req.fwd_ne
  have hposB : x.2.c.pos.val < x.2.c.req.back.hops.length := x.2.c.pos.isLt
  have hjF : x.2.c.pos.val = 0 → (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2)
        < (RSOR.path nike x.2.c.req.fwd [.recipient x.2.c.req.receiver]).size
      ∧ x.2.c.req.fwd.hops.length - 1 ≤ (drawPos nike cipher macS kdfS streamS geom hvalid hmactag
          h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS
          geom hvalid hmactag h16 W names) x.2) := fun hp => by
    unfold drawPos
    beta_reduce
    rw [backPlace_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys,
        x.2.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x.2.k.1) hp]
    exact ⟨lt_of_lt_of_eq (Nat.sub_one_lt (Nat.ne_of_gt hlenF)) (RSOR.path_size nike _ _).symm,
      le_rfl⟩
  have hjB : ∀ k, x.2.c.pos.val = k + 1 → (drawPos nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) x.2)
      < (RSOR.path nike x.2.c.req.back [.surbReply x.2.o.1.2.2.2]).size := fun k hp => by
    unfold drawPos
    beta_reduce
    rw [backPlace_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys,
        x.2.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x.2.k.1) k hp]
    exact lt_of_lt_of_eq (show k < x.2.c.req.back.hops.length by omega)
      (RSOR.path_size nike _ _).symm
  have hj : (drawPos nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS streamS geom
      hvalid hmactag h16 W names) x.2) < (drawHops nike cipher macS kdfS streamS geom hvalid
      hmactag h16 (Protocols.RSOR.backwardWith W) .relay names (backPlace nike cipher macS kdfS
      streamS geom hvalid hmactag h16 W names) x.2).size := by
    unfold drawPos drawHops
    beta_reduce
    rw [Array.size_modify]
    obtain hk | ⟨k, hk⟩ := hcases
    · rw [backPlace_exit nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys,
        x.2.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x.2.k.1) hk]
      exact lt_of_lt_of_eq (Nat.sub_one_lt (Nat.ne_of_gt hlenF)) (RSOR.path_size nike _ _).symm
    · rw [backPlace_back nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys,
        x.2.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names x.2.k.1) k hk]
      exact lt_of_lt_of_eq (show k < x.2.c.req.back.hops.length by omega)
        (RSOR.path_size nike _ _).symm
  unfold drawView backViewT1 backM1
  exact backView1_tag nike cipher macS kdfS streamS geom hvalid hmactag h16 W names (⟨x.2.keys,
      x.2.c⟩ : PropCh nike cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardWith W) .relay names x.2.k.1) x.2.o _ (drawKey nike cipher macS kdfS
      streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay names x.2) (drawHops
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2) (drawPos
      nike cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardWith W) .relay
      names (backPlace nike cipher macS kdfS streamS geom hvalid hmactag h16 W names) x.2) x.1 km _
      hj hjF hjB

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
