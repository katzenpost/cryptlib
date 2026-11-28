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

end Final

end Cryptlib.Protocols.Sphinx.NIKESphinx
