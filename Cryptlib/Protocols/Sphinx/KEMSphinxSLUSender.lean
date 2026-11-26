/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxSLU

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open OracleComp OracleSpec ENNReal
open Cryptlib.Protocols.Sphinx.Constants
open Cryptlib.Protocols.Sphinx.Geometry (Geometry)
open Cryptlib.Protocols.Sphinx.Commands
open Cryptlib.Protocols.Sphinx.Types
open Cryptlib.Protocols.Sphinx.Common
open Cryptlib.Protocols.Sphinx.NIKESphinx (HopKeys deriveHopKeys)
open Cryptlib.Primitives.WideBlockCipher (WideBlockCipher)
open Cryptlib.Primitives.MAC (MAC)
open Cryptlib.Primitives.KDF (KDF)
open Cryptlib.Primitives.StreamCipher (StreamCipher)
open Cryptlib.Primitives.KEM.KEM (KEM)
open Cryptlib.Protocols.Sphinx.KEMSphinx.RSOR (Key keygen)
open Cryptlib.Util.Bytes (ofVector)

/-! # SLU← for KEM Sphinx: the onion the relay sends on

In world 1 of SLU← the honest relay sends on the first layer of a fresh forward onion along the
rest of the backward path. Here that onion is told apart from one built like a reply layer: a
header over the same path, with a uniform payload (`replySwap`). The two differ in their last
layer only, which is the sender's. So the game is written around the sender's ciphertext. -/

section SwapGame

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

/-- An onion built like a reply layer: the header of a packet over the rest of the backward
path that ends in a reply, and a uniform payload. With it goes the header of the packet's last
layer. -/
def replySwap :
    Protocols.RSOR.BackSwap (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16) where
  X := RSOR.Randomness geom × Block geom
  draw := do
    let r' ← $ᵗ (RSOR.Randomness geom)
    let b ← $ᵗ (Block geom)
    return (r', b)
  of c x :=
    (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (c.req.back.drop c.pos)
        [.surbReply x.1.2.2.2])
        x.1.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0 with
      | .ok pkt => ((RSOR.split geom pkt).1, x.2)
      | .error _ => (default : RSOR.Onion geom),
    match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (c.req.back.drop c.pos)
        [.surbReply x.1.2.2.2])
        x.1.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ ((c.req.back.drop c.pos).hops.length -
            1) with
      | .ok pkt => (RSOR.split geom pkt).1
      | .error _ => (default : RSOR.Onion geom).1)

/-! ## The fresh forward onion around the sender's ciphertext -/

/-- World 1 with the fresh forward onion sent on, with the seed `s` at that onion's last layer,
the sender's. -/
def swapFreshWorld {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.BackwardChallenge hon) (o : (RSOR.Randomness geom × RSOR.Msg geom ×
        RSOR.Name × RSOR.Randomness geom)) (s : Vector UInt8 32) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1Of Protocols.RSOR.freshSwap c o.1
    (o.2.1, o.2.2.1, setSeed geom o.2.2.2 ((c.req.back.drop c.pos).hops.length - 1) s)

set_option maxHeartbeats 2000000 in
/-- **World 1 with the fresh onion as its draws**, with the seed of the onion's last layer drawn
on its own, and then the adversary's guess against the honest relays. -/
theorem swap_play_true_evalDistEq (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary) :
    Protocols.RSOR.Property.play names A true
      =ᵈ propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
          (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
          hmactag h16)) .sender names _ (shortDraw geom) A >>= fun d =>
        (simulateQ (Protocols.RSOR.honest
            (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .sender names d.k.1 d.keys)
            (fun h => if h = .sender then d.k.2 else (d.keys h).2)
            (swapFreshWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 d.c d.o d.s).patch)
          (A.guess d.st (swapFreshWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 d.c d.o
              d.s).onion)).run' d.log := by
  refine (play_evalDistEq_honAt kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS
      streamS geom hvalid hmactag h16)) .sender names A true).trans ?_
  unfold Protocols.RSOR.Property.playFrom propDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
    EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => ?_
  have hcong : ∀ (m m' : ProbComp (Protocols.RSOR.World 𝒮))
      (F : Protocols.RSOR.World 𝒮 → ProbComp Bool), m = m' → m >>= F =ᵈ m' >>= F :=
    fun _ _ _ h => h ▸ EvalDistEq.rfl
  have hw : (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS
      kdfS streamS geom hvalid hmactag h16)).world out.1.1 true = (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let m ← $ᵗ (RSOR.Msg geom)
      let n ← $ᵗ RSOR.Name
      let r' ← $ᵗ (RSOR.Randomness geom)
      return Protocols.RSOR.BackwardChallenge.world1Of Protocols.RSOR.freshSwap out.1.1 r (m, n,
          r')) := by
    refine (Protocols.RSOR.backwardWith_world_true _ out.1.1).trans ?_
    simp only [Protocols.RSOR.freshSwap, bind_assoc, pure_bind]
    rfl
  refine (hcong _ _ _ hw).trans ?_
  simp only [shortDraw, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun r => EvalDistEq.bind_right _ fun m =>
    EvalDistEq.bind_right _ fun n => ?_
  exact (evalDistEq_setSeed geom ((out.1.1.req.back.drop out.1.1.pos).hops.length - 1)
    (lt_of_lt_of_le (Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2
      (out.1.1.req.back.drop_ne out.1.1.pos.isLt)))) (out.1.1.req.back.drop out.1.1.pos).length_le)
    fun r' =>
      (simulateQ (Protocols.RSOR.honest
          (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .sender names k.1 (keysOf kem
              .sender k₁ k₂))
          (fun h => if h = .sender then k.2 else (keysOf kem .sender k₁ k₂ h).2)
          (Protocols.RSOR.BackwardChallenge.world1Of Protocols.RSOR.freshSwap out.1.1 r (m, n,
              r')).patch)
        (A.guess out.1.2
          (Protocols.RSOR.BackwardChallenge.world1Of Protocols.RSOR.freshSwap out.1.1 r (m, n,
              r')).onion)).run'
            out.2).symm

/-- World 1 with the fresh onion sent on, around the sender's ciphertext and keys: the onion's
first layer and the header of its last, keyed at the last. -/
def swapFreshView (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
        (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
        hmactag h16)) .sender names pk) (o : (RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name ×
        RSOR.Randomness geom)) (c : kem.Ciphertext)
    (t : KeyTuple) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1With ch.c
    (RSOR.form kem cipher macS kdfS streamS geom ch.c.req o.1 ch.c.req.first)
    (Protocols.RSOR.BackwardChallenge.ownAt ch.c o.1) (Protocols.RSOR.BackwardChallenge.exitAt ch.c
        o.1)
    (onionK kem cipher macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1
        o.2.2.1) o.2.2.2
      ((ch.c.req.back.drop ch.c.pos).hops.length - 1) c t 0)
    (onionK kem cipher macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1
        o.2.2.1) o.2.2.2
      ((ch.c.req.back.drop ch.c.pos).hops.length - 1) c t
      ((ch.c.req.back.drop ch.c.pos).hops.length - 1)).1

/-- The keyed game of that world around the sender's ciphertext. -/
abbrev swapFreshSetup (names : Role → RSOR.Name) :
    KeyedSetup kem (Protocols.RSOR.World 𝒮) Bool :=
  propSetupOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
      (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
      hmactag h16)) .sender names _ (shortDraw geom) (swapFreshView kem cipher macS kdfS streamS
          geom
      hvalid hmactag h16 names)

/-- The adversary of that keyed game. -/
abbrev swapFreshAdv (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap
    (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary) :
    KeyedAdversary (swapFreshSetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names) :=
  propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
      (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
      hmactag h16)) .sender names _ _ _ A

/-- The last relay of the rest of the backward path is the sender. -/
theorem dropLast_key (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
        (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
        hmactag h16)) .sender names pk)
    (hj : (ch.c.req.back.drop ch.c.pos).hops.length - 1
      < (ch.c.req.back.drop ch.c.pos).hops.length) :
    ((ch.c.req.back.drop ch.c.pos).hops[(ch.c.req.back.drop ch.c.pos).hops.length - 1]'hj).key
      = pk := by
  have hlast : (ch.c.req.back.drop ch.c.pos).hops.getLast?
      = some (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .sender names pk ch.keys
          .sender) := by
    show (ch.c.req.back.hops.drop ch.c.pos).getLast? = _
    rw [List.getLast?_drop, ite_eq_right (not_le.2 ch.c.pos.isLt)]
    exact ch.c.sender
  rw [Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans
    (List.getLast?_eq_getElem?.symm.trans hlast))]
  rfl

set_option maxHeartbeats 1000000 in
/-- **With the real keys, the keyed world is the world with the fresh onion.** -/
theorem swapFreshView_real (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
        (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
        hmactag h16)) .sender names pk) (o : (RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name ×
        RSOR.Randomness geom)) (s : Vector UInt8 32)
    (c : kem.Ciphertext) (ss pkt pktL : ByteArray)
    (henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s
      = .ok (ofVector (kem.encodeCiphertext c), ss))
    (hpkt : RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).fwd
              [.recipient (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).receiver])
          (setSeed geom o.2.2.2 ((ch.c.req.back.drop ch.c.pos).hops.length - 1) s).1
          (RSOR.body kem macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq ch.c
              o.2.1 o.2.2.1) (setSeed geom o.2.2.2 ((ch.c.req.back.drop ch.c.pos).hops.length - 1)
              s)) 0 = .ok pkt)
    (hpktL : RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).fwd
              [.recipient (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).receiver])
          (setSeed geom o.2.2.2 ((ch.c.req.back.drop ch.c.pos).hops.length - 1) s).1
          (RSOR.body kem macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq ch.c
              o.2.1 o.2.2.1) (setSeed geom o.2.2.2 ((ch.c.req.back.drop ch.c.pos).hops.length - 1)
              s)) ((ch.c.req.back.drop ch.c.pos).hops.length - 1) = .ok pktL) :
    swapFreshView kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c (keyTuple
        (deriveHopKeys kdfS ss))
      = swapFreshWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 ch.c o s := by
  have hj : (ch.c.req.back.drop ch.c.pos).hops.length - 1
      < (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).fwd.hops.length :=
    Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2
      (ch.c.req.back.drop_ne ch.c.pos.isLt)))
  have hkey := dropLast_key kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch hj
  have honion := onionK_real kem cipher macS kdfS streamS geom
      (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1) o.2.2.2
    ⟨(ch.c.req.back.drop ch.c.pos).hops.length - 1, hj⟩
    (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).first (Nat.zero_le _) pk hkey s c
        ss pkt henc hpkt
  have hlastL := onionK_real kem cipher macS kdfS streamS geom
      (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1) o.2.2.2
    ⟨(ch.c.req.back.drop ch.c.pos).hops.length - 1, hj⟩
    (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).last le_rfl pk hkey s c ss pktL
        henc hpktL
  unfold swapFreshView swapFreshWorld Protocols.RSOR.BackwardChallenge.world1Of
      Protocols.RSOR.freshSwap
  exact congrArg₂ (fun (on : RSOR.Onion geom) (ex : Vector UInt8 geom.headerLength) =>
    Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) ch.c
      (RSOR.form kem cipher macS kdfS streamS geom ch.c.req o.1 ch.c.req.first)
      (Protocols.RSOR.BackwardChallenge.ownAt ch.c o.1) (Protocols.RSOR.BackwardChallenge.exitAt
          ch.c o.1) on ex)
    honion (congrArg Prod.fst hlastL)

/-- The draws that the exact steps do not cover: the sender's public key is not the one its
private key gives, its seed may make the KEM fail, or the fresh onion's first or last layer
cannot be built. -/
def swapFreshBad {names : Role → RSOR.Name} {A : (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap
    (S
    := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary}
    (d : PropDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
        (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
        hmactag h16)) .sender names (RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name ×
        RSOR.Randomness geom) A) : Prop :=
  ¬ (d.k.1.1 = kem.derivePublicKey d.k.2 ∧ kem.Reliable (kem.stateFromSeed d.s) ∧
    ∃ pkt pktL, RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem (Protocols.RSOR.BackwardChallenge.swapReq d.c d.o.2.1 d.o.2.2.1).fwd
              [.recipient (Protocols.RSOR.BackwardChallenge.swapReq d.c d.o.2.1
              d.o.2.2.1).receiver])
          (setSeed geom d.o.2.2.2 ((d.c.req.back.drop d.c.pos).hops.length - 1) d.s).1
          (RSOR.body kem macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq d.c
              d.o.2.1 d.o.2.2.1) (setSeed geom d.o.2.2.2 ((d.c.req.back.drop d.c.pos).hops.length -
              1) d.s)) 0 = .ok pkt
      ∧ RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem (Protocols.RSOR.BackwardChallenge.swapReq d.c d.o.2.1 d.o.2.2.1).fwd
              [.recipient (Protocols.RSOR.BackwardChallenge.swapReq d.c d.o.2.1
              d.o.2.2.1).receiver])
          (setSeed geom d.o.2.2.2 ((d.c.req.back.drop d.c.pos).hops.length - 1) d.s).1
          (RSOR.body kem macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq d.c
              d.o.2.1 d.o.2.2.1) (setSeed geom d.o.2.2.2 ((d.c.req.back.drop d.c.pos).hops.length -
              1) d.s)) ((d.c.req.back.drop d.c.pos).hops.length - 1) = .ok pktL)

/-! ## The onion built like a reply layer, around the sender's ciphertext -/

/-- What the challenger draws in world 1′: its randomness, the randomness of the header sent
on, and the payload sent on. -/
def replyDraw : ProbComp (RSOR.Randomness geom × RSOR.Randomness geom × Block geom) := do
  let r ← $ᵗ (RSOR.Randomness geom)
  let r' ← $ᵗ (RSOR.Randomness geom)
  let b ← $ᵗ (Block geom)
  return (r, r', b)

/-- World 1′, with the seed `s` at the last layer of the header sent on, the sender's. -/
def swapReplyWorld {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.BackwardChallenge hon) (o : (RSOR.Randomness geom × RSOR.Randomness geom ×
        Block geom)) (s : Vector UInt8 32) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1Of (replySwap kem cipher macS kdfS streamS geom hvalid
      hmactag h16) c o.1
    (setSeed geom o.2.1 ((c.req.back.drop c.pos).hops.length - 1) s, o.2.2)

set_option maxHeartbeats 2000000 in
/-- **World 1′ as its draws**, with the seed of the last layer of the header sent on drawn on
its own, and then the adversary's guess against the honest relays. -/
theorem swap_play_false_evalDistEq (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary) :
    Protocols.RSOR.Property.play names A false
      =ᵈ propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
          (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
          hmactag h16)) .sender names _ (replyDraw geom) A >>= fun d =>
        (simulateQ (Protocols.RSOR.honest
            (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .sender names d.k.1 d.keys)
            (fun h => if h = .sender then d.k.2 else (d.keys h).2)
            (swapReplyWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 d.c d.o d.s).patch)
          (A.guess d.st (swapReplyWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 d.c
              d.o d.s).onion)).run' d.log := by
  refine (play_evalDistEq_honAt kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS
      streamS geom hvalid hmactag h16)) .sender names A false).trans ?_
  unfold Protocols.RSOR.Property.playFrom propDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
    EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => ?_
  have hcong : ∀ (m m' : ProbComp (Protocols.RSOR.World 𝒮))
      (F : Protocols.RSOR.World 𝒮 → ProbComp Bool), m = m' → m >>= F =ᵈ m' >>= F :=
    fun _ _ _ h => h ▸ EvalDistEq.rfl
  have hw : (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS
      kdfS streamS geom hvalid hmactag h16)).world out.1.1 false = (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let r' ← $ᵗ (RSOR.Randomness geom)
      let b ← $ᵗ (Block geom)
      return Protocols.RSOR.BackwardChallenge.world1Of (replySwap kem cipher macS kdfS streamS geom
          hvalid hmactag h16) out.1.1 r (r', b)) := by
    refine (Protocols.RSOR.backwardWith_world_true _ out.1.1).trans ?_
    simp only [replySwap, bind_assoc, pure_bind]
    rfl
  refine (hcong _ _ _ hw).trans ?_
  simp only [replyDraw, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun r => ?_
  refine EvalDistEq.symm ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact evalDistEq_setSeed geom ((out.1.1.req.back.drop out.1.1.pos).hops.length - 1)
    (lt_of_lt_of_le (Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2
      (out.1.1.req.back.drop_ne out.1.1.pos.isLt)))) (out.1.1.req.back.drop out.1.1.pos).length_le)
    fun r' => $ᵗ (Block geom) >>= fun b =>
      (simulateQ (Protocols.RSOR.honest
          (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .sender names k.1 (keysOf kem
              .sender k₁ k₂))
          (fun h => if h = .sender then k.2 else (keysOf kem .sender k₁ k₂ h).2)
          (Protocols.RSOR.BackwardChallenge.world1Of (replySwap kem cipher macS kdfS streamS geom
              hvalid hmactag h16) out.1.1 r (r', b)).patch)
        (A.guess out.1.2
          (Protocols.RSOR.BackwardChallenge.world1Of (replySwap kem cipher macS kdfS streamS geom
              hvalid hmactag h16) out.1.1 r (r', b)).onion)).run' out.2

/-- World 1′ around the sender's ciphertext and keys: the header sent on and the header of its
last layer, keyed at the last. -/
def swapReplyView (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
        (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
        hmactag h16)) .sender names pk) (o : (RSOR.Randomness geom × RSOR.Randomness geom × Block
        geom)) (c : kem.Ciphertext)
    (t : KeyTuple) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1With ch.c
    (RSOR.form kem cipher macS kdfS streamS geom ch.c.req o.1 ch.c.req.first)
    (Protocols.RSOR.BackwardChallenge.ownAt ch.c o.1) (Protocols.RSOR.BackwardChallenge.exitAt ch.c
        o.1)
    (headerF kem macS kdfS streamS geom (RSOR.path kem (ch.c.req.back.drop ch.c.pos) [.surbReply
        o.2.1.2.2.2]) o.2.1.1 ((ch.c.req.back.drop ch.c.pos).hops.length - 1) (ofVector
        (kem.encodeCiphertext c))
      (ksOf streamS geom t) (tagOf macS t) 0, o.2.2)
    (headerF kem macS kdfS streamS geom (RSOR.path kem (ch.c.req.back.drop ch.c.pos) [.surbReply
        o.2.1.2.2.2]) o.2.1.1 ((ch.c.req.back.drop ch.c.pos).hops.length - 1) (ofVector
        (kem.encodeCiphertext c))
      (ksOf streamS geom t) (tagOf macS t) ((ch.c.req.back.drop ch.c.pos).hops.length - 1))

/-- The keyed game of world 1′ around the sender's ciphertext. -/
abbrev swapReplySetup (names : Role → RSOR.Name) :
    KeyedSetup kem (Protocols.RSOR.World 𝒮) Bool :=
  propSetupOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
      (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
      hmactag h16)) .sender names _ (replyDraw geom) (swapReplyView kem cipher macS kdfS streamS
      geom hvalid hmactag h16 names)

/-- The adversary of that keyed game. -/
abbrev swapReplyAdv (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary) :
    KeyedAdversary (swapReplySetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names) :=
  propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
      (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
      hmactag h16)) .sender names _ _ _ A

set_option maxHeartbeats 1000000 in
/-- **With the real keys, the keyed world is world 1′.** -/
theorem swapReplyView_real (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
        (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
        hmactag h16)) .sender names pk) (o : (RSOR.Randomness geom × RSOR.Randomness geom × Block
        geom)) (s : Vector UInt8 32)
    (c : kem.Ciphertext) (ss pkt pktL : ByteArray)
    (henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s
      = .ok (ofVector (kem.encodeCiphertext c), ss))
    (hpkt : RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem (ch.c.req.back.drop ch.c.pos) [.surbReply o.2.1.2.2.2])
          (setSeed geom o.2.1 ((ch.c.req.back.drop ch.c.pos).hops.length - 1) s).1 ⟨Array.replicate
              geom.forwardPayloadLength 0⟩ 0 = .ok pkt)
    (hpktL : RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem (ch.c.req.back.drop ch.c.pos) [.surbReply o.2.1.2.2.2])
          (setSeed geom o.2.1 ((ch.c.req.back.drop ch.c.pos).hops.length - 1) s).1 ⟨Array.replicate
              geom.forwardPayloadLength 0⟩ ((ch.c.req.back.drop ch.c.pos).hops.length - 1) = .ok
              pktL) :
    swapReplyView kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c (keyTuple
        (deriveHopKeys kdfS ss))
      = swapReplyWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 ch.c o s := by
  have hj : ((ch.c.req.back.drop ch.c.pos).hops.length - 1) < (ch.c.req.back.drop
      ch.c.pos).hops.length :=
    Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2
      (ch.c.req.back.drop_ne ch.c.pos.isLt)))
  have hkey := dropLast_key kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch hj
  have hpub : ((RSOR.path kem (ch.c.req.back.drop ch.c.pos) [.surbReply
      o.2.1.2.2.2])[((ch.c.req.back.drop ch.c.pos).hops.length - 1)]!).publicKey = ofVector
      (kem.encodePublicKey pk.1) := by
    rw [RSOR.path_getElem! kem _ _ _ hj]
    exact congrArg (fun key : Key kem => ofVector (kem.encodePublicKey key.1)) hkey
  have henc' : kemEncap kem ((RSOR.path kem (ch.c.req.back.drop ch.c.pos) [.surbReply
      o.2.1.2.2.2])[((ch.c.req.back.drop ch.c.pos).hops.length - 1)]!).publicKey s
      = .ok (ofVector (kem.encodeCiphertext c), ss) := by
    rw [hpub]
    exact henc
  have h0 := headerF_real kem cipher macS kdfS streamS geom hvalid hmactag (RSOR.path kem
      (ch.c.req.back.drop ch.c.pos) [.surbReply o.2.1.2.2.2]) o.2.1.1 ((ch.c.req.back.drop
      ch.c.pos).hops.length - 1) 0 (Nat.zero_le _)
    (lt_of_lt_of_eq hj (RSOR.path_size kem (ch.c.req.back.drop ch.c.pos) _).symm)
    (le_of_eq_of_le (RSOR.path_size kem (ch.c.req.back.drop ch.c.pos) _)
      (ch.c.req.back.drop ch.c.pos).length_le) s _ ss pkt henc' hpkt
  have hL := headerF_real kem cipher macS kdfS streamS geom hvalid hmactag (RSOR.path kem
      (ch.c.req.back.drop ch.c.pos) [.surbReply o.2.1.2.2.2]) o.2.1.1 ((ch.c.req.back.drop
      ch.c.pos).hops.length - 1) ((ch.c.req.back.drop ch.c.pos).hops.length - 1) le_rfl
    (lt_of_lt_of_eq hj (RSOR.path_size kem (ch.c.req.back.drop ch.c.pos) _).symm)
    (le_of_eq_of_le (RSOR.path_size kem (ch.c.req.back.drop ch.c.pos) _)
      (ch.c.req.back.drop ch.c.pos).length_le) s _ ss pktL henc'
    hpktL
  have hof : (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16).of ch.c
        (setSeed geom o.2.1 ((ch.c.req.back.drop ch.c.pos).hops.length - 1) s, o.2.2)
      = (((RSOR.split geom pkt).1, o.2.2), (RSOR.split geom pktL).1) := by
    show ((match RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem (ch.c.req.back.drop ch.c.pos) [.surbReply o.2.1.2.2.2])
          (setSeed geom o.2.1 ((ch.c.req.back.drop ch.c.pos).hops.length - 1) s).1 ⟨Array.replicate
              geom.forwardPayloadLength 0⟩ 0 with
        | .ok pkt => ((RSOR.split geom pkt).1, o.2.2)
        | .error _ => (default : RSOR.Onion geom)),
      (match RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem (ch.c.req.back.drop ch.c.pos) [.surbReply o.2.1.2.2.2])
          (setSeed geom o.2.1 ((ch.c.req.back.drop ch.c.pos).hops.length - 1) s).1 ⟨Array.replicate
              geom.forwardPayloadLength 0⟩ ((ch.c.req.back.drop ch.c.pos).hops.length - 1) with
        | .ok pkt => (RSOR.split geom pkt).1
        | .error _ => (default : RSOR.Onion geom).1)) = _
    rw [hpkt, hpktL]
  unfold swapReplyView swapReplyWorld Protocols.RSOR.BackwardChallenge.world1Of
  rw [hof, h0, hL]
  rfl

/-- The draws that the exact steps do not cover: the sender's public key is not the one its
private key gives, its seed may make the KEM fail, or the first or last layer of the header
sent on cannot be built. -/
def swapReplyBad {names : Role → RSOR.Name} {A : (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap
    (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary}
    (d : PropDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
        (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
        hmactag h16)) .sender names (RSOR.Randomness geom × RSOR.Randomness geom × Block geom) A) :
        Prop :=
  ¬ (d.k.1.1 = kem.derivePublicKey d.k.2 ∧ kem.Reliable (kem.stateFromSeed d.s) ∧
    ∃ pkt pktL, RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem (d.c.req.back.drop d.c.pos) [.surbReply d.o.2.1.2.2.2])
          (setSeed geom d.o.2.1 ((d.c.req.back.drop d.c.pos).hops.length - 1) d.s).1
              ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0 = .ok pkt
      ∧ RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem (d.c.req.back.drop d.c.pos) [.surbReply d.o.2.1.2.2.2])
          (setSeed geom d.o.2.1 ((d.c.req.back.drop d.c.pos).hops.length - 1) d.s).1
              ⟨Array.replicate geom.forwardPayloadLength 0⟩ ((d.c.req.back.drop
              d.c.pos).hops.length - 1) = .ok pktL)

variable [SampleableType kem.Plaintext]

set_option maxHeartbeats 2000000 in
/-- **World 1 with the fresh onion is the keyed game with the real keys, off the bad draws.** -/
theorem swap_true_sub_keyedReal_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A true}[x = true]).toReal
      - (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
          (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
    ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS
        kdfS streamS geom hvalid hmactag h16)) .sender names _ (shortDraw geom)
        A)}[swapFreshBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal := by
  rw [(swap_play_true_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).prEvent_eq (fun x => x = true),
    (keyedReal_propAdvOf_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS
        kdfS streamS geom hvalid hmactag h16)) .sender names _ _ _ A).prEvent_eq
      (fun x => x = true)]
  refine prEvent_bind_toReal_sub_le_of_bad _ _ _
    (swapFreshBad kem cipher macS kdfS streamS geom hvalid hmactag h16) (fun d hd => ?_) (fun x =>
        x =
        true)
  obtain ⟨hpk, hrel, pkt, pktL, hpkt, hpktL⟩ := Classical.not_not.mp hd
  have hj : (d.c.req.back.drop d.c.pos).hops.length - 1
      < (Protocols.RSOR.BackwardChallenge.swapReq d.c d.o.2.1 d.o.2.2.1).fwd.hops.length :=
    Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2
      (d.c.req.back.drop_ne d.c.pos.isLt)))
  have hle : (Protocols.RSOR.BackwardChallenge.swapReq d.c d.o.2.1 d.o.2.2.1).fwd.hops.length ≤
      geom.nrHops :=
    (Protocols.RSOR.BackwardChallenge.swapReq d.c d.o.2.1 d.o.2.2.1).fwd.length_le
  obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem cipher macS kdfS streamS geom
    (Protocols.RSOR.BackwardChallenge.swapReq d.c d.o.2.1 d.o.2.2.1).fwd _ _ _ pkt hpkt
    ((d.c.req.back.drop d.c.pos).hops.length - 1) hj
  have hkey := dropLast_key kem cipher macS kdfS streamS geom hvalid hmactag h16 names
    (pk := d.k.1) ⟨d.keys, d.c⟩ hj
  have hs : (setSeed geom d.o.2.2.2 ((d.c.req.back.drop d.c.pos).hops.length - 1) d.s).1.1.toArray[
      (d.c.req.back.drop d.c.pos).hops.length - 1]! = d.s := by
    simp [setSeed, lt_of_lt_of_le hj hle]
  rw [hs] at henc
  replace henc : kemEncap kem (ofVector (kem.encodePublicKey d.k.1.1)) d.s = .ok (ct, ss) :=
    (congrArg (fun key : Key kem => kemEncap kem (ofVector (kem.encodePublicKey key.1)) d.s)
      hkey).symm.trans henc
  obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem d.k.1.1 d.s ct ss henc
  have hdec : decapOf kem d.k.2 (encapOf kem d.k.1.1 d.s).1
      = some (encapOf kem d.k.1.1 d.s).2 := by
    have h := decapOf_encapOf kem d.k.2 d.s hrel _ _ (hpk ▸ henc)
    rwa [← hpk] at h
  have hview := swapFreshView_real kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      ⟨d.keys,
      d.c⟩ d.o d.s _ _ pkt pktL henc hpkt hpktL
  rw [propAdv_post kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
      (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
      hmactag h16)) .sender names _ _ _ A d.k d.keys _ _ hdec d.st d.log _]
  exact congrArg (fun w : Protocols.RSOR.World 𝒮 =>
    (simulateQ (Protocols.RSOR.honest
        (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .sender names d.k.1 d.keys)
        (fun h => if h = .sender then d.k.2 else (d.keys h).2) w.patch)
      (A.guess d.st w.onion)).run' d.log) hview.symm

/-- **The sender's keys in world 1 with the fresh onion may be uniform**, at the cost of a bad
draw and of replacing the keys (KEM and KDF). -/
theorem swap_true_sub_keyedIdeal_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A true}[x = true]).toReal
      - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
          (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
    ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS
        kdfS streamS geom hvalid hmactag h16)) .sender names _ (shortDraw geom)
        A)}[swapFreshBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
      + keyedCost cipher macS kdfS streamS geom (swapFreshAdv kem cipher macS kdfS streamS geom
          hvalid
          hmactag h16 names A) := by
  have h1 := swap_true_sub_keyedReal_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have h2 := keyedChain_le cipher macS kdfS streamS geom (swapFreshAdv kem cipher macS kdfS streamS
      geom hvalid hmactag h16 names A)
  have t := abs_sub_le
    (Pr{let x ← Protocols.RSOR.Property.play names A true}[x = true]).toReal
    (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
      (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
          true]).toReal
    (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
      (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
          true]).toReal
  linarith

set_option maxHeartbeats 2000000 in
/-- **World 1′ is the keyed game with the real keys, off the bad draws.** -/
theorem swap_false_sub_keyedReal_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
      - (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
          (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
    ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS
        kdfS streamS geom hvalid hmactag h16)) .sender names _ (replyDraw geom)
        A)}[swapReplyBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal := by
  rw [(swap_play_false_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).prEvent_eq (fun x => x = true),
    (keyedReal_propAdvOf_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS
        kdfS streamS geom hvalid hmactag h16)) .sender names _ _ _ A).prEvent_eq
      (fun x => x = true)]
  refine prEvent_bind_toReal_sub_le_of_bad _ _ _
    (swapReplyBad kem cipher macS kdfS streamS geom hvalid hmactag h16) (fun d hd => ?_) (fun x =>
        x = true)
  obtain ⟨hpk, hrel, pkt, pktL, hpkt, hpktL⟩ := Classical.not_not.mp hd
  have hj : ((d.c.req.back.drop d.c.pos).hops.length - 1) < (d.c.req.back.drop d.c.pos).hops.length
      :=
    Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2
      (d.c.req.back.drop_ne d.c.pos.isLt)))
  have hle : (d.c.req.back.drop d.c.pos).hops.length ≤ geom.nrHops :=
    (d.c.req.back.drop d.c.pos).length_le
  obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem cipher macS kdfS streamS geom (d.c.req.back.drop
      d.c.pos) _ _ _ pkt hpkt
    ((d.c.req.back.drop d.c.pos).hops.length - 1) hj
  have hkey := dropLast_key kem cipher macS kdfS streamS geom hvalid hmactag h16 names (pk :=
      d.k.1) ⟨d.keys, d.c⟩ hj
  have hs : (setSeed geom d.o.2.1 ((d.c.req.back.drop d.c.pos).hops.length - 1)
      d.s).1.1.toArray[((d.c.req.back.drop d.c.pos).hops.length - 1)]! = d.s := by
    simp [setSeed, lt_of_lt_of_le hj hle]
  rw [hs] at henc
  replace henc : kemEncap kem (ofVector (kem.encodePublicKey d.k.1.1)) d.s = .ok (ct, ss) :=
    (congrArg (fun key : Key kem => kemEncap kem (ofVector (kem.encodePublicKey key.1)) d.s)
      hkey).symm.trans henc
  obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem d.k.1.1 d.s ct ss henc
  have hdec : decapOf kem d.k.2 (encapOf kem d.k.1.1 d.s).1
      = some (encapOf kem d.k.1.1 d.s).2 := by
    have h := decapOf_encapOf kem d.k.2 d.s hrel _ _ (hpk ▸ henc)
    rwa [← hpk] at h
  have hview := swapReplyView_real kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      ⟨d.keys, d.c⟩ d.o d.s _ _ pkt pktL henc hpkt
    hpktL
  rw [propAdv_post kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
      (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
      hmactag h16)) .sender names _ _ _ A d.k d.keys _ _ hdec d.st d.log _]
  exact congrArg (fun w : Protocols.RSOR.World 𝒮 =>
    (simulateQ (Protocols.RSOR.honest
        (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .sender names d.k.1 d.keys)
        (fun h => if h = .sender then d.k.2 else (d.keys h).2) w.patch)
      (A.guess d.st w.onion)).run' d.log) hview.symm

/-- **The sender's keys in world 1′ may be uniform**, at the cost of a bad draw and of
replacing the keys (KEM and KDF). -/
theorem swap_false_sub_keyedIdeal_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
      - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
          (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
    ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS
        kdfS streamS geom hvalid hmactag h16)) .sender names _ (replyDraw geom)
        A)}[swapReplyBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
      + keyedCost cipher macS kdfS streamS geom (swapReplyAdv kem cipher macS kdfS streamS geom
          hvalid hmactag h16 names A) := by
  have h1 := swap_false_sub_keyedReal_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      A
  have h2 := keyedChain_le cipher macS kdfS streamS geom (swapReplyAdv kem cipher macS kdfS streamS
      geom hvalid hmactag h16 names A)
  have t := abs_sub_le
    (Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
    (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
      (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
          true]).toReal
    (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
      (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
          true]).toReal
  linarith

/-! ## The MAC step at the sender -/

/-- The bytes of the fresh onion's last layer which the sender's MAC covers, from the sender's
keys other than its MAC key. -/
def swapFreshM (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
        (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
        hmactag h16)) .sender names pk) (o : (RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name ×
        RSOR.Randomness geom)) (c : kem.Ciphertext)
    (rest : RestKeys) : ByteArray :=
  relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem
      (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).fwd [.recipient
      (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).receiver]) o.2.2.2.1 (RSOR.body
      kem macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1)
      o.2.2.2) ((ch.c.req.back.drop ch.c.pos).hops.length - 1) (ofVector (kem.encodeCiphertext c))
      (ksOf streamS geom (withMAC rest default))

/-- World 1 with the fresh onion, from the tag of those bytes. -/
def swapFreshViewT (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
        (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
        hmactag h16)) .sender names pk) (o : (RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name ×
        RSOR.Randomness geom)) (c : kem.Ciphertext)
    (rest : RestKeys) (tag : Vector UInt8 macS.tagSize) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1With ch.c
    (RSOR.form kem cipher macS kdfS streamS geom ch.c.req o.1 ch.c.req.first)
    (Protocols.RSOR.BackwardChallenge.ownAt ch.c o.1) (Protocols.RSOR.BackwardChallenge.exitAt ch.c
        o.1)
    (RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom (RSOR.path kem
        (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).fwd [.recipient
        (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).receiver]) o.2.2.2.1 0
        ((ch.c.req.back.drop ch.c.pos).hops.length - 1)
      (swapFreshM kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c rest
        ++ ofVector tag
        ++ relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem
            (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).fwd [.recipient
            (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).receiver]) o.2.2.2.1
            (RSOR.body kem macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq ch.c
            o.2.1 o.2.2.1) o.2.2.2) ((ch.c.req.back.drop ch.c.pos).hops.length - 1) (ksOf streamS
            geom (withMAC rest default)) (encOf cipher (withMAC rest default)))))
    (RSOR.split geom
      (swapFreshM kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c rest
        ++ ofVector tag
        ++ relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem
            (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).fwd [.recipient
            (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).receiver]) o.2.2.2.1
            (RSOR.body kem macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq ch.c
            o.2.1 o.2.2.1) o.2.2.2) ((ch.c.req.back.drop ch.c.pos).hops.length - 1) (ksOf streamS
            geom (withMAC rest default)) (encOf cipher (withMAC rest default)))).1

/-- The draws of the fresh onion's keyed game on which the onion is as the closed form says. -/
def swapFreshGood {names : Role → RSOR.Name} {A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary}
    (d : KeyedDraw (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) :
        Prop :=
  d.k.1.1 = kem.derivePublicKey d.k.2 ∧ kem.Reliable (kem.stateFromSeed d.s) ∧
    (∃ pkt, RSOR.layer kem cipher macS kdfS streamS geom
      (RSOR.path kem (Protocols.RSOR.BackwardChallenge.swapReq (propChOf d).c (propOthOf d).2.1
          (propOthOf d).2.2.1).fwd [.recipient (Protocols.RSOR.BackwardChallenge.swapReq (propChOf
          d).c (propOthOf d).2.1 (propOthOf d).2.2.1).receiver])
      (setSeed geom (propOthOf d).2.2.2 (((propChOf d).c.req.back.drop (propChOf
          d).c.pos).hops.length
          - 1) d.s).1
      (RSOR.body kem macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq (propChOf
          d).c (propOthOf d).2.1 (propOthOf d).2.2.1)
        (setSeed geom (propOthOf d).2.2.2 (((propChOf d).c.req.back.drop (propChOf
            d).c.pos).hops.length - 1) d.s)) 0 = .ok pkt) ∧
    ∀ m, m < (((propChOf d).c.req.back.drop (propChOf d).c.pos).hops.length - 1) →
      kem.Reliable (kem.stateFromSeed (propOthOf d).2.2.2.1.1.toArray[m]!)

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- On a good draw, the fresh onion's view uses the sender's MAC key for one tag, on bytes of
the length of a header without its tag. -/
theorem swapFreshGood_view (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary)
    (d : KeyedDraw (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) (u
        : KeyTuple)
    (hg : swapFreshGood kem cipher macS kdfS streamS geom hvalid hmactag h16 d) :
    (swapFreshSetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names).view d.cs.1 d.o d.c
        u
        = swapFreshViewT kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
            (propOthOf d) d.c (restOf u)
          (macS.mac (ofVector u.2.2.1)
            (swapFreshM kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
                (propOthOf d) d.c (restOf u))) ∧
      (swapFreshM kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
          (propOthOf d) d.c (restOf u)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength := by
  obtain ⟨hpk, hrel, ⟨pkt, hpkt⟩, hfront⟩ := hg
  obtain ⟨ch, hch⟩ : ∃ ch, ch = propChOf d := ⟨_, rfl⟩
  obtain ⟨o, ho⟩ : ∃ o, o = propOthOf d := ⟨_, rfl⟩
  rw [← hch, ← ho] at hpkt hfront ⊢
  have hv : (swapFreshSetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names).view d.cs.1
      d.o d.c u
      = swapFreshView kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o d.c u := by
    rw [hch, ho]
    rfl
  rw [hv]
  have hj : ((ch.c.req.back.drop ch.c.pos).hops.length - 1) <
      (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).fwd.hops.length :=
    Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2
      (ch.c.req.back.drop_ne ch.c.pos.isLt)))
  have hle : (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).fwd.hops.length ≤
      geom.nrHops := (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).fwd.length_le
  obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem cipher macS kdfS streamS geom
      (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1).fwd _ _ _ pkt hpkt
      ((ch.c.req.back.drop ch.c.pos).hops.length - 1) hj
  have hkey := dropLast_key kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch hj
  have hs : (setSeed geom o.2.2.2 ((ch.c.req.back.drop ch.c.pos).hops.length - 1)
      d.s).1.1.toArray[((ch.c.req.back.drop ch.c.pos).hops.length - 1)]! = d.s := by
    simp [setSeed, lt_of_lt_of_le hj hle]
  rw [hs] at henc
  replace henc : kemEncap kem (ofVector (kem.encodePublicKey d.k.1.1)) d.s = .ok (ct, ss) :=
    (congrArg (fun key : Key kem => kemEncap kem (ofVector (kem.encodePublicKey key.1)) d.s)
      hkey).symm.trans henc
  obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem d.k.1.1 d.s ct ss henc
  obtain ⟨hz, hjj, hsize⟩ := onionK_parts kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.BackwardChallenge.swapReq ch.c o.2.1 o.2.2.1) o.2.2.2 ⟨((ch.c.req.back.drop
      ch.c.pos).hops.length - 1), hj⟩
    d.k.1 d.k.2 hkey hpk d.s hrel d.c _ pkt henc hpkt hfront u
  refine ⟨?_, hsize⟩
  unfold swapFreshView swapFreshViewT swapFreshM
  rw [show onionK kem cipher macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq ch.c
      o.2.1 o.2.2.1) o.2.2.2 ((ch.c.req.back.drop ch.c.pos).hops.length - 1) d.c u 0 = _ from hz,
    show onionK kem cipher macS kdfS streamS geom (Protocols.RSOR.BackwardChallenge.swapReq ch.c
        o.2.1 o.2.2.1) o.2.2.2 ((ch.c.req.back.drop ch.c.pos).hops.length - 1) d.c u
        ((ch.c.req.back.drop ch.c.pos).hops.length - 1) = _ from hjj]
  rfl

/-- **The MAC step for the fresh onion.** With uniform keys at the sender, the sender may
answer the challenge ciphertext under the onion's last header only, at the cost of a forgery
against the MAC and of the draws that are not good. -/
theorem swapFresh_keyedIdeal_sub_tagged_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary) :
    |(Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
        (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
            true]).toReal
      - (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom (swapFreshAdv kem cipher macS kdfS
          streamS geom hvalid hmactag h16 names A)
          (onlyHeader cipher macS streamS geom (tagged macS
            (swapFreshM kem cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[x =
                true]).toReal|
    ≤ (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
          (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A) (swapFreshM
              kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (swapFreshViewT kem cipher macS kdfS streamS geom hvalid hmactag h16 names)))}[x =
              true]).toReal
      + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
          (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[¬
              swapFreshGood kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal :=
  keyedIdeal_sub_tagged_le cipher macS kdfS streamS geom (swapFreshAdv kem cipher macS kdfS streamS
      geom hvalid hmactag h16 names A) hmactag
    (swapFreshM kem cipher macS kdfS streamS geom hvalid hmactag h16 names) (swapFreshViewT kem
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (swapFreshGood kem cipher macS kdfS
        streamS geom hvalid hmactag h16)
    (fun d r hg => (swapFreshGood_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
        d (withMAC r default) hg).2)
    (fun d u hg => (swapFreshGood_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
        d u hg).1)
    (fun _ _ _ _ _ => rfl)

/-- The bytes of the last layer of the header sent on in world 1′ which the sender's MAC
covers, from the sender's keys other than its MAC key. -/
def swapReplyM (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
        (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
        hmactag h16)) .sender names pk) (o : (RSOR.Randomness geom × RSOR.Randomness geom × Block
        geom)) (c : kem.Ciphertext)
    (rest : RestKeys) : ByteArray :=
  relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem (ch.c.req.back.drop ch.c.pos)
      [.surbReply o.2.1.2.2.2]) o.2.1.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩
      ((ch.c.req.back.drop ch.c.pos).hops.length - 1) (ofVector (kem.encodeCiphertext c)) (ksOf
      streamS geom (withMAC rest default))

/-- World 1′, from the tag of those bytes. -/
def swapReplyViewT (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.swapPair
        (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
        hmactag h16)) .sender names pk) (o : (RSOR.Randomness geom × RSOR.Randomness geom × Block
        geom)) (c : kem.Ciphertext)
    (rest : RestKeys) (tag : Vector UInt8 macS.tagSize) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1With ch.c
    (RSOR.form kem cipher macS kdfS streamS geom ch.c.req o.1 ch.c.req.first)
    (Protocols.RSOR.BackwardChallenge.ownAt ch.c o.1) (Protocols.RSOR.BackwardChallenge.exitAt ch.c
        o.1)
    ((RSOR.split geom (wrapUp kem default macS kdfS streamS geom (RSOR.path kem (ch.c.req.back.drop
        ch.c.pos) [.surbReply o.2.1.2.2.2]) o.2.1.1 0 ((ch.c.req.back.drop ch.c.pos).hops.length -
        1)
      (swapReplyM kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c rest
        ++ ofVector tag
        ++ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem (ch.c.req.back.drop
            ch.c.pos) [.surbReply o.2.1.2.2.2]) o.2.1.1 ⟨Array.replicate geom.forwardPayloadLength
            0⟩ ((ch.c.req.back.drop ch.c.pos).hops.length - 1) (ksOf streamS geom (withMAC rest
            default)) id))).1, o.2.2)
    (RSOR.split geom
      (swapReplyM kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c rest
        ++ ofVector tag
        ++ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem (ch.c.req.back.drop
            ch.c.pos) [.surbReply o.2.1.2.2.2]) o.2.1.1 ⟨Array.replicate geom.forwardPayloadLength
            0⟩ ((ch.c.req.back.drop ch.c.pos).hops.length - 1) (ksOf streamS geom (withMAC rest
            default)) id)).1

/-- The draws of world 1′'s keyed game on which the header sent on is as the closed form
says. -/
def swapReplyGood {names : Role → RSOR.Name} {A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary}
    (d : KeyedDraw (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) :
        Prop :=
  d.k.1.1 = kem.derivePublicKey d.k.2 ∧ kem.Reliable (kem.stateFromSeed d.s) ∧
    (∃ pkt, RSOR.layer kem default macS kdfS streamS geom (RSOR.path kem ((propChOf
        d).c.req.back.drop (propChOf d).c.pos) [.surbReply (propOthOf d).2.1.2.2.2])
      (setSeed geom (propOthOf d).2.1 (((propChOf d).c.req.back.drop (propChOf
          d).c.pos).hops.length - 1) d.s).1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0 = .ok
          pkt) ∧
    ∀ m, m < (((propChOf d).c.req.back.drop (propChOf d).c.pos).hops.length - 1) → kem.Reliable
        (kem.stateFromSeed (propOthOf d).2.1.1.1.toArray[m]!)

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- On a good draw, world 1′'s view uses the sender's MAC key for one tag, on bytes of the
length of a header without its tag. -/
theorem swapReplyGood_view (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary)
    (d : KeyedDraw (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) (u
        : KeyTuple)
    (hg : swapReplyGood kem cipher macS kdfS streamS geom hvalid hmactag h16 d) :
    (swapReplySetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names).view d.cs.1 d.o d.c
        u
        = swapReplyViewT kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
            (propOthOf d) d.c (restOf u)
          (macS.mac (ofVector u.2.2.1)
            (swapReplyM kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
                (propOthOf d) d.c (restOf u))) ∧
      (swapReplyM kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
          (propOthOf d) d.c (restOf u)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength := by
  obtain ⟨hpk, hrel, ⟨pkt, hpkt⟩, hfront⟩ := hg
  obtain ⟨ch, hch⟩ : ∃ ch, ch = propChOf d := ⟨_, rfl⟩
  obtain ⟨o, ho⟩ : ∃ o, o = propOthOf d := ⟨_, rfl⟩
  rw [← hch, ← ho] at hpkt hfront ⊢
  have hv : (swapReplySetup kem cipher macS kdfS streamS geom hvalid hmactag h16 names).view d.cs.1
      d.o d.c u
      = swapReplyView kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o d.c u := by
    rw [hch, ho]
    rfl
  rw [hv]
  have hj : ((ch.c.req.back.drop ch.c.pos).hops.length - 1) < (ch.c.req.back.drop
      ch.c.pos).hops.length :=
    Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2
      (ch.c.req.back.drop_ne ch.c.pos.isLt)))
  have hle : (ch.c.req.back.drop ch.c.pos).hops.length ≤ geom.nrHops :=
    (ch.c.req.back.drop ch.c.pos).length_le
  obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem default macS kdfS streamS geom (ch.c.req.back.drop
      ch.c.pos) _ _ _ pkt
    hpkt ((ch.c.req.back.drop ch.c.pos).hops.length - 1) hj
  have hkey := dropLast_key kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch hj
  have hs : (setSeed geom o.2.1 ((ch.c.req.back.drop ch.c.pos).hops.length - 1)
      d.s).1.1.toArray[((ch.c.req.back.drop ch.c.pos).hops.length - 1)]! = d.s := by
    simp [setSeed, lt_of_lt_of_le hj hle]
  rw [hs] at henc
  replace henc : kemEncap kem (ofVector (kem.encodePublicKey d.k.1.1)) d.s = .ok (ct, ss) :=
    (congrArg (fun key : Key kem => kemEncap kem (ofVector (kem.encodePublicKey key.1)) d.s)
      hkey).symm.trans henc
  obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem d.k.1.1 d.s ct ss henc
  obtain ⟨hz, hsize, hjj⟩ := routeK_parts kem default macS kdfS streamS geom hvalid hmactag h16
      (ch.c.req.back.drop ch.c.pos)
    [.surbReply o.2.1.2.2.2]
    (fun x hx => by
      rw [List.mem_singleton.1 hx]
      exact ⟨by simp, by simp⟩)
    o.2.1.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ ((ch.c.req.back.drop
        ch.c.pos).hops.length - 1) hj d.k.1 d.k.2 hkey hpk d.s hrel d.c _ pkt henc hpkt hfront u
  refine ⟨?_, hsize⟩
  unfold swapReplyView swapReplyViewT swapReplyM headerF
  rw [layerF_id, layerF_id,
    show layerPK kem default macS kdfS streamS geom (RSOR.path kem (ch.c.req.back.drop ch.c.pos)
        [.surbReply o.2.1.2.2.2]) o.2.1.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩
        ((ch.c.req.back.drop ch.c.pos).hops.length - 1)
      (ofVector (kem.encodeCiphertext d.c)) u 0 = _ from hz,
    show layerPK kem default macS kdfS streamS geom (RSOR.path kem (ch.c.req.back.drop ch.c.pos)
        [.surbReply o.2.1.2.2.2]) o.2.1.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩
        ((ch.c.req.back.drop ch.c.pos).hops.length - 1)
      (ofVector (kem.encodeCiphertext d.c)) u ((ch.c.req.back.drop ch.c.pos).hops.length - 1) = _
          from hjj]
  rfl

/-- **The MAC step for world 1′.** -/
theorem swapReply_keyedIdeal_sub_tagged_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary) :
    |(Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
        (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
            true]).toReal
      - (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom (swapReplyAdv kem cipher macS kdfS
          streamS geom hvalid hmactag h16 names A)
          (onlyHeader cipher macS streamS geom (tagged macS
            (swapReplyM kem cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[x =
                true]).toReal|
    ≤ (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
          (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A) (swapReplyM
              kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (swapReplyViewT kem cipher macS kdfS streamS geom hvalid hmactag h16 names)))}[x =
              true]).toReal
      + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
          (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[¬
              swapReplyGood kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal :=
  keyedIdeal_sub_tagged_le cipher macS kdfS streamS geom (swapReplyAdv kem cipher macS kdfS streamS
      geom hvalid hmactag h16 names A) hmactag
    (swapReplyM kem cipher macS kdfS streamS geom hvalid hmactag h16 names) (swapReplyViewT kem
        cipher macS kdfS streamS geom hvalid hmactag h16 names) (swapReplyGood kem cipher macS kdfS
        streamS geom hvalid hmactag h16)
    (fun d r hg => (swapReplyGood_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
        d (withMAC r default) hg).2)
    (fun d u hg => (swapReplyGood_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
        d u hg).1)
    (fun _ _ _ _ _ => rfl)

/-- **Telling the two onions apart, with uniform keys at the sender.** The advantage is at most
the chance of a bad draw with each onion, the cost of replacing the sender's keys with each (KEM
and KDF), and the distance between the two keyed games with uniform keys. -/
theorem swapPair_le_keyedIdeal (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid hmactag
    h16)).Adversary) :
    ((Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS
        streamS geom hvalid hmactag h16)).advantage names A).toReal
      ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS
          kdfS streamS geom hvalid hmactag h16)) .sender names _ (shortDraw geom)
          A)}[swapFreshBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS
            kdfS streamS geom hvalid hmactag h16)) .sender names _ (replyDraw geom)
          A)}[swapReplyBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + keyedCost cipher macS kdfS streamS geom (swapFreshAdv kem cipher macS kdfS streamS geom
            hvalid hmactag h16 names A)
        + keyedCost cipher macS kdfS streamS geom (swapReplyAdv kem cipher macS kdfS streamS geom
            hvalid hmactag h16 names A)
        + |(Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
            (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
                true]).toReal
          - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
            (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
                true]).toReal| := by
  refine (Protocols.RSOR.Property.advantage_toReal (P := (Protocols.RSOR.swapPair
      (Protocols.RSOR.freshSwap (S := 𝒮)) (replySwap kem cipher macS kdfS streamS geom hvalid
      hmactag h16))) names A).le.trans ?_
  obtain ⟨a, a'⟩ := abs_le.1 (swap_true_sub_keyedIdeal_le kem cipher macS kdfS streamS geom hvalid
      hmactag h16 names A)
  obtain ⟨b, b'⟩ := abs_le.1 (swap_false_sub_keyedIdeal_le kem cipher macS kdfS streamS geom hvalid
      hmactag h16 names A)
  have hi := le_abs_self ((Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
            (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
                true]).toReal
    - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
            (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
                true]).toReal)
  have hi' := neg_abs_le ((Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
            (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
                true]).toReal
    - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
            (swapReplyAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
                true]).toReal)
  exact abs_le.2 ⟨by linarith, by linarith⟩

end SwapGame

end Cryptlib.Protocols.Sphinx.KEMSphinx
