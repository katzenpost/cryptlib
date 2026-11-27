/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxSLURelay
import Cryptlib.Protocols.Sphinx.KEMSphinxBuilds

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

/-! # The events of SLU← on the KEM alone

The bound of SLU← for KEM Sphinx carries events on draws: a key pair that is not one, a seed
that is not reliable, a layer that cannot be built. A relay's key pair is a key pair, and with
reliable seeds every layer of a route builds (`KEMSphinxBuilds`). So each event has a seed that
is not reliable. A forward layer needs the sender's payload to have the forward payload's
length, which a geometry with room for a reply block gives (`hsurb`). -/

section BackEvents

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

variable (W : Protocols.RSOR.BackSwap (sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16))

set_option maxHeartbeats 2000000 in
/-- **A bad draw of world 0 has a seed that is not reliable**: the honest relay's. Its key pair
is a key pair, and the first layer that carries its ciphertext builds. -/
theorem prEvent_backBad0_le
    (hsurb : geom.forwardPayloadLength = 2 + geom.surbLength + geom.userForwardPayloadLength)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardWith W).Adversary) :
    Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 geom) A)}[backBad0 kem cipher
        macS kdfS streamS geom hvalid hmactag h16 W d]
      ≤ Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names _ (backDraw0 geom) A)}[¬ kem.Reliable
          (kem.stateFromSeed d.s)] := by
  refine prEvent_mono_of_support _ _ _ fun d hd hbad hgood => hbad ?_
  have hk : d.k.1.1 = kem.derivePublicKey d.k.2 := by
    unfold propDrawOf at hd
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hd
    obtain ⟨k, hk, k₁, -, k₂, -, out, -, o, -, s, -, rfl⟩ := hd
    exact RSOR.key_of_keygen kem k.1 k.2 hk
  refine ⟨hk, hgood, ?_⟩
  have hlt : d.c.pos.val < d.c.req.back.hops.length := d.c.pos.isLt
  cases hp : d.c.pos.val with
  | zero =>
    exact layer_zero_builds kem cipher macS kdfS streamS hvalid d.c.req.fwd
      (List.length_pos_iff.2 d.c.req.fwd_ne) _ (Or.inl ⟨_, rfl⟩) _ _
      ((RSOR.body_size kem macS kdfS streamS geom hvalid hmactag _ _).trans hsurb.symm)
  | succ k =>
    exact layer_zero_builds kem cipher macS kdfS streamS hvalid d.c.req.back (Nat.zero_lt_of_lt
        hlt) _
      (Or.inr ⟨_, rfl⟩) _ _ Array.size_replicate

set_option maxHeartbeats 2000000 in
/-- **A bad draw of world 1 has a seed that is not reliable**: the honest relay's, or one on
the path its layer is on. With reliable seeds every layer of that path builds. -/
theorem prEvent_backBad1_le
    (hsurb : geom.forwardPayloadLength = 2 + geom.surbLength + geom.userForwardPayloadLength)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardWith W).Adversary) :
    Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardWith W) .relay names _
        (swapDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 W) A)}[backBad1 kem cipher
            macS kdfS streamS geom hvalid hmactag h16 W d]
      ≤ Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardWith W) .relay names _
        (swapDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 W) A)}[¬ (kem.Reliable
            (kem.stateFromSeed d.s)
        ∧ match d.c.pos.val with
          | 0 => ∀ i, i < d.c.req.fwd.hops.length → kem.Reliable (kem.stateFromSeed
              (setSeed geom d.o.1 (d.c.req.fwd.hops.length - 1) d.s).1.1.toArray[i]!)
          | k + 1 => ∀ i, i < d.c.req.back.hops.length → kem.Reliable (kem.stateFromSeed
              (setSeedBack geom d.o.1 k d.s).2.1.1.toArray[i]!))] := by
  refine prEvent_mono_of_support _ _ _ fun d hd hbad hgood => hbad ?_
  have hk : d.k.1.1 = kem.derivePublicKey d.k.2 := by
    unfold propDrawOf at hd
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hd
    obtain ⟨k, hk, k₁, -, k₂, -, out, -, o, -, s, -, rfl⟩ := hd
    exact RSOR.key_of_keygen kem k.1 k.2 hk
  obtain ⟨hr, hm⟩ := hgood
  refine ⟨hk, hr, ?_⟩
  have hlt : d.c.pos.val < d.c.req.back.hops.length := d.c.pos.isLt
  have hf : 0 < d.c.req.fwd.hops.length := List.length_pos_iff.2 d.c.req.fwd_ne
  revert hm
  cases hp : d.c.pos.val with
  | zero =>
    intro hm
    have L := layer_builds_of_reliable kem cipher macS kdfS streamS hvalid hmactag h16 d.c.req.fwd
      [.recipient d.c.req.receiver] (Or.inl ⟨_, rfl⟩)
      (setSeed geom d.o.1 (d.c.req.fwd.hops.length - 1) d.s).1
      (RSOR.body kem macS kdfS streamS geom d.c.req
        (setSeed geom d.o.1 (d.c.req.fwd.hops.length - 1) d.s))
      ((RSOR.body_size kem macS kdfS streamS geom hvalid hmactag _ _).trans hsurb.symm) hm
    obtain ⟨pkt, h0⟩ := L 0 hf
    obtain ⟨pktL, hL⟩ := L (d.c.req.fwd.hops.length - 1) (Nat.sub_one_lt (Nat.ne_of_gt hf))
    exact ⟨pkt, pktL, h0, hL⟩
  | succ k =>
    intro hm
    have hk1 : k + 1 < d.c.req.back.hops.length := hp ▸ hlt
    have L := layer_builds_of_reliable kem cipher macS kdfS streamS hvalid hmactag h16 d.c.req.back
      [.surbReply d.o.1.2.2.2] (Or.inr ⟨_, rfl⟩) (setSeedBack geom d.o.1 k d.s).2.1
      (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) Array.size_replicate hm
    obtain ⟨x0, h0⟩ := L 0 (Nat.zero_lt_of_lt hlt)
    obtain ⟨xk, hxk⟩ := L k (Nat.lt_of_succ_lt hk1)
    exact ⟨x0, xk, h0, hxk⟩

end BackEvents

section SwapEvents

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

set_option maxHeartbeats 2000000 in
/-- **A bad draw of the world with a fresh onion has a seed that is not reliable**: the
sender's, or one on the rest of the backward path. -/
theorem prEvent_swapFreshBad_le
    (hsurb : geom.forwardPayloadLength = 2 + geom.surbLength + geom.userForwardPayloadLength)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮))
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary) :
    Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮))
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)) .sender names _
        (shortDraw geom) A)}[swapFreshBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]
      ≤ Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮))
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)) .sender names _
        (shortDraw geom) A)}[¬ (kem.Reliable (kem.stateFromSeed d.s)
        ∧ ∀ i, i < (d.c.req.back.drop d.c.pos).hops.length → kem.Reliable (kem.stateFromSeed
          (setSeed geom d.o.2.2.2 ((d.c.req.back.drop d.c.pos).hops.length - 1)
            d.s).1.1.toArray[i]!))] := by
  refine prEvent_mono_of_support _ _ _ fun d hd hbad hgood => hbad ?_
  have hk : d.k.1.1 = kem.derivePublicKey d.k.2 := by
    unfold propDrawOf at hd
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hd
    obtain ⟨k, hk, k₁, -, k₂, -, out, -, o, -, s, -, rfl⟩ := hd
    exact RSOR.key_of_keygen kem k.1 k.2 hk
  have hf : 0 < (d.c.req.back.drop d.c.pos).hops.length :=
    List.length_pos_iff.2 (d.c.req.back.drop_ne d.c.pos.isLt)
  have L := layer_builds_of_reliable kem cipher macS kdfS streamS hvalid hmactag h16
    (Protocols.RSOR.BackwardChallenge.swapReq d.c d.o.2.1 d.o.2.2.1).fwd
    [.recipient (Protocols.RSOR.BackwardChallenge.swapReq d.c d.o.2.1 d.o.2.2.1).receiver]
    (Or.inl ⟨_, rfl⟩)
    (setSeed geom d.o.2.2.2 ((d.c.req.back.drop d.c.pos).hops.length - 1) d.s).1
    (RSOR.body kem macS kdfS streamS geom
      (Protocols.RSOR.BackwardChallenge.swapReq d.c d.o.2.1 d.o.2.2.1)
      (setSeed geom d.o.2.2.2 ((d.c.req.back.drop d.c.pos).hops.length - 1) d.s))
    ((RSOR.body_size kem macS kdfS streamS geom hvalid hmactag _ _).trans hsurb.symm) hgood.2
  obtain ⟨pkt, h0⟩ := L 0 hf
  obtain ⟨pktL, hL⟩ := L ((d.c.req.back.drop d.c.pos).hops.length - 1)
    (Nat.sub_one_lt (Nat.ne_of_gt hf))
  exact ⟨hk, hgood.1, pkt, pktL, h0, hL⟩

set_option maxHeartbeats 2000000 in
/-- **A bad draw of the world where a reply layer is sent on has a seed that is not
reliable**: the sender's, or one on the rest of the backward path. -/
theorem prEvent_swapReplyBad_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮))
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary) :
    Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮))
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)) .sender names _
        (replyDraw geom) A)}[swapReplyBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]
      ≤ Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮))
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)) .sender names _
        (replyDraw geom) A)}[¬ (kem.Reliable (kem.stateFromSeed d.s)
        ∧ ∀ i, i < (d.c.req.back.drop d.c.pos).hops.length → kem.Reliable (kem.stateFromSeed
          (setSeed geom d.o.2.1 ((d.c.req.back.drop d.c.pos).hops.length - 1)
            d.s).1.1.toArray[i]!))] := by
  refine prEvent_mono_of_support _ _ _ fun d hd hbad hgood => hbad ?_
  have hk : d.k.1.1 = kem.derivePublicKey d.k.2 := by
    unfold propDrawOf at hd
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hd
    obtain ⟨k, hk, k₁, -, k₂, -, out, -, o, -, s, -, rfl⟩ := hd
    exact RSOR.key_of_keygen kem k.1 k.2 hk
  have hf : 0 < (d.c.req.back.drop d.c.pos).hops.length :=
    List.length_pos_iff.2 (d.c.req.back.drop_ne d.c.pos.isLt)
  have L := layer_builds_of_reliable kem cipher macS kdfS streamS hvalid hmactag h16
      (d.c.req.back.drop d.c.pos)
    [.surbReply d.o.2.1.2.2.2] (Or.inr ⟨_, rfl⟩)
    (setSeed geom d.o.2.1 ((d.c.req.back.drop d.c.pos).hops.length - 1) d.s).1
    (⟨Array.replicate geom.forwardPayloadLength 0⟩ : ByteArray) Array.size_replicate hgood.2
  obtain ⟨pkt, h0⟩ := L 0 hf
  obtain ⟨pktL, hL⟩ := L ((d.c.req.back.drop d.c.pos).hops.length - 1)
    (Nat.sub_one_lt (Nat.ne_of_gt hf))
  exact ⟨hk, hgood.1, pkt, pktL, h0, hL⟩

/-- The draws of the two keyed games of the sender on which no seed fails: the sender's, and
those of the hops in front of it on the rest of the backward path. -/
def swapSeedsGood (s : Vector UInt8 32) (n : ℕ) (seeds : Array (Vector UInt8 32)) : Prop :=
  kem.Reliable (kem.stateFromSeed s) ∧ ∀ m, m < n - 1 → kem.Reliable (kem.stateFromSeed seeds[m]!)

set_option maxHeartbeats 2000000 in
/-- With reliable seeds a draw of the world with a fresh onion is good: the sender's key pair
is a key pair and the fresh onion's first layer builds. -/
theorem swapFreshGood_of_reliable
    (hsurb : geom.forwardPayloadLength = 2 + geom.surbLength + geom.userForwardPayloadLength)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮))
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary)
    (d : KeyedDraw (swapFreshAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) (hd
        : d ∈ support (keyedDraw cipher macS kdfS streamS geom (swapFreshAdv kem cipher macS kdfS
        streamS geom hvalid hmactag h16 names A)))
    (hgood : swapSeedsGood kem d.s ((propChOf d).c.req.back.drop (propChOf d).c.pos).hops.length
      (propOthOf d).2.2.2.1.1.toArray) :
    swapFreshGood kem cipher macS kdfS streamS geom hvalid hmactag h16 d := by
  have hk : d.k.1.1 = kem.derivePublicKey d.k.2 := by
    unfold keyedDraw at hd
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hd
    obtain ⟨k, hk, cs, -, s, -, o, -, rfl⟩ := hd
    exact RSOR.key_of_keygen kem k.1 k.2 hk
  exact ⟨hk, hgood.1,
    layer_zero_builds kem cipher macS kdfS streamS hvalid
      (Protocols.RSOR.BackwardChallenge.swapReq (propChOf d).c (propOthOf d).2.1
        (propOthOf d).2.2.1).fwd
      (List.length_pos_iff.2 ((propChOf d).c.req.back.drop_ne (propChOf d).c.pos.isLt)) _
      (Or.inl ⟨_, rfl⟩) _ _
      ((RSOR.body_size kem macS kdfS streamS geom hvalid hmactag _ _).trans hsurb.symm),
    hgood.2⟩

/-- **A draw of the world with a fresh onion that is not good has a seed that is not
reliable.** -/
theorem prEvent_not_swapFreshGood_le
    (hsurb : geom.forwardPayloadLength = 2 + geom.surbLength + geom.userForwardPayloadLength)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮))
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary) :
    Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (swapFreshAdv kem cipher macS kdfS streamS
        geom hvalid hmactag h16 names A))}[¬ swapFreshGood kem cipher macS kdfS streamS geom hvalid
        hmactag h16 d]
      ≤ Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (swapFreshAdv kem cipher macS kdfS
          streamS geom hvalid hmactag h16 names A))}[¬ swapSeedsGood kem d.s
        ((propChOf d).c.req.back.drop (propChOf d).c.pos).hops.length
        (propOthOf d).2.2.2.1.1.toArray] :=
  prEvent_mono_of_support _ _ _ fun d hd hbad hgood =>
    hbad (swapFreshGood_of_reliable kem cipher macS kdfS streamS geom hvalid hmactag h16 hsurb
        names A d hd hgood)

set_option maxHeartbeats 2000000 in
/-- **So has one that is not good for the payload step**: at the sender, the last hop of the
fresh onion's path, the bytes behind the tag are the zero tag and the payload. -/
theorem prEvent_not_swapFreshGoodP_le
    (hsurb : geom.forwardPayloadLength = 2 + geom.surbLength + geom.userForwardPayloadLength)
    (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair (Protocols.RSOR.freshSwap (S := 𝒮))
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary) :
    Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (swapFreshAdv kem cipher macS kdfS streamS
        geom hvalid hmactag h16 names A))}[¬ swapFreshGoodP kem cipher macS kdfS streamS geom
        hvalid hmactag h16 d]
      ≤ Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (swapFreshAdv kem cipher macS kdfS
          streamS geom hvalid hmactag h16 names A))}[¬ swapSeedsGood kem d.s
        ((propChOf d).c.req.back.drop (propChOf d).c.pos).hops.length
        (propOthOf d).2.2.2.1.1.toArray] := by
  refine prEvent_mono_of_support _ _ _ fun d hd hbad hgood =>
    hbad ⟨swapFreshGood_of_reliable kem cipher macS kdfS streamS geom hvalid hmactag h16 hsurb
        names A d hd hgood, fun k => ?_⟩
  have hf : 0 < ((propChOf d).c.req.back.drop (propChOf d).c.pos).hops.length :=
    List.length_pos_iff.2 ((propChOf d).c.req.back.drop_ne (propChOf d).c.pos.isLt)
  refine (congrArg ByteArray.size (relayBackAt_last kem cipher macS kdfS streamS geom _ _ _ _ _
    ((Nat.sub_add_cancel hf).trans (RSOR.path_size kem _ _).symm))).trans ?_
  rw [ByteArray.size_append]
  exact congrArg₂ (· + ·) Array.size_replicate
    ((RSOR.body_size kem macS kdfS streamS geom hvalid hmactag _ _).trans hsurb.symm)

set_option maxHeartbeats 2000000 in
/-- **A draw of the world where a reply layer is sent on that is not good has a seed that is
not reliable.** -/
theorem prEvent_not_swapReplyGood_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.swapPair
    (Protocols.RSOR.freshSwap (S := 𝒮))
      (replySwap kem cipher macS kdfS streamS geom hvalid hmactag h16)).Adversary) :
    Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (swapReplyAdv kem cipher macS kdfS streamS
        geom hvalid hmactag h16 names A))}[¬ swapReplyGood kem cipher macS kdfS streamS geom hvalid
        hmactag h16 d]
      ≤ Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (swapReplyAdv kem cipher macS kdfS
          streamS geom hvalid hmactag h16 names A))}[¬ swapSeedsGood kem d.s
        ((propChOf d).c.req.back.drop (propChOf d).c.pos).hops.length
        (propOthOf d).2.1.1.1.toArray] := by
  refine prEvent_mono_of_support _ _ _ fun d hd hbad hgood => hbad ?_
  have hk : d.k.1.1 = kem.derivePublicKey d.k.2 := by
    unfold keyedDraw at hd
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hd
    obtain ⟨k, hk, cs, -, s, -, o, -, rfl⟩ := hd
    exact RSOR.key_of_keygen kem k.1 k.2 hk
  exact ⟨hk, hgood.1,
    layer_zero_builds kem default macS kdfS streamS hvalid
      ((propChOf d).c.req.back.drop (propChOf d).c.pos)
      (List.length_pos_iff.2 ((propChOf d).c.req.back.drop_ne (propChOf d).c.pos.isLt)) _
      (Or.inr ⟨_, rfl⟩) _ _ Array.size_replicate,
    hgood.2⟩

end SwapEvents

end Cryptlib.Protocols.Sphinx.KEMSphinx
