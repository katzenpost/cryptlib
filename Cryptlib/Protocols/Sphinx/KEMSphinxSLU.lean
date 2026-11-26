/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxProp
import Cryptlib.Protocols.Sphinx.KEMSphinxTLU

namespace Cryptlib.Protocols.RSOR

open OracleComp OracleSpec

variable {S : Scheme} {hon : Honest S}

/-- World 0 of SLU← from the challenger's randomness: the first layer of the adversary's onion,
and a sender that does not answer the reply's last layer. -/
def BackwardChallenge.world0 (c : BackwardChallenge hon) (r : S.Randomness) : World S where
  onion := S.form c.req r c.req.first
  patch :=
    { proc := fun h o out =>
        if h = .sender ∧ o.1 = (S.formBack c.req r c.req.msg
            ⟨c.req.back.hops.length - 1, by have := c.pos.isLt; omega⟩).1 then pure none
        else pure out }

/-- World 0 of SLU← draws the randomness and shows `world0`. -/
theorem backwardUnlinkable_world_false (c : BackwardChallenge hon) :
    (backwardUnlinkable (S := S)).world c false
      = (do
        let r ← $ᵗ S.Randomness
        return c.world0 r) := by
  simp [backwardUnlinkable, BackwardChallenge.world0]

end Cryptlib.Protocols.RSOR

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

/-! # Backward layer unlinkability (SLU←) for KEM Sphinx

A reply's layers are the layers of a packet over the backward path, with the payload as the
relays before left it (`RSOR.formBack`). So the honest relay's layer of a reply is keyed by one
seed of the backward path's draw, as its layer of a forward onion is keyed by one seed of the
forward path's. -/

section Backward

open Cryptlib.Protocols.RSOR (Role)

variable (geom : Geometry)

/-- The challenger's randomness with the seed for backward position `j` replaced. -/
def setSeedBack (r : RSOR.Randomness geom) (j : Nat) (s : Vector UInt8 32) :
    RSOR.Randomness geom :=
  (r.1, (r.2.1.1.setIfInBounds j s, r.2.1.2), r.2.2)

/-- Drawing the challenger's randomness and a seed, and putting the seed at backward position
`j`, is drawing the randomness. -/
theorem evalDistEq_setSeedBack {δ : Type} (j : ℕ) (hj : j < geom.nrHops)
    (K : RSOR.Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let s ← $ᵗ (Vector UInt8 32)
      K (setSeedBack geom r j s)) =ᵈ ($ᵗ (RSOR.Randomness geom) >>= K) := by
  have hg : Function.Bijective (Function.uncurry
      fun (r : RSOR.Randomness geom) (s : Vector UInt8 32) =>
        (setSeedBack geom r j s, r.2.1.1[j])) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun p => (setSeedBack geom p.1 j p.2, p.1.2.1.1[j]), ?_, ?_⟩ <;>
    · rintro ⟨r, s⟩
      simp [setSeedBack, Function.uncurry, setIfInBounds_getElem_self _ _ hj]
  have hp := evalDistEq_pair_of_bijective
    (g := fun (r : RSOR.Randomness geom) (s : Vector UInt8 32) => (r, s))
    ⟨fun ⟨_, _⟩ ⟨_, _⟩ h => h, fun p => ⟨p, rfl⟩⟩ (fun p => K p.1)
  exact ((evalDistEq_pair_of_bijective hg
    (fun p : RSOR.Randomness geom × Vector UInt8 32 => K p.1)).trans hp.symm).trans
    (EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 32)) (K r))

end Backward

/-! ## The reply block in the sender's payload -/

namespace RSOR

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- **The reply block is the header of the first layer on the backward path**, then the first
relay's name and the reply's payload key. -/
theorem surb_fst (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (q : Request kem geom) (r : Randomness geom) (payload x0 : ByteArray)
    (hb : 0 < q.back.hops.length)
    (hx0 : layer kem cipher macS kdfS streamS geom (path kem q.back [.surbReply r.2.2.2]) r.2.1
      payload 0 = .ok x0) :
    (surb kem macS kdfS streamS geom q r).1
      = x0.extract 0 geom.headerLength ++ ofVector q.back.hops[0].name ++ ofVector r.2.2.1 := by
  unfold layer at hx0
  dsimp only at hx0
  simp only [fillerAt, Array.extract_size] at hx0
  obtain ⟨-, hdr, keys, t, hcreate, -, -, hx⟩ :=
    newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hx0
  have hh := createKEMHeader_hdr_size kem macS kdfS streamS geom _ _ _ hdr keys hvalid hmactag
    hcreate
  have hxh : x0.extract 0 geom.headerLength = hdr := by
    rw [hx, ← hh]
    exact Cryptlib.Util.Bytes.extract_append_left hdr _
  unfold surb
  dsimp only
  rw [newKEMSURB_eq kem macS kdfS streamS geom _ _ _ _ _ _ hcreate, path_getElem! kem _ _ 0 hb,
    hxh]

/-- The sender's payload, with the header of the reply's first layer written out. -/
theorem body_eq (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (q : Request kem geom) (r : Randomness geom) (payload x0 : ByteArray)
    (hb : 0 < q.back.hops.length)
    (hx0 : layer kem cipher macS kdfS streamS geom (path kem q.back [.surbReply r.2.2.2]) r.2.1
      payload 0 = .ok x0) :
    body kem macS kdfS streamS geom q r
      = ⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩
        ++ (x0.extract 0 geom.headerLength ++ ofVector q.back.hops[0].name ++ ofVector r.2.2.1)
        ++ ofVector q.msg := by
  unfold body
  rw [surb_fst kem cipher macS kdfS streamS geom hvalid hmactag q r payload x0 hb hx0]

/-- **A reply layer has the header of the layer on the backward path.** -/
theorem formBack_fst (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (q : Request kem geom) (r : Randomness geom) (m : Msg geom) (j : Fin q.back.hops.length) :
    (formBack kem cipher macS kdfS streamS geom q r m j).1
      = (match layer kem cipher macS kdfS streamS geom (path kem q.back [.surbReply r.2.2.2]) r.2.1
          ⟨Array.replicate geom.forwardPayloadLength 0⟩ j with
        | .ok pkt => (split geom pkt).1
        | .error _ => (default : Onion geom).1) := by
  unfold formBack
  dsimp only
  cases h : layer kem cipher macS kdfS streamS geom (path kem q.back [.surbReply r.2.2.2]) r.2.1
      ⟨Array.replicate geom.forwardPayloadLength 0⟩ j with
  | error e => rfl
  | ok pkt =>
    dsimp only
    obtain ⟨hsz, -⟩ := join_split_layer kem cipher macS kdfS streamS geom hvalid hmactag _ _ _ _ _ h
    have hA : (pkt.extract 0 geom.headerLength).size = geom.headerLength := by
      rw [ByteArray.size_extract]
      omega
    unfold split
    dsimp only
    have h1 := Cryptlib.Util.Bytes.extract_append_left (pkt.extract 0 geom.headerLength)
      (peeled kem cipher kdfS (path kem q.back [.surbReply r.2.2.2])
        (r.2.1.1.toArray.extract 0 (path kem q.back [.surbReply r.2.2.2]).size)
        ((replyPacket kem cipher macS kdfS streamS geom q r m).1.extract geom.headerLength
          (replyPacket kem cipher macS kdfS streamS geom q r m).1.size) j)
    rw [hA] at h1
    rw [h1]

end RSOR

/-! ## The first layer, with the honest relay's reply layer keyed -/

section BackKeyed

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- The sender's payload with `hdr` as the header of the reply's first layer. -/
def bodyH (q : RSOR.Request kem geom) (r : RSOR.Randomness geom) (hb : 0 < q.back.hops.length)
    (hdr : ByteArray) : ByteArray :=
  ⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩
    ++ (hdr ++ ofVector q.back.hops[0].name ++ ofVector r.2.2.1) ++ ofVector q.msg

/-- The first layer of `q`'s onion, with the KEM ciphertext, header keystream, tagging function
and payload encryption of the relay at backward position `k` given. Those enter through the
header of the reply's first layer, which the sender's payload carries. -/
def backOnionF (q : RSOR.Request kem geom) (r : RSOR.Randomness geom)
    (hb : 0 < q.back.hops.length) (k : ℕ) (c U : ByteArray) (tagf encf : ByteArray → ByteArray) :
    RSOR.Onion geom :=
  match layerF kem cipher macS kdfS streamS geom (RSOR.path kem q.back [.surbReply r.2.2.2]) r.2.1
      ⟨Array.replicate geom.forwardPayloadLength 0⟩ k c U tagf encf 0 with
  | some x0 =>
    (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem q.fwd [.recipient
        q.receiver]) r.1
        (bodyH kem geom q r hb (x0.extract 0 geom.headerLength)) 0 with
      | .ok pkt => RSOR.split geom pkt
      | .error _ => default)
  | none => default

/-- **With the keys that the seed `s` gives at backward position `k`, the keyed first layer is
the first layer of `q`'s onion** built from the randomness with `s` at that position. -/
theorem backOnionF_real (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (q : RSOR.Request kem geom) (r : RSOR.Randomness geom) (hb : 0 < q.back.hops.length)
    (k : ℕ) (hk : k < q.back.hops.length) (s : Vector UInt8 32) (c ss x0 : ByteArray)
    (henc : kemEncap kem ((RSOR.path kem q.back [.surbReply r.2.2.2])[k]!).publicKey s
      = .ok (c, ss))
    (hx0 : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem q.back [.surbReply r.2.2.2])
      (setSeedBack geom r k s).2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0 = .ok x0) :
    backOnionF kem cipher macS kdfS streamS geom q r hb k c
        (ksOf streamS geom (keyTuple (deriveHopKeys kdfS ss)))
        (tagOf macS (keyTuple (deriveHopKeys kdfS ss)))
        (encOf cipher (keyTuple (deriveHopKeys kdfS ss)))
      = RSOR.form kem cipher macS kdfS streamS geom q (setSeedBack geom r k s) q.first := by
  have hF := layerF_real kem cipher macS kdfS streamS geom (RSOR.path kem q.back [.surbReply
      r.2.2.2]) r.2.1
    ⟨Array.replicate geom.forwardPayloadLength 0⟩ x0 k 0 s c ss (Nat.zero_le _)
    (by rw [RSOR.path_size]; exact hk)
    (by rw [RSOR.path_size]; exact q.back.length_le) henc hx0
  unfold backOnionF RSOR.form
  rw [hF]
  dsimp only
  rw [RSOR.body_eq kem cipher macS kdfS streamS geom hvalid hmactag q (setSeedBack geom r k s) _ x0
      hb hx0]
  rfl

/-- The header of the reply's layer at backward position `i`, past the relay at position `k`,
from that relay's header keystream. -/
def backHeaderU (q : RSOR.Request kem geom) (r : RSOR.Randomness geom) (k : ℕ) (U : ByteArray)
    (i : ℕ) : Vector UInt8 geom.headerLength :=
  match layerPast kem cipher macS kdfS streamS geom (RSOR.path kem q.back [.surbReply r.2.2.2])
      r.2.1
      ⟨Array.replicate geom.forwardPayloadLength 0⟩ k U i with
  | .ok pkt => (RSOR.split geom pkt).1
  | .error _ => (default : RSOR.Onion geom).1

/-- **A reply layer past the relay depends on the relay's keys through its keystream only.**
With the keystream of the keys that the seed `s` gives at backward position `k`, `backHeaderU`
is the header of the reply's layer built from the randomness with `s` at that position. -/
theorem formBack_fst_real (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (q : RSOR.Request kem geom) (r : RSOR.Randomness geom) (m : RSOR.Msg geom) (k : ℕ)
    (i : Fin q.back.hops.length) (hki : k < i) (s : Vector UInt8 32) (c ss : ByteArray)
    (henc : kemEncap kem ((RSOR.path kem q.back [.surbReply r.2.2.2])[k]!).publicKey s
      = .ok (c, ss)) :
    (RSOR.formBack kem cipher macS kdfS streamS geom q (setSeedBack geom r k s) m i).1
      = backHeaderU kem cipher macS kdfS streamS geom q r k
        (ksOf streamS geom (keyTuple (deriveHopKeys kdfS ss))) i := by
  rw [RSOR.formBack_fst kem cipher macS kdfS streamS geom hvalid hmactag]
  unfold backHeaderU
  rw [layerPast_real kem cipher macS kdfS streamS geom (RSOR.path kem q.back [.surbReply r.2.2.2])
      r.2.1
    ⟨Array.replicate geom.forwardPayloadLength 0⟩ k i s c ss hki
    (by rw [RSOR.path_size]; exact i.isLt.le)
    (by rw [RSOR.path_size]; exact q.back.length_le) henc]
  rfl

/-- The challenger's randomness with the seed of the honest relay's layer replaced. The relay
is the one before backward position `pos`: its layer is the last of the forward path when `pos`
is zero, and the reply's layer at backward position `pos - 1` otherwise. -/
def relaySeed (q : RSOR.Request kem geom) (pos : ℕ) (r : RSOR.Randomness geom)
    (s : Vector UInt8 32) : RSOR.Randomness geom :=
  match pos with
  | 0 => setSeed geom r (q.fwd.hops.length - 1) s
  | k + 1 => setSeedBack geom r k s

/-- Drawing the challenger's randomness and a seed, and putting the seed at the honest relay's
layer, is drawing the randomness. -/
theorem evalDistEq_relaySeed {δ : Type} (q : RSOR.Request kem geom) (pos : ℕ)
    (hpos : pos < q.back.hops.length) (K : RSOR.Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let s ← $ᵗ (Vector UInt8 32)
      K (relaySeed kem geom q pos r s)) =ᵈ ($ᵗ (RSOR.Randomness geom) >>= K) := by
  cases pos with
  | zero =>
    exact evalDistEq_setSeed geom _ (lt_of_lt_of_le
      (Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2 q.fwd_ne))) q.fwd.length_le) K
  | succ k =>
    exact evalDistEq_setSeedBack geom k (lt_of_lt_of_le (Nat.lt_of_succ_lt hpos)
      q.back.length_le) K

end BackKeyed

/-! ## World 0 as its draws -/

section BackGame

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

/-- **World 0 of SLU← as its draws**, with the seed of the honest relay's layer drawn on its
own, and then the adversary's guess against the honest relays. -/
theorem backward_play_false_evalDistEq (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary) :
    Protocols.RSOR.Property.play names A false
      =ᵈ propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness geom)
          ($ᵗ RSOR.Randomness geom) A >>= fun d =>
        (simulateQ (Protocols.RSOR.honest
            (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay names d.k.1 d.keys)
            (fun h => if h = .relay then d.k.2 else (d.keys h).2)
            (Protocols.RSOR.BackwardChallenge.world0 d.c
              (relaySeed kem geom d.c.req d.c.pos d.o d.s)).patch)
          (A.guess d.st (Protocols.RSOR.BackwardChallenge.world0 d.c
            (relaySeed kem geom d.c.req d.c.pos d.o d.s)).onion)).run' d.log := by
  refine (play_evalDistEq_honAt kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names A false).trans ?_
  unfold Protocols.RSOR.Property.playFrom propDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
    EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => ?_
  have hcong : ∀ (m m' : ProbComp (Protocols.RSOR.World 𝒮))
      (F : Protocols.RSOR.World 𝒮 → ProbComp Bool), m = m' → m >>= F =ᵈ m' >>= F :=
    fun _ _ _ h => h ▸ EvalDistEq.rfl
  refine (hcong _ _ _ (Protocols.RSOR.backwardUnlinkable_world_false (S := 𝒮) out.1.1)).trans ?_
  simp only [bind_assoc, pure_bind]
  exact (evalDistEq_relaySeed kem geom out.1.1.req out.1.1.pos out.1.1.pos.isLt _).symm

end BackGame

end Cryptlib.Protocols.Sphinx.KEMSphinx
