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

/-- World 0 of SLU← around the honest relay's ciphertext and keys. At the exit the relay's
layer is the last of the forward path; on the backward path its keys enter through the reply
block and, in the header the sender refuses, through its keystream. -/
def backView0 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (t : KeyTuple) : Protocols.RSOR.World 𝒮 :=
  match ch.c.pos.val with
  | 0 =>
    { onion := onionK kem cipher macS kdfS streamS geom ch.c.req r (ch.c.req.fwd.hops.length - 1) c
        t 0
      patch := (Protocols.RSOR.BackwardChallenge.world0 ch.c r).patch }
  | k + 1 =>
    { onion := backOnionF kem cipher macS kdfS streamS geom ch.c.req r (Nat.zero_lt_of_lt
        ch.c.pos.isLt) k
        (ofVector (kem.encodeCiphertext c)) (ksOf streamS geom t) (tagOf macS t) (encOf cipher t)
      patch :=
        { proc := fun (h : Role) (o : RSOR.Onion geom) out =>
            if h = .sender ∧ o.1 = backHeaderU kem cipher macS kdfS streamS geom ch.c.req r k (ksOf
                streamS geom t)
                (ch.c.req.back.hops.length - 1) then pure none
            else pure out } }

/-- The keyed game of world 0 of SLU← around the honest relay's ciphertext. -/
abbrev backSetup0 (names : Role → RSOR.Name) :
    KeyedSetup kem (Protocols.RSOR.World 𝒮) Bool :=
  propSetupOf kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness geom)
    ($ᵗ RSOR.Randomness geom) (backView0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names)

/-- The adversary of that keyed game. -/
abbrev backAdv0 (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary) :
    KeyedAdversary (backSetup0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) :=
  propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardUnlinkable
      (S := 𝒮)) .relay names _ _ _ A

set_option maxHeartbeats 1000000 in
/-- **On the backward path, the keyed world 0 with the real keys is world 0.** With the
ciphertext and keys that the seed `s` gives at the honest relay's backward position, `backView0`
is world 0 from the randomness with `s` at that position. -/
theorem backView0_real_back (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (r : RSOR.Randomness geom) (k : ℕ) (hp : ch.c.pos.val = k + 1) (s : Vector UInt8 32)
    (c : kem.Ciphertext) (ss x0 : ByteArray)
    (henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s
      = .ok (ofVector (kem.encodeCiphertext c), ss))
    (hx0 : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
        r.2.2.2])
      (setSeedBack geom r k s).2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0 = .ok x0) :
    backView0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c (keyTuple
        (deriveHopKeys kdfS ss))
      = Protocols.RSOR.BackwardChallenge.world0 ch.c (setSeedBack geom r k s) := by
  have hlt : ch.c.pos.val < ch.c.req.back.hops.length := ch.c.pos.isLt
  have hk : k < ch.c.req.back.hops.length := by omega
  have hrel := ch.c.relay
  rw [hp] at hrel
  have hkey : (ch.c.req.back.hops[k]'hk).key = pk := by
    have h1 : ch.c.req.back.hops[k]'hk
        = honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay names pk ch.keys .relay
            :=
      Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hrel)
    rw [h1]
    rfl
  have hpub : ((RSOR.path kem ch.c.req.back [.surbReply r.2.2.2])[k]!).publicKey
      = ofVector (kem.encodePublicKey pk.1) := by
    rw [RSOR.path_getElem! kem _ _ _ hk]
    exact congrArg (fun key : Key kem => ofVector (kem.encodePublicKey key.1)) hkey
  have henc' : kemEncap kem ((RSOR.path kem ch.c.req.back [.surbReply r.2.2.2])[k]!).publicKey s
      = .ok (ofVector (kem.encodeCiphertext c), ss) := by
    rw [hpub]
    exact henc
  have honion := backOnionF_real kem cipher macS kdfS streamS geom hvalid hmactag ch.c.req r
      (Nat.zero_lt_of_lt hlt) k hk s
    _ ss x0 henc' hx0
  have hhdr := formBack_fst_real kem cipher macS kdfS streamS geom hvalid hmactag ch.c.req r
      ch.c.req.msg k
    ⟨ch.c.req.back.hops.length - 1, Nat.sub_one_lt (Nat.ne_of_gt (Nat.zero_lt_of_lt hlt))⟩
    (Nat.lt_sub_of_add_lt (by rw [← hp]; exact hlt))
    s _ ss henc'
  unfold backView0
  rw [hp]
  exact congrArg₂ (fun on (hd : Vector UInt8 geom.headerLength) =>
    ({ onion := on
       patch := { proc := fun (h : Role) (o : RSOR.Onion geom) out =>
        if h = .sender ∧ o.1 = hd then pure none else pure out } } : Protocols.RSOR.World 𝒮))
    honion hhdr.symm

/-- **At the exit, the keyed world 0 with the real keys is world 0.** With the ciphertext and
keys that the seed `s` gives at the last forward position, `backView0` is world 0 from the
randomness with `s` at that position. -/
theorem backView0_real_exit (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (r : RSOR.Randomness geom) (hp : ch.c.pos.val = 0) (s : Vector UInt8 32)
    (c : kem.Ciphertext) (ss pkt : ByteArray)
    (henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s
      = .ok (ofVector (kem.encodeCiphertext c), ss))
    (hpkt : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
        ch.c.req.receiver])
      (setSeed geom r (ch.c.req.fwd.hops.length - 1) s).1
      (RSOR.body kem macS kdfS streamS geom ch.c.req
        (setSeed geom r (ch.c.req.fwd.hops.length - 1) s)) 0 = .ok pkt) :
    backView0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c (keyTuple
        (deriveHopKeys kdfS ss))
      = Protocols.RSOR.BackwardChallenge.world0 ch.c
        (setSeed geom r (ch.c.req.fwd.hops.length - 1) s) := by
  have hpos : 0 < ch.c.req.fwd.hops.length := List.length_pos_iff.2 ch.c.req.fwd_ne
  have hj : ch.c.req.fwd.hops.length - 1 < ch.c.req.fwd.hops.length :=
    Nat.sub_one_lt (Nat.ne_of_gt hpos)
  have hrel := ch.c.relay
  rw [hp] at hrel
  have hkey : (ch.c.req.fwd.hops[ch.c.req.fwd.hops.length - 1]'hj).key = pk := by
    have h1 : ch.c.req.fwd.hops[ch.c.req.fwd.hops.length - 1]'hj
        = honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay names pk ch.keys .relay
            :=
      Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans
        (List.getLast?_eq_getElem?.symm.trans hrel))
    rw [h1]
    rfl
  have honion := onionK_real kem cipher macS kdfS streamS geom ch.c.req r ⟨ch.c.req.fwd.hops.length
      - 1, hj⟩
    ch.c.req.first (Nat.zero_le _) pk hkey s c ss pkt henc hpkt
  unfold backView0
  rw [hp]
  exact congrArg (fun on => ({ onion := on
                               patch := (Protocols.RSOR.BackwardChallenge.world0 ch.c r).patch } :
    Protocols.RSOR.World 𝒮)) honion

/-- The draws that the exact steps do not cover: the honest relay's public key is not the one
its private key gives, its seed may make the KEM fail, or the first layer that carries its
ciphertext cannot be built. -/
def backBad0 {names : Role → RSOR.Name} {A : (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary}
    (d : PropDraw kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness geom) A) : Prop
        :=
  ¬ (d.k.1.1 = kem.derivePublicKey d.k.2 ∧ kem.Reliable (kem.stateFromSeed d.s) ∧
    match d.c.pos.val with
    | 0 => ∃ pkt, RSOR.layer kem cipher macS kdfS streamS geom
        (RSOR.path kem d.c.req.fwd [.recipient d.c.req.receiver])
        (setSeed geom d.o (d.c.req.fwd.hops.length - 1) d.s).1
        (RSOR.body kem macS kdfS streamS geom d.c.req
          (setSeed geom d.o (d.c.req.fwd.hops.length - 1) d.s)) 0 = .ok pkt
    | k + 1 => ∃ x0, RSOR.layer kem cipher macS kdfS streamS geom
        (RSOR.path kem d.c.req.back [.surbReply d.o.2.2.2])
        (setSeedBack geom d.o k d.s).2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0
          = .ok x0)

variable [SampleableType kem.Plaintext]

set_option maxHeartbeats 2000000 in
/-- **World 0 of SLU← is the keyed game with the real keys, off the bad draws.** -/
theorem backward_false_sub_keyedReal_le (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
      - (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
          (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
    ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness geom)
        ($ᵗ RSOR.Randomness geom) A)}[backBad0 kem cipher macS kdfS streamS geom hvalid hmactag h16
            d]).toReal := by
  rw [(backward_play_false_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).prEvent_eq (fun x => x = true),
    (keyedReal_propAdvOf_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ _ _ A).prEvent_eq
      (fun x => x = true)]
  refine prEvent_bind_toReal_sub_le_of_bad _ _ _
    (backBad0 kem cipher macS kdfS streamS geom hvalid hmactag h16) (fun d hd => ?_) (fun x => x =
        true)
  obtain ⟨hpk, hrel, hbuild⟩ := Classical.not_not.mp hd
  have hrelay := d.c.relay
  cases hp : d.c.pos.val with
  | zero =>
    rw [hp] at hbuild hrelay
    obtain ⟨pkt, hpkt⟩ := hbuild
    have hj : d.c.req.fwd.hops.length - 1 < d.c.req.fwd.hops.length :=
      Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2 d.c.req.fwd_ne))
    have hle : d.c.req.fwd.hops.length ≤ geom.nrHops := d.c.req.fwd.length_le
    obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem cipher macS kdfS streamS geom d.c.req.fwd _ _ _
        pkt hpkt
      (d.c.req.fwd.hops.length - 1) hj
    have hkey : (d.c.req.fwd.hops[d.c.req.fwd.hops.length - 1]'hj).key = d.k.1 := by
      have h1 : d.c.req.fwd.hops[d.c.req.fwd.hops.length - 1]'hj
          = honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay names d.k.1 d.keys
              .relay :=
        Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans
          (List.getLast?_eq_getElem?.symm.trans hrelay))
      rw [h1]
      rfl
    have hs : (setSeed geom d.o (d.c.req.fwd.hops.length - 1) d.s).1.1.toArray[
        d.c.req.fwd.hops.length - 1]! = d.s := by
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
    have hview := backView0_real_exit kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        ⟨d.keys, d.c⟩ d.o hp d.s _ _ pkt henc hpkt
    have hseed : relaySeed kem geom d.c.req 0 d.o d.s
        = setSeed geom d.o (d.c.req.fwd.hops.length - 1) d.s := rfl
    rw [propAdv_post kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ _ _ A d.k d.keys _ _ hdec d.st
        d.log _, hseed,
      ← hview]
    rfl
  | succ k =>
    rw [hp] at hbuild hrelay
    obtain ⟨x0, hx0⟩ := hbuild
    have hlt : d.c.pos.val < d.c.req.back.hops.length := d.c.pos.isLt
    have hk : k < d.c.req.back.hops.length := by omega
    have hle : d.c.req.back.hops.length ≤ geom.nrHops := d.c.req.back.length_le
    obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem cipher macS kdfS streamS geom d.c.req.back _ _ _
        x0 hx0 k hk
    have hkey : (d.c.req.back.hops[k]'hk).key = d.k.1 := by
      have h1 : d.c.req.back.hops[k]'hk
          = honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay names d.k.1 d.keys
              .relay :=
        Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hrelay)
      rw [h1]
      rfl
    have hs : (setSeedBack geom d.o k d.s).2.1.1.toArray[k]! = d.s := by
      simp [setSeedBack, lt_of_lt_of_le hk hle]
    rw [hs] at henc
    replace henc : kemEncap kem (ofVector (kem.encodePublicKey d.k.1.1)) d.s = .ok (ct, ss) :=
      (congrArg (fun key : Key kem => kemEncap kem (ofVector (kem.encodePublicKey key.1)) d.s)
        hkey).symm.trans henc
    obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem d.k.1.1 d.s ct ss henc
    have hdec : decapOf kem d.k.2 (encapOf kem d.k.1.1 d.s).1
        = some (encapOf kem d.k.1.1 d.s).2 := by
      have h := decapOf_encapOf kem d.k.2 d.s hrel _ _ (hpk ▸ henc)
      rwa [← hpk] at h
    have hview := backView0_real_back kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        ⟨d.keys, d.c⟩ d.o k hp d.s _ _ x0 henc hx0
    have hseed : relaySeed kem geom d.c.req (k + 1) d.o d.s = setSeedBack geom d.o k d.s := rfl
    rw [propAdv_post kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ _ _ A d.k d.keys _ _ hdec d.st
        d.log _, hseed,
      ← hview]
    rfl

/-- **The honest relay's keys in world 0 of SLU← may be uniform.** World 0 differs from the
keyed game with uniform keys at the relay by at most the chance of a bad draw and the cost of
replacing the keys (KEM and KDF). -/
theorem backward_false_sub_keyedIdeal_le (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
      - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
          (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
    ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness geom)
        ($ᵗ RSOR.Randomness geom) A)}[backBad0 kem cipher macS kdfS streamS geom hvalid hmactag h16
            d]).toReal
      + keyedCost cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS streamS geom hvalid
          hmactag h16 names A) := by
  have h1 := backward_false_sub_keyedReal_le kem cipher macS kdfS streamS geom hvalid hmactag h16
      names A
  have h2 := keyedChain_le cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS streamS
      geom hvalid hmactag h16 names A)
  have t := abs_sub_le
    (Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
    (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
      (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
    (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
      (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
  linarith

end BackGame

end Cryptlib.Protocols.Sphinx.KEMSphinx
