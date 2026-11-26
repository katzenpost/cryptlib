/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxProp
import Cryptlib.Protocols.Sphinx.KEMSphinxTLU
import Cryptlib.Protocols.Sphinx.KEMSphinxTLUStream

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

/-- The replacement request of SLU←: a forward onion along the rest of the backward path, with
no backward path of its own. -/
def BackwardChallenge.swapReq (c : BackwardChallenge hon) (msg : S.Msg) (rcv : S.Receiver) :
    S.Request :=
  { msg := msg, receiver := rcv, fwd := c.req.back.drop c.pos, back := .nil,
    fwd_ne := c.req.back.drop_ne c.pos.isLt }

/-- World 1 of SLU← from the challenger's draws: the first layer of the adversary's onion; the
honest relay sends on the first layer of the replacement in place of the reply's next layer;
and the sender does not answer the replacement's last layer. -/
def BackwardChallenge.world1 (c : BackwardChallenge hon) (r : S.Randomness) (msg : S.Msg)
    (rcv : S.Receiver) (r' : S.Randomness) : World S :=
  let q := c.swapReq msg rcv
  let swap : S.Name × S.Onion := (c.req.back.hops[c.pos].name, S.form q r' q.first)
  let swapAt : Option S.Header := match hk : c.pos.val with
    | 0 => none
    | k + 1 => some (S.formBack c.req r c.req.msg ⟨k, by have := c.pos.isLt; omega⟩).1
  { onion := S.form c.req r c.req.first
    patch :=
      { proc := fun h o out =>
          if h = .sender ∧ o.1 = (S.form q r' q.last).1 then pure none
          else if h = .relay ∧ swapAt = some o.1 then
            pure (out.map fun _ => .forward swap.1 swap.2)
          else pure out
        reply := fun h _ o out =>
          if h = .relay ∧ c.pos.val = 0 ∧ o.1 = (S.form c.req r c.req.last).1 then
            out.map fun _ => swap
          else out } }

/-- World 1 of SLU← draws the randomness, the replacement's message and receiver and its
randomness, and shows `world1`. -/
theorem backwardUnlinkable_world_true (c : BackwardChallenge hon) :
    (backwardUnlinkable (S := S)).world c true
      = (do
        let r ← $ᵗ S.Randomness
        let msg ← $ᵗ S.Msg
        let rcv ← $ᵗ S.Receiver
        let r' ← $ᵗ S.Randomness
        return c.world1 r msg rcv r') := by
  rfl

/-- World 1 of SLU← from the three things it reads off the adversary's onion: its first layer,
the header of the reply's layer at the honest relay (when the relay is on the backward path),
and the header of its last forward layer (when the relay is the exit relay). -/
def BackwardChallenge.world1With (c : BackwardChallenge hon) (onion : S.Onion)
    (own exit : Option S.Header) (msg : S.Msg) (rcv : S.Receiver) (r' : S.Randomness) :
    World S :=
  { onion := onion
    patch :=
      { proc := fun h o out =>
          if h = .sender ∧ o.1 = (S.form (c.swapReq msg rcv) r' (c.swapReq msg rcv).last).1 then
            pure none
          else if h = .relay ∧ own = some o.1 then
            pure (out.map fun _ => .forward (c.req.back.hops[c.pos].name)
              (S.form (c.swapReq msg rcv) r' (c.swapReq msg rcv).first))
          else pure out
        reply := fun h _ o out =>
          if h = .relay ∧ exit = some o.1 then
            out.map fun _ => (c.req.back.hops[c.pos].name,
              S.form (c.swapReq msg rcv) r' (c.swapReq msg rcv).first)
          else out } }

/-- The header of the reply's layer at the honest relay, when the relay is on the backward
path. -/
def BackwardChallenge.ownAt (c : BackwardChallenge hon) (r : S.Randomness) : Option S.Header :=
  match c.pos.val with
  | 0 => none
  | k + 1 => if h : k < c.req.back.hops.length then some (S.formBack c.req r c.req.msg ⟨k, h⟩).1
    else none

/-- The header of the onion's last forward layer, when the honest relay is the exit relay. -/
def BackwardChallenge.exitAt (c : BackwardChallenge hon) (r : S.Randomness) : Option S.Header :=
  if c.pos.val = 0 then some (S.form c.req r c.req.last).1 else none

/-- **World 1 of SLU← reads the adversary's onion through three things.** -/
theorem BackwardChallenge.world1_eq (c : BackwardChallenge hon) (r : S.Randomness) (msg : S.Msg)
    (rcv : S.Receiver) (r' : S.Randomness) :
    c.world1 r msg rcv r'
      = c.world1With (S.form c.req r c.req.first) (c.ownAt r) (c.exitAt r) msg rcv r' := by
  have hlt := c.pos.isLt
  unfold world1 world1With ownAt exitAt
  dsimp only
  congr 2
  · funext h o out
    congr 3
    split <;> rename_i hk
    · simp [hk]
    · rename_i k
      have hkl : k < c.req.back.hops.length := by omega
      simp [hk, hkl]
  · funext h m o out
    by_cases hp : c.pos.val = 0
    · simp [hp, eq_comm]
    · simp [hp]

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

/-- The first layer of `q`'s onion from the reply's first layer, which the sender's payload
carries the header of. -/
def backOnionX (q : RSOR.Request kem geom) (r : RSOR.Randomness geom)
    (hb : 0 < q.back.hops.length) (x0 : Option ByteArray) : RSOR.Onion geom :=
  match x0 with
  | some x0 =>
    (match RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem q.fwd [.recipient
        q.receiver]) r.1
        (bodyH kem geom q r hb (x0.extract 0 geom.headerLength)) 0 with
      | .ok pkt => RSOR.split geom pkt
      | .error _ => default)
  | none => default

/-- **The header of a keyed layer does not use the payload cipher.** With another cipher and
another payload encryption at hop `j`, `layerF` gives a packet with the same bytes in front of
the payload. -/
theorem layerF_header (cipher' : WideBlockCipher) (hops : Array PathHop) (d : RSOR.Draw geom)
    (payload : ByteArray) (j : ℕ) (c U : ByteArray) (tagf encf encf' : ByteArray → ByteArray)
    (i : ℕ) (x : ByteArray)
    (h : layerF kem cipher macS kdfS streamS geom hops d payload j c U tagf encf i = some x)
    (henc : ∀ b, (encf b).size = b.size) :
    ∃ x', layerF kem cipher' macS kdfS streamS geom hops d payload j c U tagf encf' i = some x' ∧
      x'.extract 0 (x.size - (geom.payloadTagLength + geom.forwardPayloadLength))
        = x.extract 0 (x.size - (geom.payloadTagLength + geom.forwardPayloadLength)) := by
  unfold layerF packetF at h ⊢
  refine pktFn_header kem geom _ _ _ _ _ _ _ _ x h fun m b => ?_
  by_cases hm : m = j - i
  · rw [hm, Function.update_self]
    exact henc b
  · rw [Function.update_of_ne hm]
    exact cipher.encrypt_size _ _ _

/-- With the identity for the payload cipher, the keyed layer from a keystream and a tagging
function is the keyed layer for the keys. -/
theorem layerF_id (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (c : ByteArray) (t : KeyTuple) (i : ℕ) :
    layerF kem default macS kdfS streamS geom hops d payload j c (ksOf streamS geom t)
        (tagOf macS t) id i
      = (layerPK kem default macS kdfS streamS geom hops d payload j c t i).toOption :=
  layerF_eq_layerPK kem default macS kdfS streamS geom hops d payload j c t i

/-- The first layer of `q`'s onion, with the KEM ciphertext, header keystream and tagging
function of the relay at backward position `k` given. Those enter through the header of the
reply's first layer. A header does not use the payload cipher, so the reply's layer is built
with the identity in its place. -/
def backOnionF (q : RSOR.Request kem geom) (r : RSOR.Randomness geom)
    (hb : 0 < q.back.hops.length) (k : ℕ) (c U : ByteArray) (tagf : ByteArray → ByteArray) :
    RSOR.Onion geom :=
  backOnionX kem cipher macS kdfS streamS geom q r hb (layerF kem default macS kdfS streamS geom
      (RSOR.path kem q.back [.surbReply r.2.2.2]) r.2.1
    ⟨Array.replicate geom.forwardPayloadLength 0⟩ k c U tagf id 0)

/-- **With the keys that the seed `s` gives at backward position `k`, the keyed first layer is
the first layer of `q`'s onion** built from the randomness with `s` at that position. -/
theorem backOnionF_real (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (q : RSOR.Request kem geom) (r : RSOR.Randomness geom) (hb : 0 < q.back.hops.length)
    (k : ℕ) (hk : k < q.back.hops.length) (s : Vector UInt8 32) (c ss x0 : ByteArray)
    (henc : kemEncap kem ((RSOR.path kem q.back [.surbReply r.2.2.2])[k]!).publicKey s = .ok (c,
        ss))
    (hx0 : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem q.back [.surbReply r.2.2.2])
        (setSeedBack geom r k s).2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0 = .ok x0) :
    backOnionF kem cipher macS kdfS streamS geom q r hb k c (ksOf streamS geom (keyTuple
        (deriveHopKeys kdfS ss))) (tagOf macS (keyTuple (deriveHopKeys kdfS ss)))
      = RSOR.form kem cipher macS kdfS streamS geom q (setSeedBack geom r k s) q.first := by
  have hF := layerF_real kem cipher macS kdfS streamS geom (RSOR.path kem q.back [.surbReply
      r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ x0 k 0 s c ss (Nat.zero_le _)
    (by rw [RSOR.path_size]; exact hk)
    (by rw [RSOR.path_size]; exact q.back.length_le) henc hx0
  obtain ⟨x', hx', hext⟩ := layerF_header kem cipher macS kdfS streamS geom default (RSOR.path kem
      q.back [.surbReply r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k c
    (ksOf streamS geom (keyTuple (deriveHopKeys kdfS ss))) (tagOf macS (keyTuple (deriveHopKeys
        kdfS ss))) (encOf cipher (keyTuple (deriveHopKeys kdfS ss))) id 0 x0 hF
    (fun b => cipher.encrypt_size _ _ _)
  rw [(RSOR.join_split_layer kem cipher macS kdfS streamS geom hvalid hmactag _ _ _ _ _ hx0).1,
      Nat.add_sub_cancel] at hext
  unfold backOnionF backOnionX RSOR.form
  rw [hx']
  dsimp only
  rw [hext, RSOR.body_eq kem cipher macS kdfS streamS geom hvalid hmactag q (setSeedBack geom r k
      s) _ x0 hb hx0]
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

/-- The header of the reply's layer at backward position `i`, up to the relay at position `k`,
with that relay's KEM ciphertext, header keystream and tagging function given. -/
def backHeaderF (q : RSOR.Request kem geom) (r : RSOR.Randomness geom) (k : ℕ) (c U : ByteArray)
    (tagf : ByteArray → ByteArray) (i : ℕ) : Vector UInt8 geom.headerLength :=
  match layerF kem default macS kdfS streamS geom (RSOR.path kem q.back [.surbReply r.2.2.2]) r.2.1
      ⟨Array.replicate geom.forwardPayloadLength 0⟩ k c U tagf id i with
  | some pkt => (RSOR.split geom pkt).1
  | none => (default : RSOR.Onion geom).1

/-- **A reply layer up to the relay, with the relay's real keys.** With the ciphertext and keys
that the seed `s` gives at backward position `k`, `backHeaderF` is the header of the reply's
layer built from the randomness with `s` at that position. -/
theorem formBack_fst_realF (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
    (q : RSOR.Request kem geom) (r : RSOR.Randomness geom) (m : RSOR.Msg geom) (k : ℕ)
    (hk : k < q.back.hops.length) (i : Fin q.back.hops.length) (hik : i ≤ k)
    (s : Vector UInt8 32) (c ss pkt : ByteArray)
    (henc : kemEncap kem ((RSOR.path kem q.back [.surbReply r.2.2.2])[k]!).publicKey s = .ok (c,
        ss))
    (hpkt : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem q.back [.surbReply
        r.2.2.2]) (setSeedBack geom r k s).2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ i =
        .ok pkt) :
    (RSOR.formBack kem cipher macS kdfS streamS geom q (setSeedBack geom r k s) m i).1
      = backHeaderF kem macS kdfS streamS geom q r k c (ksOf streamS geom (keyTuple
          (deriveHopKeys kdfS ss))) (tagOf macS (keyTuple (deriveHopKeys kdfS ss))) i := by
  have hF := layerF_real kem cipher macS kdfS streamS geom (RSOR.path kem q.back [.surbReply
      r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ pkt k i s c ss hik
    (by rw [RSOR.path_size]; exact hk)
    (by rw [RSOR.path_size]; exact q.back.length_le) henc hpkt
  obtain ⟨x', hx', hext⟩ := layerF_header kem cipher macS kdfS streamS geom default (RSOR.path kem
      q.back [.surbReply r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k c
    (ksOf streamS geom (keyTuple (deriveHopKeys kdfS ss))) (tagOf macS (keyTuple (deriveHopKeys
        kdfS ss))) (encOf cipher (keyTuple (deriveHopKeys kdfS ss))) id i pkt hF
    (fun b => cipher.encrypt_size _ _ _)
  rw [(RSOR.join_split_layer kem cipher macS kdfS streamS geom hvalid hmactag _ _ _ _ _ hpkt).1,
      Nat.add_sub_cancel] at hext
  have hL : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem q.back [.surbReply
      (setSeedBack geom r k s).2.2.2])
      (setSeedBack geom r k s).2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ i = .ok pkt :=
    hpkt
  rw [RSOR.formBack_fst kem cipher macS kdfS streamS geom hvalid hmactag, hL]
  unfold backHeaderF
  rw [hx']
  show (RSOR.split geom pkt).1 = (RSOR.split geom x').1
  unfold RSOR.split
  dsimp only
  rw [hext]

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

set_option maxHeartbeats 2000000 in
/-- **World 1 of SLU← as its draws**, with the seed of the honest relay's layer drawn on its
own, and then the adversary's guess against the honest relays. -/
theorem backward_play_true_evalDistEq (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary) :
    Protocols.RSOR.Property.play names A true
      =ᵈ propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ (shortDraw geom) A >>= fun d
          =>
        (simulateQ (Protocols.RSOR.honest
            (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay names d.k.1 d.keys)
            (fun h => if h = .relay then d.k.2 else (d.keys h).2)
            (Protocols.RSOR.BackwardChallenge.world1 d.c
              (relaySeed kem geom d.c.req d.c.pos d.o.1 d.s) d.o.2.1 d.o.2.2.1 d.o.2.2.2).patch)
          (A.guess d.st (Protocols.RSOR.BackwardChallenge.world1 d.c
            (relaySeed kem geom d.c.req d.c.pos d.o.1 d.s) d.o.2.1 d.o.2.2.1
            d.o.2.2.2).onion)).run' d.log := by
  refine (play_evalDistEq_honAt kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names A true).trans ?_
  unfold Protocols.RSOR.Property.playFrom propDrawOf
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun k₁ =>
    EvalDistEq.bind_right _ fun k₂ => EvalDistEq.bind_right _ fun out => ?_
  have hcong : ∀ (m m' : ProbComp (Protocols.RSOR.World 𝒮))
      (F : Protocols.RSOR.World 𝒮 → ProbComp Bool), m = m' → m >>= F =ᵈ m' >>= F :=
    fun _ _ _ h => h ▸ EvalDistEq.rfl
  refine (hcong _ _ _ (Protocols.RSOR.backwardUnlinkable_world_true (S := 𝒮) out.1.1)).trans ?_
  simp only [shortDraw, bind_assoc, pure_bind]
  refine EvalDistEq.symm ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact evalDistEq_relaySeed kem geom out.1.1.req out.1.1.pos out.1.1.pos.isLt fun r =>
    $ᵗ (RSOR.Msg geom) >>= fun m => $ᵗ RSOR.Name >>= fun n =>
      $ᵗ (RSOR.Randomness geom) >>= fun r' =>
        (simulateQ (Protocols.RSOR.honest
            (honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay names k.1 (keysOf
                kem .relay k₁ k₂))
            (fun h => if h = .relay then k.2 else (keysOf kem .relay k₁ k₂ h).2)
            (Protocols.RSOR.BackwardChallenge.world1 out.1.1 r m n r').patch)
          (A.guess out.1.2
            (Protocols.RSOR.BackwardChallenge.world1 out.1.1 r m n r').onion)).run' out.2

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
        (ofVector (kem.encodeCiphertext c)) (ksOf streamS geom t) (tagOf macS t)
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

/-! ## The MAC step for world 0 -/

variable {kem cipher macS kdfS streamS geom hvalid hmactag h16} in
/-- The challenge of a draw of a property's keyed game. -/
def propChOf {P : Protocols.RSOR.Property 𝒮} {ρ : Role} {names : Role → RSOR.Name} {Oth : Type}
    {draw : ProbComp Oth}
    {view : {pk : Key kem} → PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
        pk → Oth → kem.Ciphertext → KeyTuple
      → Protocols.RSOR.World 𝒮}
    {A : P.Adversary} (d : KeyedDraw (propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag
        h16 P ρ names Oth draw view A)) :
    PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names d.k.1 :=
  d.cs.1

variable {kem cipher macS kdfS streamS geom hvalid hmactag h16} in
/-- The challenger's own draws of a draw of a property's keyed game. -/
def propOthOf {P : Protocols.RSOR.Property 𝒮} {ρ : Role} {names : Role → RSOR.Name} {Oth : Type}
    {draw : ProbComp Oth}
    {view : {pk : Key kem} → PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16 P ρ names
        pk → Oth → kem.Ciphertext → KeyTuple
      → Protocols.RSOR.World 𝒮}
    {A : P.Adversary} (d : KeyedDraw (propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag
        h16 P ρ names Oth draw view A)) : Oth :=
  d.o

/-- The bytes of the honest relay's own layer which its MAC covers, from its keys other than
its MAC key: of the last forward layer at the exit, of the reply's layer on the backward
path. -/
def backM0 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (rest : RestKeys) : ByteArray :=
  match ch.c.pos.val with
  | 0 => relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
      ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
      (ch.c.req.fwd.hops.length - 1) (ofVector (kem.encodeCiphertext c)) (ksOf streamS geom
      (withMAC rest default))
  | k + 1 => relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back
      [.surbReply r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
      (kem.encodeCiphertext c)) (ksOf streamS geom (withMAC rest default))

/-- World 0 of SLU←, from the tag of those bytes. -/
def backViewT0 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (rest : RestKeys)
    (tag : Vector UInt8 macS.tagSize) : Protocols.RSOR.World 𝒮 :=
  match ch.c.pos.val with
  | 0 =>
    { onion := RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom (RSOR.path kem
        ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1 0 (ch.c.req.fwd.hops.length - 1)
        (relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
            (ch.c.req.fwd.hops.length - 1) (ofVector (kem.encodeCiphertext c)) (ksOf streamS geom
            (withMAC rest default))
          ++ ofVector tag
          ++ relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
              ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
              (ch.c.req.fwd.hops.length - 1) (ksOf streamS geom (withMAC rest default)) (encOf
              cipher (withMAC rest default))))
      patch := (Protocols.RSOR.BackwardChallenge.world0 ch.c r).patch }
  | k + 1 =>
    { onion := backOnionX kem cipher macS kdfS streamS geom ch.c.req r (Nat.zero_lt_of_lt
        ch.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            r.2.2.2]) r.2.1 0 k
          (relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
              r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
              (kem.encodeCiphertext c)) (ksOf streamS geom (withMAC rest default))
            ++ ofVector tag
            ++ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back
                [.surbReply r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ksOf
                streamS geom (withMAC rest default)) (encOf default (withMAC rest default)))))
      patch :=
        { proc := fun (h : Role) (o : RSOR.Onion geom) out =>
            if h = .sender ∧ o.1 = backHeaderU kem cipher macS kdfS streamS geom ch.c.req r k (ksOf
                streamS geom (withMAC rest default))
                (ch.c.req.back.hops.length - 1) then pure none
            else pure out } }

/-- The draws on which the adversary's onion is as the closed form says: the honest relay's
public key is the one its private key gives, its seed does not make the KEM fail, the layers up
to its own can be built, and the seeds in front of it do not make the KEM fail. -/
def backGoodAt (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (sk : kem.PrivateKey) (r : RSOR.Randomness geom) (s : Vector UInt8 32) : Prop :=
  pk.1 = kem.derivePublicKey sk ∧ kem.Reliable (kem.stateFromSeed s) ∧
    match ch.c.pos.val with
    | 0 => (∃ pkt, RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd
        [.recipient ch.c.req.receiver]) (setSeed geom r (ch.c.req.fwd.hops.length - 1) s).1
          (RSOR.body kem macS kdfS streamS geom ch.c.req (setSeed geom r (ch.c.req.fwd.hops.length
              - 1) s)) 0 = .ok pkt)
        ∧ ∀ m, m < ch.c.req.fwd.hops.length - 1 →
          kem.Reliable (kem.stateFromSeed r.1.1.toArray[m]!)
    | k + 1 => (∃ x0, RSOR.layer kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back
        [.surbReply r.2.2.2]) (setSeedBack geom r k s).2.1 ⟨Array.replicate
        geom.forwardPayloadLength 0⟩ 0 = .ok x0)
        ∧ ∀ m, m < k → kem.Reliable (kem.stateFromSeed r.2.1.1.toArray[m]!)

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 1000000 in
/-- At the exit on such a draw, the adversary's onion and its last forward layer in closed
form, for any keys given to the relay. -/
theorem backGoodAt_exit (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (sk : kem.PrivateKey) (r : RSOR.Randomness geom) (s : Vector UInt8 32)
    (hg : backGoodAt kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch sk r s) (hp :
        ch.c.pos.val = 0) (u : KeyTuple) :
    onionK kem cipher macS kdfS streamS geom ch.c.req r (ch.c.req.fwd.hops.length - 1) (encapOf kem
        pk.1 s).1 u 0
        = RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd
            [.recipient ch.c.req.receiver]) r.1 0 (ch.c.req.fwd.hops.length - 1)
        (relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
            (ch.c.req.fwd.hops.length - 1) (ofVector (kem.encodeCiphertext (encapOf kem pk.1 s).1))
            (ksOf streamS geom u)
          ++ ofVector (macS.mac (ofVector u.2.2.1) (relayFrontAt kem cipher macS kdfS streamS geom
              (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1 (RSOR.body kem macS
              kdfS streamS geom ch.c.req r) (ch.c.req.fwd.hops.length - 1) (ofVector
              (kem.encodeCiphertext (encapOf kem pk.1 s).1)) (ksOf streamS geom u)))
          ++ relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
              ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
              (ch.c.req.fwd.hops.length - 1) (ksOf streamS geom u) (encOf cipher u))) ∧
      onionK kem cipher macS kdfS streamS geom ch.c.req r (ch.c.req.fwd.hops.length - 1) (encapOf
          kem pk.1 s).1 u (ch.c.req.fwd.hops.length - 1)
        = RSOR.split geom
        (relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
            (ch.c.req.fwd.hops.length - 1) (ofVector (kem.encodeCiphertext (encapOf kem pk.1 s).1))
            (ksOf streamS geom u)
          ++ ofVector (macS.mac (ofVector u.2.2.1) (relayFrontAt kem cipher macS kdfS streamS geom
              (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1 (RSOR.body kem macS
              kdfS streamS geom ch.c.req r) (ch.c.req.fwd.hops.length - 1) (ofVector
              (kem.encodeCiphertext (encapOf kem pk.1 s).1)) (ksOf streamS geom u)))
          ++ relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
              ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
              (ch.c.req.fwd.hops.length - 1) (ksOf streamS geom u) (encOf cipher u)) ∧
      (relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
          ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
          (ch.c.req.fwd.hops.length - 1) (ofVector (kem.encodeCiphertext (encapOf kem pk.1 s).1))
          (ksOf streamS geom u)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength := by
  obtain ⟨hpk, hrel, hcase⟩ := hg
  have hrelay := ch.c.relay
  rw [hp] at hcase hrelay
  obtain ⟨⟨pkt, hpkt⟩, hfront⟩ := hcase
  have hj : ch.c.req.fwd.hops.length - 1 < ch.c.req.fwd.hops.length :=
    Nat.sub_one_lt (Nat.ne_of_gt (List.length_pos_iff.2 ch.c.req.fwd_ne))
  have hle : ch.c.req.fwd.hops.length ≤ geom.nrHops := ch.c.req.fwd.length_le
  obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem cipher macS kdfS streamS geom ch.c.req.fwd _ _ _
      pkt hpkt
    (ch.c.req.fwd.hops.length - 1) hj
  have hkey : (ch.c.req.fwd.hops[ch.c.req.fwd.hops.length - 1]'hj).key = pk := by
    have h1 : ch.c.req.fwd.hops[ch.c.req.fwd.hops.length - 1]'hj
        = honAt kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay names pk ch.keys .relay
            :=
      Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans
        (List.getLast?_eq_getElem?.symm.trans hrelay))
    rw [h1]
    rfl
  have hs : (setSeed geom r (ch.c.req.fwd.hops.length - 1) s).1.1.toArray[
      ch.c.req.fwd.hops.length - 1]! = s := by
    simp [setSeed, lt_of_lt_of_le hj hle]
  rw [hs] at henc
  replace henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s = .ok (ct, ss) :=
    (congrArg (fun key : Key kem => kemEncap kem (ofVector (kem.encodePublicKey key.1)) s)
      hkey).symm.trans henc
  obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem pk.1 s ct ss henc
  exact onionK_parts kem cipher macS kdfS streamS geom hvalid hmactag h16 ch.c.req r
      ⟨ch.c.req.fwd.hops.length - 1, hj⟩
    pk sk hkey hpk s hrel _ _ pkt henc hpkt hfront u

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 1000000 in
/-- On the backward path on such a draw, the reply's first layer and its layer at the relay in
closed form, for any keys given to the relay. -/
theorem backGoodAt_back (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (sk : kem.PrivateKey) (r : RSOR.Randomness geom) (s : Vector UInt8 32)
    (hg : backGoodAt kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch sk r s) (k : ℕ)
        (hp : ch.c.pos.val = k + 1) (u : KeyTuple) :
    layerPK kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply r.2.2.2])
        r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector (kem.encodeCiphertext
        (encapOf kem pk.1 s).1)) u 0
        = .ok (wrapUp kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            r.2.2.2]) r.2.1 0 k
        (relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
            (kem.encodeCiphertext (encapOf kem pk.1 s).1)) (ksOf streamS geom u)
          ++ ofVector (macS.mac (ofVector u.2.2.1) (relayFrontAt kem default macS kdfS streamS geom
              (RSOR.path kem ch.c.req.back [.surbReply r.2.2.2]) r.2.1 ⟨Array.replicate
              geom.forwardPayloadLength 0⟩ k (ofVector (kem.encodeCiphertext (encapOf kem pk.1
              s).1)) (ksOf streamS geom u)))
          ++ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
              r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ksOf streamS geom u)
              (encOf default u))) ∧
      (relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
          r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
          (kem.encodeCiphertext (encapOf kem pk.1 s).1)) (ksOf streamS geom u)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength ∧
      layerPK kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply r.2.2.2])
          r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector (kem.encodeCiphertext
          (encapOf kem pk.1 s).1)) u k
        = .ok
        (relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
            (kem.encodeCiphertext (encapOf kem pk.1 s).1)) (ksOf streamS geom u)
          ++ ofVector (macS.mac (ofVector u.2.2.1) (relayFrontAt kem default macS kdfS streamS geom
              (RSOR.path kem ch.c.req.back [.surbReply r.2.2.2]) r.2.1 ⟨Array.replicate
              geom.forwardPayloadLength 0⟩ k (ofVector (kem.encodeCiphertext (encapOf kem pk.1
              s).1)) (ksOf streamS geom u)))
          ++ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
              r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ksOf streamS geom u)
              (encOf default u)) := by
  obtain ⟨hpk, hrel, hcase⟩ := hg
  have hrelay := ch.c.relay
  rw [hp] at hcase hrelay
  obtain ⟨⟨x0, hx0⟩, hfront⟩ := hcase
  have hlt : ch.c.pos.val < ch.c.req.back.hops.length := ch.c.pos.isLt
  have hk : k < ch.c.req.back.hops.length := by omega
  have hle : ch.c.req.back.hops.length ≤ geom.nrHops := ch.c.req.back.length_le
  obtain ⟨ct, ss, henc⟩ := layer_zero_encap kem default macS kdfS streamS geom ch.c.req.back _ _ _
      x0 hx0 k hk
  have hkey : (ch.c.req.back.hops[k]'hk).key = pk := by
    have h1 : ch.c.req.back.hops[k]'hk = honAt kem cipher macS kdfS streamS geom hvalid hmactag h16
        .relay names pk ch.keys .relay :=
      Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hrelay)
    rw [h1]
    rfl
  have hs : (setSeedBack geom r k s).2.1.1.toArray[k]! = s := by
    simp [setSeedBack, lt_of_lt_of_le hk hle]
  rw [hs] at henc
  replace henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s = .ok (ct, ss) :=
    (congrArg (fun key : Key kem => kemEncap kem (ofVector (kem.encodePublicKey key.1)) s)
      hkey).symm.trans henc
  obtain ⟨rfl, rfl⟩ := kemEncap_encapOf kem pk.1 s ct ss henc
  exact routeK_parts kem default macS kdfS streamS geom hvalid hmactag h16 ch.c.req.back [.surbReply
      r.2.2.2]
    (fun x hx => by
      rw [List.mem_singleton.1 hx]
      exact ⟨by simp, by simp⟩)
    r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k hk pk sk hkey hpk s hrel _
    _ x0 henc hx0 hfront u

/-- The good draws of world 0's keyed game. -/
def backGood0 {names : Role → RSOR.Name} {A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary}
    (d : KeyedDraw (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) : Prop
        :=
  backGoodAt kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d) d.k.2
      (propOthOf d) d.s

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- On a good draw of world 0, the view uses the honest relay's MAC key for one tag, on bytes
of the length of a header without its tag. -/
theorem backGood0_view (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary)
    (d : KeyedDraw (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) (u :
        KeyTuple)
    (hg : backGood0 kem cipher macS kdfS streamS geom hvalid hmactag h16 d) :
    (backSetup0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names).view d.cs.1 d.o d.c u
        = backViewT0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
            (propOthOf d) d.c (restOf u)
          (macS.mac (ofVector u.2.2.1)
            (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
                (propOthOf d) d.c (restOf u))) ∧
      (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d) (propOthOf d)
          d.c (restOf u)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength := by
  obtain ⟨ch, hch⟩ : ∃ ch, ch = propChOf d := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = propOthOf d := ⟨_, rfl⟩
  unfold backGood0 at hg
  rw [← hch, ← hr] at hg ⊢
  have hv : (backSetup0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names).view d.cs.1 d.o
      d.c u
      = backView0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r d.c u := by
    rw [hch, hr]
    rfl
  rw [hv]
  cases hp : ch.c.pos.val with
  | zero =>
    obtain ⟨hz, -, hsize⟩ := backGoodAt_exit kem cipher macS kdfS streamS geom hvalid hmactag h16
        names ch d.k.2 r d.s hg hp u
    unfold backView0 backViewT0 backM0
    rw [hp]
    dsimp only
    refine ⟨?_, hsize⟩
    rw [show onionK kem cipher macS kdfS streamS geom ch.c.req r (ch.c.req.fwd.hops.length - 1) d.c
        u 0 = _ from hz]
    rfl
  | succ k =>
    obtain ⟨hz, hsize, -⟩ := backGoodAt_back kem cipher macS kdfS streamS geom hvalid hmactag h16
        names ch d.k.2 r d.s hg k hp u
    unfold backView0 backViewT0 backM0 backOnionF
    rw [hp]
    dsimp only
    rw [layerF_id, show layerPK kem default macS kdfS streamS geom (RSOR.path kem
        ch.c.req.back [.surbReply r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k
      (ofVector (kem.encodeCiphertext d.c)) u 0 = _ from hz]
    exact ⟨rfl, hsize⟩

/-- **The MAC step for world 0 of SLU←.** With uniform keys at the honest relay, the relay may
answer the challenge ciphertext under its own header only, at the cost of a forgery against
the MAC and of the draws that are not good. -/
theorem backward0_keyedIdeal_sub_tagged_le (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
        (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
      - (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS
          streamS geom hvalid hmactag h16 names A)
          (onlyHeader cipher macS streamS geom (tagged macS
            (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[x =
                true]).toReal|
    ≤ (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
          (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A) (backM0 kem
              cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (backViewT0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names)))}[x =
              true]).toReal
      + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
          (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[¬ backGood0 kem
              cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal :=
  keyedIdeal_sub_tagged_le cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS streamS
      geom hvalid hmactag h16 names A) hmactag
    (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) (backViewT0 kem cipher macS
        kdfS streamS geom hvalid hmactag h16 names) (backGood0 kem cipher macS kdfS streamS geom
        hvalid hmactag h16)
    (fun d r hg => (backGood0_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A d
        (withMAC r default) hg).2)
    (fun d u hg => (backGood0_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A d u
        hg).1)
    (fun _ _ _ _ _ => rfl)

/-! ## The payload cipher step for world 0 -/

omit [SampleableType kem.Plaintext] in
/-- The bytes the relay's MAC covers have its ciphertext in the ciphertext field, when they
have a header's length. -/
theorem backM0_ct (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (rest : RestKeys)
    (hs : (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c rest).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength) :
    (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c rest).extract 2 (2 +
        kem.ciphertextSize)
      = ofVector (kem.encodeCiphertext c) := by
  revert hs
  unfold backM0
  cases ch.c.pos.val with
  | zero => exact relayFrontAt_ct _ _ _ _ _ _ _ _ _ _ _ _ (Cryptlib.Util.Bytes.size_ofVector _)
  | succ k => exact relayFrontAt_ct _ _ _ _ _ _ _ _ _ _ _ _ (Cryptlib.Util.Bytes.size_ofVector _)

/-- The block the sender encrypts under the honest relay's payload key in world 0. At the exit
it is the bytes behind the relay's tag, before that encryption. On the backward path there is
none: the relay's payload key only decrypts. -/
def backBlock0 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (r : RSOR.Randomness geom) (k : (Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32)) : Block
        geom :=
  match ch.c.pos.val with
  | 0 => Util.Bytes.toVecN _ (relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem
      ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom
      ch.c.req r) (ch.c.req.fwd.hops.length - 1)
      (ksOf streamS geom (default, k)) id)
  | _ + 1 => default

/-- World 0 from the encrypted block. On the backward path the world does not use it. -/
def backViewE0 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (k : (Vector UInt8 16 × Vector UInt8 32 ×
        Vector UInt8 32)) (e : Block geom) :
    Protocols.RSOR.World 𝒮 :=
  match ch.c.pos.val with
  | 0 =>
    { onion := RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom (RSOR.path kem
        ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1 0 (ch.c.req.fwd.hops.length - 1)
        (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c (default, k.1,
            k.2.2)
          ++ ofVector (macS.mac (ofVector k.2.1)
            (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c (default,
                k.1, k.2.2)))
          ++ ofVector e))
      patch := (Protocols.RSOR.BackwardChallenge.world0 ch.c r).patch }
  | _ + 1 => backViewT0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r c (default,
      k.1, k.2.2)
      (macS.mac (ofVector k.2.1) (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          ch r c (default, k.1, k.2.2)))

/-- The good draws of world 0 on which, at the exit, the block has a payload's length. -/
def backGoodP0 {names : Role → RSOR.Name} {A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary}
    (d : KeyedDraw (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) : Prop
        :=
  backGood0 kem cipher macS kdfS streamS geom hvalid hmactag h16 d ∧ ((propChOf d).c.pos.val = 0 →
      ∀ k : (Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32),
    (relayBackAt kem cipher macS kdfS streamS geom
      (RSOR.path kem (propChOf d).c.req.fwd [.recipient (propChOf d).c.req.receiver])
      (propOthOf d).1
      (RSOR.body kem macS kdfS streamS geom (propChOf d).c.req (propOthOf d))
      ((propChOf d).c.req.fwd.hops.length - 1) (ksOf streamS geom (default, k)) id).size
    = geom.payloadTagLength + geom.forwardPayloadLength)

/-- World 0 with a one-header relay, as a payload game. -/
def backGameP0 (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary) :
    PayloadGame kem cipher macS kdfS streamS geom hvalid hmactag h16 :=
  propPayloadGame kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness geom) ($ᵗ
      RSOR.Randomness geom)
    (backView0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) A (backM0 kem cipher
        macS kdfS streamS geom hvalid hmactag h16 names)
    (fun ch r _ k => backBlock0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r k)
        (backViewE0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names)

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- **The payload cipher step for world 0 of SLU←.** With uniform keys at the honest relay and
its own header only, world 0 is its payload game with the ideal cipher, up to the one-block
advantage of that game's adversary against the cipher and the chance of a draw that is not
good. -/
theorem backward0_payload_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S
    := 𝒮)).Adversary) :
    |(Pr{let x ← (keyedGameH cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS streamS
        geom hvalid hmactag h16 names A)
          (onlyHeader cipher macS streamS geom (tagged macS
            (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[x =
                true]).toReal
      - (Pr{let x ← ((backGameP0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).exp
          false)}[x = true]).toReal|
    ≤ |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv true)}[x =
              true]).toReal
        - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv false)}[x =
              true]).toReal|
      + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
        (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[¬ backGoodP0 kem
            cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal := by
  refine prop_tagged_sub_ideal_le kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names
    (RSOR.Randomness geom) ($ᵗ RSOR.Randomness geom) (backView0 kem cipher macS kdfS streamS geom
        hvalid hmactag h16 names) A _ _ _
    (backGoodP0 kem cipher macS kdfS streamS geom hvalid hmactag h16)
    (fun ch o c kp kp' iv ke => rfl)
    (fun d r hg => (backGood0_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A d
        (withMAC r default) hg.1).2)
    (fun d r hg => backM0_ct kem cipher macS kdfS streamS geom hvalid hmactag h16 names _ _ _ _
      (backGood0_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A d (withMAC r
          default) hg.1).2)
    (fun d u hg => ?_)
  refine (backGood0_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A d u
      hg.1).1.trans ?_
  have hP := hg.2
  show backViewT0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
      (propOthOf d) d.c (restOf u)
      (macS.mac (ofVector u.2.2.1)
        (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d) (propOthOf
            d) d.c (restOf u)))
    = backViewE0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d) (propOthOf
        d) d.c u.2 (Util.Bytes.toVecN _
      (cipher.encrypt u.1.toArray (ofVector u.2.1)
        (ofVector (backBlock0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf
            d) (propOthOf d) u.2))))
  generalize propChOf d = ch at hP ⊢
  generalize propOthOf d = r at hP ⊢
  cases hp : ch.c.pos.val with
  | zero =>
    replace hP := hP hp u.2
    have hb : relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
        ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
        (ch.c.req.fwd.hops.length - 1)
          (ksOf streamS geom (withMAC (restOf u) default))
          (encOf cipher (withMAC (restOf u) default))
        = ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
          (cipher.encrypt u.1.toArray (ofVector u.2.1)
            (ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
              (relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd
                  [.recipient ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom
                  ch.c.req r) (ch.c.req.fwd.hops.length - 1)
                (ksOf streamS geom (default, u.2)) id))))) := by
      have e1 := relayBackAt_enc kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd
          [.recipient ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
          (ch.c.req.fwd.hops.length - 1)
        (ksOf streamS geom (default, u.2))
        (encOf cipher (withMAC (restOf u) default)) (by rw [hP]; omega)
      refine e1.trans ?_
      rw [Cryptlib.Util.Bytes.ofVector_toVecN _ hP, Cryptlib.Util.Bytes.ofVector_toVecN _
        (by rw [cipher.encrypt_size]; exact hP)]
      rfl
    unfold backViewT0 backViewE0 backM0 backBlock0
    rw [hp]
    dsimp only
    rw [hb]
    rfl
  | succ k =>
    unfold backViewE0 backViewT0 backM0
    rw [hp]
    rfl

/-! ## World 1 around the honest relay's ciphertext -/

/-- World 1 of SLU← around the honest relay's ciphertext and keys: `world1With` at the keyed
first layer, the keyed header of the relay's own reply layer, and the keyed header of the
relay's own forward layer. -/
def backView1 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (o : RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)
    (c : kem.Ciphertext) (t : KeyTuple) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1With ch.c
    (match ch.c.pos.val with
      | 0 => onionK kem cipher macS kdfS streamS geom ch.c.req o.1 (ch.c.req.fwd.hops.length - 1) c
          t 0
      | k + 1 => backOnionF kem cipher macS kdfS streamS geom ch.c.req o.1 (Nat.zero_lt_of_lt
          ch.c.pos.isLt) k
          (ofVector (kem.encodeCiphertext c)) (ksOf streamS geom t) (tagOf macS t))
    (match ch.c.pos.val with
      | 0 => none
      | k + 1 => if k < ch.c.req.back.hops.length then
          some (backHeaderF kem macS kdfS streamS geom ch.c.req o.1 k (ofVector
              (kem.encodeCiphertext c))
            (ksOf streamS geom t) (tagOf macS t) k)
        else none)
    (if ch.c.pos.val = 0 then
        some (onionK kem cipher macS kdfS streamS geom ch.c.req o.1 (ch.c.req.fwd.hops.length - 1)
            c t
          (ch.c.req.fwd.hops.length - 1)).1
      else none)
    o.2.1 o.2.2.1 o.2.2.2

/-- The keyed game of world 1 of SLU← around the honest relay's ciphertext. -/
abbrev backSetup1 (names : Role → RSOR.Name) :
    KeyedSetup kem (Protocols.RSOR.World 𝒮) Bool :=
  propSetupOf kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ (shortDraw geom) (backView1 kem
      cipher macS kdfS streamS geom hvalid hmactag h16 names)

/-- The adversary of that keyed game. -/
abbrev backAdv1 (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary) :
    KeyedAdversary (backSetup1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) :=
  propAdvOf kem cipher macS kdfS streamS geom hvalid hmactag h16 (Protocols.RSOR.backwardUnlinkable
      (S := 𝒮)) .relay names _ _ _ A

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 1000000 in
/-- **On the backward path, the keyed world 1 with the real keys is world 1.** -/
theorem backView1_real_back (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (o : RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)
    (k : ℕ) (hp : ch.c.pos.val = k + 1) (s : Vector UInt8 32)
    (c : kem.Ciphertext) (ss x0 xk : ByteArray)
    (henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s
      = .ok (ofVector (kem.encodeCiphertext c), ss))
    (hx0 : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
        o.1.2.2.2])
      (setSeedBack geom o.1 k s).2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0 = .ok x0)
    (hxk : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
        o.1.2.2.2])
      (setSeedBack geom o.1 k s).2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k = .ok xk) :
    backView1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c (keyTuple
        (deriveHopKeys kdfS ss))
      = Protocols.RSOR.BackwardChallenge.world1 ch.c (setSeedBack geom o.1 k s) o.2.1 o.2.2.1
        o.2.2.2 := by
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
  have hpub : ((RSOR.path kem ch.c.req.back [.surbReply o.1.2.2.2])[k]!).publicKey
      = ofVector (kem.encodePublicKey pk.1) := by
    rw [RSOR.path_getElem! kem _ _ _ hk]
    exact congrArg (fun key : Key kem => ofVector (kem.encodePublicKey key.1)) hkey
  have henc' : kemEncap kem ((RSOR.path kem ch.c.req.back [.surbReply o.1.2.2.2])[k]!).publicKey
      s = .ok (ofVector (kem.encodeCiphertext c), ss) := by
    rw [hpub]
    exact henc
  have honion := backOnionF_real kem cipher macS kdfS streamS geom hvalid hmactag ch.c.req o.1
      (Nat.zero_lt_of_lt hlt) k hk
    s _ ss x0 henc' hx0
  have hown := formBack_fst_realF kem cipher macS kdfS streamS geom hvalid hmactag ch.c.req o.1
      ch.c.req.msg k hk ⟨k, hk⟩
    le_rfl s _ ss xk henc' hxk
  refine Eq.trans ?_ (Protocols.RSOR.BackwardChallenge.world1_eq (S := 𝒮) ch.c
    (setSeedBack geom o.1 k s) o.2.1 o.2.2.1 o.2.2.2).symm
  unfold backView1 Protocols.RSOR.BackwardChallenge.ownAt Protocols.RSOR.BackwardChallenge.exitAt
  rw [hp]
  dsimp only
  rw [ite_eq_left hk, dite_eq_left hk, ite_eq_right (Nat.succ_ne_zero k),
    ite_eq_right (Nat.succ_ne_zero k), honion, ← hown]
  rfl

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 1000000 in
/-- **At the exit, the keyed world 1 with the real keys is world 1.** -/
theorem backView1_real_exit (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (o : RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)
    (hp : ch.c.pos.val = 0) (s : Vector UInt8 32) (c : kem.Ciphertext) (ss pkt pktL : ByteArray)
    (henc : kemEncap kem (ofVector (kem.encodePublicKey pk.1)) s
      = .ok (ofVector (kem.encodeCiphertext c), ss))
    (hpkt : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
        ch.c.req.receiver])
      (setSeed geom o.1 (ch.c.req.fwd.hops.length - 1) s).1
      (RSOR.body kem macS kdfS streamS geom ch.c.req
        (setSeed geom o.1 (ch.c.req.fwd.hops.length - 1) s)) 0 = .ok pkt)
    (hpktL : RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
        ch.c.req.receiver])
      (setSeed geom o.1 (ch.c.req.fwd.hops.length - 1) s).1
      (RSOR.body kem macS kdfS streamS geom ch.c.req
        (setSeed geom o.1 (ch.c.req.fwd.hops.length - 1) s))
      (ch.c.req.fwd.hops.length - 1) = .ok pktL) :
    backView1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c (keyTuple
        (deriveHopKeys kdfS ss))
      = Protocols.RSOR.BackwardChallenge.world1 ch.c
        (setSeed geom o.1 (ch.c.req.fwd.hops.length - 1) s) o.2.1 o.2.2.1 o.2.2.2 := by
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
  have honion := onionK_real kem cipher macS kdfS streamS geom ch.c.req o.1
      ⟨ch.c.req.fwd.hops.length - 1, hj⟩
    ch.c.req.first (Nat.zero_le _) pk hkey s c ss pkt henc hpkt
  have hlast := onionK_real kem cipher macS kdfS streamS geom ch.c.req o.1
      ⟨ch.c.req.fwd.hops.length - 1, hj⟩
    ch.c.req.last le_rfl pk hkey s c ss pktL henc hpktL
  refine Eq.trans ?_ (Protocols.RSOR.BackwardChallenge.world1_eq (S := 𝒮) ch.c
    (setSeed geom o.1 (ch.c.req.fwd.hops.length - 1) s) o.2.1 o.2.2.1 o.2.2.2).symm
  unfold backView1 Protocols.RSOR.BackwardChallenge.ownAt Protocols.RSOR.BackwardChallenge.exitAt
  rw [hp]
  dsimp only
  rw [ite_eq_left rfl, ite_eq_left rfl]
  exact congrArg₂ (fun (on : RSOR.Onion geom) (ex : Vector UInt8 geom.headerLength) =>
    Protocols.RSOR.BackwardChallenge.world1With (S := 𝒮) ch.c on none (some ex) o.2.1 o.2.2.1
      o.2.2.2) honion (congrArg Prod.fst hlast)

omit [SampleableType kem.Plaintext] in
/-- The draws of world 1 that the exact steps do not cover: as `backBad0`, and the honest
relay's own layer cannot be built. -/
def backBad1 {names : Role → RSOR.Name} {A : (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary}
    (d : PropDraw kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names
      (RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom) A) : Prop :=
  ¬ (d.k.1.1 = kem.derivePublicKey d.k.2 ∧ kem.Reliable (kem.stateFromSeed d.s) ∧
    match d.c.pos.val with
    | 0 => ∃ pkt pktL, RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem d.c.req.fwd [.recipient d.c.req.receiver])
          (setSeed geom d.o.1 (d.c.req.fwd.hops.length - 1) d.s).1
          (RSOR.body kem macS kdfS streamS geom d.c.req
            (setSeed geom d.o.1 (d.c.req.fwd.hops.length - 1) d.s)) 0 = .ok pkt
        ∧ RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem d.c.req.fwd [.recipient d.c.req.receiver])
          (setSeed geom d.o.1 (d.c.req.fwd.hops.length - 1) d.s).1
          (RSOR.body kem macS kdfS streamS geom d.c.req
            (setSeed geom d.o.1 (d.c.req.fwd.hops.length - 1) d.s))
          (d.c.req.fwd.hops.length - 1) = .ok pktL
    | k + 1 => ∃ x0 xk, RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem d.c.req.back [.surbReply d.o.1.2.2.2])
          (setSeedBack geom d.o.1 k d.s).2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ 0
            = .ok x0
        ∧ RSOR.layer kem cipher macS kdfS streamS geom
          (RSOR.path kem d.c.req.back [.surbReply d.o.1.2.2.2])
          (setSeedBack geom d.o.1 k d.s).2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k
            = .ok xk)

set_option maxHeartbeats 2000000 in
/-- **World 1 of SLU← is the keyed game with the real keys, off the bad draws.** -/
theorem backward_true_sub_keyedReal_le (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A true}[x = true]).toReal
      - (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
          (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
    ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ (shortDraw geom)
        A)}[backBad1 kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal := by
  rw [(backward_play_true_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).prEvent_eq (fun x => x = true),
    (keyedReal_propAdvOf_evalDistEq kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ _ _ A).prEvent_eq
      (fun x => x = true)]
  refine prEvent_bind_toReal_sub_le_of_bad _ _ _
    (backBad1 kem cipher macS kdfS streamS geom hvalid hmactag h16) (fun d hd => ?_) (fun x => x =
        true)
  obtain ⟨hpk, hrel, hbuild⟩ := Classical.not_not.mp hd
  have hrelay := d.c.relay
  cases hp : d.c.pos.val with
  | zero =>
    rw [hp] at hbuild hrelay
    obtain ⟨pkt, pktL, hpkt, hpktL⟩ := hbuild
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
    have hs : (setSeed geom d.o.1 (d.c.req.fwd.hops.length - 1) d.s).1.1.toArray[
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
    have hview := backView1_real_exit kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        ⟨d.keys, d.c⟩ d.o hp d.s _ _ pkt pktL henc
      hpkt hpktL
    have hseed : relaySeed kem geom d.c.req 0 d.o.1 d.s
        = setSeed geom d.o.1 (d.c.req.fwd.hops.length - 1) d.s := rfl
    rw [propAdv_post kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ _ _ A d.k d.keys _ _ hdec d.st
        d.log _, hseed,
      ← hview]
    rfl
  | succ k =>
    rw [hp] at hbuild hrelay
    obtain ⟨x0, xk, hx0, hxk⟩ := hbuild
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
    have hs : (setSeedBack geom d.o.1 k d.s).2.1.1.toArray[k]! = d.s := by
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
    have hview := backView1_real_back kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        ⟨d.keys, d.c⟩ d.o k hp d.s _ _ x0 xk henc
      hx0 hxk
    have hseed : relaySeed kem geom d.c.req (k + 1) d.o.1 d.s = setSeedBack geom d.o.1 k d.s :=
      rfl
    rw [propAdv_post kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ _ _ A d.k d.keys _ _ hdec d.st
        d.log _, hseed,
      ← hview]
    rfl

/-- **The honest relay's keys in world 1 of SLU← may be uniform.** World 1 differs from the
keyed game with uniform keys at the relay by at most the chance of a bad draw and the cost of
replacing the keys (KEM and KDF). -/
theorem backward_true_sub_keyedIdeal_le (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← Protocols.RSOR.Property.play names A true}[x = true]).toReal
      - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
          (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
    ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ (shortDraw geom)
        A)}[backBad1 kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
      + keyedCost cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS streamS geom hvalid
          hmactag h16 names A) := by
  have h1 := backward_true_sub_keyedReal_le kem cipher macS kdfS streamS geom hvalid hmactag h16
      names A
  have h2 := keyedChain_le cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS streamS
      geom hvalid hmactag h16 names A)
  have t := abs_sub_le
    (Pr{let x ← Protocols.RSOR.Property.play names A true}[x = true]).toReal
    (Pr{let x ← (keyedReal cipher macS kdfS streamS geom
      (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
    (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
      (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
  linarith

/-- **SLU← with uniform keys at the honest relay.** The advantage is at most the chance of a
bad draw in each world, the cost of replacing the relay's keys in each world (KEM and KDF),
and the distance between the two keyed games with uniform keys. -/
theorem backwardUnlinkable_le_keyedIdeal (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary) :
    ((Protocols.RSOR.backwardUnlinkable (S := 𝒮)).advantage names A).toReal
      ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness geom)
          ($ᵗ RSOR.Randomness geom) A)}[backBad0 kem cipher macS kdfS streamS geom hvalid hmactag
              h16 d]).toReal
        + (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ (shortDraw geom)
          A)}[backBad1 kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + keyedCost cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS streamS geom
            hvalid hmactag h16 names A)
        + keyedCost cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS streamS geom
            hvalid hmactag h16 names A)
        + |(Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
            (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
                true]).toReal
          - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
            (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
                true]).toReal| := by
  refine (Protocols.RSOR.Property.advantage_toReal
    (P := Protocols.RSOR.backwardUnlinkable (S := 𝒮)) names A).le.trans ?_
  have h0 := backward_false_sub_keyedIdeal_le kem cipher macS kdfS streamS geom hvalid hmactag h16
      names A
  have h1 := backward_true_sub_keyedIdeal_le kem cipher macS kdfS streamS geom hvalid hmactag h16
      names A
  have t1 := abs_sub_le
    (Pr{let x ← Protocols.RSOR.Property.play names A true}[x = true]).toReal
    (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
      (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
    (Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
  have t2 := abs_sub_le
    (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
      (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
    (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
      (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
    (Pr{let x ← Protocols.RSOR.Property.play names A false}[x = true]).toReal
  rw [abs_sub_comm] at h0
  linarith

/-! ## The MAC step for world 1 -/

/-- World 1 of SLU←, from the tag of the bytes of the honest relay's own layer which its MAC
covers. -/
def backViewT1 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk) (o : (RSOR.Randomness geom ×
        RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)) (c : kem.Ciphertext)
    (rest : RestKeys) (tag : Vector UInt8 macS.tagSize) : Protocols.RSOR.World 𝒮 :=
  Protocols.RSOR.BackwardChallenge.world1With ch.c
    (match ch.c.pos.val with
      | 0 => RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd
          [.recipient ch.c.req.receiver]) o.1.1 0 (ch.c.req.fwd.hops.length - 1)
        (relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver]) o.1.1 (RSOR.body kem macS kdfS streamS geom ch.c.req o.1)
            (ch.c.req.fwd.hops.length - 1) (ofVector (kem.encodeCiphertext c)) (ksOf streamS geom
            (withMAC rest default))
          ++ ofVector tag
          ++ relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
              ch.c.req.receiver]) o.1.1 (RSOR.body kem macS kdfS streamS geom ch.c.req o.1)
              (ch.c.req.fwd.hops.length - 1) (ksOf streamS geom (withMAC rest default)) (encOf
              cipher (withMAC rest default))))
      | k + 1 => backOnionX kem cipher macS kdfS streamS geom ch.c.req o.1 (Nat.zero_lt_of_lt
          ch.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            o.1.2.2.2]) o.1.2.1 0 k
        (relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            o.1.2.2.2]) o.1.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
            (kem.encodeCiphertext c)) (ksOf streamS geom (withMAC rest default))
          ++ ofVector tag
          ++ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
              o.1.2.2.2]) o.1.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ksOf streamS
              geom (withMAC rest default)) (encOf default (withMAC rest default))))))
    (match ch.c.pos.val with
      | 0 => none
      | k + 1 => if k < ch.c.req.back.hops.length then
          some (RSOR.split geom
        (relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            o.1.2.2.2]) o.1.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
            (kem.encodeCiphertext c)) (ksOf streamS geom (withMAC rest default))
          ++ ofVector tag
          ++ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
              o.1.2.2.2]) o.1.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ksOf streamS
              geom (withMAC rest default)) (encOf default (withMAC rest default)))).1
        else none)
    (if ch.c.pos.val = 0 then
        some (RSOR.split geom
        (relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver]) o.1.1 (RSOR.body kem macS kdfS streamS geom ch.c.req o.1)
            (ch.c.req.fwd.hops.length - 1) (ofVector (kem.encodeCiphertext c)) (ksOf streamS geom
            (withMAC rest default))
          ++ ofVector tag
          ++ relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
              ch.c.req.receiver]) o.1.1 (RSOR.body kem macS kdfS streamS geom ch.c.req o.1)
              (ch.c.req.fwd.hops.length - 1) (ksOf streamS geom (withMAC rest default)) (encOf
              cipher (withMAC rest default)))).1
      else none)
    o.2.1 o.2.2.1 o.2.2.2

/-- The bytes which the honest relay's MAC covers in world 1: those of world 0. -/
def backM1 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk) (o : (RSOR.Randomness geom ×
        RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)) (c : kem.Ciphertext)
    (rest : RestKeys) : ByteArray :=
  backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o.1 c rest

/-- The good draws of world 1's keyed game. -/
def backGood1 {names : Role → RSOR.Name} {A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary}
    (d : KeyedDraw (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) : Prop
        :=
  backGoodAt kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d) d.k.2
      (propOthOf d).1 d.s

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- On a good draw of world 1, the view uses the honest relay's MAC key for one tag, on the
same bytes as world 0. -/
theorem backGood1_view (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary)
    (d : KeyedDraw (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) (u :
        KeyTuple)
    (hg : backGood1 kem cipher macS kdfS streamS geom hvalid hmactag h16 d) :
    (backSetup1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names).view d.cs.1 d.o d.c u
        = backViewT1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
            (propOthOf d) d.c (restOf u)
          (macS.mac (ofVector u.2.2.1)
            (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
                (propOthOf d) d.c (restOf u))) ∧
      (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d) (propOthOf d)
          d.c (restOf u)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength := by
  obtain ⟨ch, hch⟩ : ∃ ch, ch = propChOf d := ⟨_, rfl⟩
  obtain ⟨o, ho⟩ : ∃ o, o = propOthOf d := ⟨_, rfl⟩
  unfold backGood1 at hg
  rw [← hch, ← ho] at hg ⊢
  have hv : (backSetup1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names).view d.cs.1 d.o
      d.c u
      = backView1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o d.c u := by
    rw [hch, ho]
    rfl
  rw [hv]
  cases hp : ch.c.pos.val with
  | zero =>
    obtain ⟨hz, hjj, hsize⟩ := backGoodAt_exit kem cipher macS kdfS streamS geom hvalid hmactag h16
        names ch d.k.2 o.1 d.s hg hp u
    unfold backView1 backViewT1 backM1 backM0
    rw [hp]
    dsimp only
    refine ⟨?_, hsize⟩
    rw [show onionK kem cipher macS kdfS streamS geom ch.c.req o.1 (ch.c.req.fwd.hops.length - 1)
        d.c u 0 = _ from hz,
      show onionK kem cipher macS kdfS streamS geom ch.c.req o.1 (ch.c.req.fwd.hops.length - 1) d.c
          u (ch.c.req.fwd.hops.length - 1) = _ from hjj]
    rfl
  | succ k =>
    obtain ⟨hz, hsize, hkk⟩ := backGoodAt_back kem cipher macS kdfS streamS geom hvalid hmactag h16
        names ch d.k.2 o.1 d.s hg k hp u
    unfold backView1 backViewT1 backM1 backM0 backOnionF backHeaderF
    rw [hp]
    dsimp only
    rw [layerF_id, layerF_id,
      show layerPK kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
          o.1.2.2.2]) o.1.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
          (kem.encodeCiphertext d.c)) u 0
        = _ from hz,
      show layerPK kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
          o.1.2.2.2]) o.1.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
          (kem.encodeCiphertext d.c)) u k
        = _ from hkk]
    exact ⟨rfl, hsize⟩

/-- **The MAC step for world 1 of SLU←.** -/
theorem backward1_keyedIdeal_sub_tagged_le (names : Role → RSOR.Name)
    (A : (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom
        (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
      - (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS
          streamS geom hvalid hmactag h16 names A)
          (onlyHeader cipher macS streamS geom (tagged macS
            (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[x =
                true]).toReal|
    ≤ (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
          (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A) (backM1 kem
              cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (backViewT1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names)))}[x =
              true]).toReal
      + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
          (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[¬ backGood1 kem
              cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal :=
  keyedIdeal_sub_tagged_le cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS streamS
      geom hvalid hmactag h16 names A) hmactag
    (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) (backViewT1 kem cipher macS
        kdfS streamS geom hvalid hmactag h16 names)
    (backGood1 kem cipher macS kdfS streamS geom hvalid hmactag h16)
    (fun d r hg => (backGood1_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A d
        (withMAC r default) hg).2)
    (fun d u hg => (backGood1_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A d u
        hg).1)
    (fun _ _ _ _ _ => rfl)

/-! ## The payload cipher step for world 1 -/

/-- World 1 from the encrypted block. On the backward path the world does not use it. -/
def backViewE1 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk) (o : (RSOR.Randomness geom ×
        RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)) (c : kem.Ciphertext) (k : (Vector UInt8
        16 × Vector UInt8 32 × Vector UInt8 32))
    (e : Block geom) : Protocols.RSOR.World 𝒮 :=
  match ch.c.pos.val with
  | 0 => Protocols.RSOR.BackwardChallenge.world1With ch.c
      (RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd
          [.recipient ch.c.req.receiver]) o.1.1 0 (ch.c.req.fwd.hops.length - 1)
        (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o.1 c (default, k.1,
            k.2.2)
          ++ ofVector (macS.mac (ofVector k.2.1)
            (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o.1 c (default,
                k.1, k.2.2)))
          ++ ofVector e)))
      none
      (some (RSOR.split geom
        (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o.1 c (default, k.1,
            k.2.2)
          ++ ofVector (macS.mac (ofVector k.2.1)
            (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o.1 c (default,
                k.1, k.2.2)))
          ++ ofVector e)).1)
      o.2.1 o.2.2.1 o.2.2.2
  | _ + 1 => backViewT1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c (default,
      k.1, k.2.2)
      (macS.mac (ofVector k.2.1) (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          ch o c (default, k.1, k.2.2)))

/-- The good draws of world 1 on which, at the exit, the block has a payload's length. -/
def backGoodP1 {names : Role → RSOR.Name} {A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary}
    (d : KeyedDraw (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)) : Prop
        :=
  backGood1 kem cipher macS kdfS streamS geom hvalid hmactag h16 d ∧ ((propChOf d).c.pos.val = 0 →
      ∀ k : (Vector UInt8 16 × Vector UInt8 32 × Vector UInt8 32),
    (relayBackAt kem cipher macS kdfS streamS geom
      (RSOR.path kem (propChOf d).c.req.fwd [.recipient (propChOf d).c.req.receiver])
      (propOthOf d).1.1
      (RSOR.body kem macS kdfS streamS geom (propChOf d).c.req (propOthOf d).1)
      ((propChOf d).c.req.fwd.hops.length - 1) (ksOf streamS geom (default, k)) id).size
    = geom.payloadTagLength + geom.forwardPayloadLength)

/-- World 1 with a one-header relay, as a payload game. -/
def backGameP1 (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary) :
    PayloadGame kem cipher macS kdfS streamS geom hvalid hmactag h16 :=
  propPayloadGame kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ (shortDraw geom)
    (backView1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) A (backM1 kem cipher
        macS kdfS streamS geom hvalid hmactag h16 names)
    (fun ch o _ k => backBlock0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o.1
        k) (backViewE1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names)

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- **The payload cipher step for world 1 of SLU←.** -/
theorem backward1_payload_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S
    := 𝒮)).Adversary) :
    |(Pr{let x ← (keyedGameH cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS streamS
        geom hvalid hmactag h16 names A)
          (onlyHeader cipher macS streamS geom (tagged macS
            (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[x =
                true]).toReal
      - (Pr{let x ← ((backGameP1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).exp
          false)}[x = true]).toReal|
    ≤ |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv true)}[x =
              true]).toReal
        - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv false)}[x =
              true]).toReal|
      + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
        (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[¬ backGoodP1 kem
            cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal := by
  refine prop_tagged_sub_ideal_le kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names
    _ (shortDraw geom) (backView1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) A _ _
        _
    (backGoodP1 kem cipher macS kdfS streamS geom hvalid hmactag h16)
    (fun ch o c kp kp' iv ke => rfl)
    (fun d r hg => (backGood1_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A d
        (withMAC r default) hg.1).2)
    (fun d r hg => backM0_ct kem cipher macS kdfS streamS geom hvalid hmactag h16 names _ _ _ _
      (backGood1_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A d (withMAC r
          default) hg.1).2)
    (fun d u hg => ?_)
  refine (backGood1_view kem cipher macS kdfS streamS geom hvalid hmactag h16 names A d u
      hg.1).1.trans ?_
  have hP := hg.2
  show backViewT1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d)
      (propOthOf d) d.c (restOf u)
      (macS.mac (ofVector u.2.2.1)
        (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d) (propOthOf
            d) d.c (restOf u)))
    = backViewE1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf d) (propOthOf
        d) d.c u.2 (Util.Bytes.toVecN _
      (cipher.encrypt u.1.toArray (ofVector u.2.1)
        (ofVector (backBlock0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names (propChOf
            d) (propOthOf d).1 u.2))))
  generalize propChOf d = ch at hP ⊢
  generalize propOthOf d = o at hP ⊢
  cases hp : ch.c.pos.val with
  | zero =>
    replace hP := hP hp u.2
    have hb : relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
        ch.c.req.receiver]) o.1.1 (RSOR.body kem macS kdfS streamS geom ch.c.req o.1)
        (ch.c.req.fwd.hops.length - 1)
          (ksOf streamS geom (withMAC (restOf u) default))
          (encOf cipher (withMAC (restOf u) default))
        = ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
          (cipher.encrypt u.1.toArray (ofVector u.2.1)
            (ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
              (relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd
                  [.recipient ch.c.req.receiver]) o.1.1 (RSOR.body kem macS kdfS streamS geom
                  ch.c.req o.1) (ch.c.req.fwd.hops.length - 1)
                (ksOf streamS geom (default, u.2)) id))))) := by
      have e1 := relayBackAt_enc kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd
          [.recipient ch.c.req.receiver]) o.1.1 (RSOR.body kem macS kdfS streamS geom ch.c.req o.1)
          (ch.c.req.fwd.hops.length - 1)
        (ksOf streamS geom (default, u.2))
        (encOf cipher (withMAC (restOf u) default)) (by rw [hP]; omega)
      refine e1.trans ?_
      rw [Cryptlib.Util.Bytes.ofVector_toVecN _ hP, Cryptlib.Util.Bytes.ofVector_toVecN _
        (by rw [cipher.encrypt_size]; exact hP)]
      rfl
    unfold backViewT1 backViewE1 backM1 backM0 backBlock0
    rw [hp]
    dsimp only
    rw [hb]
    rfl
  | succ k =>
    unfold backViewE1 backViewT1 backM1 backM0
    rw [hp]
    rfl

/-! ## The keystream step -/

/-- The bytes the honest relay's MAC covers, from its header keystream. -/
def backMU (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (U : ByteArray) : ByteArray :=
  match ch.c.pos.val with
  | 0 => relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
      ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
      (ch.c.req.fwd.hops.length - 1) (ofVector (kem.encodeCiphertext c)) U
  | k + 1 => relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back
      [.surbReply r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
      (kem.encodeCiphertext c)) U

/-- The sender's block at the exit, from the honest relay's header keystream. -/
def backBlockU (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (r : RSOR.Randomness geom) (U : ByteArray) : Block geom :=
  match ch.c.pos.val with
  | 0 => Util.Bytes.toVecN _ (relayBackAt kem cipher macS kdfS streamS geom (RSOR.path kem
      ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom
      ch.c.req r) (ch.c.req.fwd.hops.length - 1) U id)
  | _ + 1 => default

/-- World 0 from the honest relay's MAC key, its header keystream and the encrypted block. -/
def backViewU0 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk)
    (r : RSOR.Randomness geom) (c : kem.Ciphertext) (km : Vector UInt8 32) (U : ByteArray)
    (e : Block geom) : Protocols.RSOR.World 𝒮 :=
  match ch.c.pos.val with
  | 0 =>
    { onion := RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom (RSOR.path kem
        ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1 0 (ch.c.req.fwd.hops.length - 1)
        (relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver]) r.1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
            (ch.c.req.fwd.hops.length - 1) (ofVector (kem.encodeCiphertext c)) U
          ++ ofVector (macS.mac (ofVector km) (relayFrontAt kem cipher macS kdfS streamS geom
              (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) r.1 (RSOR.body kem macS
              kdfS streamS geom ch.c.req r) (ch.c.req.fwd.hops.length - 1) (ofVector
              (kem.encodeCiphertext c)) U))
          ++ ofVector e))
      patch := (Protocols.RSOR.BackwardChallenge.world0 ch.c r).patch }
  | k + 1 =>
    { onion := backOnionX kem cipher macS kdfS streamS geom ch.c.req r (Nat.zero_lt_of_lt
        ch.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            r.2.2.2]) r.2.1 0 k
        (relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
            (kem.encodeCiphertext c)) U
          ++ ofVector (macS.mac (ofVector km) (relayFrontAt kem default macS kdfS streamS geom
              (RSOR.path kem ch.c.req.back [.surbReply r.2.2.2]) r.2.1 ⟨Array.replicate
              geom.forwardPayloadLength 0⟩ k (ofVector (kem.encodeCiphertext c)) U))
          ++ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back
              [.surbReply r.2.2.2]) r.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k U id)))
      patch :=
        { proc := fun (h : Role) (o : RSOR.Onion geom) out =>
            if h = .sender ∧ o.1 = backHeaderU kem cipher macS kdfS streamS geom ch.c.req r k U
                (ch.c.req.back.hops.length - 1) then pure none
            else pure out } }

/-- The adversary against the keystream generator that plays world 0. -/
def backStreamAdv0 (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary) :
    PRGScheme.PRGAdversary (Keystream geom) :=
  propStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness geom) ($ᵗ
      RSOR.Randomness geom)
    (backView0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) A (backMU kem cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (backBlockU kem cipher macS kdfS streamS
        geom hvalid hmactag h16 names)
    (backViewU0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names)

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- **The keystream step for world 0 of SLU←.** With uniform keys at the honest relay and its
own header only, world 0 is the ideal experiment of the keystream generator for
`backStreamAdv0`, up to the one-block cipher advantage, the generator's advantage and the
chance of a draw that is not good. -/
theorem backward0_stream_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S
    := 𝒮)).Adversary) :
    |(Pr{let x ← (keyedGameH cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS streamS
        geom hvalid hmactag h16 names A)
          (onlyHeader cipher macS streamS geom (tagged macS
            (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[x =
                true]).toReal
      - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (backStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
    ≤ |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv true)}[x =
              true]).toReal
        - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv false)}[x =
              true]).toReal|
      + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
          (backStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal
        - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (backStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
      + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
        (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[¬ backGoodP0 kem
            cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal := by
  have h := backward0_payload_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have e : Pr{let x ← ((backGameP0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).exp false)}[x = true]
      = Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
        (backStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true] :=
    propPayload_exp_false_eq_prg kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness geom)
      ($ᵗ RSOR.Randomness geom) (backView0 kem cipher macS kdfS streamS geom hvalid hmactag h16
          names) A (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (fun ch r _ k => backBlock0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch r
          k) (backViewE0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (backMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names) (backBlockU kem cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (backViewU0 kem cipher macS kdfS streamS
          geom hvalid hmactag h16 names)
      (fun ch o c kp iv ke => by
        unfold backM0 backMU
        cases ch.c.pos.val <;> rfl)
      (fun ch o c iv km ke => by
        unfold backBlock0 backBlockU
        cases ch.c.pos.val <;> rfl)
      (fun ch o c iv km ke e => by
        cases hp : ch.c.pos.val with
        | zero =>
          unfold backViewE0 backViewU0 backM0
          rw [hp]
          rfl
        | succ k =>
          unfold backViewE0 backViewU0 backViewT0 backM0
          rw [hp]
          rfl)
  rw [e] at h
  have t := abs_sub_le
    (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS streamS
        geom hvalid hmactag h16 names A)
      (onlyHeader cipher macS streamS geom (tagged macS
        (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
      (backStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
          true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (backStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
          true]).toReal
  linarith

/-- The bytes the honest relay's MAC covers in world 1, from its header keystream. -/
def backMU1 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk) (o : (RSOR.Randomness geom ×
        RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)) (c : kem.Ciphertext)
    (U : ByteArray) : ByteArray :=
  backMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o.1 c U

/-- The sender's block at the exit in world 1, from the honest relay's header keystream. -/
def backBlockU1 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk) (o : (RSOR.Randomness geom ×
        RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)) (U : ByteArray) : Block geom :=
  backBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o.1 U

/-- World 1 from the honest relay's MAC key, its header keystream and the encrypted block. -/
def backViewU1 (names : Role → RSOR.Name) {pk : Key kem}
    (ch : PropCh kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names pk) (o : (RSOR.Randomness geom ×
        RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)) (c : kem.Ciphertext)
    (km : Vector UInt8 32) (U : ByteArray) (e : Block geom) : Protocols.RSOR.World 𝒮 :=
  match ch.c.pos.val with
  | 0 => Protocols.RSOR.BackwardChallenge.world1With ch.c
      (RSOR.split geom (wrapUp kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd
          [.recipient ch.c.req.receiver]) o.1.1 0 (ch.c.req.fwd.hops.length - 1)
        (relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver]) o.1.1 (RSOR.body kem macS kdfS streamS geom ch.c.req o.1)
            (ch.c.req.fwd.hops.length - 1) (ofVector (kem.encodeCiphertext c)) U
          ++ ofVector (macS.mac (ofVector km) (relayFrontAt kem cipher macS kdfS streamS geom
              (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) o.1.1 (RSOR.body kem macS
              kdfS streamS geom ch.c.req o.1) (ch.c.req.fwd.hops.length - 1) (ofVector
              (kem.encodeCiphertext c)) U))
          ++ ofVector e)))
      none
      (some (RSOR.split geom
        (relayFrontAt kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver]) o.1.1 (RSOR.body kem macS kdfS streamS geom ch.c.req o.1)
            (ch.c.req.fwd.hops.length - 1) (ofVector (kem.encodeCiphertext c)) U
          ++ ofVector (macS.mac (ofVector km) (relayFrontAt kem cipher macS kdfS streamS geom
              (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) o.1.1 (RSOR.body kem macS
              kdfS streamS geom ch.c.req o.1) (ch.c.req.fwd.hops.length - 1) (ofVector
              (kem.encodeCiphertext c)) U))
          ++ ofVector e)).1)
      o.2.1 o.2.2.1 o.2.2.2
  | k + 1 => Protocols.RSOR.BackwardChallenge.world1With ch.c
      (backOnionX kem cipher macS kdfS streamS geom ch.c.req o.1 (Nat.zero_lt_of_lt ch.c.pos.isLt)
        (some (wrapUp kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            o.1.2.2.2]) o.1.2.1 0 k
        (relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            o.1.2.2.2]) o.1.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
            (kem.encodeCiphertext c)) U
          ++ ofVector (macS.mac (ofVector km) (relayFrontAt kem default macS kdfS streamS geom
              (RSOR.path kem ch.c.req.back [.surbReply o.1.2.2.2]) o.1.2.1 ⟨Array.replicate
              geom.forwardPayloadLength 0⟩ k (ofVector (kem.encodeCiphertext c)) U))
          ++ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back
              [.surbReply o.1.2.2.2]) o.1.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k U
              id))))
      (if k < ch.c.req.back.hops.length then
        some (RSOR.split geom
        (relayFrontAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back [.surbReply
            o.1.2.2.2]) o.1.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k (ofVector
            (kem.encodeCiphertext c)) U
          ++ ofVector (macS.mac (ofVector km) (relayFrontAt kem default macS kdfS streamS geom
              (RSOR.path kem ch.c.req.back [.surbReply o.1.2.2.2]) o.1.2.1 ⟨Array.replicate
              geom.forwardPayloadLength 0⟩ k (ofVector (kem.encodeCiphertext c)) U))
          ++ relayBackAt kem default macS kdfS streamS geom (RSOR.path kem ch.c.req.back
              [.surbReply o.1.2.2.2]) o.1.2.1 ⟨Array.replicate geom.forwardPayloadLength 0⟩ k U
              id)).1
      else none)
      none
      o.2.1 o.2.2.1 o.2.2.2

/-- The adversary against the keystream generator that plays world 1. -/
def backStreamAdv1 (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S :=
    𝒮)).Adversary) :
    PRGScheme.PRGAdversary (Keystream geom) :=
  propStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16
      (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ (shortDraw geom)
    (backView1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) A (backMU1 kem cipher
        macS kdfS streamS geom hvalid hmactag h16 names) (backBlockU1 kem cipher macS kdfS streamS
        geom hvalid hmactag h16 names)
    (backViewU1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names)

omit [SampleableType kem.Plaintext] in
set_option maxHeartbeats 2000000 in
/-- **The keystream step for world 1 of SLU←.** -/
theorem backward1_stream_le (names : Role → RSOR.Name) (A : (Protocols.RSOR.backwardUnlinkable (S
    := 𝒮)).Adversary) :
    |(Pr{let x ← (keyedGameH cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS streamS
        geom hvalid hmactag h16 names A)
          (onlyHeader cipher macS streamS geom (tagged macS
            (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[x =
                true]).toReal
      - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (backStreamAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
    ≤ |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv true)}[x =
              true]).toReal
        - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv false)}[x =
              true]).toReal|
      + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
          (backStreamAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal
        - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (backStreamAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal|
      + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
        (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[¬ backGoodP1 kem
            cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal := by
  have h := backward1_payload_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have e : Pr{let x ← ((backGameP1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      A).exp false)}[x = true]
      = Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
        (backStreamAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true] :=
    propPayload_exp_false_eq_prg kem cipher macS kdfS streamS geom hvalid hmactag h16
        (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _
      (shortDraw geom) (backView1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) A
          (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (fun ch o _ k => backBlock0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o.1
          k) (backViewE1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
      (backMU1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) (backBlockU1 kem cipher
          macS kdfS streamS geom hvalid hmactag h16 names) (backViewU1 kem cipher macS kdfS streamS
          geom hvalid hmactag h16 names)
      (fun ch o c kp iv ke => by
        unfold backM1 backM0 backMU1 backMU
        cases ch.c.pos.val <;> rfl)
      (fun ch o c iv km ke => by
        unfold backBlock0 backBlockU1 backBlockU
        cases ch.c.pos.val <;> rfl)
      (fun ch o c iv km ke e => by
        cases hp : ch.c.pos.val with
        | zero =>
          unfold backViewE1 backViewU1 backM0
          rw [hp]
          rfl
        | succ k =>
          unfold backViewE1 backViewU1 backViewT1 backM1 backM0
          rw [hp]
          rfl)
  rw [e] at h
  have t := abs_sub_le
    (Pr{let x ← (keyedGameH cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS streamS
        geom hvalid hmactag h16 names A)
      (onlyHeader cipher macS streamS geom (tagged macS
        (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names))))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
      (backStreamAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
          true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (backStreamAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
          true]).toReal
  linarith

/-- **SLU← with the honest relay's keys used up.** The advantage is at most the bad draws, the
cost of replacing the relay's keys (KEM and KDF), a MAC forgery, the one-block cipher advantage
and the keystream generator's advantage, each for both worlds, and the distance between the
two worlds played from a uniform keystream. -/
theorem backwardUnlinkable_le_uniform (names : Role → RSOR.Name) (A :
    (Protocols.RSOR.backwardUnlinkable (S := 𝒮)).Adversary) :
    ((Protocols.RSOR.backwardUnlinkable (S := 𝒮)).advantage names A).toReal
      ≤ (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
          (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names (RSOR.Randomness geom)
          ($ᵗ RSOR.Randomness geom) A)}[backBad0 kem cipher macS kdfS streamS geom hvalid hmactag
              h16 d]).toReal
        + (Pr{let d ← (propDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16
            (Protocols.RSOR.backwardUnlinkable (S := 𝒮)) .relay names _ (shortDraw geom)
          A)}[backBad1 kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + keyedCost cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS streamS geom
            hvalid hmactag h16 names A)
        + keyedCost cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS streamS geom
            hvalid hmactag h16 names A)
        + (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
            (backAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
          (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) (backViewT0 kem
              cipher macS kdfS streamS geom hvalid hmactag h16 names)))}[x = true]).toReal
        + (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
            (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
          (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) (backViewT1 kem
              cipher macS kdfS streamS geom hvalid hmactag h16 names)))}[x = true]).toReal
        + |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv true)}[x =
              true]).toReal
        - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv false)}[x =
              true]).toReal|
        + |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv true)}[x =
              true]).toReal
        - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv false)}[x =
              true]).toReal|
        + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
          (backStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal
        - (Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv0 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 names A))}[x = true]).toReal|
        + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
          (backStreamAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal
        - (Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv1 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 names A))}[x = true]).toReal|
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS
            streamS geom hvalid hmactag h16 names A))}[¬ backGood0 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 d]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS
            streamS geom hvalid hmactag h16 names A))}[¬ backGood1 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 d]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS
            streamS geom hvalid hmactag h16 names A))}[¬ backGoodP0 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 d]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS
            streamS geom hvalid hmactag h16 names A))}[¬ backGoodP1 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 d]).toReal
        + |(Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv1 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 names A))}[x = true]).toReal
          - (Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv0 kem cipher macS kdfS streamS
              geom hvalid hmactag h16 names A))}[x = true]).toReal| := by
  have h := backwardUnlinkable_le_keyedIdeal kem cipher macS kdfS streamS geom hvalid hmactag h16
      names A
  obtain ⟨m0, m0'⟩ := abs_le.1 (backward0_keyedIdeal_sub_tagged_le kem cipher macS kdfS streamS
      geom hvalid hmactag h16 names A)
  obtain ⟨m1, m1'⟩ := abs_le.1 (backward1_keyedIdeal_sub_tagged_le kem cipher macS kdfS streamS
      geom hvalid hmactag h16 names A)
  obtain ⟨s0, s0'⟩ := abs_le.1 (backward0_stream_le kem cipher macS kdfS streamS geom hvalid
      hmactag h16 names A)
  obtain ⟨s1, s1'⟩ := abs_le.1 (backward1_stream_le kem cipher macS kdfS streamS geom hvalid
      hmactag h16 names A)
  have hi := le_abs_self ((Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv1 kem cipher macS
      kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
    - (Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv0 kem cipher macS kdfS streamS geom
        hvalid hmactag h16 names A))}[x = true]).toReal)
  have hi' := neg_abs_le ((Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv1 kem cipher macS
      kdfS streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
    - (Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv0 kem cipher macS kdfS streamS geom
        hvalid hmactag h16 names A))}[x = true]).toReal)
  have hI : |(Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom (backAdv1 kem cipher macS kdfS
      streamS geom hvalid hmactag h16 names A))}[x = true]).toReal
      - (Pr{let x ← (keyedIdeal cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS
          streamS geom hvalid hmactag h16 names A))}[x = true]).toReal|
      ≤ (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom (backAdv0
          kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
          (backM0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) (backViewT0 kem
              cipher macS kdfS streamS geom hvalid hmactag h16 names)))}[x = true]).toReal +
              (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
              (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
          (backM1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names) (backViewT1 kem
              cipher macS kdfS streamS geom hvalid hmactag h16 names)))}[x = true]).toReal
        + |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv true)}[x =
              true]).toReal
        - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv false)}[x =
              true]).toReal| + |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv true)}[x =
              true]).toReal
        - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
          (backGameP1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv false)}[x =
              true]).toReal|
        + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
          (backStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal
        - (Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv0 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 names A))}[x = true]).toReal| + |(Pr{let x ←
            (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
          (backStreamAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
              true]).toReal
        - (Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv1 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 names A))}[x = true]).toReal|
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS
            streamS geom hvalid hmactag h16 names A))}[¬ backGood0 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 d]).toReal + (Pr{let d ← (keyedDraw cipher macS kdfS streamS
            geom (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[¬
            backGood1 kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom (backAdv0 kem cipher macS kdfS
            streamS geom hvalid hmactag h16 names A))}[¬ backGoodP0 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 d]).toReal + (Pr{let d ← (keyedDraw cipher macS kdfS streamS
            geom (backAdv1 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[¬
            backGoodP1 kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + |(Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv1 kem cipher macS kdfS streamS
            geom hvalid hmactag h16 names A))}[x = true]).toReal
          - (Pr{let x ← (PRGScheme.prgIdealExperiment (backStreamAdv0 kem cipher macS kdfS streamS
              geom hvalid hmactag h16 names A))}[x = true]).toReal| :=
    abs_le.2 ⟨by linarith, by linarith⟩
  linarith

end BackGame

end Cryptlib.Protocols.Sphinx.KEMSphinx
