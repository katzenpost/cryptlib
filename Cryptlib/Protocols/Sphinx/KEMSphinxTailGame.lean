/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.CryptoFoundations.KeyEncapMech
import Cryptlib.Protocols.Sphinx.KEMSphinxTailIndist

namespace Cryptlib.Protocols.Sphinx.KEMSphinx

open OracleComp ENNReal
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
open Cryptlib.Util.Bytes (ofVector)

section GameHops

variable {α β : Type}

/-- A draw whose value is not used does not change an event's probability. -/
theorem prEvent_bind_unused' (mx : ProbComp α) (my : ProbComp β) (p : β → Prop) :
    Pr{let y ← mx >>= fun _ => my}[p y] = Pr{let y ← my}[p y] := by
  simp only [prEvent_norm]
  exact OracleComp.prEvent_bind_const _ _

/-- One direction of `prEvent_bind_toReal_sub_le_of_bad`. -/
theorem prEvent_bind_le_add_of_bad (mx : ProbComp α) (F G : α → ProbComp β) (bad : α → Prop)
    (h : ∀ x, ¬ bad x → F x = G x) (q : β → Prop) :
    Pr{let y ← mx >>= F}[q y] ≤ Pr{let y ← mx >>= G}[q y] + Pr{let x ← mx}[bad x] := by
  have hq : ∀ H : α → ProbComp β,
      Pr{let y ← mx >>= H}[q y]
        = Pr{let z ← mx >>= fun x => (fun y => (x, y)) <$> H x}[q z.2] := fun H =>
    prEvent_bind_congr mx H (fun x => (fun y => (x, y)) <$> H x) q (fun z : α × β => q z.2)
      fun x => by rw [prEvent_map]
  have hbad : Pr{let z ← mx >>= fun x => (fun y => (x, y)) <$> F x}[bad z.1]
      = Pr{let x ← mx}[bad x] := by
    have := prEvent_bind_congr mx (fun x => (fun y => (x, y)) <$> F x) pure
      (fun z : α × β => bad z.1) bad fun x => by
        rw [prEvent_map]
        have := prEvent_bind_unused' (F x) (pure x) bad
        simpa only [prEvent_norm] using this
    rwa [bind_pure] at this
  have hmid : Pr{let z ← mx >>= fun x => (fun y => (x, y)) <$> F x}[q z.2 ∧ ¬ bad z.1]
      = Pr{let z ← mx >>= fun x => (fun y => (x, y)) <$> G x}[q z.2 ∧ ¬ bad z.1] :=
    prEvent_bind_congr mx (fun x => (fun y => (x, y)) <$> F x)
      (fun x => (fun y => (x, y)) <$> G x) (fun z : α × β => q z.2 ∧ ¬ bad z.1)
      (fun z : α × β => q z.2 ∧ ¬ bad z.1) fun x => by
      rw [prEvent_map, prEvent_map]
      by_cases hb : bad x
      · rw [prEvent_congr (F x) _ (fun _ => False) fun y => by simp [hb],
          prEvent_congr (G x) _ (fun _ => False) fun y => by simp [hb],
          prEvent_false, prEvent_false]
      · rw [h x hb]
  rw [hq F, hq G, ← hbad]
  refine (prEvent_mono _ _ (fun z : α × β => (q z.2 ∧ ¬ bad z.1) ∨ bad z.1) fun z hz => ?_).trans
    ((prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl))
  · by_cases hb : bad z.1
    · exact Or.inr hb
    · exact Or.inl ⟨hz, hb⟩
  · rw [hmid]
    exact prEvent_mono _ _ _ fun z hz => hz.1

/-- **Identical until bad.** Two games that draw the same `mx` and then run the same computation
off a bad set of draws differ in any event's probability by at most the probability of the bad
set. -/
theorem prEvent_bind_toReal_sub_le_of_bad (mx : ProbComp α) (F G : α → ProbComp β)
    (bad : α → Prop) (h : ∀ x, ¬ bad x → F x = G x) (q : β → Prop) :
    |(Pr{let y ← mx >>= F}[q y]).toReal - (Pr{let y ← mx >>= G}[q y]).toReal|
      ≤ (Pr{let x ← mx}[bad x]).toReal := by
  have key : ∀ F G : α → ProbComp β, (∀ x, ¬ bad x → F x = G x) →
      (Pr{let y ← mx >>= F}[q y]).toReal
        ≤ (Pr{let y ← mx >>= G}[q y]).toReal + (Pr{let x ← mx}[bad x]).toReal := by
    intro F G h
    have h2 := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩)
      (prEvent_bind_le_add_of_bad mx F G bad h q)
    rwa [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at h2
  rw [abs_sub_le_iff]
  exact ⟨by linarith [key F G h], by linarith [key G F fun x hx => (h x hx).symm]⟩

end GameHops

/-! # The tail game with key generation, reduced to the KEM, the KDF and the stream cipher

The honest hop's key pair is generated inside the game and the adversary is given the public
key. The KEM is put in the form of VCVio's `KEMScheme`, and the advantage is bounded by the
difference of VCVio's two fixed-branch IND-CPA experiments, plus the advantages against two
generators (the KDF on a uniform shared secret, and the stream cipher), plus the probability of
the draws the exact theorem does not cover. -/

section Adapter

variable (kem : KEM)

/-- Key generation from a seed. A failed generation gives the default pair. -/
def keygenOf (s : Vector UInt8 32) : kem.PublicKey × kem.PrivateKey :=
  match Cryptlib.Primitives.KEM.KEM.generate kem (kem.stateFromSeed s) with
  | .ok r _ => r
  | .error _ _ => (kem.pubI.default, kem.privI.default)

/-- Encapsulation from a seed. A failed encapsulation gives the default pair. -/
def encapOf (pk : kem.PublicKey) (s : Vector UInt8 32) : kem.Ciphertext × kem.Plaintext :=
  match kem.encap pk (kem.stateFromSeed s) with
  | .ok r _ => r
  | .error _ _ => (kem.ctI.default, kem.ptI.default)

/-- Decapsulation, which draws no randomness. -/
def decapOf (sk : kem.PrivateKey) (c : kem.Ciphertext) : Option kem.Plaintext :=
  match kem.decap sk c (kem.stateFromSeed (Vector.replicate 32 0)) with
  | .ok k _ => some k
  | .error _ _ => none

/-- The KEM as a VCVio `KEMScheme`: key generation and encapsulation each run from a uniform
32-byte seed. -/
def kemScheme : KEMScheme ProbComp kem.Plaintext kem.PublicKey kem.PrivateKey kem.Ciphertext where
  keygen := do
    let s ← $ᵗ (Vector UInt8 32)
    return keygenOf kem s
  encaps pk := do
    let s ← $ᵗ (Vector UInt8 32)
    return encapOf kem pk s
  decaps sk c := return decapOf kem sk c

/-- The hop keys `newKEMPacket` derives for a hop whose public key is the encoding of `pk` are
the KDF of the shared secret `encapOf` returns. -/
theorem kemHopKeys_encapOf (kdfS : KDF) (hop0 : PathHop) (pk : kem.PublicKey)
    (hpk : hop0.publicKey = ofVector (kem.encodePublicKey pk)) (seed0 : Vector UInt8 32) :
    kemHopKeys kem kdfS #[hop0] #[seed0] 0
      = deriveHopKeys kdfS (ofVector (kem.encodePlaintext (encapOf kem pk seed0).2)) := by
  unfold kemHopKeys kemEncap encapOf
  simp only [List.getElem!_toArray, List.getElem!_cons_zero, hpk]
  rw [Cryptlib.Protocols.Sphinx.Common.toVecN_ofVector, kem.decode_encode_pub]
  dsimp only
  cases kem.encap pk (kem.stateFromSeed seed0) with
  | ok r a => rfl
  | error a b => rfl

end Adapter

section TIGame

open PRGScheme

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)

/-- The adversary of the tail game: given the honest hop's public key and a packet, it guesses
which game it is in. -/
abbrev TIAdversary := ByteArray → Option ByteArray → ProbComp Bool

/-- The honest hop: `tmpl` with the generated public key. -/
def honestHop (tmpl : PathHop) (pk : kem.PublicKey) : PathHop :=
  { tmpl with publicKey := ofVector (kem.encodePublicKey pk) }

/-- The public key bytes generated from a key-generation seed. -/
def pkBytes (ks : Vector UInt8 32) : ByteArray :=
  ofVector (kem.encodePublicKey (keygenOf kem ks).1)

/-- The private key bytes generated from a key-generation seed. -/
def skBytes (ks : Vector UInt8 32) : ByteArray :=
  ofVector (kem.encodePrivateKey (keygenOf kem ks).2)

/-- The draws of the real game: the key-generation seed, the first hop's seed, the other hops'
seeds, and the filler. -/
abbrev TIDraw (restPath : Array PathHop) (a : Nat) :=
  Vector UInt8 32 × Vector UInt8 32 × Vector (Vector UInt8 32) restPath.size × Vector UInt8 a

def tiDraw (restPath : Array PathHop) (a : Nat) : ProbComp (TIDraw restPath a) := do
  let ks ← $ᵗ (Vector UInt8 32)
  let seed0 ← $ᵗ (Vector UInt8 32)
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let filler ← $ᵗ (Vector UInt8 a)
  return (ks, seed0, restSeeds, filler)

/-- The real game: generate the honest hop's key pair, build a packet on the honest hop followed
by `restPath`, and give the adversary the public key and what the honest hop forwards. -/
def tiReal (tmpl : PathHop) (restPath : Array PathHop) (payload : ByteArray) (a : Nat)
    (A : TIAdversary) : ProbComp Bool :=
  tiDraw restPath a >>= fun d =>
    A (pkBytes kem d.1) (forwardedView kem cipher macS kdfS streamS geom
      (honestHop kem tmpl (keygenOf kem d.1).1) restPath payload (skBytes kem d.1)
      d.2.1 d.2.2.1 d.2.2.2)

/-- The fresh game: generate the honest hop's key pair, and give the adversary the public key
and a packet built on `restPath` alone. -/
def tiFresh (restPath : Array PathHop) (payload : ByteArray) (c : Nat) (A : TIAdversary) :
    ProbComp Bool := do
  let ks ← $ᵗ (Vector UInt8 32)
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let filler ← $ᵗ (Vector UInt8 c)
  A (pkBytes kem ks) (freshView kem cipher macS kdfS streamS geom restPath payload restSeeds filler)

/-- A packet on the rest of the path whose filler ends in `block`, masked. -/
def blockView (restPath : Array PathHop) (payload : ByteArray) {a : Nat}
    (restSeeds : Vector (Vector UInt8 32) restPath.size) (filler : Vector UInt8 a)
    (block : Vector UInt8 geom.perHopRoutingInfoLength) : Option ByteArray :=
  freshView kem cipher macS kdfS streamS geom restPath payload restSeeds
    (restFiller kem kdfS streamS geom restPath restSeeds filler block)

/-- The header key and IV as a generator from the KEM's shared secret: the KDF. -/
def secretKeyPRG : PRGScheme kem.Plaintext (Vector UInt8 32 × Vector UInt8 16) :=
  ⟨fun ss => ((deriveHopKeys kdfS (ofVector (kem.encodePlaintext ss))).headerEncryption,
    (deriveHopKeys kdfS (ofVector (kem.encodePlaintext ss))).headerEncryptionIV)⟩

/-- The adversary against a block that `A` gives: generate the key pair, build the packet on
the rest of the path around the block, and run `A`. -/
def tiBlockAdv (restPath : Array PathHop) (payload : ByteArray) (a : Nat) (A : TIAdversary) :
    PRGAdversary (Vector UInt8 geom.perHopRoutingInfoLength) := fun block => do
  let ks ← $ᵗ (Vector UInt8 32)
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let filler ← $ᵗ (Vector UInt8 a)
  A (pkBytes kem ks) (blockView kem cipher macS kdfS streamS geom restPath payload restSeeds filler block)

/-- `tiBlockAdv` against a header key and IV: it expands them to the block. -/
def tiKeyAdv (restPath : Array PathHop) (payload : ByteArray) (a : Nat) (A : TIAdversary) :
    PRGAdversary (Vector UInt8 32 × Vector UInt8 16) := fun k =>
  tiBlockAdv kem cipher macS kdfS streamS geom restPath payload a A ((lastBlockPRG streamS geom).gen k)

/-- The IND-CPA adversary that `A` gives. It ignores the challenge ciphertext: the packet the
honest hop forwards does not contain it. -/
def tiKEMAdv (restPath : Array PathHop) (payload : ByteArray) (a : Nat) (A : TIAdversary) :
    (kemScheme kem).IND_CPA_Adversary where
  State := kem.PublicKey
  preChallenge pk := pure pk
  postChallenge pk _ k := do
    let restSeeds ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
    let filler ← $ᵗ (Vector UInt8 a)
    A (ofVector (kem.encodePublicKey pk)) (blockView kem cipher macS kdfS streamS geom restPath payload
      restSeeds filler ((lastBlockPRG streamS geom).gen ((secretKeyPRG kem kdfS).gen k)))

variable [SampleableType kem.Plaintext]

/-- VCVio's fixed-branch IND-CPA experiment for `tiKEMAdv`, written out. -/
def tiKEMExp (restPath : Array PathHop) (payload : ByteArray) (a : Nat) (A : TIAdversary)
    (b : Bool) : ProbComp Bool := do
  let ks ← $ᵗ (Vector UInt8 32)
  let seed0 ← $ᵗ (Vector UInt8 32)
  let kRand ← $ᵗ kem.Plaintext
  let restSeeds ← $ᵗ (Vector (Vector UInt8 32) restPath.size)
  let filler ← $ᵗ (Vector UInt8 a)
  A (pkBytes kem ks) (blockView kem cipher macS kdfS streamS geom restPath payload restSeeds filler
    ((lastBlockPRG streamS geom).gen ((secretKeyPRG kem kdfS).gen
      (if b then (encapOf kem (keygenOf kem ks).1 seed0).2 else kRand))))

theorem indcpa_experiment_eq (restPath : Array PathHop) (payload : ByteArray) (a : Nat)
    (A : TIAdversary) (b : Bool) :
    KEMScheme.IND_CPA_Experiment ProbCompRuntime.probComp
        (tiKEMAdv kem cipher macS kdfS streamS geom restPath payload a A) b
      = tiKEMExp kem cipher macS kdfS streamS geom restPath payload a A b := by
  simp [KEMScheme.IND_CPA_Experiment, kemScheme, tiKEMAdv, tiKEMExp, pkBytes]
  rfl

/-- The real branch of the IND-CPA experiment as a game on `tiDraw`. -/
def tiRealBlock (tmpl : PathHop) (restPath : Array PathHop) (payload : ByteArray) (a : Nat)
    (A : TIAdversary) : ProbComp Bool :=
  tiDraw restPath a >>= fun d =>
    A (pkBytes kem d.1) (blockView kem cipher macS kdfS streamS geom restPath payload d.2.2.1 d.2.2.2
      (firstBlock kem kdfS streamS geom (honestHop kem tmpl (keygenOf kem d.1).1) d.2.1))

theorem tiKEMExp_true_evalDistEq (tmpl : PathHop) (restPath : Array PathHop)
    (payload : ByteArray) (a : Nat) (A : TIAdversary) :
    tiKEMExp kem cipher macS kdfS streamS geom restPath payload a A true
      =ᵈ tiRealBlock kem cipher macS kdfS streamS geom tmpl restPath payload a A := by
  have hfb : ∀ ks seed0, (lastBlockPRG streamS geom).gen ((secretKeyPRG kem kdfS).gen
      (encapOf kem (keygenOf kem ks).1 seed0).2)
      = firstBlock kem kdfS streamS geom (honestHop kem tmpl (keygenOf kem ks).1) seed0 := by
    intro ks seed0
    rw [firstBlock_eq]
    show _ = (lastBlockPRG streamS geom).gen
      ((kemHopKeys kem kdfS #[honestHop kem tmpl (keygenOf kem ks).1] #[seed0] 0).headerEncryption,
       (kemHopKeys kem kdfS #[honestHop kem tmpl (keygenOf kem ks).1] #[seed0]
        0).headerEncryptionIV)
    rw [kemHopKeys_encapOf kem kdfS _ (keygenOf kem ks).1 rfl seed0]
    rfl
  unfold tiKEMExp tiRealBlock tiDraw
  simp only [bind_assoc, pure_bind, if_true, hfb]
  refine EvalDistEq.bind_right _ fun ks => EvalDistEq.bind_right _ fun seed0 => ?_
  exact OracleComp.EvalDistEq.bind_const _ _

theorem tiKEMExp_false_evalDistEq (restPath : Array PathHop) (payload : ByteArray) (a : Nat)
    (A : TIAdversary) :
    tiKEMExp kem cipher macS kdfS streamS geom restPath payload a A false
      =ᵈ prgRealExperiment (secretKeyPRG kem kdfS)
          (tiKeyAdv kem cipher macS kdfS streamS geom restPath payload a A) := by
  unfold tiKEMExp prgRealExperiment tiKeyAdv tiBlockAdv
  simp only [Bool.false_eq_true, if_false]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun ks =>
    OracleComp.EvalDistEq.bind_const _ _) ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- Two independent uniform draws combined by a bijection, then a continuation, are one uniform
draw and the continuation. -/
theorem evalDistEq_pair_of_bijective {α β γ δ : Type} [SampleableType α] [SampleableType β]
    [SampleableType γ] {g : α → β → γ} (hg : Function.Bijective (Function.uncurry g))
    (K : γ → ProbComp δ) :
    (do let x ← $ᵗ α; let y ← $ᵗ β; K (g x y)) =ᵈ ($ᵗ γ >>= K) := by
  have e : (do let x ← $ᵗ α; let y ← $ᵗ β; pure (g x y)) =ᵈ ($ᵗ γ : ProbComp γ) :=
    EvalDistEq.of_forall_prEvent_eq fun p => by
      have h := SampleableType.prEvent_uniformSample_pair_of_bijective hg p
      simpa only [prEvent_norm] using h
  have h := e.bind_left K
  simpa only [bind_assoc, pure_bind] using h

omit [SampleableType kem.Plaintext] in
theorem prgIdeal_tiBlockAdv_evalDistEq (restPath : Array PathHop) (payload : ByteArray) (a : Nat)
    (A : TIAdversary) :
    prgIdealExperiment (tiBlockAdv kem cipher macS kdfS streamS geom restPath payload a A)
      =ᵈ tiFresh kem cipher macS kdfS streamS geom restPath payload (a + geom.perHopRoutingInfoLength) A := by
  unfold prgIdealExperiment tiBlockAdv tiFresh blockView
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun ks => ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.bind_right _ fun restSeeds => ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact evalDistEq_pair_of_bijective
    (restFiller_bijective kem kdfS streamS geom restPath restSeeds (a := a)
      (b := geom.perHopRoutingInfoLength))
    (fun z => A (pkBytes kem ks) (freshView kem cipher macS kdfS streamS geom restPath payload restSeeds z))

/-- The draws the exact theorem does not cover: the generated private key does not derive the
generated public key, some seed is not `Reliable` for the KEM, or the packet cannot be built. -/
def tiBad (tmpl : PathHop) (restPath : Array PathHop) (payload : ByteArray) {a : Nat}
    (d : TIDraw restPath a) : Prop :=
  ¬ (kemSelfPublicKeyBytes kem (skBytes kem d.1) = pkBytes kem d.1 ∧
    (∀ j, j < restPath.size + 1 →
      kem.Reliable (kem.stateFromSeed (#[d.2.1] ++ d.2.2.1.toArray)[j]!)) ∧
    ∃ pkt, newKEMPacket kem cipher macS kdfS streamS geom (#[d.2.1] ++ d.2.2.1.toArray) (ofVector d.2.2.2)
      (#[honestHop kem tmpl (keygenOf kem d.1).1] ++ restPath) payload = Except.ok pkt)

omit [SampleableType kem.Plaintext] in
/-- The real game is the block game, off `tiBad`. -/
theorem tiReal_sub_tiRealBlock_le (hvalid : geom.ValidForKEM kem)
    (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (tmpl : PathHop) (restPath : Array PathHop) (payload : ByteArray)
    (hrest : 1 ≤ restPath.size)
    (hcmdnn : ∀ c ∈ tmpl.commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ tmpl.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (A : TIAdversary) :
    |(Pr{let x ← tiReal kem cipher macS kdfS streamS geom tmpl restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A}[x = true]).toReal
      - (Pr{let x ← tiRealBlock kem cipher macS kdfS streamS geom tmpl restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A}[x = true]).toReal|
    ≤ (Pr{let d ← tiDraw restPath ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)}[tiBad kem cipher macS kdfS streamS geom tmpl restPath payload d]).toReal :=
  prEvent_bind_toReal_sub_le_of_bad (tiDraw restPath ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)) _ _
    (tiBad kem cipher macS kdfS streamS geom tmpl restPath payload) (fun d hd => by
      obtain ⟨hpp, hrel, pkt, hnk⟩ := Classical.not_not.mp hd
      show A _ _ = A _ _
      rw [forwardedView_eq kem cipher macS kdfS streamS geom hvalid hmactag h16
        (honestHop kem tmpl (keygenOf kem d.1).1) restPath payload (skBytes kem d.1) hrest hpp
        hcmdnn hcmdnh d.2.1 d.2.2.1 d.2.2.2 hrel pkt hnk]
      rfl) (fun x => x = true)

/-- **Tail indistinguishability for KEM-Sphinx with the honest hop first, reduced to the KEM,
the KDF and the stream cipher.** The honest hop's key pair is generated in the game. The
advantage of `A` in telling what the honest hop forwards from a fresh packet on the rest of the
path is at most the sum of:

- the difference of VCVio's two IND-CPA experiments for the KEM, with the adversary `tiKEMAdv`;
- the advantage of `tiKeyAdv` in telling the header key and IV the KDF derives from a uniform
  shared secret from a uniform key and IV;
- the advantage of `tiBlockAdv` in telling the last keystream block under a uniform key and IV
  from a uniform block;
- the probability of `tiBad`. -/
theorem tiAdvantage_le (hvalid : geom.ValidForKEM kem)
    (hmactag : macS.tagSize = macLength)
    (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)
    (tmpl : PathHop) (restPath : Array PathHop) (payload : ByteArray)
    (hrest : 1 ≤ restPath.size)
    (hcmdnn : ∀ c ∈ tmpl.commands, c ≠ RoutingCommand.null)
    (hcmdnh : ∀ c ∈ tmpl.commands, ∀ id m, c ≠ RoutingCommand.nextNodeHop id m)
    (A : TIAdversary) :
    |(Pr{let x ← tiReal kem cipher macS kdfS streamS geom tmpl restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A}[x = true]).toReal
      - (Pr{let x ← tiFresh kem cipher macS kdfS streamS geom restPath payload
                      (((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) + geom.perHopRoutingInfoLength) A}[x = true]).toReal|
    ≤ |(Pr{let x ← KEMScheme.IND_CPA_Experiment ProbCompRuntime.probComp
                      (tiKEMAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A) true}[x = true]).toReal
        - (Pr{let x ← KEMScheme.IND_CPA_Experiment ProbCompRuntime.probComp
                        (tiKEMAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A) false}[x = true]).toReal|
      + |(Pr{let x ← prgRealExperiment (secretKeyPRG kem kdfS)
                        (tiKeyAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A)}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment
                        (tiKeyAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A)}[x = true]).toReal|
      + |(Pr{let x ← prgRealExperiment (lastBlockPRG streamS geom)
                        (tiBlockAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A)}[x = true]).toReal
        - (Pr{let x ← prgIdealExperiment
                        (tiBlockAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A)}[x = true]).toReal|
      + (Pr{let d ← tiDraw restPath ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength)}[tiBad kem cipher macS kdfS streamS geom tmpl restPath payload d]).toReal := by
  have h1 := tiReal_sub_tiRealBlock_le kem cipher macS kdfS streamS geom hvalid hmactag h16 tmpl restPath payload hrest
    hcmdnn hcmdnh A
  have e1 := (tiKEMExp_true_evalDistEq kem cipher macS kdfS streamS geom tmpl restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A).prEvent_eq
    (fun x => x = true)
  have e0 := (tiKEMExp_false_evalDistEq kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A).prEvent_eq
    (fun x => x = true)
  have e4 := (prgIdeal_tiBlockAdv_evalDistEq kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A).prEvent_eq
    (fun x => x = true)
  have hd : prgIdealExperiment (tiKeyAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A)
      = prgRealExperiment (lastBlockPRG streamS geom)
          (tiBlockAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A) := rfl
  rw [indcpa_experiment_eq, indcpa_experiment_eq, e1, e0, hd, ← e4]
  have t1 := abs_sub_le
    (Pr{let x ← tiReal kem cipher macS kdfS streamS geom tmpl restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A}[x = true]).toReal
    (Pr{let x ← tiRealBlock kem cipher macS kdfS streamS geom tmpl restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A}[x = true]).toReal
    (Pr{let x ← prgIdealExperiment
                    (tiBlockAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A)}[x = true]).toReal
  have t2 := abs_sub_le
    (Pr{let x ← tiRealBlock kem cipher macS kdfS streamS geom tmpl restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A}[x = true]).toReal
    (Pr{let x ← prgRealExperiment (secretKeyPRG kem kdfS)
                    (tiKeyAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A)}[x = true]).toReal
    (Pr{let x ← prgIdealExperiment
                    (tiBlockAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A)}[x = true]).toReal
  have t3 := abs_sub_le
    (Pr{let x ← prgRealExperiment (secretKeyPRG kem kdfS)
                    (tiKeyAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A)}[x = true]).toReal
    (Pr{let x ← prgRealExperiment (lastBlockPRG streamS geom)
                    (tiBlockAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A)}[x = true]).toReal
    (Pr{let x ← prgIdealExperiment
                    (tiBlockAdv kem cipher macS kdfS streamS geom restPath payload ((geom.nrHops - (restPath.size + 1)) * geom.perHopRoutingInfoLength) A)}[x = true]).toReal
  linarith

end TIGame

end Cryptlib.Protocols.Sphinx.KEMSphinx
