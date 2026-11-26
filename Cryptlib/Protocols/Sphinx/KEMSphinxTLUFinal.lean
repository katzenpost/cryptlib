/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxTLUNext
import Cryptlib.Protocols.Sphinx.KEMSphinxPad
import Cryptlib.Protocols.Sphinx.KEMSphinxLU

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

/-! # The last step of TLU→

Both worlds have been brought to games where the honest relay's keystreams are uniform. Here
they are compared. -/

/-! ## A pad on the head of one keystream and the tail of another -/

/-- **Two keystreams read through one pad are one keystream.** A game that reads the head of
one uniform string masked by a function of the tail of another, followed by that tail masked by
a constant, reads one uniform string. -/
theorem evalDistEq_headTail {δ : Type} {h t n : ℕ} (hn : h + t = n) (A : ByteArray → ByteArray)
    (B : ByteArray) (K : Vector UInt8 n → ProbComp δ) :
    (do
      let U ← $ᵗ (Vector UInt8 n)
      let U' ← $ᵗ (Vector UInt8 n)
      K (Util.Bytes.toVecN n
        (xorBytes ((ofVector U).extract 0 h) (A ((ofVector U').extract h n))
          ++ xorBytes ((ofVector U').extract h n) B)))
      =ᵈ ($ᵗ (Vector UInt8 n) >>= K) := by
  have hcat := padFiller_bijective (a := h) (b := t) hn (zeroBytes 0)
  have e0 : ∀ (x : Vector UInt8 h) (y : Vector UInt8 t),
      (ofVector (padFiller hn (zeroBytes 0) x y)).extract 0 h = ofVector x
        ∧ (ofVector (padFiller hn (zeroBytes 0) x y)).extract h n = ofVector y := by
    intro x y
    rw [ofVector_padFiller, xorBytes_zeroBytes]
    constructor
    · have h1 := Util.Bytes.extract_append_left (ofVector x) (ofVector y)
      rwa [Util.Bytes.size_ofVector] at h1
    · have h1 := Util.Bytes.extract_append_right (ofVector x) (ofVector y)
      rwa [Util.Bytes.size_ofVector, Util.Bytes.size_ofVector, hn] at h1
  let G : Vector UInt8 h → Vector UInt8 t → ProbComp δ := fun x y' =>
    K (Util.Bytes.toVecN n
      (xorBytes (ofVector x) (A (ofVector y')) ++ xorBytes (ofVector y') B))
  have t1 := (evalDistEq_pair_of_bijective hcat (fun U => $ᵗ (Vector UInt8 n) >>= fun U' =>
    K (Util.Bytes.toVecN n
      (xorBytes ((ofVector U).extract 0 h) (A ((ofVector U').extract h n))
        ++ xorBytes ((ofVector U').extract h n) B)))).symm
  refine EvalDistEq.trans t1 ?_
  have t2 : ∀ (x : Vector UInt8 h) (y : Vector UInt8 t),
      ($ᵗ (Vector UInt8 n) >>= fun U' => K (Util.Bytes.toVecN n
        (xorBytes ((ofVector (padFiller hn (zeroBytes 0) x y)).extract 0 h)
            (A ((ofVector U').extract h n))
          ++ xorBytes ((ofVector U').extract h n) B)))
        =ᵈ ($ᵗ (Vector UInt8 t) >>= fun y' => G x y') := fun x y => by
    refine EvalDistEq.trans (evalDistEq_pair_of_bijective hcat _).symm ?_
    simp only [(e0 _ _).1, (e0 _ _).2]
    exact OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 h))
      ($ᵗ (Vector UInt8 t) >>= fun y' => G x y')
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun x => EvalDistEq.bind_right _ fun y =>
    t2 x y) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun x =>
    OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 t))
      ($ᵗ (Vector UInt8 t) >>= fun y' => G x y')) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ fun x y' => G x y') ?_
  have t5 : ∀ y' : Vector UInt8 t, ($ᵗ (Vector UInt8 h) >>= fun x => G x y')
      =ᵈ ($ᵗ (Vector UInt8 h) >>= fun x => K (padFiller hn B x y')) := fun y' => by
    have h5 := evalDistEq_otp h (A (ofVector y')) (fun z => K (padFiller hn B z y'))
    simpa only [G, padFiller, Util.Bytes.ofVector_toVecN _
      ((size_xorBytes _ _).trans (Util.Bytes.size_ofVector _))] using h5
  refine EvalDistEq.trans (EvalDistEq.bind_right _ t5) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _
    fun y' x => K (padFiller hn B x y')) ?_
  exact evalDistEq_pair_of_bijective (padFiller_bijective hn B) K

/-- **A pad on the head of a keystream.** A game that reads a uniform string with its head
masked by a constant reads a uniform string. -/
theorem evalDistEq_headPad {δ : Type} {h t n : ℕ} (hn : h + t = n) (X : ByteArray)
    (K : Vector UInt8 n → ProbComp δ) :
    ($ᵗ (Vector UInt8 n) >>= fun U => K (Util.Bytes.toVecN n
        (xorBytes ((ofVector U).extract 0 h) X ++ (ofVector U).extract h n)))
      =ᵈ ($ᵗ (Vector UInt8 n) >>= K) := by
  have hcat := padFiller_bijective (a := h) (b := t) hn (zeroBytes 0)
  have e0 : ∀ (x : Vector UInt8 h) (y : Vector UInt8 t),
      (ofVector (padFiller hn (zeroBytes 0) x y)).extract 0 h = ofVector x
        ∧ (ofVector (padFiller hn (zeroBytes 0) x y)).extract h n = ofVector y := by
    intro x y
    rw [ofVector_padFiller, xorBytes_zeroBytes]
    constructor
    · have h1 := Util.Bytes.extract_append_left (ofVector x) (ofVector y)
      rwa [Util.Bytes.size_ofVector] at h1
    · have h1 := Util.Bytes.extract_append_right (ofVector x) (ofVector y)
      rwa [Util.Bytes.size_ofVector, Util.Bytes.size_ofVector, hn] at h1
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective hcat _).symm ?_
  simp only [(e0 _ _).1, (e0 _ _).2]
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  have t5 : ∀ y : Vector UInt8 t, ($ᵗ (Vector UInt8 h) >>= fun x =>
        K (Util.Bytes.toVecN n (xorBytes (ofVector x) X ++ ofVector y)))
      =ᵈ ($ᵗ (Vector UInt8 h) >>= fun x => K (padFiller hn (zeroBytes 0) x y)) := fun y => by
    have h5 := evalDistEq_otp h X (fun z => K (padFiller hn (zeroBytes 0) z y))
    simpa only [padFiller, xorBytes_zeroBytes, Util.Bytes.ofVector_toVecN _
      ((size_xorBytes _ _).trans (Util.Bytes.size_ofVector _))] using h5
  refine EvalDistEq.trans (EvalDistEq.bind_right _ t5) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _
    fun y x => K (padFiller hn (zeroBytes 0) x y)) ?_
  exact evalDistEq_pair_of_bijective hcat K

/-- **A bound that holds after every outcome of a common prefix holds with the prefix in
front**, for the distance of two games with boolean output. -/
theorem abs_prEvent_bind_sub_le {α γ : Type} (mx : ProbComp α) (F G : α → ProbComp Bool)
    (B : α → ProbComp γ) (r : γ → Prop)
    (h : ∀ x, |(Pr{let y ← F x}[y = true]).toReal - (Pr{let y ← G x}[y = true]).toReal|
      ≤ (Pr{let z ← B x}[r z]).toReal) :
    |(Pr{let y ← mx >>= F}[y = true]).toReal - (Pr{let y ← mx >>= G}[y = true]).toReal|
      ≤ (Pr{let z ← mx >>= B}[r z]).toReal := by
  have hle : ∀ (a b c : ENNReal), a ≠ ⊤ → b ≠ ⊤ → c ≠ ⊤ → a.toReal - b.toReal ≤ c.toReal →
      a ≤ b + c := fun a b c ha hb hc habc => by
    rw [← ENNReal.toReal_le_toReal ha (ENNReal.add_ne_top.mpr ⟨hb, hc⟩),
      ENNReal.toReal_add hb hc]
    linarith
  have h12 := Util.UntilBad.prEvent_bind_le_add mx F G B (· = true) r fun x =>
    hle _ _ _ (prEvent_ne_top _) (prEvent_ne_top _) (prEvent_ne_top _)
      (abs_sub_le_iff.1 (h x)).1
  have h21 := Util.UntilBad.prEvent_bind_le_add mx G F B (· = true) r fun x =>
    hle _ _ _ (prEvent_ne_top _) (prEvent_ne_top _) (prEvent_ne_top _)
      (abs_sub_le_iff.1 (h x)).2
  have r12 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h12
  have r21 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h21
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at r12 r21
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-! ## The chance that a uniform block begins with the zero tag -/

/-- A byte vector is all zero exactly when it is the zero vector. -/
theorem all_zero_iff {a : ℕ} (x : Vector UInt8 a) :
    (ofVector x).data.all (· == 0) = true ↔ x = Vector.replicate a 0 := by
  constructor
  · intro h
    rw [Array.all_eq_true] at h
    refine Vector.ext fun i hi => ?_
    have h1 := h i (by simpa [ofVector] using hi)
    simpa [ofVector] using h1
  · rintro rfl
    rw [Array.all_eq_true]
    intro i hi
    simp [ofVector]

/-- **A uniform string begins with `a` zero bytes with chance one in the number of strings of
`a` bytes.** -/
theorem prEvent_zeroPrefix {a b n : ℕ} (hn : a + b = n) :
    Pr{let v ← $ᵗ (Vector UInt8 n)}[((ofVector v).extract 0 a).data.all (· == 0) = true]
      = (Fintype.card (Vector UInt8 a) : ENNReal)⁻¹ := by
  have hcat := padFiller_bijective (a := a) (b := b) hn (zeroBytes 0)
  have e0 : ∀ (x : Vector UInt8 a) (y : Vector UInt8 b),
      (ofVector (padFiller hn (zeroBytes 0) x y)).extract 0 a = ofVector x := by
    intro x y
    rw [ofVector_padFiller, xorBytes_zeroBytes]
    have h1 := Util.Bytes.extract_append_left (ofVector x) (ofVector y)
    rwa [Util.Bytes.size_ofVector] at h1
  have h : ($ᵗ (Vector UInt8 n) >>= fun v =>
        (pure (((ofVector v).extract 0 a).data.all (· == 0)) : ProbComp Bool))
      =ᵈ ($ᵗ (Vector UInt8 a) >>= fun x =>
        (pure ((ofVector x).data.all (· == 0)) : ProbComp Bool)) := by
    refine EvalDistEq.trans (evalDistEq_pair_of_bijective hcat _).symm ?_
    simp only [e0]
    exact EvalDistEq.bind_right _ fun x => OracleComp.EvalDistEq.bind_const _ _
  have key := h (fun b => b = true)
  simp only [bind_pure_comp, prEvent_map] at key
  rw [key]
  simp only [all_zero_iff]
  exact SampleableType.prEvent_uniformSample_eq_singleton _

section ForwardFinal

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

variable (names : Role → RSOR.Name)

/-! ## The hidden ciphertext -/

/-- The honest relay's own answer to a packet. -/
def ownAns (sk : kem.PrivateKey) (pkt : ByteArray) : ProcResult :=
  procWith kem cipher macS kdfS streamS geom (kemDecap kem (ofVector (kem.encodePrivateKey sk)))
    pkt

/-- Whether the adversary of world 1 sends the honest relay a packet with the ciphertext of
the original's layer at the relay, which it is never shown. -/
def nextHidden (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) : ProbComp Bool := do
  let U' ← $ᵗ (Keystream geom)
  let k ← keygen kem
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
    ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre k.1)
  let s' ← $ᵗ (Vector UInt8 32)
  let x ← nextDraw geom
  let z ← (simulateQ (Util.UntilBad.logged
      (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
        (ownAns kem cipher macS kdfS streamS geom k.2)))
    ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post cs.2
      (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names cs.1 x
        (ofVector U')))).run []
  return z.2.any (badQuery kem (encapOf kem k.1.1 s').1 fun _ => true)

/-- **The hidden ciphertext.** Rejecting the ciphertext of the original's layer at the relay
changes world 1 by at most the chance that the adversary sends it. -/
theorem next_hidden_le (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let x ← (PRGScheme.prgIdealExperiment
          (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))}[x = true]).toReal
      - (Pr{let x ← (PRGScheme.prgIdealExperiment
          (nextStreamAdvF kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            (ownAns kem cipher macS kdfS streamS geom) A))}[x = true]).toReal|
    ≤ (Pr{let b ← (nextHidden kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        A)}[b = true]).toReal := by
  have hstep : ∀ (k : Key kem × kem.PrivateKey) (s' : Vector UInt8 32)
      (oa : OracleComp procSpec Bool),
      Pr{let x ← (simulateQ (procImplF kem cipher macS kdfS streamS geom k.2
          (encapOf kem k.1.1 s').1 (fun _ => none)) oa)}[x = true]
        ≤ Pr{let x ← (simulateQ (procImplF kem cipher macS kdfS streamS geom k.2
            (encapOf kem k.1.1 s').1 (ownAns kem cipher macS kdfS streamS geom k.2))
            oa)}[x = true]
          + Pr{let b ← (do
              let z ← (simulateQ (Util.UntilBad.logged
                (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
                  (ownAns kem cipher macS kdfS streamS geom k.2))) oa).run []
              return z.2.any (badQuery kem (encapOf kem k.1.1 s').1 fun _ => true))}[b = true]
      ∧ Pr{let x ← (simulateQ (procImplF kem cipher macS kdfS streamS geom k.2
            (encapOf kem k.1.1 s').1 (ownAns kem cipher macS kdfS streamS geom k.2))
            oa)}[x = true]
        ≤ Pr{let x ← (simulateQ (procImplF kem cipher macS kdfS streamS geom k.2
            (encapOf kem k.1.1 s').1 (fun _ => none)) oa)}[x = true]
          + Pr{let b ← (do
              let z ← (simulateQ (Util.UntilBad.logged
                (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
                  (ownAns kem cipher macS kdfS streamS geom k.2))) oa).run []
              return z.2.any (badQuery kem (encapOf kem k.1.1 s').1 fun _ => true))}[b = true] :=
    fun k s' oa => by
      have h := procImplF_le_add_bad kem cipher macS kdfS streamS geom k.2
        (encapOf kem k.1.1 s').1 (fun _ => none) (ownAns kem cipher macS kdfS streamS geom k.2)
        (fun _ => true) (fun _ _ hb => by cases hb) oa (· = true)
      simpa only [bind_pure_comp, prEvent_map, Function.comp_def] using h
  have h12 : Pr{let x ← (PRGScheme.prgIdealExperiment
        (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]
      ≤ Pr{let x ← (PRGScheme.prgIdealExperiment
          (nextStreamAdvF kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            (ownAns kem cipher macS kdfS streamS geom) A))}[x = true]
        + Pr{let b ← (nextHidden kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A)}[b = true] :=
    Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun U' =>
      Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun k =>
        Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun cs =>
          Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun s' =>
            Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun x => (hstep k s' _).1
  have h21 : Pr{let x ← (PRGScheme.prgIdealExperiment
        (nextStreamAdvF kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          (ownAns kem cipher macS kdfS streamS geom) A))}[x = true]
      ≤ Pr{let x ← (PRGScheme.prgIdealExperiment
          (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x = true]
        + Pr{let b ← (nextHidden kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A)}[b = true] :=
    Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun U' =>
      Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun k =>
        Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun cs =>
          Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun s' =>
            Util.UntilBad.prEvent_bind_le_add _ _ _ _ _ _ fun x => (hstep k s' _).2
  have r12 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h12
  have r21 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) h21
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at r12 r21
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-! ## World 1 as a relay that answers one header -/

/-- With its own answers for the ciphertext `c`, the keyed oracle is the honest node's. -/
theorem procImplF_ownAns (sk : kem.PrivateKey) (c : kem.Ciphertext) :
    procImplF kem cipher macS kdfS streamS geom sk c (ownAns kem cipher macS kdfS streamS geom sk)
      = procImpl kem cipher macS kdfS streamS geom sk := by
  rw [procImplF_eq_relayImpl]
  have h : relayAns kem cipher macS kdfS streamS geom sk c
      (ownAns kem cipher macS kdfS streamS geom sk)
      = ownAns kem cipher macS kdfS streamS geom sk := by
    funext pkt
    unfold relayAns ownAns
    split_ifs <;> rfl
  rw [h]
  rfl

set_option maxHeartbeats 1000000 in
/-- **World 1 after its draws, as a relay that answers one header.** With the honest relay's
own answers for the hidden ciphertext, the second phase of world 1 is the game where the relay
answers the replacement's ciphertext under the replacement's header only, from its MAC key, its
uniform keystream and the ideal payload cipher. -/
theorem nextOwn_run (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (s' : Vector UInt8 32) (x : NextOth geom) (U' : ByteArray)
    (hsz : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
      (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength) :
    simulateQ (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
        (ownAns kem cipher macS kdfS streamS geom k.2))
      ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post st
        (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x U'))
    = (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay
          (fun h => if h = .relay then k.2 else st.2.2 h) (encapOf kem k.1.1 x.2.2.1).1 x.2.1
          (ofVector x.1)
          (Util.Bytes.toVecN _
            (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)
              ++ ofVector (macS.mac (ofVector x.2.1)
                (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                  (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)))))
          (fun y => if y = x.2.2.2.2.1 then
              shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                (ofVector x.1)
            else x.2.2.2.2.2)
          (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x U').1.patch)
        (A.guess st.1 (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x
          U').1.onion)).run' st.2.1 := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  obtain ⟨U, km, s, o, u, v⟩ := x
  obtain ⟨W, hW⟩ : ∃ W,
      W = nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
        (U, km, s, o, u, v) U' := ⟨_, rfl⟩
  rw [procImplF_ownAns, ← hW]
  show simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
    (simulateQ (relayFirst kem W.2.1 W.2.2)
      ((simulateQ (viaOracle kem cipher macS kdfS streamS geom hvalid hmactag h16
          .relay st.2.2 W.1.patch)
        (A.guess st.1 W.1.onion)).run' st.2.1)) = _
  have hcomp : procImpl kem cipher macS kdfS streamS geom k.2 ∘ₛ relayFirst kem W.2.1 W.2.2
      = relayImpl (relayAns kem cipher macS kdfS streamS geom k.2 W.2.1 W.2.2) :=
    relayImpl_comp_relayFirst kem _ W.2.1 W.2.2
  rw [← QueryImpl.simulateQ_compose, hcomp]
  obtain ⟨Hv, hHv⟩ : ∃ Hv : Vector UInt8 geom.headerLength, Hv = Util.Bytes.toVecN _
      (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)
        ++ ofVector (macS.mac (ofVector km)
          (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)))) := ⟨_, rfl⟩
  have hsize : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)
      ++ ofVector (macS.mac (ofVector km)
        (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o
        (encapOf kem k.1.1 s).1 (ofVector U)))).size = geom.headerLength := by
    rw [ByteArray.size_append, hsz, Cryptlib.Util.Bytes.size_ofVector, hmactag, hhdr]
    rfl
  have hcar : ∀ pkt : ByteArray, pkt.extract 0 (payloadOffset kem geom) = ofVector Hv
      → carries kem (encapOf kem k.1.1 s).1 pkt = true := by
    intro pkt hp
    refine carries_of_extract kem _ pkt ?_
    have h' := congrArg (fun x : ByteArray => x.extract 2 (2 + kem.ciphertextSize)) hp
    simp only [ByteArray.extract_extract] at h'
    rw [Nat.zero_add, Nat.zero_add, Nat.min_eq_left (by unfold payloadOffset; omega)] at h'
    rw [h', hHv, Cryptlib.Util.Bytes.ofVector_toVecN _ hsize,
      Cryptlib.Util.Bytes.extract_append_of_le _ _ (by rw [hsz]; omega)]
    exact relayFrontAt_ct kem cipher macS kdfS streamS geom _ _ _ _ _ _
      (Cryptlib.Util.Bytes.size_ofVector _) hsz
  obtain ⟨skf, hskf⟩ : ∃ skf : Role → kem.PrivateKey,
      skf = fun h => if h = .relay then k.2 else st.2.2 h := ⟨_, rfl⟩
  have hrel' : skf .relay = k.2 := by rw [hskf]; simp
  have hsk : ∀ h, h ≠ Role.relay → st.2.2 h = skf h := fun h hr => by rw [hskf]; simp [hr]
  obtain ⟨Dd, hDd⟩ : ∃ Dd : Block geom → Block geom, Dd = (fun y => if y = u then
          shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o (ofVector U)
        else v) := ⟨_, rfl⟩
  have hW1 : W.2.1 = (encapOf kem k.1.1 s).1 := by rw [hW]; rfl
  have hW2 : W.2.2 = headerHand kem macS geom km (ofVector U) Hv Dd := by
    rw [hW, hHv, hDd]
    rfl
  rw [viaOracle_congr kem cipher macS kdfS streamS geom hvalid hmactag h16
      .relay st.2.2 skf hsk, hW1, hW2]
  simp only [StateT.run'_eq, simulateQ_map]
  have hf : ∀ o' : RSOR.Onion geom,
      relayAns kem cipher macS kdfS streamS geom (skf .relay) (encapOf kem k.1.1 s).1
          (headerHand kem macS geom km (ofVector U) Hv Dd) (RSOR.join o')
        = if o'.1 = Hv then procKeysD kem macS geom km (ofVector U)
            (ofVector (Dd o'.2)) (RSOR.join o')
          else relayAns kem cipher macS kdfS streamS geom (skf .relay)
            (encapOf kem k.1.1 s).1 (fun _ => none) (RSOR.join o') := fun o' => by
    rw [hrel']
    exact relayAns_headerHand kem cipher macS kdfS streamS geom hvalid k.2 _ km (ofVector U) Hv Dd
      hcar o'
  have hvo := viaOracle_header kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay skf
    (encapOf kem k.1.1 s).1 (headerHand kem macS geom km (ofVector U) Hv Dd) km (ofVector U)
    Hv Dd hf W.1.patch (A.guess st.1 W.1.onion) st.2.1
  rw [hrel'] at hvo
  rw [hvo]
  rw [hskf, hDd, hHv]

/-! ## World 1 with its random payload drawn first -/

/-- **World 1's relay may draw its random payload first.** The game where the relay answers
one header and the challenger patches its answers as in world 1 is the game that draws the
random payload `g` first and patches with it. -/
theorem headerRelays_patchWith_draw {pk kb ks : Key kem} (names : Role → RSOR.Name)
    (c : Protocols.RSOR.ForwardChallenge (S := 𝒮)
      (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk kb ks))
    (next : RSOR.Onion geom) (r : RSOR.Randomness geom) (mine : RSOR.Onion geom)
    (sk : Role → kem.PrivateKey) (ct : kem.Ciphertext) (km : Vector UInt8 32) (U : ByteArray)
    (Hv : Vector UInt8 geom.headerLength) (D : Block geom → Block geom)
    {α : Type} (oa : OracleComp (Protocols.RSOR.oracleSpec 𝒮) α)
    (log : Protocols.RSOR.Log 𝒮) :
    (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16
        .relay sk ct km U Hv D
        (c.patchWith next r mine)) oa).run' log
      =ᵈ $ᵗ (Block geom) >>= fun g =>
        (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16
            .relay sk ct km U Hv
          D
          (c.patchDrawn next r mine g)) oa).run' log := by
  have h := c.patchWith_draw next r mine
    (fun (h : Role) (o : RSOR.Onion geom) => pure (if h = Role.relay ∧ o.1 = Hv then
        RSOR.stepOf geom (procKeysD kem macS geom km U (ofVector (D o.2)) (RSOR.join o))
      else if h = .relay then
        RSOR.stepOf geom
          (relayAns kem cipher macS kdfS streamS geom (sk .relay) ct (fun _ => none) (RSOR.join o))
      else RSOR.proc kem cipher macS kdfS streamS geom (sk h) o))
    (fun (h : Role) (msg : RSOR.Msg geom) (o : RSOR.Onion geom) =>
      pure (if h = Role.relay ∧ o.1 = Hv then
        RSOR.replyOf cipher geom msg
          (procKeysD kem macS geom km U (ofVector (D o.2)) (RSOR.join o))
      else if h = .relay then
        RSOR.replyOf cipher geom msg
          (relayAns kem cipher macS kdfS streamS geom (sk .relay) ct (fun _ => none) (RSOR.join o))
      else RSOR.reply kem cipher macS kdfS streamS geom (sk h) msg o))
    oa log
  have h2 := h.map Prod.fst
  rw [map_bind] at h2
  exact h2

/-! ## Two relays that answer one header alike -/

/-- **A patched relay that answers one header is an unpatched one.** If the patch changes
answers under the header `Hv` at `.relay` only, and there takes the answers from the keystream
`U₁` and the decryption `D₁` to the answers from `U₀` and `D₀`, the two games are the same. -/
theorem headerRelays_patch_eq (sk : Role → kem.PrivateKey) (ct : kem.Ciphertext)
    (km : Vector UInt8 32) (U₀ U₁ : ByteArray) (Hv : Vector UInt8 geom.headerLength)
    (D₀ D₁ : Block geom → Block geom) (patch : Protocols.RSOR.Patch 𝒮)
    (hstep : ∀ o : RSOR.Onion geom, o.1 = Hv →
      patch.proc .relay o (RSOR.stepOf geom
          (procKeysD kem macS geom km U₁ (ofVector (D₁ o.2)) (RSOR.join o)))
        = pure (RSOR.stepOf geom
          (procKeysD kem macS geom km U₀ (ofVector (D₀ o.2)) (RSOR.join o))))
    (hrep : ∀ (m : RSOR.Msg geom) (o : RSOR.Onion geom), o.1 = Hv →
      patch.reply .relay m o (RSOR.replyOf cipher geom m
          (procKeysD kem macS geom km U₁ (ofVector (D₁ o.2)) (RSOR.join o)))
        = RSOR.replyOf cipher geom m
          (procKeysD kem macS geom km U₀ (ofVector (D₀ o.2)) (RSOR.join o)))
    (hproc : ∀ (h : Role) (o : RSOR.Onion geom) out, ¬ (h = .relay ∧ o.1 = Hv) →
      patch.proc h o out = pure out)
    (hreply : ∀ (h : Role) (m : RSOR.Msg geom) (o : RSOR.Onion geom) out,
      ¬ (h = .relay ∧ o.1 = Hv) → patch.reply h m o out = out) :
    headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay sk ct km U₁ Hv D₁ patch
      = headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16
          .relay sk ct km U₀ Hv D₀ {} := by
  refine Protocols.RSOR.oracle_pure_patch (S := 𝒮) patch _ _ _ _ (fun h o => ?_)
    (fun h m o => ?_)
  · by_cases hc : h = Role.relay ∧ o.1 = Hv
    · obtain ⟨rfl, ho⟩ := hc
      exact (congrArg (patch.proc Role.relay o) (ite_eq_left ⟨rfl, ho⟩)).trans
        ((hstep o ho).trans (congrArg pure (ite_eq_left ⟨rfl, ho⟩).symm))
    · exact (congrArg (patch.proc h o) (ite_eq_right hc)).trans
        ((hproc h o _ hc).trans (congrArg pure (ite_eq_right hc).symm))
  · by_cases hc : h = Role.relay ∧ o.1 = Hv
    · obtain ⟨rfl, ho⟩ := hc
      exact (congrArg (patch.reply Role.relay m o) (ite_eq_left ⟨rfl, ho⟩)).trans
        ((hrep m o ho).trans (ite_eq_left ⟨rfl, ho⟩).symm)
    · exact (congrArg (patch.reply h m o) (ite_eq_right hc)).trans
        ((hreply h m o _ hc).trans (ite_eq_right hc).symm)

/-! ## The truncated path and the mixed randomness -/

namespace RSOR

omit hvalid hmactag h16 in
/-- A route truncated within its length has the length it was truncated to. -/
theorem take_length {N : ℕ} {Nm Ky : Type} (R : Protocols.RSOR.Route N Nm Ky) (k : ℕ)
    (hk : k ≤ R.hops.length) : (R.take k).hops.length = k := by
  simp [Protocols.RSOR.Route.take]
  omega

omit hvalid hmactag h16 in
/-- A hop before the last of a truncated route is the same hop of the route. -/
theorem path_take_getElem! (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last last' : List RoutingCommand) (k i : ℕ) (hi : i + 1 < k) (hk : k ≤ R.hops.length) :
    (path kem (R.take k) last)[i]! = (path kem R last')[i]! := by
  have hl : (R.take k).hops.length = k := by simp [Protocols.RSOR.Route.take]; omega
  rw [path_getElem! kem _ _ _ (by omega), path_getElem! kem _ _ _ (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega)]
  simp [Protocols.RSOR.Route.take]

omit hvalid hmactag h16 in
/-- The last hop of a truncated route has that hop's name and key, and the last commands. -/
theorem path_take_last (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last : List RoutingCommand) (j : ℕ) (hj : j < R.hops.length) :
    (path kem (R.take (j + 1)) last)[j]!
      = ⟨R.hops[j].name, ofVector (kem.encodePublicKey R.hops[j].key.1), last⟩ := by
  have hl : (R.take (j + 1)).hops.length = j + 1 := by simp [Protocols.RSOR.Route.take]; omega
  rw [path_getElem! kem _ _ _ (by omega), ite_eq_left (by omega)]
  simp [Protocols.RSOR.Route.take]

/-- The original's randomness with the seeds of the first `j` forward hops taken from the
replacement's. -/
def mixSeeds (r r' : Randomness geom) (j : ℕ) : Randomness geom :=
  ((Vector.ofFn fun i : Fin geom.nrHops =>
      if i.val < j then r'.1.1[i.val]'i.isLt else r.1.1[i.val]'i.isLt, r.1.2),
    r.2)

omit hvalid hmactag h16 in
theorem mixSeeds_getElem! (r r' : Randomness geom) (j k : ℕ) (hk : k < geom.nrHops) :
    (mixSeeds geom r r' j).1.1.toArray[k]!
      = if k < j then r'.1.1.toArray[k]! else r.1.1.toArray[k]! := by
  rw [getElem!_pos _ _ (by simpa using hk)]
  split_ifs <;> simp [mixSeeds, getElem!_pos, *]

omit hvalid hmactag h16 in
/-- Mixing twice gives the original back. -/
theorem mixSeeds_mixSeeds (r r' : Randomness geom) (j : ℕ) :
    mixSeeds geom (mixSeeds geom r r' j) (mixSeeds geom r' r j) j = r := by
  obtain ⟨⟨a, f⟩, b⟩ := r
  obtain ⟨⟨a', f'⟩, b'⟩ := r'
  unfold mixSeeds
  refine Prod.ext (Prod.ext (Vector.ext fun i hi => ?_) rfl) rfl
  by_cases h : i < j <;> simp [h]

omit hvalid hmactag h16 in
/-- **The mixed randomness is uniform.** A game that reads two uniform draws through their
mix reads one uniform draw. -/
theorem evalDistEq_mixSeeds {δ : Type} (j : ℕ) (K : Randomness geom → ProbComp δ) :
    (do let r ← $ᵗ (Randomness geom); let r' ← $ᵗ (Randomness geom); K (mixSeeds geom r r' j))
      =ᵈ ($ᵗ (Randomness geom) >>= K) := by
  have hb : Function.Bijective (Function.uncurry fun (r r' : Randomness geom) =>
      (mixSeeds geom r r' j, mixSeeds geom r' r j)) :=
    Function.Involutive.bijective fun p => by
      obtain ⟨r, r'⟩ := p
      exact Prod.ext (mixSeeds_mixSeeds geom r r' j) (mixSeeds_mixSeeds geom r' r j)
  have hid : Function.Bijective (Function.uncurry fun (a b : Randomness geom) => (a, b)) :=
    Function.bijective_id
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective hb fun p => K p.1) ?_
  refine EvalDistEq.trans (evalDistEq_pair_of_bijective hid fun p => K p.1).symm ?_
  exact EvalDistEq.bind_right _ fun r =>
    OracleComp.EvalDistEq.bind_const ($ᵗ (Randomness geom)) (K r)

omit hvalid hmactag h16 in
/-- After position `j` the mixed randomness has the original's seeds. -/
theorem mixSeeds_extract_after (r r' : Randomness geom) (j n : ℕ) (hn : n ≤ geom.nrHops) :
    ((mixSeeds geom r r' j).1.1.toArray.extract 0 n).extract (j + 1)
        ((mixSeeds geom r r' j).1.1.toArray.extract 0 n).size
      = (r.1.1.toArray.extract 0 n).extract (j + 1) (r.1.1.toArray.extract 0 n).size := by
  apply Array.ext
  · simp
  · intro i h1 h2
    have hi : j + 1 + i < n := by
      simp at h1
      omega
    simp [mixSeeds, show ¬ (j + 1 + i < j) by omega]

omit hvalid hmactag h16 in
/-- **The layers in front of the relay are the replacement's.** On the original's path with
the mixed randomness, the layers of the hops before the honest relay are those on the
replacement's path with the replacement's randomness. -/
theorem wrapUp_mixSeeds (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last last' : List RoutingCommand) (r r' : Randomness geom) (j : ℕ)
    (hj : j < R.hops.length) (L : ByteArray) :
    wrapUp kem cipher macS kdfS streamS geom (path kem R last) (mixSeeds geom r r' j).1 0 j L
      = wrapUp kem cipher macS kdfS streamS geom (path kem (R.take (j + 1)) last') r'.1 0 j
        L := by
  have hl : (R.take (j + 1)).hops.length = j + 1 := by simp [Protocols.RSOR.Route.take]; omega
  have hle := R.length_le
  refine wrapUp_congr geom kem kdfS streamS cipher macS _ _ _ _ (by rw [path_size]; exact hle)
    (by rw [path_size, hl]; omega) 0 j L fun k _ hk => ⟨by rw [path_size]; omega,
      by rw [path_size, hl]; omega,
      (path_take_getElem! kem geom R last' last (j + 1) k (by omega) (by omega)).symm, ?_, ?_⟩
  · by_cases hkj : k + 1 < j
    · rw [path_take_getElem! kem geom R last' last (j + 1) (k + 1) (by omega) (by omega)]
    · obtain rfl : k + 1 = j := by omega
      rw [path_take_last kem geom R last' (k + 1) hj, path_getElem! kem R last (k + 1) hj]
  · rw [mixSeeds_getElem! geom r r' j k (by omega), ite_eq_left (by omega)]

omit hvalid hmactag h16 in
/-- The hops before the relay have the same keys on the original's path with the mixed
randomness as on the replacement's path with the replacement's randomness. -/
theorem kemHopKeys_mixSeeds (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last last' : List RoutingCommand) (r r' : Randomness geom) (j : ℕ)
    (hj : j < R.hops.length) (m : ℕ) (hm : m < j) :
    kemHopKeys kem kdfS (path kem R last)
        ((mixSeeds geom r r' j).1.1.toArray.extract 0 (path kem R last).size) m
      = kemHopKeys kem kdfS (path kem (R.take (j + 1)) last')
        (r'.1.1.toArray.extract 0 (path kem (R.take (j + 1)) last').size) m := by
  have hl : (R.take (j + 1)).hops.length = j + 1 := take_length R (j + 1) (by omega)
  have hle := R.length_le
  have hx : ∀ (a : Array (Vector UInt8 32)) (n m : ℕ), m < n → n ≤ a.size →
      (a.extract 0 n)[m]! = a[m]! := fun a n m h1 h2 => by
    rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega)]
    simp
  unfold kemHopKeys
  rw [← path_take_getElem! kem geom R last' last (j + 1) m (by omega) (by omega),
    hx _ _ m (by rw [path_size]; omega) (by rw [path_size]; simpa using hle),
    hx _ _ m (by rw [path_size, hl]; omega) (by rw [path_size, hl]; simp; omega),
    mixSeeds_getElem! geom r r' j m (by omega), ite_eq_left hm]

omit hvalid hmactag h16 in
/-- The message is at the end of the sender's payload. -/
theorem msgOf_body (q : Request kem geom) (r : Randomness geom) :
    msgOf geom (body kem macS kdfS streamS geom q r) = q.msg := by
  unfold msgOf body
  rw [ByteArray.size_append, Util.Bytes.size_ofVector, Nat.add_sub_cancel]
  have h := Util.Bytes.extract_append_right
    ((⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ : ByteArray)
      ++ (surb kem macS kdfS streamS geom q r).1) (ofVector q.msg)
  rw [Util.Bytes.size_ofVector] at h
  rw [h, Cryptlib.Protocols.Sphinx.Common.toVecN_ofVector]

omit h16 in
include hvalid hmactag in
/-- **A sender's payload has one length**, whatever the request and the randomness: the two
flag bytes, a reply block, and the message. -/
theorem body_size (q : Request kem geom) (r : Randomness geom) :
    (body kem macS kdfS streamS geom q r).size
      = 2 + geom.surbLength + geom.userForwardPayloadLength := by
  have hs : (surb kem macS kdfS streamS geom q r).1.size = geom.surbLength := by
    unfold surb
    dsimp only
    split
    · rename_i x hx
      exact newKEMSURB_size kem macS kdfS streamS geom _ _ _ _ hvalid hmactag x.1 x.2 hx
    · exact Array.size_replicate
  have h2 : (⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ : ByteArray).size = 2 := rfl
  unfold body
  rw [ByteArray.size_append, ByteArray.size_append, h2, hs, Util.Bytes.size_ofVector]

omit hvalid hmactag h16 in
/-- A request with no backward path has a payload that starts with the flag for no reply
block. -/
theorem body_get_zero (q : Request kem geom) (r : Randomness geom) (hq : q.back.hops = []) :
    (body kem macS kdfS streamS geom q r).get! 0 = 0 := by
  have h2 : (⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ : ByteArray).size = 2 := rfl
  unfold body
  rw [get!_eq_getElem _ 0 (by rw [ByteArray.size_append, ByteArray.size_append, h2]; omega),
    ByteArray.getElem_append_left (by rw [ByteArray.size_append, h2]; omega),
    ByteArray.getElem_append_left (by rw [h2]; omega)]
  simp only [hq, List.isEmpty_nil, ↓reduceIte]
  rfl

omit hvalid hmactag h16 in
/-- A block made of the zero tag and a payload begins with the zero tag and has the payload
behind it. -/
theorem zeroTag_block (X : ByteArray) (hX : X.size = geom.forwardPayloadLength) :
    ((ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ X))).extract 0
        geom.payloadTagLength).data.all (· == 0) = true
      ∧ (ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
          ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ X))).extract
            geom.payloadTagLength
            (ofVector (Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
              ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) ++ X))).size
        = X := by
  have hz : (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray).size
      = geom.payloadTagLength := Array.size_replicate
  rw [Util.Bytes.ofVector_toVecN _ (by rw [ByteArray.size_append, hz, hX])]
  constructor
  · have h := Util.Bytes.extract_append_left
      (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) X
    rw [hz] at h
    rw [h]
    show (Array.replicate geom.payloadTagLength (0 : UInt8)).all (· == 0) = true
    rw [Array.all_eq_true]
    intro i hi
    simp
  · have h := Util.Bytes.extract_append_right
      (⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray) X
    rw [hz] at h
    rw [ByteArray.size_append, hz, h]

omit h16 in
include hvalid hmactag in
set_option maxHeartbeats 1000000 in
/-- **The shifted keystream on the game's paths.** Before the end of the original's path, with
the mixed randomness and the shifted keystream, the honest relay has the next layer the
original has with its own randomness, and the header bytes the replacement has. -/
theorem shiftStream_path (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last last' : List RoutingCommand) (r r' : Randomness geom) (payload : ByteArray) (j : ℕ)
    (c U U' fwd : ByteArray) (hn : j + 1 < R.hops.length)
    (hU : U.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hU' : U'.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hc : c.size = kem.ciphertextSize)
    (hfwd : layerPast kem cipher macS kdfS streamS geom (path kem R last) r.1 payload j U'
      (j + 1) = .ok fwd)
    (hs' : (relayFrontLast kem kdfS streamS geom (path kem (R.take (j + 1)) last') r'.1 j c
      U).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength) :
    layerPast kem cipher macS kdfS streamS geom (path kem R last) (mixSeeds geom r r' j).1 payload j
        (shiftStream geom kem kdfS streamS (path kem R last) (path kem (R.take (j + 1)) last')
          r.1 (mixSeeds geom r r' j).1 r'.1 j c U U' fwd) (j + 1) = .ok fwd
      ∧ relayFront kem cipher macS kdfS streamS geom (path kem R last) (mixSeeds geom r r' j).1
          payload j c
          (shiftStream geom kem kdfS streamS (path kem R last) (path kem (R.take (j + 1)) last')
            r.1 (mixSeeds geom r r' j).1 r'.1 j c U U' fwd)
        = relayFrontLast kem kdfS streamS geom (path kem (R.take (j + 1)) last') r'.1 j c U := by
  have hl : (R.take (j + 1)).hops.length = j + 1 := by simp [Protocols.RSOR.Route.take]; omega
  have hle := R.length_le
  refine shiftStream_spec geom kem kdfS streamS cipher macS hvalid hmactag _ _ _ _ _ payload j
    c U U' fwd (by rw [path_size]; exact hn) (by rw [path_size]; exact hle)
    (by rw [path_size, hl]) hU hU' hc rfl
    (mixSeeds_extract_after geom r r' j _ (by rw [path_size]; exact hle))
    (kemHopKeys_mixSeeds kem kdfS geom R last last' r r' j (by omega)) ?_ hfwd hs'
  rw [path_getElem! kem R last j (by omega), ite_eq_right (by omega)]

omit h16 in
include hvalid in
set_option maxHeartbeats 1000000 in
/-- **The relabelled draws are uniform, before the end of the path.** A game that reads the
two randomness draws through their mix, and the two keystreams through the shifted keystream,
reads one randomness draw and one keystream. -/
theorem evalDistEq_shiftStream {δ : Type} (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last last' : List RoutingCommand) (payload : Randomness geom → ByteArray) (j : ℕ)
    (hn : j + 1 < R.hops.length) (c : ByteArray)
    (K : Keystream geom → Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (Randomness geom)
      let r' ← $ᵗ (Randomness geom)
      let U ← $ᵗ (Keystream geom)
      let U' ← $ᵗ (Keystream geom)
      K (Util.Bytes.toVecN _ (shiftStream geom kem kdfS streamS (path kem R last)
          (path kem (R.take (j + 1)) last') r.1 (mixSeeds geom r r' j).1 r'.1 j c (ofVector U)
          (ofVector U')
          (match layerPast kem cipher macS kdfS streamS geom (path kem R last) r.1 (payload r) j
              (ofVector U') (j + 1) with
            | .ok f => f
            | .error _ => ByteArray.empty)))
        (mixSeeds geom r r' j))
      =ᵈ (do
        let r ← $ᵗ (Randomness geom)
        let U ← $ᵗ (Keystream geom)
        K U r) := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hle := R.length_le
  have hjp : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  obtain ⟨h, hh⟩ : ∃ h, h = geom.routingInfoLength + geom.perHopRoutingInfoLength
      - (j + 1) * geom.perHopRoutingInfoLength := ⟨_, rfl⟩
  have hht : h + (j + 1) * geom.perHopRoutingInfoLength
      = geom.routingInfoLength + geom.perHopRoutingInfoLength := by omega
  have hh' : geom.routingInfoLength - j * geom.perHopRoutingInfoLength = h := by
    rw [Nat.succ_mul] at hh hjp
    omega
  have step : ∀ r r' : Randomness geom,
      (do
        let U ← $ᵗ (Keystream geom)
        let U' ← $ᵗ (Keystream geom)
        K (Util.Bytes.toVecN _ (shiftStream geom kem kdfS streamS (path kem R last)
            (path kem (R.take (j + 1)) last') r.1 (mixSeeds geom r r' j).1 r'.1 j c (ofVector U)
            (ofVector U')
            (match layerPast kem cipher macS kdfS streamS geom (path kem R last) r.1 (payload r) j
                (ofVector U')
                (j + 1) with
              | .ok f => f
              | .error _ => ByteArray.empty)))
          (mixSeeds geom r r' j))
        =ᵈ ($ᵗ (Keystream geom) >>= fun U₀ => K U₀ (mixSeeds geom r r' j)) := fun r r' => by
    obtain ⟨F, hF⟩ : ∃ F : ByteArray → ByteArray, F = fun T =>
        match layerPast kem cipher macS kdfS streamS geom (path kem R last) r.1 (payload r) j
            (zeroBytes h ++ T)
            (j + 1) with
          | .ok f => f
          | .error _ => ByteArray.empty := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A : ByteArray → ByteArray, A = (fun T => xorBytes
              (lastFrag geom kem (path kem (R.take (j + 1)) last') j c
                ++ (zeroFiller geom kem kdfS streamS (path kem (R.take (j + 1)) last') r'.1
                  j).extract 0
                  ((geom.nrHops - (path kem (R.take (j + 1)) last').size)
                    * geom.perHopRoutingInfoLength))
              (midFrag geom kem (path kem R last) j (F T)
                ++ (F T).extract (2 + kem.ciphertextSize)
                  (2 + kem.ciphertextSize
                    + ((path kem R last).size - (j + 1)) * geom.perHopRoutingInfoLength)
                ++ (midPad geom kem kdfS streamS (path kem R last) (mixSeeds geom r r' j).1
                  j).extract 0
                  ((geom.nrHops - (path kem R last).size) * geom.perHopRoutingInfoLength))) := ⟨_,
                      rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : ByteArray, B = (xorBytes
              ((fillerAtF kem kdfS streamS geom (path kem R last)
                (r.1.1.toArray.extract 0 (path kem R last).size)
                ((ofVector r.1.2).extract 0
                  ((geom.nrHops - (path kem R last).size) * geom.perHopRoutingInfoLength)) j
                (zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength))
                (j + 1)).extract
                  ((geom.nrHops - (path kem R last).size) * geom.perHopRoutingInfoLength)
                  ((geom.nrHops - (path kem R last).size) * geom.perHopRoutingInfoLength
                    + (j + 1) * geom.perHopRoutingInfoLength))
              ((fillerAtF kem kdfS streamS geom (path kem R last)
                ((mixSeeds geom r r' j).1.1.toArray.extract 0 (path kem R last).size)
                ((ofVector r.1.2).extract 0
                  ((geom.nrHops - (path kem R last).size) * geom.perHopRoutingInfoLength)) j
                (zeroBytes (geom.routingInfoLength + geom.perHopRoutingInfoLength))
                (j + 1)).extract
                  ((geom.nrHops - (path kem R last).size) * geom.perHopRoutingInfoLength)
                  ((geom.nrHops - (path kem R last).size) * geom.perHopRoutingInfoLength
                    + (j + 1) * geom.perHopRoutingInfoLength))) := ⟨_, rfl⟩
    have hform : ∀ U U' : Keystream geom,
        shiftStream geom kem kdfS streamS (path kem R last) (path kem (R.take (j + 1)) last')
          r.1 (mixSeeds geom r r' j).1 r'.1 j c (ofVector U) (ofVector U')
          (match layerPast kem cipher macS kdfS streamS geom (path kem R last) r.1 (payload r) j
              (ofVector U') (j + 1) with
            | .ok f => f
            | .error _ => ByteArray.empty)
        = xorBytes ((ofVector U).extract 0 h)
            (A ((ofVector U').extract h
              (geom.routingInfoLength + geom.perHopRoutingInfoLength)))
          ++ xorBytes ((ofVector U').extract h
              (geom.routingInfoLength + geom.perHopRoutingInfoLength)) B := by
      intro U U'
      have hT : ((ofVector U').extract h
          (geom.routingInfoLength + geom.perHopRoutingInfoLength)).size
          = (j + 1) * geom.perHopRoutingInfoLength := by
        rw [ByteArray.size_extract, Util.Bytes.size_ofVector]
        omega
      have hL := layerPast_tail geom kem kdfS streamS cipher macS hrouting (path kem R last) r.1
        (payload r) j (ofVector U')
        (zeroBytes h ++ (ofVector U').extract h
          (geom.routingInfoLength + geom.perHopRoutingInfoLength))
        (Util.Bytes.size_ofVector _)
        (by rw [ByteArray.size_append, zeroBytes_size, hT]; exact hht)
        (by rw [path_size]; exact hle) (by rw [path_size]; exact hn)
        (by
          rw [← hh]
          have h1 := Util.Bytes.extract_append_right (zeroBytes h) ((ofVector U').extract h
            (geom.routingInfoLength + geom.perHopRoutingInfoLength))
          rw [zeroBytes_size, hT, hht] at h1
          exact h1.symm)
      unfold shiftStream
      rw [hL, hh', ← hh, hA, hB, hF]
    simp only [hform]
    exact evalDistEq_headTail hht A B (fun U₀ => K U₀ (mixSeeds geom r r' j))
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun r => EvalDistEq.bind_right _ fun r' =>
    step r r') ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun r =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ fun r' U₀ => K U₀ (mixSeeds geom r r' j)) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _
    fun r U₀ => $ᵗ (Randomness geom) >>= fun r' => K U₀ (mixSeeds geom r r' j)) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U₀ =>
    evalDistEq_mixSeeds geom j (K U₀)) ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ fun U₀ r => K U₀ r

omit hmactag h16 in
include hvalid in
/-- **The relabelled draws are uniform, at the end of the path.** A game that reads the two
randomness draws through their mix, and the keystream with its head shifted, reads one
randomness draw and one keystream. -/
theorem evalDistEq_lastShift {δ : Type} (R : Protocols.RSOR.Route geom.nrHops Name (Key kem))
    (last last' : List RoutingCommand) (j : ℕ) (hj : j < R.hops.length) (c : ByteArray)
    (K : Keystream geom → Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (Randomness geom)
      let r' ← $ᵗ (Randomness geom)
      let U ← $ᵗ (Keystream geom)
      K (Util.Bytes.toVecN _ (lastShift geom kem kdfS streamS (path kem R last)
          (path kem (R.take (j + 1)) last') (mixSeeds geom r r' j).1 r'.1 j c (ofVector U)))
        (mixSeeds geom r r' j))
      =ᵈ (do
        let r ← $ᵗ (Randomness geom)
        let U ← $ᵗ (Keystream geom)
        K U r) := by
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hle := R.length_le
  have hjp : (j + 1) * geom.perHopRoutingInfoLength ≤ geom.routingInfoLength := by
    rw [hrouting, Nat.mul_comm geom.perHopRoutingInfoLength]
    exact Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at hjp
  have hht : geom.routingInfoLength - j * geom.perHopRoutingInfoLength
      + (j * geom.perHopRoutingInfoLength + geom.perHopRoutingInfoLength)
      = geom.routingInfoLength + geom.perHopRoutingInfoLength := by omega
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun r => EvalDistEq.bind_right _ fun r' =>
    evalDistEq_headPad hht _ (fun U₀ => K U₀ (mixSeeds geom r r' j))) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun r =>
    OracleComp.EvalDistEq.bind_bind_swap _ _ fun r' U₀ => K U₀ (mixSeeds geom r r' j)) ?_
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_bind_swap _ _
    fun r U₀ => $ᵗ (Randomness geom) >>= fun r' => K U₀ (mixSeeds geom r r' j)) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun U₀ =>
    evalDistEq_mixSeeds geom j (K U₀)) ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ fun U₀ r => K U₀ r

end RSOR

/-! ## The exit relay's reply -/

namespace RSOR

omit h16 in
include hvalid hmactag in
/-- **A reply from the sender's own payload is the first layer of the reply onion.** -/
theorem replyOf_body (q : Request kem geom) (r : Randomness geom) (m : Msg geom)
    (hr : Reliable kem cipher macS kdfS streamS geom q r) (hjlt : 0 < q.back.hops.length)
    (tag : Vector UInt8 32) (cmds : List RoutingCommand) :
    replyOf cipher geom m (some (some (body kem macS kdfS streamS geom q r), tag, cmds, none))
      = some (q.back.hops[0].name,
        formBack kem cipher macS kdfS streamS geom q r m ⟨0, hjlt⟩) := by
  obtain ⟨-, x0, keys, hx0, -, -, -, hnp, hP0⟩ :=
    replyPacket_eq kem cipher macS kdfS streamS geom hvalid hmactag q r m hr hjlt
  have hss : (surb kem macS kdfS streamS geom q r).1.size = geom.surbLength := by
    have := hnp
    unfold SURB.newPacketFromSURB at this
    by_contra hne
    simp [hne] at this
    cases this
  have hfl : (body kem macS kdfS streamS geom q r).get! 0 = 1 := by
    have hne : ¬ q.back.hops.isEmpty := by
      rw [List.isEmpty_iff]; exact List.ne_nil_of_length_pos hjlt
    have h2 : (⟨#[if q.back.hops.isEmpty then 0 else 1, 0]⟩ : ByteArray).size = 2 := rfl
    unfold body
    rw [get!_eq_getElem _ 0 (by rw [ByteArray.size_append, ByteArray.size_append, h2]; omega),
      ByteArray.getElem_append_left (by rw [ByteArray.size_append, h2]; omega),
      ByteArray.getElem_append_left (by rw [h2]; omega)]
    simp only [hne]
    rfl
  have hsb : (body kem macS kdfS streamS geom q r).extract 2 (2 + geom.surbLength)
      = (surb kem macS kdfS streamS geom q r).1 := by
    unfold body
    rw [Cryptlib.Util.Bytes.extract_append_of_le _ _ (by
      rw [ByteArray.size_append, hss]; exact Nat.le_refl _)]
    exact extract_append_tail _ _ _ _ rfl (by rw [hss])
  unfold replyOf formBack
  dsimp only
  rw [ite_eq_left hfl, hsb, hnp, hx0]
  dsimp only
  rw [hP0]
  rfl

end RSOR

/-! ## The two worlds before the end of the path -/

omit hvalid hmactag h16 in
/-- A header's bytes followed by a payload split into the two. -/
theorem split_append (P : ByteArray) (x : Block geom) (hP : P.size = geom.headerLength) :
    RSOR.split geom (P ++ ofVector x) = (toVecN _ P, x) := by
  have e1 : (P ++ ofVector x).extract 0 geom.headerLength = P := by
    rw [← hP]
    exact Util.Bytes.extract_append_left P _
  have e2 : (P ++ ofVector x).extract geom.headerLength (P ++ ofVector x).size = ofVector x := by
    rw [← hP, ByteArray.size_append]
    exact Util.Bytes.extract_append_right P _
  unfold RSOR.split
  rw [e1, e2, Cryptlib.Protocols.Sphinx.Common.toVecN_ofVector]

set_option maxHeartbeats 1000000 in
/-- **Before the end of the path, world 1's patched relay is world 0's relay.** World 0's relay
has the header of a path that goes on, and forwards the next layer `fwd` with the payload it
decrypts: the next layer's own payload for the unchanged block, the random block `g`
otherwise. World 1's relay, whatever it would answer, is patched to forward the same. The two
games are the same when the headers agree and world 1's relay would not reply. -/
theorem headerRelays_forward_eq {pk kb ks : Key kem} (names : Role → RSOR.Name)
    (c : Protocols.RSOR.ForwardChallenge (S := 𝒮)
      (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk kb ks))
    (hn : c.pos + 1 < c.req.fwd.hops.length)
    (r : RSOR.Randomness geom) (mine : RSOR.Onion geom) (g : Block geom)
    (sk : Role → kem.PrivateKey) (ct : kem.Ciphertext) (km : Vector UInt8 32)
    (U₀ U₁ : ByteArray) (D₁ : Block geom → Block geom)
    (hops : Array PathHop) (d : RSOR.Draw geom) (payload : ByteArray) (j : ℕ)
    (cc fwd : ByteArray)
    (hj : j + 1 < hops.size) (hlen : hops.size ≤ geom.nrHops)
    (hU : U₀.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hc : cc.size = kem.ciphertextSize)
    (hfwd : layerPast kem cipher macS kdfS streamS geom hops d payload j U₀ (j + 1) = .ok fwd)
    (hs : (relayFront kem cipher macS kdfS streamS geom hops d payload j cc U₀).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hcmd : (hops[j]!).commands = [])
    (hname : (hops[j + 1]!).id = c.req.fwd.hops[c.pos.val + 1].name)
    (hmine : mine.1 = Util.Bytes.toVecN geom.headerLength
      (relayFront kem cipher macS kdfS streamS geom hops d payload j cc U₀
        ++ ofVector (macS.mac (ofVector km)
          (relayFront kem cipher macS kdfS streamS geom hops d payload j cc U₀))))
    (hrep : ∀ (m : RSOR.Msg geom) (o : RSOR.Onion geom), o.1 = mine.1 →
      RSOR.replyOf cipher geom m
        (procKeysD kem macS geom km U₁ (ofVector (D₁ o.2)) (RSOR.join o)) = none) :
    headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay sk ct km U₁ mine.1 D₁
        (c.patchDrawn (RSOR.split geom fwd) r mine g)
      = headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay sk ct km U₀ mine.1
        (fun y => if y = mine.2 then (RSOR.split geom fwd).2 else g) {} := by
  obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
  have had : adLength = 2 := rfl
  refine headerRelays_patch_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U₀ U₁
    mine.1 _ D₁ _ (fun o ho => ?_) (fun m o ho => ?_) (fun h o out hc => ?_)
    (fun h m o out hc => ?_)
  · obtain ⟨o1, o2⟩ := o
    obtain rfl : o1 = mine.1 := ho
    have hst := stepOf_relayFront geom kem kdfS streamS cipher macS hvalid hmactag hops d payload
      j cc U₀ fwd km (if o2 = mine.2 then (RSOR.split geom fwd).2 else g) o2 hj hlen hU hc hfwd hs
      (by omega) hcmd
    rw [← hmine] at hst
    have hfwd' := hfwd
    unfold layerPast at hfwd'
    have hfsz : fwd.size = geom.packetLength :=
      newKEMPacket_size kem cipher macS kdfS streamS geom _ _ _ _ _ hvalid hmactag hfwd'
        (newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hfwd').1
    have hH : 2 + kem.ciphertextSize + geom.routingInfoLength + macLength = geom.headerLength := by
      rw [hhdr, had]
    rw [hH] at hst
    unfold Protocols.RSOR.ForwardChallenge.patchDrawn
    dsimp only
    rw [hst, hname, split_append geom _ _ (by
      rw [ByteArray.size_extract]
      omega)]
    refine congrArg pure ((ite_eq_left ⟨rfl, rfl⟩).trans ((dite_eq_left hn).trans ?_))
    refine congrArg (fun z => some (Protocols.RSOR.Step.forward _ z)) ?_
    by_cases ho : o2 = mine.2
    · exact (ite_eq_left ho).trans (Prod.ext rfl (ite_eq_left ho).symm)
    · exact (ite_eq_right ho).trans (Prod.ext rfl (ite_eq_right ho).symm)
  · obtain ⟨o1, o2⟩ := o
    obtain rfl : o1 = mine.1 := ho
    have hrp := replyOf_relayFront geom kem kdfS streamS cipher macS hvalid hmactag hops d payload
      j cc U₀ fwd km (if o2 = mine.2 then (RSOR.split geom fwd).2 else g) o2 hj hlen hU hc hfwd hs
      (by omega) hcmd m
    rw [← hmine] at hrp
    have h1 := hrep m (mine.1, o2) rfl
    rw [hrp]
    unfold Protocols.RSOR.ForwardChallenge.patchDrawn Protocols.RSOR.ForwardChallenge.patchWith
    exact (ite_eq_right fun hx => absurd hx.2.2 (by omega)).trans h1
  · unfold Protocols.RSOR.ForwardChallenge.patchDrawn
    exact congrArg pure (ite_eq_right hc)
  · unfold Protocols.RSOR.ForwardChallenge.patchDrawn Protocols.RSOR.ForwardChallenge.patchWith
    exact ite_eq_right fun hx => hc ⟨hx.1, by rw [hx.2.1]⟩

/-! ## The two worlds at the end of the path -/

set_option maxHeartbeats 1000000 in
/-- **At the end of the path, world 1's patched relay is world 0's relay.** Both relays have
the header of a path that ends at them, and deliver when the block they decrypt begins with
the zero tag. The patch puts the original's message and reply in place of the replacement's.
The two games are the same when the headers agree, both senders' blocks begin with the zero
tag, and the random block for a changed payload does not. -/
theorem headerRelays_last_eq {pk kb ks : Key kem} (names : Role → RSOR.Name)
    (c : Protocols.RSOR.ForwardChallenge (S := 𝒮)
      (honOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk kb ks))
    (hl : c.pos + 1 = c.req.fwd.hops.length)
    (next : RSOR.Onion geom) (r : RSOR.Randomness geom) (mine : RSOR.Onion geom) (g : Block geom)
    (sk : Role → kem.PrivateKey) (ct : kem.Ciphertext) (km : Vector UInt8 32)
    (U₀ U₁ : ByteArray) (hops₀ hops₁ : Array PathHop) (d₀ d₁ : RSOR.Draw geom) (j : ℕ)
    (cc : ByteArray) (rc₁ : Vector UInt8 32) (B₀ B₁ v : Block geom)
    (hj₀ : j + 1 = hops₀.size) (hlen₀ : hops₀.size ≤ geom.nrHops)
    (hj₁ : j + 1 = hops₁.size) (hlen₁ : hops₁.size ≤ geom.nrHops)
    (hU₀ : U₀.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hU₁ : U₁.size = geom.routingInfoLength + geom.perHopRoutingInfoLength)
    (hc : cc.size = kem.ciphertextSize)
    (hs₀ : (relayFrontLast kem kdfS streamS geom hops₀ d₀ j cc U₀).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hs₁ : (relayFrontLast kem kdfS streamS geom hops₁ d₁ j cc U₁).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hcmd₀ : (hops₀[j]!).commands = [.recipient c.req.receiver])
    (hcmd₁ : (hops₁[j]!).commands = [.recipient rc₁])
    (hmine₀ : mine.1 = Util.Bytes.toVecN geom.headerLength
      (relayFrontLast kem kdfS streamS geom hops₀ d₀ j cc U₀
        ++ ofVector (macS.mac (ofVector km)
          (relayFrontLast kem kdfS streamS geom hops₀ d₀ j cc U₀))))
    (hmine₁ : mine.1 = Util.Bytes.toVecN geom.headerLength
      (relayFrontLast kem kdfS streamS geom hops₁ d₁ j cc U₁
        ++ ofVector (macS.mac (ofVector km)
          (relayFrontLast kem kdfS streamS geom hops₁ d₁ j cc U₁))))
    (hB₀ : ((ofVector B₀).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
    (hB₁ : ((ofVector B₁).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
    (hv : ¬ ((ofVector v).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
    (hbody : (ofVector B₀).extract geom.payloadTagLength (ofVector B₀).size
      = RSOR.body kem macS kdfS streamS geom c.req r)
    (hmsg : RSOR.msgOf geom (RSOR.body kem macS kdfS streamS geom c.req r) = c.req.msg)
    (hr : RSOR.Reliable kem cipher macS kdfS streamS geom c.req r) :
    headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay sk ct km U₁ mine.1
        (fun y => if y = mine.2 then B₁ else v) (c.patchDrawn next r mine g)
      = headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay sk ct km U₀ mine.1
        (fun y => if y = mine.2 then B₀ else v) {} := by
  have hx : 0 < geom.payloadTagLength + geom.forwardPayloadLength := by omega
  have hjlt : 0 < c.req.back.hops.length :=
    List.length_pos_iff.2 fun h => by simpa [h] using c.sender
  refine headerRelays_patch_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 sk ct km U₀ U₁
    mine.1 _ _ _ (fun o ho => ?_) (fun m o ho => ?_) (fun h o out hc => ?_)
    (fun h m o out hc => ?_)
  · obtain ⟨o1, o2⟩ := o
    obtain rfl : o1 = mine.1 := ho
    have h0 := stepOf_relayFrontLast geom kem kdfS streamS macS hvalid hmactag hops₀ d₀ j cc U₀
      km (if o2 = mine.2 then B₀ else v) o2 hj₀ hlen₀ hU₀ hc hs₀ hx _ hcmd₀
    have h1 := stepOf_relayFrontLast geom kem kdfS streamS macS hvalid hmactag hops₁ d₁ j cc U₁
      km (if o2 = mine.2 then B₁ else v) o2 hj₁ hlen₁ hU₁ hc hs₁ hx _ hcmd₁
    rw [← hmine₀] at h0
    rw [← hmine₁] at h1
    unfold Protocols.RSOR.ForwardChallenge.patchDrawn
    dsimp only
    rw [h0, h1]
    refine congrArg pure ((ite_eq_left ⟨rfl, rfl⟩).trans ((dite_eq_right (by omega)).trans ?_))
    by_cases ho : o2 = mine.2
    · rw [ite_eq_left ho, ite_eq_left ho, ite_eq_left hB₀, ite_eq_left hB₁, hbody, hmsg]
      rfl
    · rw [ite_eq_right ho, ite_eq_right ho, ite_eq_right hv, ite_eq_right hv]
      rfl
  · obtain ⟨o1, o2⟩ := o
    obtain rfl : o1 = mine.1 := ho
    have h0 := replyOf_relayFrontLast geom kem kdfS streamS cipher macS hvalid hmactag hops₀ d₀ j
      cc U₀ km (if o2 = mine.2 then B₀ else v) o2 hj₀ hlen₀ hU₀ hc hs₀ hx _ hcmd₀ m
    have h1 := replyOf_relayFrontLast geom kem kdfS streamS cipher macS hvalid hmactag hops₁ d₁ j
      cc U₁ km (if o2 = mine.2 then B₁ else v) o2 hj₁ hlen₁ hU₁ hc hs₁ hx _ hcmd₁ m
    rw [← hmine₀] at h0
    rw [← hmine₁] at h1
    rw [h0, h1]
    unfold Protocols.RSOR.ForwardChallenge.patchDrawn Protocols.RSOR.ForwardChallenge.patchWith
    by_cases ho : o2 = mine.2
    · subst ho
      refine (ite_eq_left ⟨rfl, rfl, hl⟩).trans ?_
      rw [ite_eq_left rfl, ite_eq_left hB₀, hbody,
        RSOR.replyOf_body kem cipher macS kdfS streamS geom hvalid hmactag c.req r m hr hjlt]
      rfl
    · refine (ite_eq_right fun hx' => ho (congrArg Prod.snd hx'.2.1)).trans ?_
      rw [ite_eq_right ho, ite_eq_right ho, ite_eq_right hv, ite_eq_right hv]
  · unfold Protocols.RSOR.ForwardChallenge.patchDrawn
    exact congrArg pure (ite_eq_right hc)
  · unfold Protocols.RSOR.ForwardChallenge.patchDrawn Protocols.RSOR.ForwardChallenge.patchWith
    exact ite_eq_right fun hx' => hc ⟨hx'.1, by rw [hx'.2.1]⟩

/-! ## World 1's relay does not reply -/

set_option maxHeartbeats 1000000 in
/-- **World 1's relay does not reply under the replacement's header.** The replacement has no
backward path, so its own block carries no reply block; and the ideal cipher's second block
does not begin with the zero tag. -/
theorem short_noreply (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1) (x : NextOth
        geom)
    (hb₁ : (RSOR.body kem macS kdfS streamS geom
        (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1) x.2.2.2.1.2.2.2).size
      = geom.forwardPayloadLength)
    (hv : ¬ ((ofVector x.2.2.2.2.2).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
    (m : RSOR.Msg geom) (o : RSOR.Onion geom)
    (ho : o.1 = Util.Bytes.toVecN geom.headerLength
      (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1 (encapOf kem
          k.1.1 x.2.2.1).1 (ofVector x.1)
        ++ ofVector (macS.mac (ofVector x.2.1)
          (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1 (encapOf
              kem k.1.1 x.2.2.1).1 (ofVector x.1))))) :
    RSOR.replyOf cipher geom m (procKeysD kem macS geom x.2.1 (ofVector x.1)
      (ofVector (if o.2 = x.2.2.2.2.1 then
          shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
              (ofVector x.1)
        else x.2.2.2.2.2)) (RSOR.join o)) = none := by
  obtain ⟨U, km, s, ⟨r, msg, nm, r'⟩, u, v⟩ := x
  obtain ⟨o1, o2⟩ := o
  dsimp only at hb₁ hv ho ⊢
  subst ho
  have hpos : (ch.c.pos : ℕ) < ch.c.req.fwd.hops.length := ch.c.pos.isLt
  have hp1 : (ch.c.pos : ℕ) + 1 = (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient
      (ch.c.short msg nm).receiver]).size :=
    ((RSOR.path_size kem _ _).trans (RSOR.take_length _ _ hpos)).symm
  have hle1 : (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg
      nm).receiver]).size ≤ geom.nrHops :=
    le_of_eq_of_le hp1.symm (le_trans hpos ch.c.req.fwd.length_le)
  have hcmd1 : ((RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg
      nm).receiver])[(ch.c.pos : ℕ)]!).commands = [.recipient (ch.c.short msg nm).receiver] :=
    congrArg (·.commands) (RSOR.path_take_last kem geom ch.c.req.fwd _ ch.c.pos hpos)
  have hnl1 : ¬ (ch.c.pos : ℕ) + 1 < (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient
      (ch.c.short msg nm).receiver]).size := Nat.not_lt.2 (Nat.le_of_eq hp1.symm)
  have hs1 := relayFrontLast_size geom kem kdfS streamS hvalid (RSOR.path kem (ch.c.req.fwd.take
      (ch.c.pos + 1)) [.recipient (ch.c.short msg nm).receiver]) r'.1 ch.c.pos (ofVector
      (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
    (ofVector U) hp1 hle1 (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) _ hcmd1
  have eM1 : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
      r') (encapOf kem k.1.1 s).1 (ofVector U)) = relayFrontLast kem kdfS streamS geom (RSOR.path
      kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg nm).receiver]) r'.1
      ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
      (ofVector U) := by
    unfold shortMU relayFrontAt
    exact ite_eq_right hnl1
  have eB1 : shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
      r') (ofVector U)
      = Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)
          ++ RSOR.body kem macS kdfS streamS geom (ch.c.short msg nm) r') := by
    unfold shortBlockU relayBackAt
    exact congrArg (Util.Bytes.toVecN _) (ite_eq_right hnl1)
  have h := replyOf_relayFrontLast geom kem kdfS streamS cipher macS hvalid hmactag (RSOR.path kem
      (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg nm).receiver]) r'.1
    ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) km
    (if o2 = u then shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r,
        msg, nm, r') (ofVector U) else v) o2 hp1 hle1
    (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) hs1 (by omega) _ hcmd1 m
  rw [← eM1] at h
  refine h.trans ?_
  by_cases hou : o2 = u
  · obtain ⟨hB1, hbody1⟩ := RSOR.zeroTag_block geom _ hb₁
    rw [← eB1] at hB1 hbody1
    rw [ite_eq_left hou, ite_eq_left hB1, hbody1]
    have hfl := RSOR.body_get_zero kem macS kdfS streamS geom (ch.c.short msg nm) r' rfl
    unfold RSOR.replyOf
    dsimp only
    rw [ite_eq_right (by rw [hfl]; decide)]
  · rw [ite_eq_right hou, ite_eq_right hv]

/-! ## World 1 is world 0 under the relabelling, before the end of the path -/

set_option maxHeartbeats 2000000 in
/-- **Before the end of the path, world 1 with its payload drawn is world 0 at the relabelled
draws.** World 0 is played with the mixed randomness, the shifted keystream, and the random
payload `g` in place of the ideal cipher's second block. -/
theorem nextDrawn_eq_forward (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (x : NextOth geom) (U' : Keystream geom) (g : Block geom) (fwd : ByteArray)
    (hn : ch.c.pos + 1 < ch.c.req.fwd.hops.length)
    (hfwd : layerPast kem cipher macS kdfS streamS geom
      (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) x.2.2.2.1.1.1
      (RSOR.body kem macS kdfS streamS geom ch.c.req x.2.2.2.1.1) ch.c.pos (ofVector U')
      (ch.c.pos + 1) = .ok fwd)
    (hsz : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
      (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)).size
        = 2 + kem.ciphertextSize + geom.routingInfoLength)
    (hb₁ : (RSOR.body kem macS kdfS streamS geom
        (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1) x.2.2.2.1.2.2.2).size
      = geom.forwardPayloadLength)
    (hv : ¬ ((ofVector x.2.2.2.2.2).extract 0 geom.payloadTagLength).data.all (· == 0) = true) :
    (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay
          (fun h => if h = .relay then k.2 else st.2.2 h) (encapOf kem k.1.1 x.2.2.1).1 x.2.1
          (ofVector x.1)
          (Util.Bytes.toVecN _
            (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)
              ++ ofVector (macS.mac (ofVector x.2.1)
                (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                  (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)))))
          (fun y => if y = x.2.2.2.2.1 then
              shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                (ofVector x.1)
            else x.2.2.2.2.2)
          (ch.c.patchDrawn (RSOR.split geom fwd) x.2.2.2.1.1
            (RSOR.split geom
              (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x)) g))
        (A.guess st.1 (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x
          (ofVector U')).1.onion)).run' st.2.1
      = forwardRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          (RSOR.Randomness geom) ($ᵗ RSOR.Randomness geom)
          (fun ch r c t =>
            { onion := onionK kem cipher macS kdfS streamS geom ch.c.req r ch.c.pos c t 0 }) A
          (forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (forwardViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          x.2.1
          (shiftStream geom kem kdfS streamS
            (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
            (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
              [.recipient (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1).receiver])
            x.2.2.2.1.1.1 (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos).1
            x.2.2.2.1.2.2.2.1 ch.c.pos
            (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 x.2.2.1).1))
            (ofVector x.1) (ofVector U') fwd)
          ⟨k, (ch, st), x.2.2.1, RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos⟩
          x.2.2.2.2.1 g := by
  obtain ⟨U, km, s, ⟨r, msg, nm, r'⟩, u, v⟩ := x
  dsimp only at hfwd hsz hb₁ hv ⊢
  have hpos : (ch.c.pos : ℕ) < ch.c.req.fwd.hops.length := ch.c.pos.isLt
  have hp1 : (RSOR.path kem (ch.c.short msg nm).fwd
      [.recipient (ch.c.short msg nm).receiver]).size = ch.c.pos + 1 :=
    (RSOR.path_size kem _ _).trans (RSOR.take_length _ _ hn.le)
  have hspec := RSOR.shiftStream_path kem cipher macS kdfS streamS geom hvalid hmactag
    ch.c.req.fwd [.recipient ch.c.req.receiver]
    [.recipient (ch.c.short msg nm).receiver] r r'
    (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U') fwd hn
    (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) hfwd
    (by
      unfold shortMU relayFrontAt at hsz
      dsimp only at hsz
      rw [ite_eq_right (by have := hp1; omega)] at hsz
      exact hsz)
  obtain ⟨hF, hM⟩ := hspec
  have hp0 : ch.c.pos + 1 < (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size :=
    lt_of_lt_of_eq hn (RSOR.path_size kem _ _).symm
  have e1 : forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
      (RSOR.mixSeeds geom r r' ch.c.pos) (encapOf kem k.1.1 s).1
        (shiftStream geom kem kdfS streamS
          (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
            [.recipient (ch.c.short msg nm).receiver])
          r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U')
          fwd)
      = shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r')
        (encapOf kem k.1.1 s).1 (ofVector U) := by
    unfold forwardMU shortMU relayFrontAt
    dsimp only
    rw [ite_eq_left hp0, ite_eq_right (by have := hp1; omega)]
    exact hM
  have e2 : forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
      (RSOR.mixSeeds geom r r' ch.c.pos)
        (shiftStream geom kem kdfS streamS
          (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
            [.recipient (ch.c.short msg nm).receiver])
          r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U')
          fwd)
      = (RSOR.split geom fwd).2 := by
    unfold forwardBlockU relayBackAt
    rw [ite_eq_left hp0]
    unfold relayBack
    refine (congrArg (fun z : Except String ByteArray => Util.Bytes.toVecN _
      (match z with
        | .ok fwd => id (fwd.extract (payloadOffset kem geom) fwd.size)
        | .error _ => ByteArray.empty)) hF).trans ?_
    have hoff : payloadOffset kem geom = geom.headerLength := by
      obtain ⟨-, -, -, hhdr, -, -⟩ := id hvalid
      unfold payloadOffset
      rw [hhdr]
      rfl
    dsimp only
    rw [hoff]
    rfl
  unfold forwardRunU
  dsimp only [KeyedDraw.c]
  rw [e1, e2]
  obtain ⟨-, -, hrouting, hhdr, -, -⟩ := id hvalid
  have hle0 : (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size
      ≤ geom.nrHops := le_of_eq_of_le (RSOR.path_size kem _ _) ch.c.req.fwd.length_le
  have hcmd0 : ((RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])[(ch.c.pos :
      ℕ)]!).commands = [] :=
    (congrArg (·.commands) (RSOR.path_getElem! kem _ _ _ hpos)).trans
      (ite_eq_right (Nat.ne_of_lt hn))
  have hname : ((RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])[(ch.c.pos : ℕ) + 1]!).id
      = ch.c.req.fwd.hops[(ch.c.pos : ℕ) + 1].name :=
    congrArg (·.id) (RSOR.path_getElem! kem _ _ _ hn)
  have hszM := relayFront_size geom kem kdfS streamS cipher macS hvalid hmactag _ _ _ _
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) _ fwd hp0 hle0
    (Util.Bytes.size_ofVector _) hF hcmd0
  have hUs := shiftStream_size geom kem kdfS streamS hrouting
    (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
    (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg nm).receiver])
    r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U') fwd
    ((Nat.le_of_lt hp0).trans hle0) (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _)
  have hsplit : RSOR.split geom (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16
      names ch (U, km, s, (r, msg, nm, r'), u, v))
      = (Util.Bytes.toVecN geom.headerLength
          (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r')
              (encapOf kem k.1.1 s).1 (ofVector U)
            ++ ofVector (macS.mac (ofVector km)
              (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
                  r') (encapOf kem k.1.1 s).1 (ofVector U)))), u) :=
    split_append geom _ u (by
      rw [ByteArray.size_append, hsz, Util.Bytes.size_ofVector, hmactag, hhdr]
      rfl)
  have honion : (forwardViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
        (RSOR.mixSeeds geom r r' ch.c.pos) (encapOf kem k.1.1 s).1 km
        (shiftStream geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
            [.recipient (ch.c.short msg nm).receiver])
          r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U')
          fwd) u).onion
      = (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (U, km, s, (r,
          msg, nm, r'), u, v) (ofVector U')).1.onion := by
    unfold forwardViewU nextViewU nextLayer shortLayerU
    dsimp only
    rw [e1]
    exact congrArg (RSOR.split geom) (RSOR.wrapUp_mixSeeds kem cipher macS kdfS streamS geom
        ch.c.req.fwd
      _ _ r r' ch.c.pos hpos _)
  rw [honion]
  have hm1 := congrArg Prod.fst hsplit
  have hm2 := congrArg Prod.snd hsplit
  dsimp only at hm1 hm2
  have eM : shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r')
      (encapOf kem k.1.1 s).1 (ofVector U)
      = relayFront kem cipher macS kdfS streamS geom (RSOR.path kem ch.c.req.fwd [.recipient
          ch.c.req.receiver])
        (RSOR.mixSeeds geom r r' ch.c.pos).1 (RSOR.body kem macS kdfS streamS geom ch.c.req r)
        ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
        (shiftStream geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient
            ch.c.req.receiver])
        (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
          [.recipient (ch.c.short msg nm).receiver])
        r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
        (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U')
        fwd) :=
    e1.symm.trans (by
      unfold forwardMU relayFrontAt
      exact ite_eq_left hp0)
  have H := headerRelays_forward_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
    ch.c hn r (RSOR.split geom (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16
        names ch (U, km, s, (r, msg, nm, r'), u, v))) g
    (fun h => if h = .relay then k.2 else st.2.2 h) (encapOf kem k.1.1 s).1 km
    (shiftStream geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
        (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
          [.recipient (ch.c.short msg nm).receiver])
        r.1 (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
        (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) (ofVector U')
        fwd) (ofVector U)
    (fun y => if y = u then
        shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r')
            (ofVector U)
      else v)
    (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1
    (RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) fwd hp0 hle0 hUs
    (Util.Bytes.size_ofVector _) hF hszM hcmd0 hname
    (hm1.trans (by rw [eM])) (fun m o ho => short_noreply kem cipher macS kdfS streamS geom hvalid
        hmactag h16 names k ch
      (U, km, s, (r, msg, nm, r'), u, v) hb₁ hv m o (ho.trans hm1))
  rw [hm1, hm2] at H
  exact congrArg (fun impl => (simulateQ impl (A.guess st.1
    (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (U, km, s, (r, msg,
        nm, r'), u, v) (ofVector U')).1.onion)).run' st.2.1) H

/-! ## World 1 is world 0 under the relabelling, at the end of the path -/

set_option maxHeartbeats 2000000 in
/-- **At the end of the path, world 1 with its payload drawn is world 0 at the relabelled
draws.** World 0 is played with the mixed randomness and the keystream with its head shifted.
The two senders' payloads have a payload's length, the original's request is reliable, and the
ideal cipher's second block does not begin with the zero tag. -/
theorem nextDrawn_eq_last (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (x : NextOth geom) (U' : Keystream geom) (g : Block geom) (next : RSOR.Onion geom)
    (hl : ch.c.pos + 1 = ch.c.req.fwd.hops.length)
    (hb₀ : (RSOR.body kem macS kdfS streamS geom ch.c.req x.2.2.2.1.1).size
      = geom.forwardPayloadLength)
    (hb₁ : (RSOR.body kem macS kdfS streamS geom
        (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1) x.2.2.2.1.2.2.2).size
      = geom.forwardPayloadLength)
    (hr : RSOR.Reliable kem cipher macS kdfS streamS geom ch.c.req x.2.2.2.1.1)
    (hv : ¬ ((ofVector x.2.2.2.2.2).extract 0 geom.payloadTagLength).data.all (· == 0) = true) :
    (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay
          (fun h => if h = .relay then k.2 else st.2.2 h) (encapOf kem k.1.1 x.2.2.1).1 x.2.1
          (ofVector x.1)
          (Util.Bytes.toVecN _
            (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)
              ++ ofVector (macS.mac (ofVector x.2.1)
                (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                  (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)))))
          (fun y => if y = x.2.2.2.2.1 then
              shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                (ofVector x.1)
            else x.2.2.2.2.2)
          (ch.c.patchDrawn next x.2.2.2.1.1
            (RSOR.split geom
              (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x)) g))
        (A.guess st.1 (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x
          (ofVector U')).1.onion)).run' st.2.1
      = forwardRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          (RSOR.Randomness geom) ($ᵗ RSOR.Randomness geom)
          (fun ch r c t =>
            { onion := onionK kem cipher macS kdfS streamS geom ch.c.req r ch.c.pos c t 0 }) A
          (forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          (forwardViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
          x.2.1
          (lastShift geom kem kdfS streamS
            (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
            (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
              [.recipient (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1).receiver])
            (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos).1
            x.2.2.2.1.2.2.2.1 ch.c.pos
            (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 x.2.2.1).1)) (ofVector x.1))
          ⟨k, (ch, st), x.2.2.1, RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos⟩
          x.2.2.2.2.1 x.2.2.2.2.2 := by
  obtain ⟨U, km, s, ⟨r, msg, nm, r'⟩, u, v⟩ := x
  dsimp only at hb₀ hb₁ hr hv ⊢
  obtain ⟨-, -, hrouting, hhdr, -, -⟩ := id hvalid
  have hpos : (ch.c.pos : ℕ) < ch.c.req.fwd.hops.length := ch.c.pos.isLt
  have hp0 : (ch.c.pos : ℕ) + 1 = (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size
      :=
    hl.trans (RSOR.path_size kem _ _).symm
  have hp1 : (ch.c.pos : ℕ) + 1 = (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient
      (ch.c.short msg nm).receiver]).size :=
    ((RSOR.path_size kem _ _).trans (RSOR.take_length _ _ hl.le)).symm
  have hle0 : (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]).size ≤ geom.nrHops :=
    le_of_eq_of_le (RSOR.path_size kem _ _) ch.c.req.fwd.length_le
  have hcmd0 : ((RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])[(ch.c.pos :
      ℕ)]!).commands = [.recipient ch.c.req.receiver] :=
    (congrArg (·.commands) (RSOR.path_getElem! kem _ _ _ hpos)).trans (ite_eq_left hl)
  have hcmd1 : ((RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg
      nm).receiver])[(ch.c.pos : ℕ)]!).commands = [.recipient (ch.c.short msg nm).receiver] :=
    congrArg (·.commands) (RSOR.path_take_last kem geom ch.c.req.fwd _ ch.c.pos hpos)
  obtain ⟨hUs, hM⟩ := lastShift_spec geom kem kdfS streamS hvalid (RSOR.path kem ch.c.req.fwd
      [.recipient ch.c.req.receiver])
    (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg nm).receiver])
        (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U) hp0 hle0 hp1
    (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _)
    (RSOR.kemHopKeys_mixSeeds kem kdfS geom ch.c.req.fwd _ _ r r' ch.c.pos hpos) _ _ hcmd0 hcmd1
  have hnl0 : ¬ (ch.c.pos : ℕ) + 1 < (RSOR.path kem ch.c.req.fwd [.recipient
      ch.c.req.receiver]).size := Nat.not_lt.2 (Nat.le_of_eq hp0.symm)
  have hnl1 : ¬ (ch.c.pos : ℕ) + 1 < (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient
      (ch.c.short msg nm).receiver]).size := Nat.not_lt.2 (Nat.le_of_eq hp1.symm)
  have hle1 : (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg
      nm).receiver]).size ≤ geom.nrHops := le_of_eq_of_le hp1.symm (le_of_eq_of_le hp0 hle0)
  have hs0 := relayFrontLast_size geom kem kdfS streamS hvalid (RSOR.path kem ch.c.req.fwd
      [.recipient ch.c.req.receiver])
    (RSOR.mixSeeds geom r r' ch.c.pos).1 ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem
        k.1.1 s).1)) (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient
        ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient
        (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos (ofVector
        (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) hp0 hle0 hUs
    (Util.Bytes.size_ofVector _) _ hcmd0
  have hs1 := relayFrontLast_size geom kem kdfS streamS hvalid (RSOR.path kem (ch.c.req.fwd.take
      (ch.c.pos + 1)) [.recipient (ch.c.short msg nm).receiver]) r'.1 ch.c.pos (ofVector
      (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
    (ofVector U) hp1 hle1 (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) _ hcmd1
  have eM1 : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
      r') (encapOf kem k.1.1 s).1 (ofVector U)) = relayFrontLast kem kdfS streamS geom (RSOR.path
      kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg nm).receiver]) r'.1
      ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
      (ofVector U) := by
    unfold shortMU relayFrontAt
    exact ite_eq_right hnl1
  have e1 : forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (RSOR.mixSeeds
      geom r r' ch.c.pos) (encapOf kem k.1.1 s).1
      (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg
          nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos (ofVector
          (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) = (shortMU kem cipher macS
          kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r') (encapOf kem k.1.1 s).1
          (ofVector U)) := by
    refine Eq.trans ?_ (hM.trans eM1.symm)
    unfold forwardMU relayFrontAt
    exact ite_eq_right hnl0
  have eM0 : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
      r') (encapOf kem k.1.1 s).1 (ofVector U)) = relayFrontLast kem kdfS streamS geom (RSOR.path
      kem ch.c.req.fwd [.recipient ch.c.req.receiver])
      (RSOR.mixSeeds geom r r' ch.c.pos).1 ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem
          k.1.1 s).1)) (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient
          ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient
          (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) := eM1.trans
          hM.symm
  have hsz : (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
      r') (encapOf kem k.1.1 s).1 (ofVector U)).size = 2 + kem.ciphertextSize +
      geom.routingInfoLength := by
    rw [eM1]
    exact hs1
  have eB0 : forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
      (RSOR.mixSeeds geom r r' ch.c.pos) (lastShift geom kem kdfS streamS (RSOR.path kem
      ch.c.req.fwd [.recipient ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos +
      1)) [.recipient (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1
      ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U))
      = Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)
          ++ RSOR.body kem macS kdfS streamS geom ch.c.req r) := by
    unfold forwardBlockU relayBackAt
    rw [ite_eq_right hnl0]
    rfl
  have eB1 : shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm,
      r') (ofVector U)
      = Util.Bytes.toVecN (geom.payloadTagLength + geom.forwardPayloadLength)
        ((⟨Array.replicate geom.payloadTagLength 0⟩ : ByteArray)
          ++ RSOR.body kem macS kdfS streamS geom (ch.c.short msg nm) r') := by
    unfold shortBlockU relayBackAt
    exact congrArg (Util.Bytes.toVecN _) (ite_eq_right hnl1)
  obtain ⟨hB0, hbody⟩ := RSOR.zeroTag_block geom _ hb₀
  obtain ⟨hB1, -⟩ := RSOR.zeroTag_block geom _ hb₁
  rw [← eB0] at hB0 hbody
  rw [← eB1] at hB1
  have hsplit : RSOR.split geom (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16
      names ch (U, km, s, (r, msg, nm, r'), u, v))
      = (Util.Bytes.toVecN geom.headerLength ((shortMU kem cipher macS kdfS streamS geom hvalid
          hmactag h16 names ch (r, msg, nm, r') (encapOf kem k.1.1 s).1 (ofVector U))
          ++ ofVector (macS.mac (ofVector km) (shortMU kem cipher macS kdfS streamS geom hvalid
              hmactag h16 names ch (r, msg, nm, r') (encapOf kem k.1.1 s).1 (ofVector U)))), u) :=
    split_append geom _ u (by
      rw [ByteArray.size_append, hsz, Util.Bytes.size_ofVector, hmactag, hhdr]
      rfl)
  have honion : (forwardViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch
      (RSOR.mixSeeds geom r r' ch.c.pos)
        (encapOf kem k.1.1 s).1 km (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd
            [.recipient ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
            [.recipient (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1
            ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U))
            u).onion
      = (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (U, km, s, (r,
          msg, nm, r'), u, v) (ofVector U')).1.onion := by
    unfold forwardViewU nextViewU nextLayer shortLayerU
    dsimp only
    rw [e1]
    exact congrArg (RSOR.split geom) (RSOR.wrapUp_mixSeeds kem cipher macS kdfS streamS geom
        ch.c.req.fwd
      _ _ r r' ch.c.pos hpos _)
  unfold forwardRunU
  dsimp only [KeyedDraw.c]
  rw [e1, honion]
  have hm1 := congrArg Prod.fst hsplit
  have hm2 := congrArg Prod.snd hsplit
  dsimp only at hm1 hm2
  have H := headerRelays_last_eq kem cipher macS kdfS streamS geom hvalid hmactag h16 names
    ch.c hl next r (RSOR.split geom (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16
        names ch (U, km, s, (r, msg, nm, r'), u, v))) g
    (fun h => if h = .relay then k.2 else st.2.2 h) (encapOf kem k.1.1 s).1 km
    (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
        (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient (ch.c.short msg
        nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1 ch.c.pos (ofVector
        (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)) (ofVector U) (RSOR.path kem
        ch.c.req.fwd [.recipient ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos +
        1)) [.recipient (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1
        ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
    (ch.c.short msg nm).receiver
    (forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (RSOR.mixSeeds
        geom r r' ch.c.pos) (lastShift geom kem kdfS streamS (RSOR.path kem ch.c.req.fwd
        [.recipient ch.c.req.receiver]) (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
        [.recipient (ch.c.short msg nm).receiver]) (RSOR.mixSeeds geom r r' ch.c.pos).1 r'.1
        ch.c.pos (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1)) (ofVector U)))
    (shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (r, msg, nm, r')
        (ofVector U)) v
    hp0 hle0 hp1 hle1 hUs (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) hs0 hs1
    hcmd0 hcmd1 (hm1.trans (by rw [eM0])) (hm1.trans (by rw [eM1])) hB0 hB1 hv hbody
    (RSOR.msgOf_body kem macS kdfS streamS geom ch.c.req r) hr
  rw [hm1, hm2] at H
  exact congrArg (fun impl => (simulateQ impl (A.guess st.1
    (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch (U, km, s, (r, msg,
        nm, r'), u, v) (ofVector U')).1.onion)).run' st.2.1) H

/-! ## The two worlds over their draws -/

/-- World 0 after its draws: the ideal game with the relay's MAC key, its header keystream,
the seed of its ciphertext, the challenger's randomness and the ideal cipher's two blocks. -/
def run0 (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (U : Keystream geom) (km s : Vector UInt8 32) (r : RSOR.Randomness geom)
    (u v : Block geom) : ProbComp Bool :=
  forwardRunU kem cipher macS kdfS streamS geom hvalid hmactag h16 names
    (RSOR.Randomness geom) ($ᵗ RSOR.Randomness geom)
    (fun ch r c t =>
      { onion := onionK kem cipher macS kdfS streamS geom ch.c.req r ch.c.pos c t 0 }) A
    (forwardMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
    (forwardBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
    (forwardViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
    km (ofVector U) ⟨k, (ch, st), s, r⟩ u v

set_option maxHeartbeats 2000000 in
/-- **World 1's draws, relabelled, are world 0's draws, before the end of the path.** -/
theorem relabel_forward (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (hn : ch.c.pos + 1 < ch.c.req.fwd.hops.length) :
    (do
      let U' ← $ᵗ (Keystream geom)
      let x ← nextDraw geom
      let g ← $ᵗ (Block geom)
      run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st
        (Util.Bytes.toVecN _ (shiftStream geom kem kdfS streamS
          (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient x.2.2.2.1.2.2.1])
          x.2.2.2.1.1.1 (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos).1
          x.2.2.2.1.2.2.2.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 x.2.2.1).1)) (ofVector x.1)
          (ofVector U')
          (match layerPast kem cipher macS kdfS streamS geom
              (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) x.2.2.2.1.1.1
              (RSOR.body kem macS kdfS streamS geom ch.c.req x.2.2.2.1.1) ch.c.pos (ofVector U')
              (ch.c.pos + 1) with
            | .ok f => f
            | .error _ => ByteArray.empty)))
        x.2.1 x.2.2.1 (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos) x.2.2.2.2.1 g)
      =ᵈ (do
        let U ← $ᵗ (Keystream geom)
        let km ← $ᵗ (Vector UInt8 32)
        let s ← $ᵗ (Vector UInt8 32)
        let r ← $ᵗ (RSOR.Randomness geom)
        let u ← $ᵗ (Block geom)
        let v ← $ᵗ (Block geom)
        run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st U km s r u v) :=
            by
  simp only [nextDraw, shortDraw, bind_assoc, pure_bind]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun
      _ => EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right
      _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun
      _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun
      _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun
      _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun s =>
    EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun nm =>
    RSOR.evalDistEq_shiftStream kem cipher macS kdfS streamS geom hvalid ch.c.req.fwd
      [.recipient ch.c.req.receiver] [.recipient nm]
      (fun r => RSOR.body kem macS kdfS streamS geom ch.c.req r) ch.c.pos hn
      (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
      (fun U₀ r₀ => $ᵗ (Block geom) >>= fun u => $ᵗ (Block geom) >>= fun g =>
        run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st U₀ km s r₀ u g))
            ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact EvalDistEq.rfl

set_option maxHeartbeats 2000000 in
/-- **World 1's draws, relabelled, are world 0's draws, at the end of the path.** -/
theorem relabel_last (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey)) :
    (do
      let _ ← $ᵗ (Keystream geom)
      let x ← nextDraw geom
      let _ ← $ᵗ (Block geom)
      run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st
        (Util.Bytes.toVecN _ (lastShift geom kem kdfS streamS
          (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient x.2.2.2.1.2.2.1])
          (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos).1
          x.2.2.2.1.2.2.2.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 x.2.2.1).1)) (ofVector x.1)))
        x.2.1 x.2.2.1 (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos) x.2.2.2.2.1
        x.2.2.2.2.2)
      =ᵈ (do
        let U ← $ᵗ (Keystream geom)
        let km ← $ᵗ (Vector UInt8 32)
        let s ← $ᵗ (Vector UInt8 32)
        let r ← $ᵗ (RSOR.Randomness geom)
        let u ← $ᵗ (Block geom)
        let v ← $ᵗ (Block geom)
        run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st U km s r u v) :=
            by
  simp only [nextDraw, shortDraw, bind_assoc, pure_bind]
  refine EvalDistEq.trans (
    OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun
      _ => EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right
      _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun
      _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ =>
      EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun km => EvalDistEq.bind_right _ fun s =>
    EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun nm =>
    RSOR.evalDistEq_lastShift kem kdfS streamS geom hvalid ch.c.req.fwd
      [.recipient ch.c.req.receiver] [.recipient nm] ch.c.pos ch.c.pos.isLt
      (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 s).1))
      (fun U₀ r₀ => $ᵗ (Block geom) >>= fun u => $ᵗ (Block geom) >>= fun v =>
        run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st U₀ km s r₀ u v))
            ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_const _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => 
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  refine EvalDistEq.trans (
    OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
  exact EvalDistEq.rfl

/-! ## The bound for fixed keys and challenge -/

/-- The replacement's header bytes at the honest relay have a header's length. -/
theorem shortMU_size {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk)
    (o : RSOR.Randomness geom × RSOR.Msg geom × RSOR.Name × RSOR.Randomness geom)
    (c : kem.Ciphertext) (U : Keystream geom) :
    (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch o c (ofVector U)).size
      = 2 + kem.ciphertextSize + geom.routingInfoLength := by
  have hpos : (ch.c.pos : ℕ) < ch.c.req.fwd.hops.length := ch.c.pos.isLt
  have hp1 : (ch.c.pos : ℕ) + 1 = (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1))
      [.recipient (ch.c.short o.2.1 o.2.2.1).receiver]).size :=
    ((RSOR.path_size kem _ _).trans (RSOR.take_length _ _ hpos)).symm
  unfold shortMU relayFrontAt
  refine (congrArg ByteArray.size (ite_eq_right (Nat.not_lt.2 (Nat.le_of_eq hp1.symm)))).trans ?_
  exact relayFrontLast_size geom kem kdfS streamS hvalid _ _ _ _ _ hp1
    (le_of_eq_of_le hp1.symm (le_trans hpos ch.c.req.fwd.length_le))
    (Util.Bytes.size_ofVector _) (Util.Bytes.size_ofVector _) _
    (congrArg (·.commands) (RSOR.path_take_last kem geom ch.c.req.fwd _ ch.c.pos hpos))

/-- The draws of world 1 on which it is world 0 at the relabelled draws: the original's next
layer builds when there is one, at the end of the path the original's request is reliable, and
the ideal cipher's second block does not begin with the zero tag. -/
def finalGood {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk) (x : NextOth
        geom) (U' : Keystream geom) : Prop :=
  (ch.c.pos + 1 < ch.c.req.fwd.hops.length →
      ∃ fwd, layerPast kem cipher macS kdfS streamS geom
        (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) x.2.2.2.1.1.1
        (RSOR.body kem macS kdfS streamS geom ch.c.req x.2.2.2.1.1) ch.c.pos (ofVector U')
        (ch.c.pos + 1) = .ok fwd)
    ∧ (¬ ch.c.pos + 1 < ch.c.req.fwd.hops.length →
      RSOR.Reliable kem cipher macS kdfS streamS geom ch.c.req x.2.2.2.1.1)
    ∧ ¬ ((ofVector x.2.2.2.2.2).extract 0 geom.payloadTagLength).data.all (· == 0) = true

/-- World 1 after its draws, with the random payload `g` of its patch drawn: the relay answers
the replacement's header from its MAC key, its uniform keystream and the ideal payload
cipher, and the challenger patches its answers. -/
def run1g (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (x : NextOth geom) (U' : Keystream geom) (g : Block geom) : ProbComp Bool :=
  (simulateQ (headerRelays kem cipher macS kdfS streamS geom hvalid hmactag h16 .relay
      (fun h => if h = .relay then k.2 else st.2.2 h) (encapOf kem k.1.1 x.2.2.1).1 x.2.1
      (ofVector x.1)
      (Util.Bytes.toVecN _
        (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1 (encapOf
            kem k.1.1 x.2.2.1).1 (ofVector x.1)
          ++ ofVector (macS.mac (ofVector x.2.1)
            (shortMU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
                (encapOf kem k.1.1 x.2.2.1).1 (ofVector x.1)))))
      (fun y => if y = x.2.2.2.2.1 then
          shortBlockU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1
              (ofVector x.1)
        else x.2.2.2.2.2)
      (ch.c.patchDrawn
        (nextU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1.1
            (RSOR.split geom (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            ch x)) (ofVector U'))
        x.2.2.2.1.1 (RSOR.split geom (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag
            h16 names ch x)) g))
    (A.guess st.1 (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x
        (ofVector U')).1.onion)).run' st.2.1

/-- **World 1 after its draws may draw its random payload first.** -/
theorem nextOwn_evalDistEq_run1g (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (s' : Vector UInt8 32) (x : NextOth geom) (U' : Keystream geom) :
    simulateQ (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
        (ownAns kem cipher macS kdfS streamS geom k.2))
      ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post st (nextViewU
          kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x (ofVector U')))
    =ᵈ $ᵗ (Block geom) >>= fun g => run1g kem cipher macS kdfS streamS geom hvalid hmactag h16
        names A k ch st x U' g := by
  rw [nextOwn_run kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st s' x
      (ofVector U')
    (shortMU_size kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch _ _ _)]
  exact headerRelays_patchWith_draw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
    ch.c _ _ _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 1000000 in
/-- On a good draw before the end of the path, world 1 with its payload drawn is world 0 at
the relabelled draws. -/
theorem run1g_eq_forward (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (x : NextOth geom) (U' : Keystream geom) (g : Block geom)
    (hn : ch.c.pos + 1 < ch.c.req.fwd.hops.length)
    (hg : finalGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x U') :
    run1g kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st x U' g
      = run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st
        (Util.Bytes.toVecN _ (shiftStream geom kem kdfS streamS
          (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient x.2.2.2.1.2.2.1])
          x.2.2.2.1.1.1 (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos).1
          x.2.2.2.1.2.2.2.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 x.2.2.1).1)) (ofVector x.1)
          (ofVector U')
          (match layerPast kem cipher macS kdfS streamS geom
              (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) x.2.2.2.1.1.1
              (RSOR.body kem macS kdfS streamS geom ch.c.req x.2.2.2.1.1) ch.c.pos (ofVector U')
              (ch.c.pos + 1) with
            | .ok f => f
            | .error _ => ByteArray.empty)))
        x.2.1 x.2.2.1 (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos) x.2.2.2.2.1 g := by
  obtain ⟨hfw, -, hv⟩ := hg
  obtain ⟨fwd, hfwd⟩ := hfw hn
  have hfwd' := hfwd
  unfold layerPast at hfwd'
  have hb₁ : (RSOR.body kem macS kdfS streamS geom
      (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1) x.2.2.2.1.2.2.2).size
      = geom.forwardPayloadLength :=
    (RSOR.body_size kem macS kdfS streamS geom hvalid hmactag _ _).trans
      ((RSOR.body_size kem macS kdfS streamS geom hvalid hmactag ch.c.req x.2.2.2.1.1).symm.trans
        (newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _ _ hfwd').1)
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hm : (match layerPast kem cipher macS kdfS streamS geom
      (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) x.2.2.2.1.1.1
      (RSOR.body kem macS kdfS streamS geom ch.c.req x.2.2.2.1.1) ch.c.pos (ofVector U')
      (ch.c.pos + 1) with
    | .ok f => f
    | .error _ => ByteArray.empty) = fwd :=
    congrArg (fun z : Except String ByteArray =>
      match z with
      | .ok f => f
      | .error _ => ByteArray.empty) hfwd
  have hnext : nextU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x.2.2.2.1.1
      (RSOR.split geom (nextLayer kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x))
      (ofVector U')
      = RSOR.split geom fwd := by
    unfold nextU
    exact (ite_eq_left hn).trans (congrArg (fun z : Except String ByteArray =>
      match z with
      | .ok pkt => RSOR.split geom pkt
      | .error _ => default) hfwd)
  have hsz := shiftStream_size geom kem kdfS streamS hrouting
    (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
    (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient x.2.2.2.1.2.2.1])
    x.2.2.2.1.1.1 (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos).1
    x.2.2.2.1.2.2.2.1 ch.c.pos
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 x.2.2.1).1)) (ofVector x.1)
    (ofVector U') fwd
    (le_trans hn.le ch.c.req.fwd.length_le) (Util.Bytes.size_ofVector _)
    (Util.Bytes.size_ofVector _)
  unfold run1g run0
  rw [hnext, hm, Util.Bytes.ofVector_toVecN _ hsz]
  exact nextDrawn_eq_forward kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st x
      U' g fwd hn hfwd
    (shortMU_size kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch _ _ _) hb₁ hv

set_option maxHeartbeats 1000000 in
/-- On a good draw at the end of the path, world 1 with its payload drawn is world 0 at the
relabelled draws. -/
theorem run1g_eq_last (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (x : NextOth geom) (U' : Keystream geom) (g : Block geom)
    (hn : ¬ ch.c.pos + 1 < ch.c.req.fwd.hops.length)
    (hg : finalGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x U') :
    run1g kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st x U' g
      = run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st
        (Util.Bytes.toVecN _ (lastShift geom kem kdfS streamS
          (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient x.2.2.2.1.2.2.1])
          (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos).1
          x.2.2.2.1.2.2.2.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 x.2.2.1).1)) (ofVector x.1)))
        x.2.1 x.2.2.1 (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos) x.2.2.2.2.1
        x.2.2.2.2.2 := by
  obtain ⟨-, hlast, hv⟩ := hg
  have hr := hlast hn
  obtain ⟨pkt, hpkt⟩ := hr.1.2 (Nat.zero_lt_of_lt ch.c.pos.isLt)
  unfold RSOR.layer at hpkt
  have hb₀ : (RSOR.body kem macS kdfS streamS geom ch.c.req x.2.2.2.1.1).size
      = geom.forwardPayloadLength := (newKEMPacket_unfold kem cipher macS kdfS streamS geom _ _ _ _
          _ hpkt).1
  have hb₁ : (RSOR.body kem macS kdfS streamS geom
      (ch.c.short x.2.2.2.1.2.1 x.2.2.2.1.2.2.1) x.2.2.2.1.2.2.2).size
      = geom.forwardPayloadLength :=
    (RSOR.body_size kem macS kdfS streamS geom hvalid hmactag _ _).trans
      ((RSOR.body_size kem macS kdfS streamS geom hvalid hmactag ch.c.req x.2.2.2.1.1).symm.trans
          hb₀)
  obtain ⟨-, -, hrouting, -⟩ := id hvalid
  have hl : ch.c.pos + 1 = ch.c.req.fwd.hops.length :=
    Nat.le_antisymm ch.c.pos.isLt (Nat.not_lt.1 hn)
  have hsz := lastShift_size geom kem kdfS streamS hrouting
    (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
    (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient x.2.2.2.1.2.2.1])
    (RSOR.mixSeeds geom x.2.2.2.1.1 x.2.2.2.1.2.2.2 ch.c.pos).1
    x.2.2.2.1.2.2.2.1 ch.c.pos
    (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 x.2.2.1).1)) (ofVector x.1)
    (le_trans ch.c.pos.isLt ch.c.req.fwd.length_le) (Util.Bytes.size_ofVector _)
  unfold run1g run0
  rw [Util.Bytes.ofVector_toVecN _ hsz]
  exact nextDrawn_eq_last kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st x U'
      g _ hl hb₀ hb₁ hr hv

/-- World 0 at the relabelled draws of world 1, before the end of the path. -/
def phiForward (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (p : Keystream geom × NextOth geom) (g : Block geom) : ProbComp Bool :=
  run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st
        (Util.Bytes.toVecN _ (shiftStream geom kem kdfS streamS
          (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient p.2.2.2.2.1.2.2.1])
          p.2.2.2.2.1.1.1 (RSOR.mixSeeds geom p.2.2.2.2.1.1 p.2.2.2.2.1.2.2.2 ch.c.pos).1
          p.2.2.2.2.1.2.2.2.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 p.2.2.2.1).1)) (ofVector p.2.1)
          (ofVector p.1)
          (match layerPast kem cipher macS kdfS streamS geom
              (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) p.2.2.2.2.1.1.1
              (RSOR.body kem macS kdfS streamS geom ch.c.req p.2.2.2.2.1.1) ch.c.pos (ofVector p.1)
              (ch.c.pos + 1) with
            | .ok f => f
            | .error _ => ByteArray.empty)))
        p.2.2.1 p.2.2.2.1 (RSOR.mixSeeds geom p.2.2.2.2.1.1 p.2.2.2.2.1.2.2.2 ch.c.pos)
        p.2.2.2.2.2.1 g

/-- World 0 at the relabelled draws of world 1, at the end of the path. -/
def phiLast (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (p : Keystream geom × NextOth geom) : ProbComp Bool :=
  run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st
        (Util.Bytes.toVecN _ (lastShift geom kem kdfS streamS
          (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver])
          (RSOR.path kem (ch.c.req.fwd.take (ch.c.pos + 1)) [.recipient p.2.2.2.2.1.2.2.1])
          (RSOR.mixSeeds geom p.2.2.2.2.1.1 p.2.2.2.2.1.2.2.2 ch.c.pos).1
          p.2.2.2.2.1.2.2.2.1 ch.c.pos
          (ofVector (kem.encodeCiphertext (encapOf kem k.1.1 p.2.2.2.1).1)) (ofVector p.2.1)))
        p.2.2.1 p.2.2.2.1 (RSOR.mixSeeds geom p.2.2.2.2.1.1 p.2.2.2.2.1.2.2.2 ch.c.pos)
        p.2.2.2.2.2.1 p.2.2.2.2.2.2

/-- On a good draw before the end of the path, world 1 with its payload drawn is world 0 at
the relabelled draws. -/
theorem run1g_eq_phiForward (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (p : Keystream geom × NextOth geom) (g : Block geom)
    (hn : ch.c.pos + 1 < ch.c.req.fwd.hops.length)
    (hg : finalGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch p.2 p.1) :
    run1g kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st p.2 p.1 g =
        phiForward kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st p g := by
  unfold phiForward
  exact run1g_eq_forward kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st p.2
      p.1 g hn hg

/-- On a good draw at the end of the path, world 1 with its payload drawn is world 0 at the
relabelled draws. -/
theorem run1g_eq_phiLast (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
    (p : Keystream geom × NextOth geom) (g : Block geom)
    (hn : ¬ ch.c.pos + 1 < ch.c.req.fwd.hops.length)
    (hg : finalGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch p.2 p.1) :
    run1g kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st p.2 p.1 g = phiLast
        kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st p := by
  unfold phiLast
  exact run1g_eq_last kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st p.2 p.1
      g hn hg

set_option maxHeartbeats 2000000 in
/-- **For fixed keys and challenge, world 1 is world 0 up to the bad draws.** After the first
phase, world 1 with the honest relay's own answers for the hidden ciphertext differs from world
0 from a uniform keystream by at most the chance of a draw that is not good. -/
theorem final_fixed_le (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary)
    (k : Key kem × kem.PrivateKey)
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1)
    (st : A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey)) (s' : Vector UInt8 32) :
    |(Pr{let b ← (do
          let U' ← $ᵗ (Keystream geom)
          let x ← nextDraw geom
          simulateQ (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
              (ownAns kem cipher macS kdfS streamS geom k.2))
            ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post st
              (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x (ofVector
                  U'))))}[b = true]).toReal
      - (Pr{let b ← (do
          let U ← $ᵗ (Keystream geom)
          let km ← $ᵗ (Vector UInt8 32)
          let s ← $ᵗ (Vector UInt8 32)
          let r ← $ᵗ (RSOR.Randomness geom)
          let u ← $ᵗ (Block geom)
          let v ← $ᵗ (Block geom)
          run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st U km s r u
              v)}[b = true]).toReal|
    ≤ (Pr{let p ← (do let U' ← $ᵗ (Keystream geom); let x ← nextDraw geom; pure (U', x))}[¬
        finalGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch p.2 p.1]).toReal :=
        by
  have h1 : (do
        let U' ← $ᵗ (Keystream geom)
        let x ← nextDraw geom
        simulateQ (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
            (ownAns kem cipher macS kdfS streamS geom k.2))
          ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post st
            (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names ch x (ofVector
                U'))))
      =ᵈ ((do let U' ← $ᵗ (Keystream geom); let x ← nextDraw geom; pure (U', x)) >>= fun p => $ᵗ
          (Block geom) >>= fun g =>
        run1g kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st p.2 p.1 g) := by
    simp only [bind_assoc, pure_bind]
    exact EvalDistEq.bind_right _ fun U' => EvalDistEq.bind_right _ fun x =>
      nextOwn_evalDistEq_run1g kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st
          s' x U'
  rw [h1 (fun b => b = true)]
  by_cases hn : ch.c.pos + 1 < ch.c.req.fwd.hops.length
  · have h3 : ((do let U' ← $ᵗ (Keystream geom); let x ← nextDraw geom; pure (U', x)) >>= (fun p :
      Keystream geom × NextOth geom => $ᵗ (Block geom) >>= fun g =>
      phiForward kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st p g))
        =ᵈ (do
          let U ← $ᵗ (Keystream geom)
          let km ← $ᵗ (Vector UInt8 32)
          let s ← $ᵗ (Vector UInt8 32)
          let r ← $ᵗ (RSOR.Randomness geom)
          let u ← $ᵗ (Block geom)
          let v ← $ᵗ (Block geom)
          run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st U km s r u v)
              := by
      simp only [bind_assoc, pure_bind]
      exact relabel_forward kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st hn
    rw [← h3 (fun b => b = true)]
    exact abs_prEvent_bind_sub_le_bad
      (do let U' ← $ᵗ (Keystream geom); let x ← nextDraw geom; pure (U', x))
      (fun p : Keystream geom × NextOth geom =>
        $ᵗ (Block geom) >>= fun g => run1g kem cipher macS kdfS streamS geom hvalid hmactag h16
            names A k ch st p.2 p.1 g)
      (fun p : Keystream geom × NextOth geom => $ᵗ (Block geom) >>= fun g => phiForward kem cipher
          macS kdfS streamS geom hvalid hmactag h16 names A k ch st p g)
      (fun p : Keystream geom × NextOth geom => ¬ finalGood kem cipher macS kdfS streamS geom
          hvalid hmactag h16 names ch p.2 p.1) fun p hp =>
        congrArg (fun f => $ᵗ (Block geom) >>= f) (funext fun g =>
          run1g_eq_phiForward kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st
              p g hn (Classical.not_not.mp hp))
  · have h3 : ((do let U' ← $ᵗ (Keystream geom); let x ← nextDraw geom; pure (U', x)) >>= (fun p :
      Keystream geom × NextOth geom => $ᵗ (Block geom) >>= fun _ =>
      phiLast kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st p))
        =ᵈ (do
          let U ← $ᵗ (Keystream geom)
          let km ← $ᵗ (Vector UInt8 32)
          let s ← $ᵗ (Vector UInt8 32)
          let r ← $ᵗ (RSOR.Randomness geom)
          let u ← $ᵗ (Block geom)
          let v ← $ᵗ (Block geom)
          run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st U km s r u v)
              := by
      simp only [bind_assoc, pure_bind]
      exact relabel_last kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st
    rw [← h3 (fun b => b = true)]
    exact abs_prEvent_bind_sub_le_bad
      (do let U' ← $ᵗ (Keystream geom); let x ← nextDraw geom; pure (U', x))
      (fun p : Keystream geom × NextOth geom =>
        $ᵗ (Block geom) >>= fun g => run1g kem cipher macS kdfS streamS geom hvalid hmactag h16
            names A k ch st p.2 p.1 g)
      (fun p : Keystream geom × NextOth geom => $ᵗ (Block geom) >>= fun _ => phiLast kem cipher
          macS kdfS streamS geom hvalid hmactag h16 names A k ch st p)
      (fun p : Keystream geom × NextOth geom => ¬ finalGood kem cipher macS kdfS streamS geom
          hvalid hmactag h16 names ch p.2 p.1) fun p hp =>
        congrArg (fun f => $ᵗ (Block geom) >>= f) (funext fun g =>
          run1g_eq_phiLast kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k ch st p g
              hn (Classical.not_not.mp hp))

/-! ## The bound over the whole game -/

/-- The draws of world 1 that the last comparison reads: the honest relay's keys, the
challenge and the adversary's state after the first phase, the keystream of the original's
layer at the relay, and the rest of world 1's draws. -/
structure FinalDraw (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) where
  k : Key kem × kem.PrivateKey
  cs : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1
    × (A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))
  U' : Keystream geom
  x : NextOth geom

/-- The draw of `FinalDraw`. -/
def finalDraw (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    ProbComp (FinalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A) := do
  let k ← keygen kem
  let cs ← simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
    ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre k.1)
  let U' ← $ᵗ (Keystream geom)
  let x ← nextDraw geom
  return ⟨k, cs, U', x⟩

set_option maxHeartbeats 2000000 in
/-- **World 1 with both keystreams uniform is world 0 from a uniform keystream, up to the bad
draws.** With the honest relay's own answers for the hidden ciphertext, the two games differ
by at most the chance of a draw of world 1 that is not good. -/
theorem next_final_le (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    |(Pr{let b ← (PRGScheme.prgIdealExperiment
          (nextStreamAdvF kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            (ownAns kem cipher macS kdfS streamS geom) A))}[b = true]).toReal
      - (Pr{let b ← (PRGScheme.prgIdealExperiment
          (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[b =
              true]).toReal|
    ≤ (Pr{let d ← (finalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[¬
        finalGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names d.cs.1 d.x
        d.U']).toReal := by
  have hA : PRGScheme.prgIdealExperiment
      (nextStreamAdvF kem cipher macS kdfS streamS geom hvalid hmactag h16 names (ownAns kem cipher
          macS kdfS streamS geom) A)
      =ᵈ (keygen kem >>= fun k => (simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
        ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre k.1)) >>= fun
            cs =>
        $ᵗ (Vector UInt8 32) >>= fun s' => (do
        let U' ← $ᵗ (Keystream geom)
        let x ← nextDraw geom
        simulateQ (procImplF kem cipher macS kdfS streamS geom k.2 (encapOf kem k.1.1 s').1
            (ownAns kem cipher macS kdfS streamS geom k.2))
          ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).post cs.2
              (nextViewU kem cipher macS kdfS streamS geom hvalid hmactag h16 names cs.1 x
              (ofVector U'))))) := by
    unfold PRGScheme.prgIdealExperiment nextStreamAdvF
    refine EvalDistEq.trans (
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => 
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    exact EvalDistEq.rfl
  have hB : PRGScheme.prgIdealExperiment
      (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
      =ᵈ (keygen kem >>= fun k => (simulateQ (procImpl kem cipher macS kdfS streamS geom k.2)
        ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre k.1)) >>= fun
            cs =>
        $ᵗ (Vector UInt8 32) >>= fun _ => (do
        let U ← $ᵗ (Keystream geom)
        let km ← $ᵗ (Vector UInt8 32)
        let s ← $ᵗ (Vector UInt8 32)
        let r ← $ᵗ (RSOR.Randomness geom)
        let u ← $ᵗ (Block geom)
        let v ← $ᵗ (Block geom)
        run0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k cs.1 cs.2 U km s r u
            v)) := by
    unfold PRGScheme.prgIdealExperiment forwardStreamAdv0 forwardStreamAdv
    simp only [keyedDraw, bind_assoc, pure_bind]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => 
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun _ => 
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ => 
      OracleComp.EvalDistEq.bind_bind_swap _ _ _) ?_
    refine EvalDistEq.trans ?_ (EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun cs =>
      (OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 32)) _).symm)
    exact EvalDistEq.rfl
  have hD : (keygen kem >>= fun (k : Key kem × kem.PrivateKey) => (simulateQ (procImpl kem cipher
      macS kdfS streamS geom k.2)
        ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre k.1)) >>= fun
            (cs : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1
      × (A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))) =>
        $ᵗ (Vector UInt8 32) >>= fun _ => (do
        let U' ← $ᵗ (Keystream geom)
        let x ← nextDraw geom
        pure (⟨k, cs, U', x⟩ : FinalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A)))
      =ᵈ finalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A := by
    unfold finalDraw
    exact EvalDistEq.bind_right _ fun k => EvalDistEq.bind_right _ fun cs =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 32)) _
  rw [hA (fun b => b = true), hB (fun b => b = true),
    ← hD (fun d => ¬ finalGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names d.cs.1
        d.x d.U')]
  refine abs_prEvent_bind_sub_le _ _ _ (fun (k : Key kem × kem.PrivateKey) => (simulateQ (procImpl
      kem cipher macS kdfS streamS geom k.2)
        ((nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).pre k.1)) >>= fun
            (cs : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names k.1
      × (A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))) =>
    $ᵗ (Vector UInt8 32) >>= fun _ => (do
        let U' ← $ᵗ (Keystream geom)
        let x ← nextDraw geom
        pure (⟨k, cs, U', x⟩ : FinalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))) _ fun k => ?_
  refine abs_prEvent_bind_sub_le _ _ _ (fun (cs : ForwardCh kem cipher macS kdfS streamS geom
      hvalid hmactag h16 names k.1
      × (A.State × Protocols.RSOR.Log 𝒮 × (Role → kem.PrivateKey))) =>
    $ᵗ (Vector UInt8 32) >>= fun _ => (do
        let U' ← $ᵗ (Keystream geom)
        let x ← nextDraw geom
        pure (⟨k, cs, U', x⟩ : FinalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))) _ fun cs => ?_
  refine abs_prEvent_bind_sub_le _ _ _ (fun _ => (do
        let U' ← $ᵗ (Keystream geom)
        let x ← nextDraw geom
        pure (⟨k, cs, U', x⟩ : FinalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))) _ fun s' => ?_
  refine (final_fixed_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A k cs.1 cs.2
      s').trans (le_of_eq ?_)
  have e : (do
        let U' ← $ᵗ (Keystream geom)
        let x ← nextDraw geom
        pure (⟨k, cs, U', x⟩ : FinalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A))
      = (fun p : Keystream geom × NextOth geom =>
          (⟨k, cs, p.1, p.2⟩ : FinalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))
        <$> (do let U' ← $ᵗ (Keystream geom); let x ← nextDraw geom; pure (U', x)) := by
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  rw [e, prEvent_map]

/-! ## The zero-tag event -/

/-- The draws of world 1 on which the layers the last comparison needs can be built: the
original's next layer when there is one, and at the end of the path a reliable request. -/
def finalBuilds {pk : Key kem}
    (ch : ForwardCh kem cipher macS kdfS streamS geom hvalid hmactag h16 names pk) (x : NextOth
        geom) (U' : Keystream geom) : Prop :=
  (ch.c.pos + 1 < ch.c.req.fwd.hops.length →
      ∃ fwd, layerPast kem cipher macS kdfS streamS geom
        (RSOR.path kem ch.c.req.fwd [.recipient ch.c.req.receiver]) x.2.2.2.1.1.1
        (RSOR.body kem macS kdfS streamS geom ch.c.req x.2.2.2.1.1) ch.c.pos (ofVector U')
        (ch.c.pos + 1) = .ok fwd)
    ∧ (¬ ch.c.pos + 1 < ch.c.req.fwd.hops.length →
      RSOR.Reliable kem cipher macS kdfS streamS geom ch.c.req x.2.2.2.1.1)

set_option maxHeartbeats 1000000 in
/-- **The zero-tag event has the chance of one tag.** A draw of world 1 is not good with at
most the chance that a layer cannot be built, plus one in the number of payload tags. -/
theorem prEvent_not_finalGood_le (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    Pr{let d ← (finalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[¬
        finalGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names d.cs.1 d.x d.U']
      ≤ Pr{let d ← (finalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)}[¬
          finalBuilds kem cipher macS kdfS streamS geom hvalid hmactag h16 names d.cs.1 d.x d.U']
        + (Fintype.card (Vector UInt8 geom.payloadTagLength) : ENNReal)⁻¹ := by
  have hE : (finalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A >>= fun d =>
        (pure (((ofVector d.x.2.2.2.2.2).extract 0 geom.payloadTagLength).data.all (· == 0)) :
          ProbComp Bool))
      =ᵈ ($ᵗ (Block geom) >>= fun v =>
        (pure (((ofVector v).extract 0 geom.payloadTagLength).data.all (· == 0)) :
          ProbComp Bool)) := by
    simp only [finalDraw, nextDraw, shortDraw, bind_assoc, pure_bind]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun _ =>
      OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_const _ _) ?_
    exact EvalDistEq.rfl
  have key := hE (fun b => b = true)
  simp only [bind_pure_comp, prEvent_map] at key
  have hmono := prEvent_mono (finalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
      A)
    (fun d : FinalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A => ¬ finalGood
        kem cipher macS kdfS streamS geom hvalid hmactag h16 names d.cs.1 d.x d.U')
    (fun d : FinalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A => ¬
        finalBuilds kem cipher macS kdfS streamS geom hvalid hmactag h16 names d.cs.1 d.x d.U'
      ∨ ((ofVector d.x.2.2.2.2.2).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
    fun d h => by
      unfold finalGood at h
      unfold finalBuilds
      by_cases hz : ((ofVector d.x.2.2.2.2.2).extract 0
          geom.payloadTagLength).data.all (· == 0) = true
      · exact Or.inr hz
      · exact Or.inl fun hb => h ⟨hb.1, hb.2, hz⟩
  have hor := prEvent_or_le (finalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
    (fun d : FinalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A => ¬
        finalBuilds kem cipher macS kdfS streamS geom hvalid hmactag h16 names d.cs.1 d.x d.U')
    (fun d : FinalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names A =>
      ((ofVector d.x.2.2.2.2.2).extract 0 geom.payloadTagLength).data.all (· == 0) = true)
  have hz := key.trans (prEvent_zeroPrefix (a := geom.payloadTagLength)
    (b := geom.forwardPayloadLength) rfl)
  exact hmono.trans (hor.trans (add_le_add le_rfl (le_of_eq hz)))

/-! ## TLU→ for KEM Sphinx -/

variable [SampleableType kem.Plaintext] in
/-- **TLU→ for KEM Sphinx, down to the draws.** The advantage in telling the adversary's own
onion from a replacement that ends at the honest relay is at most: the chance of a draw on
which a layer does not build; the cost of replacing the relay's keys in each world and for the
original's hidden layer; a forgery against the MAC for each; the one-block advantage against
the payload cipher in each world; the keystream generator's advantage for each of the three
keystreams; the chance that the adversary sends the hidden ciphertext; and the chance of a
draw of world 1 that is not good for the last comparison. No term is left as a distance
between two games. -/
theorem forwardUnlinkable_le
    (A : (Protocols.RSOR.forwardUnlinkable (S := 𝒮)).Adversary) :
    ((Protocols.RSOR.forwardUnlinkable (S := 𝒮)).advantage names A).toReal
      ≤ (Pr{let d ← (forwardDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
          A)}[forwardBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + (Pr{let d ← (forwardDrawOf kem cipher macS kdfS streamS geom hvalid hmactag h16 names _
          (shortDraw geom)
          A)}[shortBad kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + keyedCost cipher macS kdfS streamS geom
          (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        + keyedCost cipher macS kdfS streamS geom
          (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        + (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
            (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
            (forwardM kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (forwardViewT kem cipher macS kdfS streamS geom hvalid hmactag h16
              names)))}[x = true]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
            (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[¬ forwardGood kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
            (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
            (shortM kem cipher macS kdfS streamS geom hvalid hmactag h16 names)
            (shortViewT kem cipher macS kdfS streamS geom hvalid hmactag h16
              names)))}[x = true]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
            (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[¬ shortGood kem cipher macS kdfS streamS geom hvalid hmactag h16 d]).toReal
        + |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (forwardGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
            true)}[x = true]).toReal
          - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (forwardGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
            false)}[x = true]).toReal|
        + |(Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (shortGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
            true)}[x = true]).toReal
          - (Pr{let x ← (Primitives.WideBlockCipher.oneQueryExp cipher _
            (shortGameP kem cipher macS kdfS streamS geom hvalid hmactag h16 names A).adv
            false)}[x = true]).toReal|
        + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
            (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal
          - (Pr{let x ← (PRGScheme.prgIdealExperiment
            (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal|
        + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
            (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal
          - (Pr{let x ← (PRGScheme.prgIdealExperiment
            (shortStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[x = true]).toReal|
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
            (forwardAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[¬ forwardGoodP kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                d]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
            (shortAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[¬ shortGoodP kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                d]).toReal
        + (Pr{let d ← (keyedDraw cipher macS kdfS streamS geom
            (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
              A))}[¬ nextGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                d]).toReal
        + keyedCost cipher macS kdfS streamS geom
          (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
        + (Pr{let x ← (Primitives.MAC.forgeExp macS (forgeAdv cipher macS kdfS streamS geom
          (nextAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A)
          (fun _ _ _ _ => nextM0 kem geom)
          (fun ch o c rest _ => nextView kem cipher macS kdfS streamS geom hvalid hmactag h16
            names ch o c
            (withMAC rest default))))}[x = true]).toReal
        + |(Pr{let x ← (PRGScheme.prgRealExperiment (keystreamPRG streamS geom)
              (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                A))}[x = true]).toReal
          - (Pr{let x ← (PRGScheme.prgIdealExperiment
              (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names
                A))}[x = true]).toReal|
        + (Pr{let b ← (nextHidden kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A)}[b = true]).toReal
        + (Pr{let d ← (finalDraw kem cipher macS kdfS streamS geom hvalid hmactag h16 names
            A)}[¬ finalGood kem cipher macS kdfS streamS geom hvalid hmactag h16 names d.cs.1 d.x
              d.U']).toReal := by
  have h := forwardUnlinkable_le_next kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have h1 := next_hidden_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have h2 := next_final_le kem cipher macS kdfS streamS geom hvalid hmactag h16 names A
  have t := abs_sub_le
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (nextStreamAdv kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
          true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (nextStreamAdvF kem cipher macS kdfS streamS geom hvalid hmactag h16 names
        (ownAns kem cipher macS kdfS streamS geom) A))}[x = true]).toReal
    (Pr{let x ← (PRGScheme.prgIdealExperiment
      (forwardStreamAdv0 kem cipher macS kdfS streamS geom hvalid hmactag h16 names A))}[x =
          true]).toReal
  linarith

end ForwardFinal

end Cryptlib.Protocols.Sphinx.KEMSphinx
