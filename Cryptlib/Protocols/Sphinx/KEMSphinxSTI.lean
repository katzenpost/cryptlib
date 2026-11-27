/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Cryptlib.Protocols.Sphinx.KEMSphinxSLURelay

namespace Cryptlib.Protocols.RSOR

open OracleComp OracleSpec

variable {S : Scheme}

/-- The game that tells two worlds for a challenge of STI↔ apart. -/
def tailPair (w₀ w₁ : {hon : Honest S} → TailChallenge hon → ProbComp (World S)) : Property S where
  Challenge := TailChallenge
  world c b := match b with
    | false => w₀ c
    | true => w₁ c

/-- An adversary of one such game, against another. -/
def tailPair.cast {u₀ u₁ : {hon : Honest S} → TailChallenge hon → ProbComp (World S)}
    (w₀ w₁ : {hon : Honest S} → TailChallenge hon → ProbComp (World S))
    (A : (tailPair u₀ u₁).Adversary) : (tailPair w₀ w₁).Adversary :=
  ⟨A.State, A.choose, A.guess⟩

/-- An adversary of STI↔, against the game of its two worlds. -/
def tailPair.ofTail (A : (tailIndistinguishable (S := S)).Adversary) :
    (tailPair (fun c => (tailIndistinguishable (S := S)).world c false)
      (fun c => (tailIndistinguishable (S := S)).world c true)).Adversary :=
  ⟨A.State, A.choose, A.guess⟩

/-- STI↔ is the game of its two worlds. -/
theorem tailIndistinguishable_advantage_eq (names : Role → S.Name)
    (A : (tailIndistinguishable (S := S)).Adversary) :
    (tailIndistinguishable (S := S)).advantage names A
      = (tailPair (fun c => (tailIndistinguishable (S := S)).world c false)
        (fun c => (tailIndistinguishable (S := S)).world c true)).advantage names
          (tailPair.ofTail A) :=
  rfl

/-- **Two worlds through a world in the middle.** -/
theorem tailPair_advantage_le
    (w₀ w₁ w₂ : {hon : Honest S} → TailChallenge hon → ProbComp (World S)) (names : Role → S.Name)
    (A : (tailPair w₀ w₂).Adversary) :
    ((tailPair w₀ w₂).advantage names A).toReal
      ≤ ((tailPair w₁ w₂).advantage names (tailPair.cast w₁ w₂ A)).toReal
        + ((tailPair w₀ w₁).advantage names (tailPair.cast w₀ w₁ A)).toReal := by
  rw [Property.advantage_toReal, Property.advantage_toReal, Property.advantage_toReal]
  have e1 : Property.play names (tailPair.cast w₁ w₂ A) true = Property.play names A true := rfl
  have e2 : Property.play names (tailPair.cast w₁ w₂ A) false
      = Property.play names (tailPair.cast w₀ w₁ A) true := rfl
  have e3 : Property.play names (tailPair.cast w₀ w₁ A) false = Property.play names A false :=
    rfl
  rw [e1, e2, e3]
  exact abs_sub_le _ _ _

/-- Worlds that are the same in distribution give the same game. -/
theorem tailPair_play_congr
    (w₀ w₁ u₀ u₁ : {hon : Honest S} → TailChallenge hon → ProbComp (World S))
    (h₀ : ∀ {hon : Honest S} (c : TailChallenge hon), w₀ c =ᵈ u₀ c)
    (h₁ : ∀ {hon : Honest S} (c : TailChallenge hon), w₁ c =ᵈ u₁ c)
    (names : Role → S.Name) (A : (tailPair w₀ w₁).Adversary) (b : Bool) :
    Property.play names A b =ᵈ Property.play names (tailPair.cast u₀ u₁ A) b := by
  unfold Property.play Property.playFrom
  refine EvalDistEq.bind_right _ fun kr => EvalDistEq.bind_right _ fun kb =>
    EvalDistEq.bind_right _ fun ks => EvalDistEq.bind_right _ fun out => ?_
  cases b
  · exact (h₀ out.1.1).bind_left _
  · exact (h₁ out.1.1).bind_left _

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

/-! # STI↔ for KEM Sphinx

World 0 of STI↔ shows a layer of the adversary's onion from a forward position on; world 1
shows the first layer of an onion over the rest of the forward path. A layer from a position on
is a layer over the rest of the path, with the filler there as the rest's padding.

The two worlds are compared through worlds in the middle (`tailPair`). -/

section RestOfForward

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF)
  (streamS : StreamCipher) (geom : Geometry)

omit cipher macS in
/-- The fillers from position `j` on are the fillers built on the rest of the path from the
filler at `j`. -/
theorem fillerAt_drop (hops : Array PathHop) (seeds : Array (Vector UInt8 32))
    (filler : ByteArray) (j i : ℕ) :
    RSOR.fillerAt kem kdfS streamS geom hops seeds filler (j + i)
      = RSOR.fillerAt kem kdfS streamS geom (hops.extract j hops.size)
        (seeds.extract j seeds.size) (RSOR.fillerAt kem kdfS streamS geom hops seeds filler j)
        i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show RSOR.fillerAt kem kdfS streamS geom hops seeds filler (j + i + 1) = _
    simp only [RSOR.fillerAt]
    rw [ih, extract_tail_tail hops j i, extract_tail_tail seeds j i]

/-- **A layer from a position on is a layer over the rest of the path**, when the seeds from
there on are the rest's seeds and the filler there is the rest's padding. -/
theorem layer_drop (R : Protocols.RSOR.Route geom.nrHops RSOR.Name (Key kem))
    (last : List RoutingCommand) (d d' : RSOR.Draw geom) (payload : ByteArray) (j i : ℕ)
    (hj : j ≤ R.hops.length)
    (hseeds : (d.1.toArray.extract 0 (RSOR.path kem R last).size).extract j
        (d.1.toArray.extract 0 (RSOR.path kem R last).size).size
      = d'.1.toArray.extract 0 (RSOR.path kem (R.drop j) last).size)
    (hfill : RSOR.fillerAt kem kdfS streamS geom (RSOR.path kem R last)
        (d.1.toArray.extract 0 (RSOR.path kem R last).size)
        ((ofVector d.2).extract 0
          ((geom.nrHops - (RSOR.path kem R last).size) * geom.perHopRoutingInfoLength)) j
      = (ofVector d'.2).extract 0
        ((geom.nrHops - (RSOR.path kem (R.drop j) last).size)
          * geom.perHopRoutingInfoLength)) :
    RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem R last) d payload (j + i)
      = RSOR.layer kem cipher macS kdfS streamS geom (RSOR.path kem (R.drop j) last) d' payload
        i := by
  unfold RSOR.layer
  dsimp only
  rw [fillerAt_drop, hfill,
    extract_tail_tail (d.1.toArray.extract 0 (RSOR.path kem R last).size) j i,
    extract_tail_tail (RSOR.path kem R last) j i, hseeds,
    path_extract_drop kem geom R last j hj]

end RestOfForward

section TailGame

open Cryptlib.Protocols.RSOR (Role)

variable (kem : KEM) (cipher : WideBlockCipher) (macS : MAC) (kdfS : KDF) (streamS : StreamCipher)
  (geom : Geometry)
  (hvalid : geom.ValidForKEM kem) (hmactag : macS.tagSize = macLength)
  (h16 : 16 ≤ geom.payloadTagLength + geom.forwardPayloadLength)

local notation "𝒮" => sphinx kem cipher macS kdfS streamS geom hvalid hmactag h16

/-- The first layer of an onion over the rest of the forward path, with the forward draw `d`,
around the payload of the adversary's onion. The honest backward relay answers nothing to the
reply's layer, as in world 0. -/
def tailMidWorld {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (r : RSOR.Randomness geom) (d : RSOR.Draw geom) : Protocols.RSOR.World 𝒮 where
  onion :=
    (match RSOR.layer kem cipher macS kdfS streamS geom
        (RSOR.path kem (c.req.fwd.drop c.pos) [.recipient c.req.receiver]) d
        (RSOR.body kem macS kdfS streamS geom c.req r) 0 with
    | .ok pkt => RSOR.split geom pkt
    | .error _ => (default : RSOR.Onion geom))
  patch := (Protocols.RSOR.tailWorld (S := 𝒮) c.req r c.pos c.back).patch

/-- **The world in the middle of STI↔**: `tailMidWorld` with its draws. The payload still
carries the SURB over the whole backward path. -/
def tailMid {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon) :
    ProbComp (Protocols.RSOR.World 𝒮) := do
  let r ← $ᵗ (RSOR.Randomness geom)
  let d ← $ᵗ (RSOR.Draw geom)
  return tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c r d

/-- The challenger's randomness with the seed `s` at the forward hop before position `pos`. -/
def tailSeed (pos : ℕ) (r : RSOR.Randomness geom) (s : Vector UInt8 32) : RSOR.Randomness geom :=
  match pos with
  | 0 => r
  | k + 1 => setSeed geom r k s

omit kem cipher macS kdfS streamS hvalid hmactag h16 in
/-- Drawing the challenger's randomness and a seed, and putting the seed at the hop before the
shown layer, is drawing the randomness. -/
theorem evalDistEq_tailSeed {δ : Type} (pos : ℕ) (hpos : pos ≤ geom.nrHops)
    (K : RSOR.Randomness geom → ProbComp δ) :
    (do
      let r ← $ᵗ (RSOR.Randomness geom)
      let s ← $ᵗ (Vector UInt8 32)
      K (tailSeed geom pos r s)) =ᵈ ($ᵗ (RSOR.Randomness geom) >>= K) := by
  cases pos with
  | zero =>
    exact EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (Vector UInt8 32)) (K r)
  | succ k => exact evalDistEq_setSeed geom k (by omega) K

/-- The hop before the shown layer needs no further step: there is none, or it is the honest
relay with a role in `done`. -/
def tailDone {hon : Protocols.RSOR.Honest 𝒮} (done : Role → Bool)
    (c : Protocols.RSOR.TailChallenge hon) : Prop :=
  c.pos.val = 0
    ∨ ∃ ρ, done ρ = true ∧ ∃ k, k + 1 = c.pos.val ∧ c.req.fwd.hops[k]? = some (hon ρ)

open Classical in
/-- **A world between world 0 and the world in the middle**: the middle world when the hop
before the shown layer needs no further step, and world 0 otherwise. -/
noncomputable def tailHyb (done : Role → Bool) {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) : ProbComp (Protocols.RSOR.World 𝒮) := do
  let r ← $ᵗ (RSOR.Randomness geom)
  let d ← $ᵗ (RSOR.Draw geom)
  return if tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 done c then tailMidWorld
      kem cipher macS kdfS streamS geom hvalid hmactag h16 c r d
    else Protocols.RSOR.tailWorld (S := 𝒮) c.req r c.pos c.back

/-- With both roles the relay before the shown layer can have handled, the hybrid is the world
in the middle. -/
theorem tailHyb_all {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon) :
    tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun ρ => ρ == .relay || ρ ==
        .back) c = tailMid kem cipher macS kdfS streamS geom hvalid hmactag h16 c := by
  have hd : tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun ρ => ρ == .relay ||
      ρ == .back) c := by
    by_cases hp : c.pos.val = 0
    · exact Or.inl hp
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hp
      rcases c.relay k hk.symm with h | h
      · exact Or.inr ⟨.relay, rfl, k, hk.symm, h⟩
      · exact Or.inr ⟨.back, rfl, k, hk.symm, h⟩
  unfold tailHyb tailMid
  simp only [hd, ite_true]

/-- The middle world reads the challenger's randomness through its backward part only. -/
theorem tailMidWorld_congr {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) (r r' : RSOR.Randomness geom) (d : RSOR.Draw geom)
    (h : r.2 = r'.2) :
    tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c r d = tailMidWorld kem
        cipher macS kdfS streamS geom hvalid hmactag h16 c r' d := by
  obtain ⟨a, b⟩ := r
  obtain ⟨a', b'⟩ := r'
  obtain rfl : b = b' := h
  rfl

/-- When the shown layer is the first, world 0 is the middle world with the challenger's own
forward draw. -/
theorem tailWorld_zero {hon : Protocols.RSOR.Honest 𝒮} (c : Protocols.RSOR.TailChallenge hon)
    (r : RSOR.Randomness geom) (hp : c.pos.val = 0) :
    Protocols.RSOR.tailWorld (S := 𝒮) c.req r c.pos c.back
      = tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c r r.1 := by
  unfold Protocols.RSOR.tailWorld tailMidWorld
  congr 1
  show RSOR.form kem cipher macS kdfS streamS geom c.req r c.pos = _
  unfold RSOR.form
  rw [hp]
  rfl

set_option maxHeartbeats 2000000 in
/-- **World 0 is the hybrid with no role handled.** When the shown layer is the first there is
no relay before it, and world 0 is the middle world after renaming the forward draw. -/
theorem tailWorld_evalDistEq_tailHyb {hon : Protocols.RSOR.Honest 𝒮}
    (c : Protocols.RSOR.TailChallenge hon) :
    (Protocols.RSOR.tailIndistinguishable (S := 𝒮)).world c false
      =ᵈ tailHyb kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun _ => false) c := by
  have hw : (Protocols.RSOR.tailIndistinguishable (S := 𝒮)).world c false
      = ($ᵗ (RSOR.Randomness geom) >>= fun r =>
        pure (Protocols.RSOR.tailWorld (S := 𝒮) c.req r c.pos c.back)) := by
    simp [Protocols.RSOR.tailIndistinguishable]
    rfl
  rw [hw]
  unfold tailHyb
  by_cases hp : c.pos.val = 0
  · have hd : tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun _ => false) c :=
      Or.inl hp
    simp only [hd, ite_true]
    have e : ∀ (r : RSOR.Randomness geom) (d : RSOR.Draw geom),
        tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c r d = tailMidWorld kem
            cipher macS kdfS streamS geom hvalid hmactag h16 c (default, r.2) d :=
      fun r d => tailMidWorld_congr kem cipher macS kdfS streamS geom hvalid hmactag h16 c r _ d rfl
    simp only [tailWorld_zero kem cipher macS kdfS streamS geom hvalid hmactag h16 c _ hp]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ fun r => by rw [e r r.1]) ?_
    refine EvalDistEq.trans ?_ (EvalDistEq.bind_right _ fun r =>
      EvalDistEq.bind_right _ fun d => by rw [e r d]).symm
    refine EvalDistEq.trans (evalDistEq_pair_of_bijective
      (g := fun (x : RSOR.Draw geom) (y : RSOR.Draw geom × Vector UInt8 64 × Vector UInt8 16) =>
        (x, y)) Function.bijective_id
      (fun r : RSOR.Randomness geom =>
        (pure (tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c (default, r.2)
            r.1) :
          ProbComp (Protocols.RSOR.World 𝒮)))).symm ?_
    refine EvalDistEq.trans ?_ (evalDistEq_snd (α := RSOR.Draw geom)
      (fun b : RSOR.Draw geom × Vector UInt8 64 × Vector UInt8 16 =>
        $ᵗ (RSOR.Draw geom) >>= fun d =>
          (pure (tailMidWorld kem cipher macS kdfS streamS geom hvalid hmactag h16 c (default, b)
              d) :
            ProbComp (Protocols.RSOR.World 𝒮)))).symm
    exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  · have hd : ¬ tailDone kem cipher macS kdfS streamS geom hvalid hmactag h16 (fun _ => false) c :=
      fun h => by
      rcases h with h | ⟨ρ, h, -⟩
      · exact hp h
      · cases h
    simp only [hd, ite_false]
    exact (EvalDistEq.bind_right _ fun r =>
      OracleComp.EvalDistEq.bind_const ($ᵗ (RSOR.Draw geom)) _).symm

end TailGame

end Cryptlib.Protocols.Sphinx.KEMSphinx
