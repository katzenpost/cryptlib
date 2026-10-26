/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.CryptoFoundations.PRG
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.SampleableType

/-! # §4.4: Indistinguishability of forward and reply messages

Models the first challenge hop's tuple `((α0,β0,γ0),δ0)` over a generic DDH group with ρ/μ/π as
PRGs; the paper reduces general `j` to `j = 0`. Assumptions: DDH, and that `hρ, hμ, hπ` at a fresh
`s0` are jointly pseudorandom (`jointKeyPRG`). General `j` and reply-vs-nymserver
indistinguishability are not mechanized. -/

namespace Cryptlib.Protocols.Sphinx.Indistinguishability

open OracleComp OracleSpec ENNReal
open PRGScheme (PRGAdversary prgRealExperiment prgIdealExperiment)
open DiffieHellman (DDHAdversary ddhRealExperiment ddhRandomExperiment)

variable {F G Seed KeyMu KeyPi Beta Gamma Delta : Type}
variable [Field F] [AddCommGroup G] [Module F G] [AddCommGroup Beta]

/-- §3.1's system parameters: the generator `g`, the random oracles `hρ, hμ, hπ`, and ρ/μ/π. -/
structure Sys (F G Seed KeyMu KeyPi Beta Gamma Delta : Type) where
  g : G
  hρ : G → Seed
  hμ : G → KeyMu
  hπ : G → KeyPi
  ρgen : Seed → Beta
  μeval : KeyMu → Beta → Gamma
  πenc : KeyPi → Delta → Delta

/-- The two challenge branches: the routing plaintext XORed into `β0`, and `δ0`'s plaintext. -/
structure Choice (Beta Delta : Type) where
  betaPt : Beta
  deltaPt : Delta

variable (S : Sys F G Seed KeyMu KeyPi Beta Gamma Delta)

omit [Field F] [AddCommGroup G] [Module F G] [AddCommGroup Beta] in
/-- A leading draw whose result goes unused leaves an event unchanged. -/
theorem prEvent_bind_unused {α β : Type} (mx : ProbComp α) (my : ProbComp β) (p : β → Prop) :
    Pr{let y ← mx >>= fun _ => my}[p y] = Pr{let y ← my}[p y] := by
  simp only [prEvent_norm]
  exact OracleComp.prEvent_bind_const _ _

/-- Hop 0's tuple `((α0,β0,γ0),δ0)` from `α0 = x • g` and `s0`. -/
def buildFrom (α0 s0 : G) (c : Choice Beta Delta) : G × Beta × Gamma × Delta :=
  let β0 := c.betaPt + S.ρgen (S.hρ s0)
  let γ0 := S.μeval (S.hμ s0) β0
  let δ0 := S.πenc (S.hπ s0) c.deltaPt
  (α0, β0, γ0, δ0)

/-- An adversary that guesses which challenge branch produced hop 0's tuple. -/
abbrev Adversary := G × Beta × Gamma × Delta → ProbComp Bool

section Games

variable [SampleableType F]

/-- Game `G` (§4.4) at `j = 0`: hop 0's tuple built from branch `b` with the real DH secret. -/
def gameReal (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) : ProbComp Bool := do
  let x ← $ᵗ F
  let xn0 ← $ᵗ F
  let b ← $ᵗ Bool
  let guess ← A (buildFrom S (x • S.g) ((x * xn0) • S.g) (if b then c1 else c0))
  return (b == guess)

/-- Game `G2`: `s0` replaced by an independent random group element. -/
def game2 (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) : ProbComp Bool := do
  let x ← $ᵗ F
  let c' ← $ᵗ F
  let b ← $ᵗ Bool
  let guess ← A (buildFrom S (x • S.g) (c' • S.g) (if b then c1 else c0))
  return (b == guess)

/-- The adversary's advantage in game `G` over a coin flip. -/
noncomputable def advantage
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) : ℝ :=
  |(Pr{let x ← gameReal S A c0 c1}[x = true]).toReal - 1 / 2|

end Games

section DDHReduction

variable [SampleableType F]

/-- The DDH adversary built from an `Adversary`. -/
def ddhAdversaryOf
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) : DDHAdversary F G :=
  fun _g' α0 _n0pub s0 => do
    let b ← $ᵗ Bool
    let guess ← A (buildFrom S α0 s0 (if b then c1 else c0))
    return (b == guess)

/-- `ddhRealExperiment` equals `gameReal`. -/
theorem probTrue_gameReal_eq_ddhExpReal
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) :
    Pr{let x ← gameReal S A c0 c1}[x = true] =
      Pr{let x ← ddhRealExperiment S.g (ddhAdversaryOf S A c0 c1)}[x = true] := by
  unfold gameReal ddhRealExperiment ddhAdversaryOf
  rfl

/-- `ddhRandomExperiment` equals `game2`. -/
theorem probTrue_game2_eq_ddhExpRand
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) :
    Pr{let x ← game2 S A c0 c1}[x = true] =
      Pr{let x ← ddhRandomExperiment S.g (ddhAdversaryOf S A c0 c1)}[x = true] := by
  unfold game2 ddhRandomExperiment ddhAdversaryOf
  refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
  rw [prEvent_bind_unused]

end DDHReduction


section KeyIndependence

variable [SampleableType F] [SampleableType Seed] [SampleableType KeyMu] [SampleableType KeyPi]
  [SampleableType (Seed × KeyMu × KeyPi)] [Finite F]

/-- `buildFrom` with the three oracle outputs as arguments. -/
def buildFromKeys (α0 : G) (seed : Seed) (kmu : KeyMu) (kpi : KeyPi) (c : Choice Beta Delta) :
    G × Beta × Gamma × Delta :=
  let β0 := c.betaPt + S.ρgen seed
  let γ0 := S.μeval kmu β0
  let δ0 := S.πenc kpi c.deltaPt
  (α0, β0, γ0, δ0)

omit [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [SampleableType Seed]
  [SampleableType KeyMu] [SampleableType KeyPi] [SampleableType (Seed × KeyMu × KeyPi)]
  [Finite F] in
@[simp] lemma buildFrom_eq_buildFromKeys (α0 s0 : G) (c : Choice Beta Delta) :
    buildFrom S α0 s0 c = buildFromKeys S α0 (S.hρ s0) (S.hμ s0) (S.hπ s0) c := rfl

/-- Game `G2'`: the three oracle outputs replaced by an independent uniform triple. -/
def game2' (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) : ProbComp Bool := do
  let x ← $ᵗ F
  let b ← $ᵗ Bool
  let p ← $ᵗ (Seed × KeyMu × KeyPi)
  let guess ← A (buildFromKeys S (x • S.g) p.1 p.2.1 p.2.2 (if b then c1 else c0))
  return (b == guess)

/-- The map `c' ↦ (hρ(c'•g), hμ(c'•g), hπ(c'•g))` as a PRG; `G2` and `G2'` are its real and
ideal experiments. -/
def jointKeyPRG : PRGScheme F (Seed × KeyMu × KeyPi) :=
  ⟨fun c' => (S.hρ (c' • S.g), S.hμ (c' • S.g), S.hπ (c' • S.g))⟩

/-- The `jointKeyPRG` reduction adversary. -/
def jointAdversaryOf
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) (x : F) : PRGAdversary (Seed × KeyMu × KeyPi) := fun p => do
  let b ← $ᵗ Bool
  let guess ← A (buildFromKeys S (x • S.g) p.1 p.2.1 p.2.2 (if b then c1 else c0))
  return (b == guess)

omit [SampleableType Seed] [SampleableType KeyMu] [SampleableType KeyPi]
  [SampleableType (Seed × KeyMu × KeyPi)] [Finite F] in
/-- The `jointKeyPRG` real experiment equals `game2`. -/
theorem probTrue_game2_eq_prgRealExp_joint
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) :
    Pr{let x ← game2 S A c0 c1}[x = true] =
      Pr{let y ← (do
        let x ← $ᵗ F
        prgRealExperiment (jointKeyPRG S) (jointAdversaryOf S A c0 c1 x))}[y = true] := by
  unfold game2 prgRealExperiment jointKeyPRG jointAdversaryOf
  rfl

omit [SampleableType Seed] [SampleableType KeyMu] [SampleableType KeyPi] [Finite F] in
/-- The `jointKeyPRG` ideal experiment equals `game2'`. -/
theorem probTrue_game2'_eq_prgIdealExp_joint
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) :
    Pr{let x ← game2' S A c0 c1}[x = true] =
      Pr{let y ← (do
        let x ← $ᵗ F
        prgIdealExperiment (jointAdversaryOf S A c0 c1 x))}[y = true] := by
  unfold game2' prgIdealExperiment jointAdversaryOf
  refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
  simp only [prEvent_norm]
  exact OracleComp.prEvent_bind_bind_swap _ _ _

end KeyIndependence

section PRGHybrid

variable [SampleableType F] [SampleableType Seed] [SampleableType KeyMu] [SampleableType KeyPi]
  [SampleableType Beta] [SampleableType Gamma] [SampleableType Delta]
  [SampleableType (Seed × KeyMu × KeyPi)] [SampleableType (Beta × Gamma × Delta)]

/-- ρ/μ/π combined into one PRG `(seed, kmu, kpi) ↦ (β0, γ0, δ0)` for a fixed branch `c`. -/
def combinedGen (c : Choice Beta Delta) (p : Seed × KeyMu × KeyPi) : Beta × Gamma × Delta :=
  let β0 := c.betaPt + S.ρgen p.1
  let γ0 := S.μeval p.2.1 β0
  let δ0 := S.πenc p.2.2 c.deltaPt
  (β0, γ0, δ0)

def combinedPRG (c : Choice Beta Delta) : PRGScheme (Seed × KeyMu × KeyPi) (Beta × Gamma × Delta) :=
  ⟨combinedGen S c⟩

/-- The combined-PRG reduction adversary. -/
def combinedAdversaryOf
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (x : F) (b : Bool) : PRGAdversary (Beta × Gamma × Delta) := fun t =>
  A (x • S.g, t.1, t.2.1, t.2.2) >>= fun guess => pure (b == guess)

omit [SampleableType Seed] [SampleableType KeyMu] [SampleableType KeyPi] [SampleableType Beta]
  [SampleableType Gamma] [SampleableType Delta] [SampleableType (Beta × Gamma × Delta)] in
theorem probTrue_game2'_eq_prgRealExp_combined
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) :
    Pr{let x ← game2' S A c0 c1}[x = true] =
      Pr{let y ← (do
        let x ← $ᵗ F
        let b ← $ᵗ Bool
        prgRealExperiment (combinedPRG S (if b then c1 else c0)) (combinedAdversaryOf S A x b))}[y = true] := by
  unfold game2' prgRealExperiment combinedPRG combinedAdversaryOf combinedGen
  rfl

/-- Game `G3`: `β0, γ0, δ0` replaced by an independent uniform triple. -/
def game3 (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (_c0 _c1 : Choice Beta Delta) : ProbComp Bool := do
  let x ← $ᵗ F
  let b ← $ᵗ Bool
  let t ← $ᵗ (Beta × Gamma × Delta)
  let guess ← A (x • S.g, t.1, t.2.1, t.2.2)
  return (b == guess)

omit [AddCommGroup Beta] [SampleableType Seed] [SampleableType KeyMu] [SampleableType KeyPi]
  [SampleableType Beta] [SampleableType Gamma] [SampleableType Delta]
  [SampleableType (Seed × KeyMu × KeyPi)] in
theorem probTrue_game3_eq_prgIdealExp_combined
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) :
    Pr{let x ← game3 S A c0 c1}[x = true] =
      Pr{let y ← (do
        let x ← $ᵗ F
        let b ← $ᵗ Bool
        prgIdealExperiment (combinedAdversaryOf S A x b))}[y = true] := by
  unfold game3 prgIdealExperiment combinedAdversaryOf
  rfl

omit [AddCommGroup Beta] [SampleableType Seed] [SampleableType KeyMu] [SampleableType KeyPi]
  [SampleableType Beta] [SampleableType Gamma] [SampleableType Delta]
  [SampleableType (Seed × KeyMu × KeyPi)] in
/-- In `G3` the adversary guesses `b` with probability exactly `1/2`. -/
theorem probTrue_game3
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) :
    (Pr{let x ← game3 S A c0 c1}[x = true]).toReal = 1 / 2 := by
  have hstep : ∀ x : F,
      Pr{let y ← (do
        let b ← $ᵗ Bool
        let t ← $ᵗ (Beta × Gamma × Delta)
        let guess ← A (x • S.g, t.1, t.2.1, t.2.2)
        return (b == guess))}[y = true] = 1 / 2 := by
    intro x
    -- The adversary's input does not depend on `b`.
    have h := ProbComp.evalDist_decide_eq_uniformBool_half
      (f := fun _ : Bool => do
        let t ← $ᵗ (Beta × Gamma × Delta)
        A (x • S.g, t.1, t.2.1, t.2.2))
      rfl
    rw [prEvent_eq_evalDist_singleton]
    simpa only [show ∀ a b : Bool, decide (a = b) = (a == b) from fun _ _ => rfl,
      bind_assoc] using h
  unfold game3
  have hconst : Pr{let y ← (do
        let x ← $ᵗ F
        let b ← $ᵗ Bool
        let t ← $ᵗ (Beta × Gamma × Delta)
        let guess ← A (x • S.g, t.1, t.2.1, t.2.2)
        return (b == guess))}[y = true] =
      Pr{let x ← (do
        let _x ← $ᵗ F
        let b ← $ᵗ Bool
        let t ← $ᵗ (Beta × Gamma × Delta)
        let guess ← A ((0 : F) • S.g, t.1, t.2.1, t.2.2)
        return (b == guess))}[x = true] := by
    refine prEvent_bind_congr _ _ _ _ _ fun x => ?_
    rw [hstep x, hstep 0]
  rw [hconst, prEvent_bind_unused, hstep 0]
  norm_num

end PRGHybrid

section MainTheorem

variable [SampleableType F] [SampleableType Seed] [SampleableType KeyMu] [SampleableType KeyPi]
  [SampleableType Beta] [SampleableType Gamma] [SampleableType Delta]
  [SampleableType (Seed × KeyMu × KeyPi)] [Finite F]

omit [Finite F] [SampleableType Seed] [SampleableType KeyMu] [SampleableType KeyPi] in
/-- §4.4: the advantage is bounded by the DDH advantage (`hddh`), the joint-key PRG advantage
(`hjointPRG`), and the combined ρ/μ/π PRG advantage (`hprg`). -/
theorem advantage_le
    (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) (εDDH εJoint εPRG : ℝ)
    (hddh : |(Pr{let x ← ddhRealExperiment S.g (ddhAdversaryOf S A c0 c1)}[x = true]).toReal -
      (Pr{let x ← ddhRandomExperiment S.g (ddhAdversaryOf S A c0 c1)}[x = true]).toReal| ≤ εDDH)
    (hjointPRG : |(Pr{let x ← game2 S A c0 c1}[x = true]).toReal -
      (Pr{let x ← game2' S A c0 c1}[x = true]).toReal| ≤ εJoint)
    (hprg : |(Pr{let x ← game2' S A c0 c1}[x = true]).toReal - (Pr{let x ← game3 S A c0 c1}[x = true]).toReal| ≤ εPRG) :
    advantage S A c0 c1 ≤ εDDH + εJoint + εPRG := by
  unfold advantage
  have e1 : (Pr{let x ← gameReal S A c0 c1}[x = true]).toReal =
      (Pr{let x ← ddhRealExperiment S.g (ddhAdversaryOf S A c0 c1)}[x = true]).toReal := by
    rw [probTrue_gameReal_eq_ddhExpReal]
  have e2 : (Pr{let x ← game2 S A c0 c1}[x = true]).toReal =
      (Pr{let x ← ddhRandomExperiment S.g (ddhAdversaryOf S A c0 c1)}[x = true]).toReal := by
    rw [probTrue_game2_eq_ddhExpRand]
  have e4 : (Pr{let x ← game3 S A c0 c1}[x = true]).toReal = 1 / 2 := probTrue_game3 S A c0 c1
  calc |(Pr{let x ← gameReal S A c0 c1}[x = true]).toReal - 1 / 2|
      = |(Pr{let x ← gameReal S A c0 c1}[x = true]).toReal - (Pr{let x ← game3 S A c0 c1}[x = true]).toReal| := by
        rw [e4]
    _ ≤ |(Pr{let x ← gameReal S A c0 c1}[x = true]).toReal - (Pr{let x ← game2 S A c0 c1}[x = true]).toReal| +
          |(Pr{let x ← game2 S A c0 c1}[x = true]).toReal - (Pr{let x ← game3 S A c0 c1}[x = true]).toReal| :=
        abs_sub_le _ _ _
    _ ≤ |(Pr{let x ← gameReal S A c0 c1}[x = true]).toReal - (Pr{let x ← game2 S A c0 c1}[x = true]).toReal| +
          (|(Pr{let x ← game2 S A c0 c1}[x = true]).toReal - (Pr{let x ← game2' S A c0 c1}[x = true]).toReal| +
           |(Pr{let x ← game2' S A c0 c1}[x = true]).toReal - (Pr{let x ← game3 S A c0 c1}[x = true]).toReal|) := by
        gcongr
        exact abs_sub_le _ _ _
    _ = |(Pr{let x ← ddhRealExperiment S.g (ddhAdversaryOf S A c0 c1)}[x = true]).toReal -
          (Pr{let x ← ddhRandomExperiment S.g (ddhAdversaryOf S A c0 c1)}[x = true]).toReal| +
        (|(Pr{let x ← game2 S A c0 c1}[x = true]).toReal - (Pr{let x ← game2' S A c0 c1}[x = true]).toReal| +
         |(Pr{let x ← game2' S A c0 c1}[x = true]).toReal - (Pr{let x ← game3 S A c0 c1}[x = true]).toReal|) := by
        congr 1
        rw [e1, e2]
    _ ≤ εDDH + (εJoint + εPRG) := add_le_add hddh (add_le_add hjointPRG hprg)
    _ = εDDH + εJoint + εPRG := by ring

/-- The statement of `advantage_le`. -/
abbrev AdvantageLeType :=
  ∀ (A : Adversary (G := G) (Beta := Beta) (Gamma := Gamma) (Delta := Delta))
    (c0 c1 : Choice Beta Delta) (εDDH εJoint εPRG : ℝ),
    |(Pr{let x ← ddhRealExperiment S.g (ddhAdversaryOf S A c0 c1)}[x = true]).toReal -
      (Pr{let x ← ddhRandomExperiment S.g (ddhAdversaryOf S A c0 c1)}[x = true]).toReal| ≤ εDDH →
    |(Pr{let x ← game2 S A c0 c1}[x = true]).toReal - (Pr{let x ← game2' S A c0 c1}[x = true]).toReal| ≤ εJoint →
    |(Pr{let x ← game2' S A c0 c1}[x = true]).toReal - (Pr{let x ← game3 S A c0 c1}[x = true]).toReal| ≤ εPRG →
    advantage S A c0 c1 ≤ εDDH + εJoint + εPRG

end MainTheorem

end Cryptlib.Protocols.Sphinx.Indistinguishability
