/-
SPDX-FileCopyrightText: © 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/
import Cryptlib.Primitives.NIKE.X25519
import Cryptlib.Primitives.NIKE.X25519_montgomery_ladder
import Cryptlib.Primitives.NIKE.NIKE

/-! # The Montgomery ladder computes scalar multiplication

`montgomery_ladder` works on projective x-coordinates `(X : Z)`. `Rep X Z R` says `(X : Z)` is the
x-coordinate of the point `R`, with `(X : 0)`, `X ≠ 0`, standing for infinity. Doubling and
differential addition preserve `Rep`, so the ladder keeps `n•P` and `(n+1)•P` for the scalar's
leading bits `n`, and `scalarmult n (xCoord P) = xCoord (n • P)` for every curve point `P`. -/

namespace Cryptlib.Primitives.NIKE.X25519_montgomery_ladder

open Cryptlib.Primitives.NIKE.X25519Common
open Cryptlib.Primitives.NIKE.X25519 (Point curve onCurve xCoord nonsingular_iff_onCurve)
open WeierstrassCurve.Affine

lemma two_ne_zero' : (2 : ZMod p) ≠ 0 := by decide
lemma four_ne_zero' : (4 : ZMod p) ≠ 0 := by decide
lemma A_add_two_ne_zero : (486664 : ZMod p) ≠ 0 := by decide
lemma A_sub_two_ne_zero : (486660 : ZMod p) ≠ 0 := by decide

/-- `(X : Z)` is the x-coordinate of `R`; infinity is `(X : 0)` with `X ≠ 0`. -/
def Rep (X Z : ZMod p) : Point → Prop
  | .zero => Z = 0 ∧ X ≠ 0
  | .some x _ _ => Z ≠ 0 ∧ X = x * Z

lemma Rep.xCoord {X Z : ZMod p} {R : Point} (h : Rep X Z R) : X * Z⁻¹ = xCoord R := by
  cases R with
  | zero => simp [Rep] at h; simp [h.1, X25519.xCoord]
  | some x y _ =>
    obtain ⟨hz, hx⟩ := h
    simp [X25519.xCoord, hx, mul_assoc, mul_inv_cancel₀ hz]

lemma curve_negY (x y : ZMod p) : curve.negY x y = -y := by simp [WeierstrassCurve.Affine.negY, curve]

lemma eq_zero_of_eq_neg {y : ZMod p} (e : y = -y) : y = 0 :=
  (mul_eq_zero.mp (show 2 * y = 0 by linear_combination e)).resolve_left two_ne_zero'

/-- `x(2Q) · 4y² = (x² - 1)²` for a point `Q = (x, y)` with `y ≠ 0`. -/
lemma double_x {x y : ZMod p} (h : onCurve x y) (hy : y ≠ 0) :
    curve.addX x x (curve.slope x x y y) * (4 * y ^ 2) = (x ^ 2 - 1) ^ 2 := by
  have hy' : y ≠ curve.negY x y := by
    rw [curve_negY]; intro e; exact hy (eq_zero_of_eq_neg e)
  have h2y : y - -y ≠ 0 := by
    rw [sub_neg_eq_add, ← two_mul]; exact mul_ne_zero two_ne_zero' hy
  have hl : curve.slope x x y y * (2 * y) = 3 * x ^ 2 + 2 * 486662 * x + 1 := by
    rw [slope_of_Y_ne rfl hy', curve_negY, show 2 * y = y - -y by ring, div_mul_cancel₀ _ h2y]
    simp [curve]
  simp only [WeierstrassCurve.Affine.addX, show curve.a₁ = 0 from rfl, show curve.a₂ = 486662 from rfl]
  unfold onCurve at h
  linear_combination (curve.slope x x y y * (2 * y) + (3 * x ^ 2 + 2 * 486662 * x + 1)) * hl
    - 4 * (486662 + 2 * x) * h

/-- Doubling preserves `Rep`. -/
lemma Rep.double {X Z : ZMod p} {Q : Point} (h : Rep X Z Q) :
    Rep ((X ^ 2 - Z ^ 2) ^ 2) (4 * X * Z * (X ^ 2 + 486662 * X * Z + Z ^ 2)) (Q + Q) := by
  cases Q with
  | zero =>
    obtain ⟨hz, hx⟩ := h
    refine ⟨by simp [hz], by simp [hz, hx]⟩
  | some x y hq =>
    obtain ⟨hz, hx⟩ := h
    subst hx
    have hc : onCurve x y := nonsingular_iff_onCurve.mp hq
    by_cases hy : y = 0
    · have hyn : y = curve.negY x y := by rw [curve_negY, hy, neg_zero]
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hyn]
      have hx0 : x * (x ^ 2 + 486662 * x + 1) = 0 := by
        unfold onCurve at hc; rw [hy] at hc; linear_combination -hc
      refine ⟨?_, ?_⟩
      · linear_combination (4 * Z ^ 4) * hx0
      · have hx2 : x ^ 2 - 1 ≠ 0 := by
          intro e
          rcases mul_eq_zero.mp hx0 with h0 | h1
          · rw [h0] at e; norm_num at e
          · have : (x - 1) * (x + 1) = 0 := by linear_combination e
            rcases mul_eq_zero.mp this with e1 | e1
            · have : x = 1 := by linear_combination e1
              rw [this] at h1; norm_num at h1; exact A_add_two_ne_zero (by linear_combination h1)
            · have : x = -1 := by linear_combination e1
              rw [this] at h1; norm_num at h1; exact A_sub_two_ne_zero (by linear_combination h1)
        have : (x * Z) ^ 2 - Z ^ 2 = Z ^ 2 * (x ^ 2 - 1) := by ring
        rw [this]
        exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hz) hx2)
    · have hyn : y ≠ curve.negY x y := by
        rw [curve_negY]; intro e; exact hy (eq_zero_of_eq_neg e)
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyn]
      have hd := double_x hc hy
      unfold onCurve at hc
      refine ⟨?_, ?_⟩
      · have : 4 * (x * Z) * Z * ((x * Z) ^ 2 + 486662 * (x * Z) * Z + Z ^ 2) = 4 * Z ^ 4 * y ^ 2 := by
          linear_combination (-4 * Z ^ 4) * hc
        rw [this]
        exact mul_ne_zero (mul_ne_zero four_ne_zero' (pow_ne_zero _ hz)) (pow_ne_zero _ hy)
      · linear_combination (-Z ^ 4) * hd + (4 * Z ^ 4 * curve.addX x x (curve.slope x x y y)) * hc

/-- Montgomery's identity: `x(Q+R) · x(Q-R) · (x_R - x_Q)² = (x_Q x_R - 1)²`, with `a` and `b` the
chord formulas for `x(Q+R)` and `x(R-Q)`. -/
lemma diff_add_x {xq yq xr yr l m : ZMod p} (hq : onCurve xq yq) (hr : onCurve xr yr) (hx : xq ≠ xr)
    (hl : l * (xq - xr) = yq - yr) (hm : m * (xr - xq) = yr + yq) :
    (l ^ 2 - 486662 - xq - xr) * (m ^ 2 - 486662 - xr - xq) * (xr - xq) ^ 2 = (xq * xr - 1) ^ 2 := by
  have hs : xr - xq ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  unfold onCurve at hq hr
  apply mul_right_cancel₀ (pow_ne_zero 2 hs)
  have ha : (l ^ 2 - 486662 - xq - xr) * (xr - xq) ^ 2 =
      (yq - yr) ^ 2 - (486662 + xq + xr) * (xr - xq) ^ 2 := by
    linear_combination (l * (xq - xr) + (yq - yr)) * hl
  have hb : (m ^ 2 - 486662 - xr - xq) * (xr - xq) ^ 2 =
      (yr + yq) ^ 2 - (486662 + xq + xr) * (xr - xq) ^ 2 := by
    linear_combination (m * (xr - xq) + (yr + yq)) * hm
  have e : (l ^ 2 - 486662 - xq - xr) * (m ^ 2 - 486662 - xr - xq) * (xr - xq) ^ 2 * (xr - xq) ^ 2 =
      ((yq - yr) ^ 2 - (486662 + xq + xr) * (xr - xq) ^ 2) *
        ((yr + yq) ^ 2 - (486662 + xq + xr) * (xr - xq) ^ 2) := by
    rw [← ha, ← hb]; ring
  rw [e]
  linear_combination
    (yq ^ 2 - yr ^ 2 + (xq ^ 3 + 486662 * xq ^ 2 + xq) - (xr ^ 3 + 486662 * xr ^ 2 + xr)
      - 2 * (486662 + xq + xr) * (xr - xq) ^ 2) * hq
    + (-(yq ^ 2 - yr ^ 2 + (xq ^ 3 + 486662 * xq ^ 2 + xq) - (xr ^ 3 + 486662 * xr ^ 2 + xr))
      - 2 * (486662 + xq + xr) * (xr - xq) ^ 2) * hr

open WeierstrassCurve.Affine.Point in
/-- Differential addition preserves `Rep`: from `Q` and `R = Q + P`, where `x(P) = x₁ ≠ 0`, it
gives `Q + R`. -/
lemma Rep.addDiff' {X2 Z2 X3 Z3 x1 y1 : ZMod p} {hP : curve.Nonsingular x1 y1} (hx1 : x1 ≠ 0)
    {Q R : Point} (hQ : Rep X2 Z2 Q) (hR : Rep X3 Z3 R) (hd : R = Q + .some x1 y1 hP) :
    Rep (4 * (X2 * X3 - Z2 * Z3) ^ 2) (4 * x1 * (X3 * Z2 - Z3 * X2) ^ 2) (Q + R) := by
  cases Q with
  | zero =>
    change R = 0 + _ at hd
    change Rep _ _ (0 + R)
    rw [zero_add] at hd ⊢
    subst hd
    obtain ⟨hz2, hx2⟩ := hQ
    obtain ⟨hz3, hx3⟩ := hR
    subst hz2 hx3
    refine ⟨?_, by ring⟩
    have : 4 * x1 * (x1 * Z3 * 0 - Z3 * X2) ^ 2 = 4 * x1 * (Z3 * X2) ^ 2 := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero four_ne_zero' hx1) (pow_ne_zero _ (mul_ne_zero hz3 hx2))
  | some xq yq hq =>
    obtain ⟨hz2, hx2⟩ := hQ
    subst hx2
    cases R with
    | zero =>
      change (0 : Point) = _ at hd
      change Rep _ _ (_ + 0)
      rw [add_zero]
      obtain ⟨hz3, hx3⟩ := hR
      subst hz3
      have hneg : some xq yq hq = -some x1 y1 hP := eq_neg_of_add_eq_zero_left hd.symm
      rw [neg_some, some.injEq] at hneg
      obtain ⟨rfl, -⟩ := hneg
      refine ⟨?_, by ring⟩
      have : 4 * xq * (X3 * Z2 - 0 * (xq * Z2)) ^ 2 = 4 * xq * (X3 * Z2) ^ 2 := by ring
      rw [this]
      exact mul_ne_zero (mul_ne_zero four_ne_zero' hx1) (pow_ne_zero _ (mul_ne_zero hx3 hz2))
    | some xr yr hr =>
      obtain ⟨hz3, hx3⟩ := hR
      subst hx3
      have hqc := nonsingular_iff_onCurve.mp hq
      have hrc := nonsingular_iff_onCurve.mp hr
      by_cases hx : xq = xr
      · subst hx
        rcases (X_eq_iff (h₁ := hq) (h₂ := hr)).mp rfl with he | he
        · rw [← he, left_eq_add] at hd
          exact absurd hd (by simp)
        · rw [he, neg_add_cancel]
          refine ⟨by ring, ?_⟩
          -- P = R + R, so x(2R) = x₁ ≠ 0 and x_R² ≠ 1.
          have hP2 : some xq yr hr + some xq yr hr = some x1 y1 hP := by
            have h1 : some x1 y1 hP = some xq yr hr - some xq yq hq := by rw [hd]; abel
            rw [h1, he, sub_neg_eq_add]
          have hyr : yr ≠ curve.negY xq yr := by
            intro hy
            rw [add_self_of_Y_eq hy] at hP2
            exact absurd hP2 (by simp)
          rw [add_self_of_Y_ne hyr, some.injEq] at hP2
          have hyr0 : yr ≠ 0 := fun h => hyr (by rw [curve_negY, h, _root_.neg_zero])
          have hdbl := double_x hrc hyr0
          rw [hP2.1] at hdbl
          have hsq : xq ^ 2 - 1 ≠ 0 := by
            intro e
            rw [e] at hdbl
            have : x1 * (4 * yr ^ 2) ≠ 0 :=
              mul_ne_zero hx1 (mul_ne_zero four_ne_zero' (pow_ne_zero _ hyr0))
            exact this (by rw [hdbl]; ring)
          have : 4 * (xq * Z2 * (xq * Z3) - Z2 * Z3) ^ 2 = 4 * (Z2 * Z3 * (xq ^ 2 - 1)) ^ 2 := by ring
          rw [this]
          exact mul_ne_zero four_ne_zero'
            (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hz2 hz3) hsq))
      · -- P = R - Q, both chords are defined
        have hP' : some xr yr hr + -some xq yq hq = some x1 y1 hP := by rw [hd]; abel
        rw [neg_some, add_of_X_ne (Ne.symm hx), some.injEq] at hP'
        rw [add_of_X_ne hx]
        have hs : xr - xq ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
        have hl : curve.slope xq xr yq yr * (xq - xr) = yq - yr := by
          rw [slope_of_X_ne hx, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]
        have hm : curve.slope xr xq yr (curve.negY xq yq) * (xr - xq) = yr + yq := by
          rw [slope_of_X_ne (Ne.symm hx), div_mul_cancel₀ _ hs, curve_negY]; ring
        have key := diff_add_x hqc hrc hx hl hm
        have ha : curve.addX xq xr (curve.slope xq xr yq yr) =
            curve.slope xq xr yq yr ^ 2 - 486662 - xq - xr := by
          simp only [WeierstrassCurve.Affine.addX, show curve.a₁ = 0 from rfl,
            show curve.a₂ = 486662 from rfl]; ring
        have hb : x1 = curve.slope xr xq yr (curve.negY xq yq) ^ 2 - 486662 - xr - xq := by
          rw [← hP'.1]
          simp only [WeierstrassCurve.Affine.addX, show curve.a₁ = 0 from rfl,
            show curve.a₂ = 486662 from rfl]; ring
        rw [← ha, ← hb] at key
        refine ⟨?_, ?_⟩
        · have : 4 * x1 * (xr * Z3 * Z2 - Z3 * (xq * Z2)) ^ 2 = 4 * x1 * (Z2 * Z3 * (xr - xq)) ^ 2 := by
            ring
          rw [this]
          exact mul_ne_zero (mul_ne_zero four_ne_zero' hx1)
            (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hz2 hz3) hs))
        · linear_combination (-4 * Z2 ^ 2 * Z3 ^ 2) * key

/-- `Rep.addDiff'` with either of `Q`, `R` the other plus `P`. -/
lemma Rep.addDiff {X2 Z2 X3 Z3 x1 y1 : ZMod p} {hP : curve.Nonsingular x1 y1} (hx1 : x1 ≠ 0)
    {Q R : Point} (hQ : Rep X2 Z2 Q) (hR : Rep X3 Z3 R)
    (hd : R = Q + .some x1 y1 hP ∨ Q = R + .some x1 y1 hP) :
    Rep (4 * (X2 * X3 - Z2 * Z3) ^ 2) (4 * x1 * (X3 * Z2 - Z3 * X2) ^ 2) (Q + R) := by
  rcases hd with hd | hd
  · exact Rep.addDiff' hx1 hQ hR hd
  · have h := Rep.addDiff' hx1 hR hQ hd
    rw [add_comm R Q] at h
    convert h using 1 <;> ring

/-! ## The loop -/

lemma step_eq (s : LadderState) : montgomery_step s =
    { x1 := s.x1, x2 := (s.x2 ^ 2 - s.z2 ^ 2) ^ 2,
      z2 := 4 * s.x2 * s.z2 * (s.x2 ^ 2 + 486662 * s.x2 * s.z2 + s.z2 ^ 2),
      x3 := 4 * (s.x2 * s.x3 - s.z2 * s.z3) ^ 2, z3 := 4 * s.x1 * (s.x3 * s.z2 - s.z3 * s.x2) ^ 2 } := by
  simp only [montgomery_step, LadderState.mk.injEq]
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩ <;> ring

/-- One iteration of `montgomery_ladder`'s loop: the swap flag and the state. -/
def body (e : Vector UInt8 keySize) (b : LadderState × Bool) (a : ℕ) : LadderState × Bool :=
  (montgomery_step
      { x1 := b.1.x1, x2 := (cswap (b.2 != (e[a / 8]!.toNat >>> (a % 8) &&& 1 == 1)) b.1.x2 b.1.x3).1,
        z2 := (cswap (b.2 != (e[a / 8]!.toNat >>> (a % 8) &&& 1 == 1)) b.1.z2 b.1.z3).1,
        x3 := (cswap (b.2 != (e[a / 8]!.toNat >>> (a % 8) &&& 1 == 1)) b.1.x2 b.1.x3).2,
        z3 := (cswap (b.2 != (e[a / 8]!.toNat >>> (a % 8) &&& 1 == 1)) b.1.z2 b.1.z3).2 },
    e[a / 8]!.toNat >>> (a % 8) &&& 1 == 1)

/-- The state after the final swap. -/
def finish (s : LadderState × Bool) : LadderState :=
  { x1 := s.1.x1, x2 := (cswap s.2 s.1.x2 s.1.x3).1, z2 := (cswap s.2 s.1.z2 s.1.z3).1,
    x3 := (cswap s.2 s.1.x2 s.1.x3).2, z3 := (cswap s.2 s.1.z2 s.1.z3).2 }

lemma ladder_eq (e : Vector UInt8 keySize) (x : ZMod p) :
    montgomery_ladder e x = finish ((List.range 255).reverse.foldl (body e)
      ({ x1 := x, x2 := 1, z2 := 0, x3 := x, z3 := 1 }, false)) := by
  unfold montgomery_ladder
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind]
  generalize (List.range 255).reverse = l
  rfl

/-! ## Scalar bits -/

/-- The scalar a byte vector encodes, little-endian. -/
def scalarNat (e : Vector UInt8 keySize) : ℕ := Nat.ofDigits 256 (e.toList.map UInt8.toNat)

lemma shift_and_one (x a : ℕ) : (x >>> a &&& 1 == 1) = x.testBit a := by
  rw [Nat.testBit, Nat.and_comm, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (x >>> a) with h | h <;> simp [h]

lemma bit_list (L : List UInt8) (a : ℕ) (ha : a < 8 * L.length) :
    ((L[a / 8]!).toNat >>> (a % 8) &&& 1 == 1) =
      (Nat.ofDigits 256 (L.map UInt8.toNat)).testBit a := by
  induction L generalizing a with
  | nil => simp at ha
  | cons d L ih =>
    rw [List.map_cons, Nat.ofDigits_cons, show (256 : ℕ) = 2 ^ 8 by rfl, add_comm,
      Nat.testBit_two_pow_mul_add _ d.toNat_lt]
    by_cases h8 : a < 8
    · simp only [h8, ↓reduceIte]
      rw [Nat.div_eq_of_lt h8, Nat.mod_eq_of_lt h8, List.getElem!_cons_zero]
      exact shift_and_one _ _
    · simp only [h8, ↓reduceIte]
      have h1 : a / 8 = (a - 8) / 8 + 1 := by omega
      have h2 : a % 8 = (a - 8) % 8 := by omega
      rw [h1, h2, List.getElem!_cons_succ]
      exact ih (a - 8) (by simp at ha; omega)

lemma bit_vec (e : Vector UInt8 keySize) (a : ℕ) (ha : a < 256) :
    (e[a / 8]!.toNat >>> (a % 8) &&& 1 == 1) = (scalarNat e).testBit a := by
  rw [scalarNat, ← bit_list e.toList a (by simp; omega)]
  have : a / 8 < 32 := by omega
  simp [getElem!_pos, this]

lemma shift_succ (n k : ℕ) : n >>> k = 2 * (n >>> (k + 1)) + (if n.testBit k then 1 else 0) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq, pow_succ,
    ← Nat.div_div_eq_div_mul]
  generalize n / 2 ^ k = x
  split <;> rename_i h <;> simp at h <;> omega

/-! ## The invariant -/

section pairs
variable {x1 y1 : ZMod p} {hP : curve.Nonsingular x1 y1} {X2 Z2 X3 Z3 : ZMod p} {m : ℕ}

/-- A step on `(m•P, (m+1)•P)` gives `(2m•P, (2m+1)•P)`. -/
lemma pair_even (hx1 : x1 ≠ 0) (hU : Rep X2 Z2 (m • .some x1 y1 hP))
    (hV : Rep X3 Z3 ((m + 1) • .some x1 y1 hP)) :
    Rep ((X2 ^ 2 - Z2 ^ 2) ^ 2) (4 * X2 * Z2 * (X2 ^ 2 + 486662 * X2 * Z2 + Z2 ^ 2))
        ((2 * m) • .some x1 y1 hP) ∧
      Rep (4 * (X2 * X3 - Z2 * Z3) ^ 2) (4 * x1 * (X3 * Z2 - Z3 * X2) ^ 2)
        ((2 * m + 1) • .some x1 y1 hP) := by
  refine ⟨?_, ?_⟩
  · have := hU.double
    rwa [← add_nsmul, ← two_mul] at this
  · have := Rep.addDiff hx1 hU hV (Or.inl (succ_nsmul _ _))
    rwa [← add_nsmul, show m + (m + 1) = 2 * m + 1 by ring] at this

/-- A step on `((m+1)•P, m•P)` gives `((2m+2)•P, (2m+1)•P)`. -/
lemma pair_odd (hx1 : x1 ≠ 0) (hU : Rep X2 Z2 ((m + 1) • .some x1 y1 hP))
    (hV : Rep X3 Z3 (m • .some x1 y1 hP)) :
    Rep (4 * (X2 * X3 - Z2 * Z3) ^ 2) (4 * x1 * (X3 * Z2 - Z3 * X2) ^ 2)
        ((2 * m + 1) • .some x1 y1 hP) ∧
      Rep ((X2 ^ 2 - Z2 ^ 2) ^ 2) (4 * X2 * Z2 * (X2 ^ 2 + 486662 * X2 * Z2 + Z2 ^ 2))
        ((2 * m + 1 + 1) • .some x1 y1 hP) := by
  refine ⟨?_, ?_⟩
  · have := Rep.addDiff hx1 hU hV (Or.inr (succ_nsmul _ _))
    rwa [← add_nsmul, show m + 1 + m = 2 * m + 1 by ring] at this
  · have := hU.double
    rwa [← add_nsmul, show m + 1 + (m + 1) = 2 * m + 1 + 1 by ring] at this

end pairs

/-- After the bits of `n` above `k`: the state holds `(n >>> k) • P` and `(n >>> k + 1) • P`,
swapped when the flag, bit `k`, is set. -/
def Inv (P : Point) (n k : ℕ) (acc : LadderState × Bool) : Prop :=
  acc.1.x1 = xCoord P ∧ acc.2 = n.testBit k ∧
  if acc.2 then Rep acc.1.x3 acc.1.z3 ((n >>> k) • P) ∧ Rep acc.1.x2 acc.1.z2 ((n >>> k + 1) • P)
  else Rep acc.1.x2 acc.1.z2 ((n >>> k) • P) ∧ Rep acc.1.x3 acc.1.z3 ((n >>> k + 1) • P)

lemma inv_step {P : Point} (hx : xCoord P ≠ 0) (e : Vector UInt8 keySize) {k : ℕ} (hk : k < 255)
    {acc : LadderState × Bool} (h : Inv P (scalarNat e) (k + 1) acc) :
    Inv P (scalarNat e) k (body e acc k) := by
  obtain ⟨h1, hsw, hr⟩ := h
  have hb := bit_vec e k (by omega)
  have hm := shift_succ (scalarNat e) k
  cases P with
  | zero => exact absurd rfl hx
  | some x1 y1 hP =>
    unfold body
    rw [hb, step_eq]
    obtain ⟨st, sw⟩ := acc
    simp only at h1 hsw hr
    subst hsw
    generalize scalarNat e >>> (k + 1) = m at hm hr
    refine ⟨h1, rfl, ?_⟩
    have hx1 : x1 ≠ 0 := hx
    rw [show st.x1 = x1 from h1]
    cases hbit : (scalarNat e).testBit k <;> cases hs : (scalarNat e).testBit (k + 1) <;>
      simp only [hbit, hs, cswap, hm, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false,
        Bool.bne_true, Bool.bne_false, Bool.not_false, add_zero] at hr ⊢
    · exact pair_even hx1 hr.1 hr.2
    · exact pair_even hx1 hr.1 hr.2
    · exact pair_odd hx1 hr.2 hr.1
    · exact pair_odd hx1 hr.2 hr.1

lemma inv_fold {P : Point} (hx : xCoord P ≠ 0) (e : Vector UInt8 keySize) :
    ∀ j ≤ 255, ∀ acc, Inv P (scalarNat e) j acc →
      Inv P (scalarNat e) 0 ((List.range j).reverse.foldl (body e) acc) := by
  intro j
  induction j with
  | zero => intro _ acc h; simpa using h
  | succ j ih =>
    intro hj acc h
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    exact ih (by omega) _ (inv_step hx e (by omega) h)

lemma inv_init {P : Point} (hx : xCoord P ≠ 0) {n : ℕ} (hn : n < 2 ^ 255) :
    Inv P n 255 ({ x1 := xCoord P, x2 := 1, z2 := 0, x3 := xCoord P, z3 := 1 }, false) := by
  have h0 : n >>> 255 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hn
  refine ⟨rfl, (Nat.testBit_lt_two_pow hn).symm, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte, h0, zero_nsmul, zero_add, one_nsmul]
  refine ⟨⟨rfl, one_ne_zero⟩, ?_⟩
  cases P with
  | zero => exact absurd rfl hx
  | some x y _ => exact ⟨one_ne_zero, (mul_one x).symm⟩

lemma inv_finish {P : Point} {n : ℕ} {acc : LadderState × Bool} (h : Inv P n 0 acc) :
    Rep (finish acc).x2 (finish acc).z2 (n • P) := by
  obtain ⟨_, _, hr⟩ := h
  rw [Nat.shiftRight_zero] at hr
  obtain ⟨st, sw⟩ := acc
  cases sw <;> simp only [finish, cswap, Bool.false_eq_true, ↓reduceIte] at hr ⊢
  · exact hr.1
  · exact hr.1

/-! ## `x(P) = 0` -/

/-- With `x₁ = 0` every pair has `X = 0` or `Z = 0`, so the ladder outputs `0`. -/
def Inv0 (acc : LadderState × Bool) : Prop :=
  acc.1.x1 = 0 ∧ acc.1.x2 * acc.1.z2 = 0 ∧ acc.1.x3 * acc.1.z3 = 0

lemma inv0_step (e : Vector UInt8 keySize) (a : ℕ) {acc : LadderState × Bool} (h : Inv0 acc) :
    Inv0 (body e acc a) := by
  obtain ⟨st, sw⟩ := acc
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3
  unfold body Inv0
  rw [step_eq]
  simp only [cswap]
  refine ⟨h1, ?_, ?_⟩ <;> split
  · linear_combination (4 * (st.x3 ^ 2 - st.z3 ^ 2) ^ 2 *
      (st.x3 ^ 2 + 486662 * st.x3 * st.z3 + st.z3 ^ 2)) * h3
  · linear_combination (4 * (st.x2 ^ 2 - st.z2 ^ 2) ^ 2 *
      (st.x2 ^ 2 + 486662 * st.x2 * st.z2 + st.z2 ^ 2)) * h2
  · simp [h1]
  · simp [h1]

lemma inv0_fold (e : Vector UInt8 keySize) :
    ∀ (l : List ℕ) acc, Inv0 acc → Inv0 (l.foldl (body e) acc) := by
  intro l
  induction l with
  | nil => intro _ h; exact h
  | cons a l ih => intro acc h; exact ih _ (inv0_step e a h)

lemma mul_inv_eq_zero {a b : ZMod p} (h : a * b = 0) : a * b⁻¹ = 0 := by
  rcases mul_eq_zero.mp h with h | h <;> simp [h]

lemma xCoord_smul_of_xCoord_zero {P : Point} (h : xCoord P = 0) (n : ℕ) : xCoord (n • P) = 0 := by
  cases P with
  | zero => change xCoord (n • (0 : Point)) = 0; rw [X25519.nsmul_zero_point]; rfl
  | some x y hP =>
    have : x = 0 := h
    subst this
    exact X25519.xCoord_smul_zero hP n

/-! ## The ladder computes `x(n•P)` -/

theorem ladder_correct (e : Vector UInt8 keySize) (hn : scalarNat e < 2 ^ 255) (P : Point) :
    (montgomery_ladder e (xCoord P)).x2 * (montgomery_ladder e (xCoord P)).z2⁻¹ =
      xCoord (scalarNat e • P) := by
  rw [ladder_eq]
  by_cases hx : xCoord P = 0
  · rw [xCoord_smul_of_xCoord_zero hx]
    have h := inv0_fold e (List.range 255).reverse _
      (show Inv0 (({ x1 := xCoord P, x2 := 1, z2 := 0, x3 := xCoord P, z3 := 1 } : LadderState), false)
        from ⟨hx, by simp, by simp [hx]⟩)
    generalize (List.range 255).reverse.foldl (body e) _ = acc at h ⊢
    obtain ⟨st, sw⟩ := acc
    obtain ⟨_, h2, h3⟩ := h
    apply mul_inv_eq_zero
    cases sw
    · exact h2
    · exact h3
  · exact (inv_finish (inv_fold hx e 255 le_rfl _ (inv_init hx hn))).xCoord

lemma scalarNat_lt (e : Vector UInt8 keySize) : scalarNat e < 2 ^ 256 := by
  have := Nat.ofDigits_lt_base_pow_length (b := 256) (l := e.toList.map UInt8.toNat) (by norm_num)
    (by simp only [List.mem_map]; rintro _ ⟨d, -, rfl⟩; exact d.toNat_lt)
  rw [scalarNat, show (2 : ℕ) ^ 256 = 256 ^ keySize by norm_num [keySize]]
  simpa using this

/-- Clamping clears bit 255, so the ladder's 255 bits cover the whole scalar. -/
lemma scalarNat_clamp_lt (v : Vector UInt8 keySize) : scalarNat (clampScalar v) < 2 ^ 255 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases h : i = 255
  · subst h
    rw [← bit_vec _ 255 (by norm_num)]
    have hb : ∀ b : UInt8, ((b &&& 0x7f ||| 0x40).toNat >>> 7 &&& 1 == 1) = false := by
      intro b
      have hlt : (b &&& 0x7f ||| 0x40).toNat < 2 ^ 7 := by
        rw [UInt8.toNat_or, UInt8.toNat_and]
        exact Nat.or_lt_two_pow (lt_of_le_of_lt Nat.and_le_right (by decide)) (by decide)
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]; rfl
    simpa [clampScalar] using hb _
  · exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le (scalarNat_lt _) (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem scalarmult_eq (sk : Vector UInt8 keySize) (P : Point) :
    scalarmult sk (xCoord P) = xCoord (scalarNat (clampScalar sk) • P) :=
  ladder_correct _ (scalarNat_clamp_lt sk) P

/-! ## Bytes -/

/-- Masking bit 255, as `toField` does, reduces the scalar modulo `2^255`. -/
lemma scalarNat_mask (v : Vector UInt8 keySize) :
    scalarNat (v.set 31 (v[31] &&& 0x7f)) = scalarNat v % 2 ^ 255 := by
  apply Nat.eq_of_testBit_eq
  intro a
  rw [Nat.testBit_mod_two_pow]
  by_cases ha : a < 256
  · rw [← bit_vec _ a ha, ← bit_vec _ a ha, shift_and_one, shift_and_one]
    by_cases h31 : a / 8 = 31
    · have h31' : (31 : ℕ) < keySize := by decide
      rw [h31, getElem!_pos (v.set 31 (v[31] &&& 0x7f)) 31 h31', getElem!_pos v 31 h31',
        Vector.getElem_set_self,
        UInt8.toNat_and, Nat.testBit_and, show (0x7f : UInt8).toNat = 2 ^ 7 - 1 from rfl,
        Nat.testBit_two_pow_sub_one, Bool.and_comm]
      congr 1
      simp only [decide_eq_decide]
      omega
    · have hlt : a / 8 < keySize := by simp [keySize]; omega
      rw [getElem!_pos (v.set 31 (v[31] &&& 0x7f)) (a / 8) hlt, getElem!_pos v (a / 8) hlt,
        Vector.getElem_set_ne _ _ (by omega)]
      simp only [show a < 255 by omega, decide_true, Bool.true_and]
  · have h1 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (scalarNat_lt (v.set 31 (v[31] &&& 0x7f)))
      (Nat.pow_le_pow_right (by norm_num) (show 256 ≤ a by omega)))
    rw [h1]
    simp [show ¬a < 255 by omega]

lemma p_lt_two_pow : p < 2 ^ 255 := by norm_num [p]

theorem toField_fromField (x : ZMod p) : toField (fromField x) = x := by
  show ((scalarNat ((fromField x).set 31 ((fromField x)[31] &&& 0x7f)) : ℕ) : ZMod p) = x
  rw [scalarNat_mask]
  have h : scalarNat (fromField x) = x.val := by
    simp [scalarNat, fromField, X25519.encodeFieldChecked, X25519.ofDigits_encodeField]
  rw [h, Nat.mod_eq_of_lt (lt_trans (ZMod.val_lt x) p_lt_two_pow), ZMod.natCast_zmod_val]

/-! ## The NIKE

A public key is safe when its u-coordinate is on the curve, as for `X25519.Scheme`; then the
ladder is scalar multiplication on a point, and the group's laws carry over. -/

open Cryptlib.Primitives.NIKE.NIKE
open X25519 (G toPoint SafeX)

def SafeU (pk : PublicKey) : Prop := SafeX (toField pk.data)

instance : DecidablePred SafeU := fun pk => inferInstanceAs (Decidable (SafeX (toField pk.data)))

lemma curve25519_of_xCoord (sk pk : Vector UInt8 keySize) {P : Point} (h : toField pk = xCoord P) :
    curve25519 sk pk = fromField (xCoord (scalarNat (clampScalar sk) • P)) := by
  unfold curve25519
  rw [h, scalarmult_eq]

lemma toField_basepointBytes : toField basepointBytes = xCoord G := by
  rw [basepointBytes, toField_fromField]
  rfl

lemma derivePub_data (sk : PrivateKey) :
    (derivePub sk).data = fromField (xCoord (scalarNat (clampScalar sk.data) • G)) :=
  curve25519_of_xCoord _ _ toField_basepointBytes

lemma safeU_fromField (P : Point) : SafeU ⟨fromField (xCoord P)⟩ := by
  unfold SafeU
  rw [toField_fromField]
  exact X25519.liftX_isSome_of_exists (X25519.exists_onCurve_xCoord P)

lemma toPoint_xCoord (pk : PublicKey) (h : SafeU pk) : toField pk.data = xCoord (toPoint _ h) :=
  (X25519.xCoord_toPoint _ h).symm

/-- RFC 7748 X25519 by the `ZMod p` Montgomery ladder, under the given name. -/
def ladderScheme (name : String) : NIKE where
  PrivateKey   := PrivateKey
  PublicKey    := PublicKey
  SharedSecret := SharedSecret

  name := name
  privateKeySize   := keySize
  publicKeySize    := keySize
  sharedSecretSize := keySize

  Safe    := SafeU
  decSafe := inferInstance

  privateKeyFromSeed := fun seed => ⟨clampScalar seed⟩
  derivePublicKey    := derivePub
  groupAction        := fun sk spk => ⟨curve25519 sk.data spk.1.data⟩

  encodePrivateKey   := fun sk => sk.data
  decodePrivateKey   := fun v => some ⟨v⟩
  encodePublicKey    := fun pk => pk.data
  decodePublicKey    := fun v => some ⟨v⟩
  encodeSharedSecret := fun ss => ss.data

  derive_safe        := fun sk => by
    show SafeX (toField (derivePub sk).data)
    rw [derivePub_data]
    exact safeU_fromField _
  decode_encode_priv := fun _ => rfl
  decodePrivateKey_total := fun v => ⟨⟨v⟩, rfl⟩
  decode_encode_pub  := fun _ => rfl
  encode_decode_pub  := fun _ _ h => congrArg PublicKey.data (Option.some.inj h) ▸ rfl
  commutes           := fun sk₁ sk₂ => congrArg SharedSecret.mk (by
    rw [curve25519_of_xCoord _ _ (P := scalarNat (clampScalar sk₂.data) • G)
        (by rw [derivePub_data, toField_fromField]),
      curve25519_of_xCoord _ _ (P := scalarNat (clampScalar sk₁.data) • G)
        (by rw [derivePub_data, toField_fromField]),
      X25519.dh_commutes])
  reinterpret        := fun ss => ⟨ss.data⟩
  reinterpret_safe   := fun sk spk => by
    show SafeU ⟨curve25519 sk.data spk.1.data⟩
    rw [curve25519_of_xCoord _ _ (toPoint_xCoord spk.1 spk.2)]
    exact safeU_fromField _
  groupAction_comm   := fun sk₁ sk₂ spk => congrArg SharedSecret.mk (by
    show curve25519 sk₁.data (curve25519 sk₂.data spk.1.data) =
      curve25519 sk₂.data (curve25519 sk₁.data spk.1.data)
    rw [curve25519_of_xCoord sk₂.data _ (toPoint_xCoord spk.1 spk.2),
      curve25519_of_xCoord sk₁.data _ (toPoint_xCoord spk.1 spk.2),
      curve25519_of_xCoord sk₁.data _ (toField_fromField _),
      curve25519_of_xCoord sk₂.data _ (toField_fromField _), X25519.dh_commutes])
  publicKeySize_eq_sharedSecretSize := rfl
  encodePublicKey_reinterpret := fun _ => rfl

def LadderScheme : NIKE := ladderScheme "X25519-ladder"

end Cryptlib.Primitives.NIKE.X25519_montgomery_ladder
