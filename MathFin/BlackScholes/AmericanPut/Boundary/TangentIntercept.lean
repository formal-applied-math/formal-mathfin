/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Init
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Bound
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic

/-!
# Selecting a negative-intercept concave tangent

This formalizes the calculus reduction in Step 1, conditional on the stated
near-expiry ratio limit. The limit itself is not assumed in the pricing model
and remains to be derived from the actual American/European value comparison.

## Main definitions

* `tangentIntercept`: the value at `0` of the tangent to `b` at `t`, `b t − t · deriv b t`.

## Main results

* `tangentIntercept_hasDeriv`: for `b` smooth on `(0, ∞)` and `0 < t`, the tangent intercept
  `tangentIntercept b` has derivative `-t * b''(t)` at `t`.
* `boundaryRatio_hasDeriv`: under the same hypotheses, `s ↦ b s / s` has derivative
  `-tangentIntercept b t / t ^ 2` at `t`.
* `negative_stays_negative_of_deriv_nonpos`: if `D` is differentiable on `(0, ∞)` and
  `deriv D t ≤ 0` wherever `D t < 0`, then `D a < 0` with `0 < a ≤ T` gives `D T < 0`.
* `exists_negative_intercept_before`: if `b` is smooth on `(0, ∞)` and `b t / t → -∞` as
  `t → 0+`, every `T > 0` has some `s ∈ (0, T)` with negative tangent intercept.
* `curvature_nonneg_of_negative_intercepts`: under the same two hypotheses, if `b'' ≥ 0` at every
  `t > 0` whose tangent intercept is negative, then `b'' ≥ 0` at every `t > 0`.

## Tags

tangent intercept, negative intercept, boundary ratio, concave boundary, MSC 35R35, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

/-- Value at `0` of the tangent to `b` at `t`: `b t - t * deriv b t`. -/
noncomputable def tangentIntercept (b : ℝ → ℝ) (t : ℝ) : ℝ := b t - t * deriv b t

theorem tangentIntercept_hasDeriv {b : ℝ → ℝ} (hb : ContDiffOn ℝ ∞ b (Ioi 0))
    {t : ℝ} (ht : 0 < t) : HasDerivAt (tangentIntercept b) (-t * deriv (deriv b) t) t := by
  have hs : ContDiffAt ℝ 2 b t :=
    (hb.contDiffAt (Ioi_mem_nhds ht)).of_le (WithTop.coe_le_coe.mpr le_top)
  have h₁ := (hs.differentiableAt (by norm_num)).hasDerivAt
  have h₂ := ((hs.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  convert! h₁.sub ((hasDerivAt_id t).mul h₂) using 1
  simp only [id_eq]
  ring

theorem boundaryRatio_hasDeriv {b : ℝ → ℝ} (hb : ContDiffOn ℝ ∞ b (Ioi 0))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => b s / s) (-tangentIntercept b t / t ^ 2) t := by
  have hs := (hb.contDiffAt (Ioi_mem_nhds ht)).differentiableAt (by simp)
  convert! hs.hasDerivAt.div (hasDerivAt_id t) ht.ne' using 1
  dsimp [tangentIntercept]
  ring

/-- If a differentiable function cannot increase while negative, a negative
value persists forward. Multiplication by `exp(t)` permits the strict scalar
fencing theorem to be used at a fixed negative barrier. -/
theorem negative_stays_negative_of_deriv_nonpos {D : ℝ → ℝ}
    (hD : ∀ t, 0 < t → DifferentiableAt ℝ D t)
    (hd : ∀ t, 0 < t → D t < 0 → deriv D t ≤ 0)
    {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) (hDa : D a < 0) : D T < 0 := by
  let W := fun t => Real.exp t * D t
  have hW (t : ℝ) (ht : 0 < t) : HasDerivAt W (Real.exp t * (D t + deriv D t)) t := by
    convert! (Real.hasDerivAt_exp t).mul (hD t ht).hasDerivAt using 1
    ring
  have hWa : W a < 0 := mul_neg_of_pos_of_neg (Real.exp_pos _) hDa
  have hf : ContinuousOn W (Icc a T) := fun t ht =>
    (hW t (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have hbound : W T ≤ W a := image_le_of_deriv_right_lt_deriv_boundary (B := fun _ => W a) hf
    (fun t ht => (hW t (ha.trans_le ht.1)).hasDerivWithinAt) le_rfl
    (fun t => hasDerivAt_const t (W a)) (by
      intro t ht heq
      have ht0 := ha.trans_le ht.1
      have hDt : D t < 0 := by
        by_contra hn
        have hnonneg : 0 ≤ W t := mul_nonneg (Real.exp_pos t).le (le_of_not_gt hn)
        have := heq.trans_lt hWa
        linarith
      exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith [hd t ht0 hDt]))
    ⟨haT,le_rfl⟩
  by_contra hn
  have hnonneg : 0 ≤ W T := mul_nonneg (Real.exp_pos T).le (le_of_not_gt hn)
  linarith

/-- The near-expiry ratio limit produces a negative tangent intercept before
every positive time, by the ordinary mean value theorem. -/
theorem exists_negative_intercept_before {b : ℝ → ℝ}
    (hb : ContDiffOn ℝ ∞ b (Ioi 0))
    (hlim : Tendsto (fun t => b t / t) (𝓝[>] 0) atBot) {T : ℝ} (hT : 0 < T) :
    ∃ s, 0 < s ∧ s < T ∧ tangentIntercept b s < 0 := by
  have hsmall : ∀ᶠ s in 𝓝[>] 0, b s / s < b T / T :=
    hlim.eventually (eventually_lt_atBot (b T / T))
  have hpositive : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hless : ∀ᶠ s : ℝ in 𝓝[>] 0, s < T := nhdsWithin_le_nhds (Iio_mem_nhds hT)
  obtain ⟨a,ha0,haT,haR⟩ := (hpositive.and (hless.and hsmall)).exists
  have hd (s : ℝ) (hs : 0 < s) := (boundaryRatio_hasDeriv hb hs).differentiableAt
  have hc : ContinuousOn (fun s => b s / s) (Icc a T) := fun s hs =>
    (hd s (ha0.trans_le hs.1)).continuousAt.continuousWithinAt
  obtain ⟨s,hs,heq⟩ := exists_deriv_eq_slope (fun s => b s / s) haT hc
    (fun s hs => (hd s (ha0.trans hs.1)).differentiableWithinAt)
  have hpos : 0 < deriv (fun s => b s / s) s := by
    rw [heq]
    exact div_pos (sub_pos.mpr haR) (sub_pos.mpr haT)
  rw [(boundaryRatio_hasDeriv hb (ha0.trans hs.1)).deriv] at hpos
  have hnum : 0 < -tangentIntercept b s :=
    (div_pos_iff_of_pos_right (sq_pos_of_pos (ha0.trans hs.1))).mp hpos
  exact ⟨s,ha0.trans hs.1,hs.2,by linarith⟩

/-- To establish global nonnegative curvature, it suffices to establish it
at negative-intercept tangents. This is Step 1's reduction, not a curvature
assumption on the pricing solution. -/
theorem curvature_nonneg_of_negative_intercepts {b : ℝ → ℝ}
    (hb : ContDiffOn ℝ ∞ b (Ioi 0))
    (hlim : Tendsto (fun t => b t / t) (𝓝[>] 0) atBot)
    (hcurv : ∀ t, 0 < t → tangentIntercept b t < 0 → 0 ≤ deriv (deriv b) t) :
    ∀ T, 0 < T → 0 ≤ deriv (deriv b) T := by
  intro T hT
  obtain ⟨s,hs,hsT,hsd⟩ := exists_negative_intercept_before hb hlim hT
  have hneg : tangentIntercept b T < 0 := negative_stays_negative_of_deriv_nonpos
    (fun t ht => (tangentIntercept_hasDeriv hb ht).differentiableAt)
    (fun t ht hd => by
      rw [(tangentIntercept_hasDeriv hb ht).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) (hcurv t ht hd))
    hs hsT.le hsd
  exact hcurv T hT hneg

end MathFin.BlackScholes.AmericanPut.Boundary
