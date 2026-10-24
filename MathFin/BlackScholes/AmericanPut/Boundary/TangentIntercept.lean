/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib

/-!
# Selecting a negative-intercept concave tangent

This formalizes the calculus reduction in Step 1, conditional on the stated
near-expiry ratio limit. The limit itself is not assumed in the pricing model
and remains to be derived from the actual American/European value comparison.

## Result

Public entry points include `tangentIntercept`, `tangentIntercept_hasDeriv`,
`boundaryRatio_hasDeriv`, `negative_stays_negative_of_deriv_nonpos`.
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
