/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualContactMartingale
public import MathFin.BlackScholes.AmericanPut.Stopping.RectangleExit
public import MathFin.BlackScholes.AmericanPut.Stopping.ContinuationRectangles

/-! # Local rectangular mean-value property of the actual American price

The exit rule is constructed from the log-price path, independently of any PDE.
For rectangles inside continuation it precedes contact, so the actual-price
martingale gives an exact local exit representation.

## Result

Public entry points include `brownianLogState_continuous`, `brownianLogState_usual_adapted`,
`actualRectangleExitRule`, `actualRectangleExitTime`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

theorem brownianLogState_continuous (β σ x : ℝ) (ω : ℝ≥0 → ℝ) :
    Continuous (fun t => brownianLogState β σ x t ω) := by
  have hw := continuous_brownian ω
  unfold brownianLogState
  fun_prop

theorem brownianLogState_usual_adapted (β σ x : ℝ) :
    @Adapted _ _ (completedMeasurableSpace gaussianLimit) _ _ _ brownianUsualFiltration
      (brownianLogState β σ x) := by
  intro t
  exact measurable_const.add (measurable_const.mul (brownianUsual_adapted t))

/-- Exit rule from the rectangle of spatial half-width `R` and duration `δ`, for the
Brownian log-state started at `x`, on the completed usual filtration. -/
noncomputable def actualRectangleExitRule (k h x R : ℝ) (δ : ℝ≥0) :
    @StoppingRule (ℝ≥0 → ℝ) (completedMeasurableSpace gaussianLimit) ℝ≥0 _
      brownianUsualFiltration δ :=
  @rectangleExitRule _ (completedMeasurableSpace gaussianLimit) brownianUsualFiltration
    (brownianLogState (k-h-1) (Real.sqrt 2) x)
    (brownianLogState_usual_adapted (k-h-1) (Real.sqrt 2) x)
    (brownianLogState_continuous (k-h-1) (Real.sqrt 2) x) x R δ

/-- The stopping time of `actualRectangleExitRule`. -/
noncomputable def actualRectangleExitTime (k h x R : ℝ) (δ : ℝ≥0) : (ℝ≥0 → ℝ) → ℝ≥0 :=
  @StoppingRule.time _ (completedMeasurableSpace gaussianLimit) ℝ≥0 _ brownianUsualFiltration δ
    (actualRectangleExitRule k h x R δ)

theorem actualRectangleExit_boundary_ae (k h x : ℝ) {R : ℝ} (hR : 0 < R)
    {δ : ℝ≥0} (hδ : 0 < δ) :
    ∀ᵐ ω ∂completedMeasure gaussianLimit,
      let s := actualRectangleExitTime k h x R δ ω
      0 < s ∧ |brownianLogState (k-h-1) (Real.sqrt 2) x s ω-x| ≤ R ∧
        (|brownianLogState (k-h-1) (Real.sqrt 2) x s ω-x| = R ∨ s = δ) := by
  let μ := completedMeasure gaussianLimit
  have hz : ∀ᵐ ω ∂μ, brownian 0 ω = 0 := isBrownianReal_brownian.eval_zero_ae_eq_zero
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  filter_upwards [hz] with ω hω
  have hs : |brownianLogState (k-h-1) (Real.sqrt 2) x 0 ω-x| < R := by
    simpa only [brownianLogState,NNReal.coe_zero,mul_zero,add_zero,hω,sub_self,abs_zero] using hR
  have hp := rectangleExitRule_pos (brownianLogState_usual_adapted (k-h-1) (Real.sqrt 2) x)
    (brownianLogState_continuous (k-h-1) (Real.sqrt 2) x) hδ ω hs
  exact ⟨hp,rectangleExitRule_spatial_bound _ _ ω hp,rectangleExitRule_boundary _ _ ω hp⟩

theorem actualRectangleExit_le_contact {k h : ℝ} (hk : 0 ≤ k) {x R : ℝ} {T δ : ℝ≥0}
    (hrect : InContinuationRectangle k h x T R δ) (ω : ℝ≥0 → ℝ) :
    actualRectangleExitTime k h x R δ ω ≤ brownianUsualActualContactTime (h := h) hk x T ω := by
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  let τ := brownianUsualActualContactRule (h := h) hk x T
  let ρ := actualRectangleExitRule k h x R δ
  change ρ.time ω ≤ τ.time ω
  by_contra! hlt
  have hs := rectangleExitRule_before (brownianLogState_usual_adapted (k-h-1) (Real.sqrt 2) x)
    (brownianLogState_continuous (k-h-1) (Real.sqrt 2) x) ω hlt
  have hp :=
      hrect (τ.time ω) hs.2.le (brownianLogState (k-h-1) (Real.sqrt 2) x (τ.time ω) ω) hs.1.le
  have hz :=
      canonicalContactRule_contact (h := h) hk brownianUsual_adapted continuous_brownian x T ω
  change canonicalGap brownian k h x T (τ.time ω) ω = 0 at hz
  have ht : (τ.time ω : ℝ) ≤ T := by exact_mod_cast τ.le_horizon ω
  have hg : 0 < canonicalGap brownian k h x T (τ.time ω) ω := by
    simpa only [canonicalGap,canonicalLogPath,brownianLogState,NNReal.coe_min,
      min_eq_left (τ.le_horizon ω),min_eq_left ht] using sub_pos.mpr hp.2
  exact (ne_of_gt hg) hz

theorem canonicalPrice_rectangle_meanValue {k h : ℝ} (hk : 0 ≤ k) {x R : ℝ} {T δ : ℝ≥0}
    (hδT : δ ≤ T) (hrect : InContinuationRectangle k h x T R δ) :
    (∫ ω, Real.exp (-k*(actualRectangleExitTime k h x R δ ω : ℝ))*
      canonicalPrice k h
        (brownianLogState (k-h-1) (Real.sqrt 2) x (actualRectangleExitTime k h x R δ ω) ω)
        ((T : ℝ)-(actualRectangleExitTime k h x R δ ω : ℝ)) ∂completedMeasure gaussianLimit) =
      canonicalPrice k h x (T : ℝ) := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  let ρ := actualRectangleExitRule k h x R δ
  let η := ρ.extend hδT
  have he := canonicalPrice_contact_meanValue (h := h) hk x T η
  have hfun : (fun ω => canonicalDiscountedPrice k h x T
      (min (η.time ω) (brownianUsualActualContactTime (h := h) hk x T ω)) ω) =
      fun ω => Real.exp (-k*(actualRectangleExitTime k h x R δ ω : ℝ))*
        canonicalPrice k h
          (brownianLogState (k-h-1) (Real.sqrt 2) x (actualRectangleExitTime k h x R δ ω) ω)
          ((T : ℝ)-(actualRectangleExitTime k h x R δ ω : ℝ)) := by
    funext ω
    have hle := actualRectangleExit_le_contact hk hrect ω
    change canonicalDiscountedPrice k h x T
      (min (actualRectangleExitTime k h x R δ ω) (brownianUsualActualContactTime (h := h) hk x T ω))
          ω = _
    rw [min_eq_left hle]
    have ht : actualRectangleExitTime k h x R δ ω ≤ T := (ρ.le_horizon ω).trans hδT
    simp only [canonicalDiscountedPrice,min_eq_left ht]
  rw [hfun] at he
  exact he

end MathFin.BlackScholes.AmericanPut.Stopping
