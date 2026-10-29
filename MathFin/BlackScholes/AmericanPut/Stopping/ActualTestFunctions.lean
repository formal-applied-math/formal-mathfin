/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.PlaneDynkin
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualLocalMeanValue

/-! # Smooth test-function inequalities for the actual continuation price

The American price is only known continuous here. Its rectangle mean-value
identity and the independently proved test-function Dynkin identity give signs
of expected generator integrals for tests touching from above or below.

## Result

Public entry points include `brownianLogState_adapted`, `rawRectangleExitRule`,
`rawRectangleExitRule_time`, `canonicalDiscountedPlane`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

theorem brownianLogState_adapted (β σ x : ℝ) :
    Adapted brownianFiltration (brownianLogState β σ x) := by
  intro t
  exact measurable_const.add (measurable_const.mul (brownian_adapted t))

/-- The same rectangle exit rule as `actualRectangleExitRule`, built on the raw Brownian
filtration. -/
noncomputable def rawRectangleExitRule (k h x R : ℝ) (δ : ℝ≥0) :
    BoundedRule brownianFiltration δ :=
  rectangleExitRule (brownianLogState_adapted (k-h-1) (Real.sqrt 2) x)
    (brownianLogState_continuous (k-h-1) (Real.sqrt 2) x) x R δ

theorem rawRectangleExitRule_time (k h x R : ℝ) (δ : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    (rawRectangleExitRule k h x R δ).time ω = actualRectangleExitTime k h x R δ ω := rfl

/-- The discounted canonical price as a function of `z = (elapsed time, Brownian value)`:
`Real.exp (-k*z.1)*canonicalPrice k h (x+(k-h-1)*z.1+Real.sqrt 2*z.2) ((T : ℝ)-z.1)`. -/
noncomputable def canonicalDiscountedPlane (k h x : ℝ) (T : ℝ≥0) (z : ℝ × ℝ) : ℝ :=
  Real.exp (-k*z.1)*canonicalPrice k h (x+(k-h-1)*z.1+Real.sqrt 2*z.2) ((T : ℝ)-z.1)

/-- Space-time set where `z.1` lies in `[0,δ]` and `(k-h-1)*z.1+Real.sqrt 2*z.2` has
absolute value at most `R`. -/
def driverRectangle (k h R : ℝ) (δ : ℝ≥0) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ δ ∧ |(k-h-1)*z.1+Real.sqrt 2*z.2| ≤ R}

theorem canonicalDiscountedPlane_path (k h x : ℝ) {T s : ℝ≥0} (hs : s ≤ T)
    (ω : ℝ≥0 → ℝ) :
    canonicalDiscountedPlane k h x T (s,brownian s ω) = canonicalDiscountedPrice k h x T s ω := by
  simp only [canonicalDiscountedPlane,canonicalDiscountedPrice,min_eq_left hs,brownianLogState]

theorem rawRectangleExit_path_mem_ae (k h x : ℝ) {R : ℝ} (hR : 0 < R)
    {δ : ℝ≥0} (hδ : 0 < δ) :
    ∀ᵐ ω ∂gaussianLimit,
      0 < (rawRectangleExitRule k h x R δ).time ω ∧
      ∀ s ≤ (rawRectangleExitRule k h x R δ).time ω,
        ((s : ℝ),brownian s ω) ∈ driverRectangle k h R δ := by
  filter_upwards [isBrownianReal_brownian.eval_zero_ae_eq_zero] with ω hω
  let θ := rawRectangleExitRule k h x R δ
  have hs : |brownianLogState (k-h-1) (Real.sqrt 2) x 0 ω-x| < R := by
    simpa only [brownianLogState,NNReal.coe_zero,mul_zero,add_zero,hω,sub_self,abs_zero] using hR
  have hp := rectangleExitRule_pos (brownianLogState_adapted (k-h-1) (Real.sqrt 2) x)
    (brownianLogState_continuous (k-h-1) (Real.sqrt 2) x) hδ ω hs
  refine ⟨hp,?_⟩
  intro s hst
  refine ⟨s.coe_nonneg,by exact_mod_cast hst.trans (θ.le_horizon ω),?_⟩
  have hb : |brownianLogState (k-h-1) (Real.sqrt 2) x s ω-x| ≤ R := by
    rcases lt_or_eq_of_le hst with hl | he
    · exact (rectangleExitRule_before (brownianLogState_adapted (k-h-1) (Real.sqrt 2) x)
        (brownianLogState_continuous (k-h-1) (Real.sqrt 2) x) ω hl).1.le
    · subst s
      exact rectangleExitRule_spatial_bound _ _ ω hp
  have he : brownianLogState (k-h-1) (Real.sqrt 2) x s ω-x =
      (k-h-1)*(s : ℝ)+Real.sqrt 2*brownian s ω := by unfold brownianLogState; ring
  rwa [he] at hb

theorem canonicalPrice_rectangle_meanValue_raw {k h : ℝ} (hk : 0 ≤ k)
    {x R : ℝ} {T δ : ℝ≥0} (hδT : δ ≤ T)
    (hrect : InContinuationRectangle k h x T R δ) :
    (∫ ω, canonicalDiscountedPrice k h x T ((rawRectangleExitRule k h x R δ).time ω) ω
      ∂gaussianLimit) = canonicalPrice k h x (T : ℝ) := by
  let θ := rawRectangleExitRule k h x R δ
  have hm := measurable_uncurry_of_continuous_of_measurable
    (canonicalDiscountedPrice_continuous (h := h) hk x T)
    (fun t => (canonicalDiscountedPrice_adapted hk x T t).mono (brownianFiltration.le t) le_rfl)
  have hs : StronglyMeasurable (fun ω => canonicalDiscountedPrice k h x T (θ.time ω) ω) :=
    (hm.comp (θ.measurable_time.prodMk measurable_id)).stronglyMeasurable
  change (∫ ω, canonicalDiscountedPrice k h x T (θ.time ω) ω ∂gaussianLimit) = _
  rw [← integral_completion_original gaussianLimit hs]
  have he := canonicalPrice_rectangle_meanValue hk hδT hrect
  have hfun : (fun ω => canonicalDiscountedPrice k h x T (θ.time ω) ω) =
      fun ω => Real.exp (-k*(actualRectangleExitTime k h x R δ ω : ℝ))*
        canonicalPrice k h
          (brownianLogState (k-h-1) (Real.sqrt 2) x (actualRectangleExitTime k h x R δ ω) ω)
          ((T : ℝ)-(actualRectangleExitTime k h x R δ ω : ℝ)) := by
    funext ω
    have ht : θ.time ω ≤ T := (θ.le_horizon ω).trans hδT
    simp only [canonicalDiscountedPrice,min_eq_left ht]
    rfl
  rw [hfun]
  exact he

theorem canonicalPrice_rectangle_upper_test {k h : ℝ} (hk : 0 ≤ k)
    {x R : ℝ} {T δ : ℝ≥0} (hδT : δ ≤ T)
    (hrect : InContinuationRectangle k h x T R δ)
    {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hc : HasCompactSupport G)
    (h0 : G (0, 0) = canonicalPrice k h x (T : ℝ))
    (hupper : ∀ᵐ ω ∂gaussianLimit,
      let s := (rawRectangleExitRule k h x R δ).time ω
      canonicalDiscountedPrice k h x T s ω ≤ G (s, brownian s ω)) :
    0 ≤ ∫ ω, planeDrift G ((rawRectangleExitRule k h x R δ).time ω) ω ∂gaussianLimit := by
  let θ := rawRectangleExitRule k h x R δ
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuous hG.continuous
  have hi := candidate_stopped_integrable (canonicalDiscountedPrice_supermartingale (h := h) hk x T)
    (canonicalDiscountedPrice_continuous hk x T) (canonicalDiscountedPrice_bound hk x T) θ
  have ht := integral_mono_ae hi
    (planeValue_stopped_integrable hG.continuous θ (fun s _ w => hA (s,w))) hupper
  rw [canonicalPrice_rectangle_meanValue_raw hk hδT hrect,plane_dynkin_compact hG hc θ,h0] at ht
  linarith

theorem canonicalPrice_rectangle_lower_test {k h : ℝ} (hk : 0 ≤ k)
    {x R : ℝ} {T δ : ℝ≥0} (hδT : δ ≤ T)
    (hrect : InContinuationRectangle k h x T R δ)
    {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hc : HasCompactSupport G)
    (h0 : G (0, 0) = canonicalPrice k h x (T : ℝ))
    (hlower : ∀ᵐ ω ∂gaussianLimit,
      let s := (rawRectangleExitRule k h x R δ).time ω
      G (s, brownian s ω) ≤ canonicalDiscountedPrice k h x T s ω) :
    (∫ ω, planeDrift G ((rawRectangleExitRule k h x R δ).time ω) ω ∂gaussianLimit) ≤ 0 := by
  let θ := rawRectangleExitRule k h x R δ
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuous hG.continuous
  have hi := candidate_stopped_integrable (canonicalDiscountedPrice_supermartingale (h := h) hk x T)
    (canonicalDiscountedPrice_continuous hk x T) (canonicalDiscountedPrice_bound hk x T) θ
  have ht := integral_mono_ae
    (planeValue_stopped_integrable hG.continuous θ (fun s _ w => hA (s,w))) hi hlower
  rw [canonicalPrice_rectangle_meanValue_raw hk hδT hrect,plane_dynkin_compact hG hc θ,h0] at ht
  linarith

/-- A deterministic upper bound on the whole driver rectangle supplies the
random-exit hypothesis. No smoothness of the price is used. -/
theorem canonicalPrice_rectangle_upper_test_of_patch {k h : ℝ} (hk : 0 ≤ k)
    {x R : ℝ} (hR : 0 < R) {T δ : ℝ≥0} (hδ : 0 < δ) (hδT : δ ≤ T)
    (hrect : InContinuationRectangle k h x T R δ)
    {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hc : HasCompactSupport G)
    (h0 : G (0, 0) = canonicalPrice k h x (T : ℝ))
    (hpatch : ∀ z ∈ driverRectangle k h R δ, canonicalDiscountedPlane k h x T z ≤ G z) :
    0 ≤ ∫ ω, planeDrift G ((rawRectangleExitRule k h x R δ).time ω) ω ∂gaussianLimit := by
  apply canonicalPrice_rectangle_upper_test hk hδT hrect hG hc h0
  filter_upwards [rawRectangleExit_path_mem_ae k h x hR hδ] with ω hω
  let θ := rawRectangleExitRule k h x R δ
  have hh := hpatch (θ.time ω,brownian (θ.time ω) ω) (hω.2 _ le_rfl)
  rw [canonicalDiscountedPlane_path k h x ((θ.le_horizon ω).trans hδT) ω] at hh
  exact hh

theorem canonicalPrice_rectangle_lower_test_of_patch {k h : ℝ} (hk : 0 ≤ k)
    {x R : ℝ} (hR : 0 < R) {T δ : ℝ≥0} (hδ : 0 < δ) (hδT : δ ≤ T)
    (hrect : InContinuationRectangle k h x T R δ)
    {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hc : HasCompactSupport G)
    (h0 : G (0, 0) = canonicalPrice k h x (T : ℝ))
    (hpatch : ∀ z ∈ driverRectangle k h R δ, G z ≤ canonicalDiscountedPlane k h x T z) :
    (∫ ω, planeDrift G ((rawRectangleExitRule k h x R δ).time ω) ω ∂gaussianLimit) ≤ 0 := by
  apply canonicalPrice_rectangle_lower_test hk hδT hrect hG hc h0
  filter_upwards [rawRectangleExit_path_mem_ae k h x hR hδ] with ω hω
  let θ := rawRectangleExitRule k h x R δ
  have hh := hpatch (θ.time ω,brownian (θ.time ω) ω) (hω.2 _ le_rfl)
  rw [canonicalDiscountedPlane_path k h x ((θ.le_horizon ω).trans hδT) ω] at hh
  exact hh

end MathFin.BlackScholes.AmericanPut.Stopping
