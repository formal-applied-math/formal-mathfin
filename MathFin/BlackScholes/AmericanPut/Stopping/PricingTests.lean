/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.PointwiseTests

/-! # Smooth-test pricing inequalities in log-price and remaining time

The actual price has not been assumed differentiable. At an interior touching
point, derivatives below belong to the smooth test, not to the option price.

## Result

Public entry points include `pricingTestKernel`, `pricingTestKernel_contDiff`,
`pricingTestKernel_eq_brownian`, `pricingTestKernel_generator`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- The test function `F` composed with the affine space-time map
`z ↦ (x+(k-h-1)*z.1+Real.sqrt 2*z.2, T-z.1)` and discounted by `exp (-k*z.1)`. -/
noncomputable def pricingTestKernel (F : ℝ × ℝ → ℝ) (k h x : ℝ) (T : ℝ≥0)
    (z : ℝ × ℝ) : ℝ :=
  Real.exp (-k*z.1)*F (x+(k-h-1)*z.1+Real.sqrt 2*z.2,(T : ℝ)-z.1)

theorem pricingTestKernel_contDiff {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (k h x : ℝ) (T : ℝ≥0) : ContDiff ℝ 3 (pricingTestKernel F k h x T) := by
  unfold pricingTestKernel
  fun_prop

theorem pricingTestKernel_eq_brownian (F : ℝ × ℝ → ℝ) (k h x : ℝ) (T : ℝ≥0) :
    pricingTestKernel F k h x T =
      fun z => brownianPriceKernel (fun y t => F (y,t)) 1 k h (Real.sqrt 2) x T z.1 z.2 := by
  funext z
  simp [pricingTestKernel,brownianPriceKernel,Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem pricingTestKernel_generator {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (k h x : ℝ) (T : ℝ≥0) :
    planeGenerator (pricingTestKernel F k h x T) (0,0) =
      deriv (deriv (fun y => F (y,(T : ℝ)))) x +
      (k-h-1)*deriv (fun y => F (y,(T : ℝ))) x -
      deriv (fun t => F (x,t)) (T : ℝ) - k*F (x,(T : ℝ)) := by
  rw [planeGenerator_eq_partials (pricingTestKernel_contDiff hF k h x T),
    pricingTestKernel_eq_brownian]
  have hd : DifferentiableAt ℝ (fun z : ℝ × ℝ => F (z.1,z.2))
      (x+(k-h-(Real.sqrt 2)^2/2)*0+Real.sqrt 2*0,(Real.sqrt 2)^2/2*((T : ℝ)-0)) :=
    hF.differentiable (by norm_num) _
  rw [(brownianPriceKernel_hasDeriv_time (K := 1) hd).deriv,brownianPriceKernel_deriv2_space]
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),div_self (show (2 : ℝ) ≠ 0 by norm_num),
    mul_zero,add_zero,sub_zero,Real.exp_zero,one_mul,mul_one]
  ring

theorem canonicalPrice_upper_pricing_test {k h x : ℝ} (hk : 0 ≤ k) {T : ℝ≥0}
    (hp : (x, (T : ℝ)) ∈ canonicalContinuationRegion k h)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (h0 : F (x, (T : ℝ)) = canonicalPrice k h x (T : ℝ))
    (htouch : ∀ᶠ z in 𝓝 (x, (T : ℝ)), canonicalPrice k h z.1 z.2 ≤ F z) :
    deriv (fun t => F (x,t)) (T : ℝ) ≤
      deriv (deriv (fun y => F (y,(T : ℝ)))) x +
      (k-h-1)*deriv (fun y => F (y,(T : ℝ))) x - k*F (x,(T : ℝ)) := by
  have hkernel := pricingTestKernel_contDiff hF k h x T
  have hinit : pricingTestKernel F k h x T (0,0) = canonicalPrice k h x (T : ℝ) := by
    simpa [pricingTestKernel] using h0
  have hmap : Tendsto (fun z : ℝ × ℝ =>
      (x+(k-h-1)*z.1+Real.sqrt 2*z.2,(T : ℝ)-z.1)) (𝓝 (0,0)) (𝓝 (x,(T : ℝ))) := by
    convert! (show Continuous (fun z : ℝ × ℝ =>
      (x+(k-h-1)*z.1+Real.sqrt 2*z.2,(T : ℝ)-z.1)) by fun_prop).tendsto (0,0) using 1
    simp
  have hbound : ∀ᶠ z in 𝓝 (0,0),
      canonicalDiscountedPlane k h x T z ≤ pricingTestKernel F k h x T z := by
    filter_upwards [hmap.eventually htouch] with z hz
    exact mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le
  have hh := canonicalPrice_upper_generator_test hk hp hkernel hinit hbound
  rw [pricingTestKernel_generator hF] at hh
  linarith

theorem canonicalPrice_lower_pricing_test {k h x : ℝ} (hk : 0 ≤ k) {T : ℝ≥0}
    (hp : (x, (T : ℝ)) ∈ canonicalContinuationRegion k h)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (h0 : F (x, (T : ℝ)) = canonicalPrice k h x (T : ℝ))
    (htouch : ∀ᶠ z in 𝓝 (x, (T : ℝ)), F z ≤ canonicalPrice k h z.1 z.2) :
    deriv (deriv (fun y => F (y,(T : ℝ)))) x +
      (k-h-1)*deriv (fun y => F (y,(T : ℝ))) x - k*F (x,(T : ℝ)) ≤
      deriv (fun t => F (x,t)) (T : ℝ) := by
  have hkernel := pricingTestKernel_contDiff hF k h x T
  have hinit : pricingTestKernel F k h x T (0,0) = canonicalPrice k h x (T : ℝ) := by
    simpa [pricingTestKernel] using h0
  have hmap : Tendsto (fun z : ℝ × ℝ =>
      (x+(k-h-1)*z.1+Real.sqrt 2*z.2,(T : ℝ)-z.1)) (𝓝 (0,0)) (𝓝 (x,(T : ℝ))) := by
    convert! (show Continuous (fun z : ℝ × ℝ =>
      (x+(k-h-1)*z.1+Real.sqrt 2*z.2,(T : ℝ)-z.1)) by fun_prop).tendsto (0,0) using 1
    simp
  have hbound : ∀ᶠ z in 𝓝 (0,0),
      pricingTestKernel F k h x T z ≤ canonicalDiscountedPlane k h x T z := by
    filter_upwards [hmap.eventually htouch] with z hz
    exact mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le
  have hh := canonicalPrice_lower_generator_test hk hp hkernel hinit hbound
  rw [pricingTestKernel_generator hF] at hh
  linarith

end MathFin.BlackScholes.AmericanPut.Stopping
