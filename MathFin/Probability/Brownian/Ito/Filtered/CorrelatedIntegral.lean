/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CorrelatedNoise
public import MathFin.Probability.Brownian.Ito.Filtered.CommonIntegral

/-!
# Correlated Integral

Rotation of the genuine common-filtration Itô integrals. The identity is
proved on actual increment sums, then extended to all predictable L2 kernels.
The volatility kernel can therefore depend on the variance driver's history
while being integrated against the correlated price driver.

## Main results

* `IndependentPair.itoSimpleLp_rotation`
* `IndependentPair.itoIntegral_rotation`
* `IndependentPair.itoIntegral_correlated`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.CommonNoise
open MeasureTheory ProbabilityTheory
open MathFin.FilteredIto.CommonIntegral MathFin.FilteredIto.CommonPredictable
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B Z : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

omit [IsProbabilityMeasure μ] in
theorem IndependentPair.itoSimple_rotation (h : IndependentPair ℱ B Z μ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (V : SimpleProcess ℝ ℱ) :
    CommonL2.itoSimple (h.linear_brownian a b hab).measurable V =
      a • CommonL2.itoSimple h.left.measurable V +
      b • CommonL2.itoSimple h.right.measurable V := by
  funext ω
  simp only [CommonL2.itoSimple, Finsupp.sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  dsimp [linearNoise]
  ring

theorem IndependentPair.itoSimpleLp_rotation (h : IndependentPair ℱ B Z μ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (V : SimpleProcess ℝ ℱ) :
    CommonL2.itoSimpleLp (h.linear_brownian a b hab) (h.linear_brownian a b hab).measurable V =
      a • CommonL2.itoSimpleLp h.left h.left.measurable V +
      b • CommonL2.itoSimpleLp h.right h.right.measurable V := by
  apply Lp.ext
  filter_upwards [
    (CommonL2.memLp_itoSimple (h.linear_brownian a b hab)
      (h.linear_brownian a b hab).measurable V).coeFn_toLp,
    (CommonL2.memLp_itoSimple h.left h.left.measurable V).coeFn_toLp,
    (CommonL2.memLp_itoSimple h.right h.right.measurable V).coeFn_toLp,
    Lp.coeFn_add (a • CommonL2.itoSimpleLp h.left h.left.measurable V)
      (b • CommonL2.itoSimpleLp h.right h.right.measurable V),
    Lp.coeFn_smul a (CommonL2.itoSimpleLp h.left h.left.measurable V),
    Lp.coeFn_smul b (CommonL2.itoSimpleLp h.right h.right.measurable V)]
    with ω hw hb hz hadd hsa hsb
  change CommonL2.itoSimpleLp (h.linear_brownian a b hab)
    (h.linear_brownian a b hab).measurable V ω = _
  rw [hadd, Pi.add_apply, hsa, hsb, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [show CommonL2.itoSimpleLp h.left h.left.measurable V ω =
    CommonL2.itoSimple h.left.measurable V ω from hb,
    show CommonL2.itoSimpleLp h.right h.right.measurable V ω =
    CommonL2.itoSimple h.right.measurable V ω from hz,
    show CommonL2.itoSimpleLp (h.linear_brownian a b hab)
      (h.linear_brownian a b hab).measurable V ω =
      CommonL2.itoSimple (h.linear_brownian a b hab).measurable V ω from hw]
  exact congrFun (h.itoSimple_rotation a b hab V) ω

/-- The correlated stochastic integral is the corresponding linear combination
of the two independent-driver integrals, for every common predictable L2 kernel. -/
theorem IndependentPair.itoIntegral_rotation (h : IndependentPair ℱ B Z μ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (T : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    itoIntegralCLM_T (h.linear_brownian a b hab) T f =
      a • itoIntegralCLM_T h.left T f + b • itoIntegralCLM_T h.right T f := by
  have he : (fun g => itoIntegralCLM_T (h.linear_brownian a b hab) T g) =
      (fun g => a • itoIntegralCLM_T h.left T g + b • itoIntegralCLM_T h.right T g) := by
    apply (simpleAssembly_T_denseRange (μ := μ) T ℱ).equalizer
      (itoIntegralCLM_T (h.linear_brownian a b hab) T).continuous
      (((itoIntegralCLM_T h.left T).continuous.const_smul a).add
        ((itoIntegralCLM_T h.right T).continuous.const_smul b))
    funext V
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, itoIntegralCLM_T_simpleAssembly]
    exact h.itoSimpleLp_rotation a b hab V.val
  exact congrFun he f

theorem IndependentPair.itoIntegral_correlated (h : IndependentPair ℱ B Z μ)
    {ρ : ℝ} (hρ : |ρ| ≤ 1) (T : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)) :
    itoIntegralCLM_T (h.correlated_brownian hρ) T f =
      ρ • itoIntegralCLM_T h.left T f +
      orthogonalWeight ρ • itoIntegralCLM_T h.right T f :=
  h.itoIntegral_rotation ρ (orthogonalWeight ρ) (sq_add_orthogonalWeight_sq hρ) T f

end MathFin.FilteredIto.CommonNoise
