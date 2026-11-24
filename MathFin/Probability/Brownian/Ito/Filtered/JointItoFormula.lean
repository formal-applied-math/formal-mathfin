/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonItoFormula
public import MathFin.Probability.Brownian.Ito.Filtered.JointStochasticIntegral

/-!
# Joint Ito Formula

## Main results

* `ito_formula_stochasticIntegral`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

namespace MathFin.FilteredIto.CommonIto
open MeasureTheory ProbabilityTheory
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonPredictable
      MathFin.FilteredIto.CommonRiemann MathFin.FilteredIto.CommonCovariation
open scoped NNReal ENNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 mΩ} {B Z : ℝ≥0 → Ω → ℝ}
local notation "leb" => MathFin.ItoIntegralL2.timeMeasure

/-- The two-driver Itô formula written using the stochastic integrals on the common filtration.
Taking the coordinate type to be Fin 2 gives the two-dimensional state formula. -/
theorem ito_formula_stochasticIntegral {ι : Type*} [Fintype ι] [DecidableEq ι] (hP :
      IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} {Y : ι → ℝ≥0 → Ω → ℝ} {y : ι → ℝ} {a b c : ι → ℝ≥0 → Ω → ℝ}
    {φB φZ : ι → Lp ℝ 2 (trimMeasure_T (μ := μ) T ℱ)} (hY : ItoProc hP T Y y a b c φB φZ)
    {f : (ι → ℝ) → ℝ} {C₁ C₂ : ℝ} (hf : ItoTest f C₁ C₂) :
    ∀ᵐ ω ∂μ, f (fun i ↦ Y i T ω) = f y
      + ∫ s in Set.Ioc 0 T, (∑ i, pd f i (fun l ↦ Y l s ω) * a i s ω
          + (1 / 2) * ∑ i, ∑ k, pd2 f i k (fun l ↦ Y l s ω)
              * (b i s ω * b k s ω + c i s ω * c k s ω)) ∂leb
      + ∑ i, CommonIntegral.sIntegral T ℱ hP.left (Function.curry ⇑(mulKernel T (goodProcess_pd
            hY.proc hf i).pred
          (goodProcess_pd hY.proc hf i).bdd (φB i))) ω
      + ∑ i, CommonIntegral.sIntegral T ℱ hP.right (Function.curry ⇑(mulKernel T (goodProcess_pd
            hY.proc hf i).pred
          (goodProcess_pd hY.proc hf i).bdd (φZ i))) ω := by
  simpa only [CommonIntegral.sIntegral_curry] using ito_formula hP hBc hZc hY hf

end MathFin.FilteredIto.CommonIto
