/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.StochasticIntegralVersion
public import MathFin.Probability.Brownian.Ito.Filtered.CommonLift
public import MathFin.Probability.Brownian.Ito.Filtered.CommonContinuous
public import MathFin.Probability.Brownian.Ito.StochasticIntegralCharacterisation

/-!
# Stochastic Integral Identification

## Main results

* `lifted_modification_ae_eq_integrator`
* `lifted_modification_isStochasticIntegral`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

namespace MathFin.FilteredIto.CommonLift

open MeasureTheory ProbabilityTheory
open MathFin.FilteredIto.CommonNoise MathFin.StochasticIntegralCharacterisation
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- Lifting a natural-filtration kernel to the common filtration gives a continuous
version of the integrator used by the library's stochastic integral. -/
theorem lifted_modification_ae_eq_integrator (hB : BrownianOn ℱ B μ)
    (hpath : ∀ ω, Continuous (fun t ↦ B t ω)) (T t : ℝ≥0)
    (φ : Lp ℝ 2 (MathFin.ItoIntegralCLM.trimMeasure (μ := μ) T hB.measurable)) :
    CommonContinuous.itoContinuousMod T hB.measurable (lpLift (natural_le hB) T φ) (min t T)
      =ᵐ[μ] integrator T hB.measurable φ hB.law t := by
  have h := CommonContinuous.itoContinuousMod_modification hB T hB.measurable hpath
    (lpLift (natural_le hB) T φ) (min_le_right t T)
  have e := (process_commutes (natural_le hB) (brownianOn_natural hB.law hB.measurable)
    hB T (min t T) φ).trans (process_natural_eq hB.law hB.measurable T (min t T) φ)
  exact h.trans (Filter.Eventually.of_forall fun ω ↦ congrArg (fun z : Lp ℝ 2 μ ↦ z ω) e)


/-- BrownianMotion's stochastic-integral predicate for the continuous common-filtration
version of a lifted kernel, on the library's natural-filtration domain. -/
theorem lifted_modification_isStochasticIntegral (hB : BrownianOn ℱ B μ)
    (hpath : ∀ ω, Continuous (fun t ↦ B t ω)) (T : ℝ≥0)
    (φ : Lp ℝ 2 (MathFin.ItoIntegralCLM.trimMeasure (μ := μ) T hB.measurable)) :
    IsStochasticIntegral μ
      (fun t ↦ CommonContinuous.itoContinuousMod T hB.measurable
        (lpLift (natural_le hB) T φ) (min t T))
      (MathFin.ItoIntegralL2.natFiltration hB.measurable)
      (sIntegral T hB.measurable φ hB.law) (domain T hB.measurable φ) :=
  isStochasticIntegral_of_modification hB.law
    (fun t ↦ lifted_modification_ae_eq_integrator hB hpath T t φ)

end MathFin.FilteredIto.CommonLift
