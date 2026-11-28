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
theorem lifted_modification_ae_eq_integrator (hB : IsFilteredPreBrownian B ℱ μ)
    (hpath : ∀ ω, Continuous (fun t ↦ B t ω)) (T t : ℝ≥0)
    (φ : Lp ℝ 2 (MathFin.ItoIntegralCLM.trimMeasure (μ := μ) T hB.measurable_eval)) :
    CommonContinuous.itoContinuousMod T hB.measurable_eval (lpLift (natural_le hB) T φ) (min t T)
      =ᵐ[μ] integrator T hB.measurable_eval φ hB.toIsPreBrownianReal t := by
  have h := CommonContinuous.itoContinuousMod_modification hB T hB.measurable_eval hpath
    (lpLift (natural_le hB) T φ) (min_le_right t T)
  have e := (process_commutes (natural_le hB) (hB.toIsPreBrownianReal.isFilteredPreBrownian
        hB.measurable_eval)
    hB T (min t T) φ).trans (process_natural_eq hB.toIsPreBrownianReal hB.measurable_eval T (min
          t T) φ)
  exact h.trans (Filter.Eventually.of_forall fun ω ↦ congrArg (fun z : Lp ℝ 2 μ ↦ z ω) e)


/-- BrownianMotion's stochastic-integral predicate for the continuous common-filtration
version of a lifted kernel, on the library's natural-filtration domain. -/
theorem lifted_modification_isStochasticIntegral (hB : IsFilteredPreBrownian B ℱ μ)
    (hpath : ∀ ω, Continuous (fun t ↦ B t ω)) (T : ℝ≥0)
    (φ : Lp ℝ 2 (MathFin.ItoIntegralCLM.trimMeasure (μ := μ) T hB.measurable_eval)) :
    IsStochasticIntegral μ
      (fun t ↦ CommonContinuous.itoContinuousMod T hB.measurable_eval
        (lpLift (natural_le hB) T φ) (min t T))
      (MathFin.ItoIntegralL2.natFiltration hB.measurable_eval)
      (sIntegral T hB.measurable_eval φ hB.toIsPreBrownianReal) (domain T hB.measurable_eval φ) :=
  isStochasticIntegral_of_modification hB.toIsPreBrownianReal
    (fun t ↦ lifted_modification_ae_eq_integrator hB hpath T t φ)

end MathFin.FilteredIto.CommonLift
