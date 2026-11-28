/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonContinuous

/-!
# Common Predictable Process

Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Common-filtration extension of ItoProcessPredictable, 2026-10-18.

## Main results

* `itoSimpleProcess_continuous`
* `itoSimpleProcess_isStronglyPredictable`
* `itoContinuousMod_isStronglyPredictable`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.CommonContinuous
open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonL2
      MathFin.FilteredIto.CommonPredictable
open MathFin.FilteredIto.CommonProcess MathFin.FilteredIto.CommonProcessGeneral
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}
  (hB : IsFilteredPreBrownian B ℱ μ)
include hB

omit [IsProbabilityMeasure μ] hB in
theorem itoSimpleProcess_continuous (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (V : SimpleProcess ℝ ℱ) (ω : Ω) :
    Continuous (fun t : ℝ≥0 => itoSimpleProcess hm V t ω) := by
  simp_rw [itoSimpleProcess_apply hm V, Finsupp.sum]
  refine continuous_finsetSum _ (fun p _ => ?_)
  refine Continuous.const_mul ?_ _
  exact ((hc ω).comp (continuous_const.min continuous_id)).sub
    ((hc ω).comp (continuous_const.min continuous_id))

omit [IsProbabilityMeasure μ] in
theorem itoSimpleProcess_isStronglyPredictable (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => B t ω) (V : SimpleProcess ℝ ℱ) :
    IsStronglyPredictable ℱ (itoSimpleProcess hm V) := by
  apply StronglyAdapted.isStronglyPredictable_of_leftContinuous
  · exact (itoSimpleProcess_isMartingale hB hm V).1
  · exact fun ω _ => (itoSimpleProcess_continuous hm hc V ω).continuousWithinAt

theorem itoContinuousMod_isStronglyPredictable (T : ℝ≥0) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (φ : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)) :
    IsStronglyPredictable ℱ (itoContinuousMod T hm φ) := by
  rw [IsStronglyPredictable]
  have hrw : Function.uncurry (itoContinuousMod T hm φ) =
      fun z : ℝ≥0 × Ω => limUnder atTop (fun n =>
        Function.uncurry (itoSimpleProcess hm ((approxSeq T hm φ).choose n).val) z) := by
    funext z
    rfl
  rw [hrw]
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  exact StronglyMeasurable.limUnder (fun n =>
    itoSimpleProcess_isStronglyPredictable hB hm hc ((approxSeq T hm φ).choose n).val)

end MathFin.FilteredIto.CommonContinuous
