/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.ItoIntegralL2

/-!
# Filtered Brownian motion from future-increment independence

The joint independence of the future of two drivers gives past-independent increments
for each coordinate and each fixed linear combination. This criterion constructs
BrownianMotion's filtered scalar driver directly.

## Main results

* `isFilteredPreBrownian_of_indep_shift` tests independence against real observables of the past.

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, independent increments, MSC 60H05
-/

@[expose] public section

namespace MathFin.FilteredIto.CommonNoise
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Whole-shift independence implies the single-increment condition of a filtered Brownian
motion. Applying the assumption to the indicator of a past event recovers sigma-algebra
independence. -/
theorem isFilteredPreBrownian_of_indep_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B μ) (ha : StronglyAdapted ℱ B)
    (hshift : ∀ s : ℝ≥0, ∀ {f : Ω → ℝ}, Measurable[ℱ s] f →
      IndepFun f (fun ω u ↦ B (s + u) ω - B s ω) μ) :
    IsFilteredPreBrownian B ℱ μ where
  toIsPreBrownianReal := hB
  stronglyAdapted := ha
  indep s t hst := by
    apply Indep.symm
    rw [Indep_iff]
    rintro A _ hA ⟨S, hS, rfl⟩
    have hA' : A = A.indicator (1 : Ω → ℝ) ⁻¹' ({1} : Set ℝ) := by
      ext ω
      by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
    have hstep {f : Ω → ℝ} (hf : Measurable[ℱ s] f) :
        IndepFun f (fun ω ↦ B t ω - B s ω) μ := by
      have he := (hshift s hf).comp measurable_id (measurable_pi_apply (t - s))
      simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst] using he
    have hi := hstep (f := A.indicator (1 : Ω → ℝ)) (measurable_const.indicator hA)
    rw [hA']
    exact hi.measure_inter_preimage_eq_mul ({1} : Set ℝ) S (by simp) hS

end MathFin.FilteredIto.CommonNoise
