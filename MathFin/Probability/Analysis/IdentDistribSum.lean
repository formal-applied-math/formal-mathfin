/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import Mathlib.Probability.IdentDistrib

/-!
# Wald's bound for a fixed number of identically distributed summands

The `L¹` norm of a sum is at most the sum of the `L¹` norms, and identically distributed summands
have one `L¹` norm. So `𝔼|∑_{i∈s} Xᵢ| ≤ #s·𝔼|Y|` when every `Xᵢ` has the law of an integrable
`Y`, with no independence between the summands. It is the first half of Wald's bound for a random
number of summands (`Risk/CompoundPoissonCVaR.lean`): the count is then integrated out against
a mean.

## Main results

* `ProbabilityTheory.integral_abs_sum_le_of_identDistrib`: `𝔼|∑_{i∈s} Xᵢ| ≤ #s·𝔼|Y|`.

## References

* [Klugman, Panjer and Willmot, *Loss Models*][KlugmanPanjerWillmot], Thm 9.3

## Tags

Wald bound, identically distributed, sum of random variables, MSC 60E15, MSC 60G50
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Wald's bound for a fixed number of summands**: if every `Xᵢ`, `i ∈ s`, has the law of an
integrable `Y`, then `𝔼|∑_{i∈s} Xᵢ| ≤ #s·𝔼|Y|`. No independence is assumed. -/
theorem integral_abs_sum_le_of_identDistrib {ι : Type*} {s : Finset ι}
    {X : ι → Ω → ℝ} {Y : Ω → ℝ} (hident : ∀ i ∈ s, IdentDistrib (X i) Y μ μ)
    (hY : Integrable Y μ) :
    ∫ ω, |∑ i ∈ s, X i ω| ∂μ ≤ s.card * ∫ ω, |Y ω| ∂μ := by
  have habs (i : ι) (hi : i ∈ s) : Integrable (fun ω ↦ |X i ω|) μ :=
    ((hident i hi).integrable_iff.mpr hY).abs
  calc ∫ ω, |∑ i ∈ s, X i ω| ∂μ
      ≤ ∫ ω, ∑ i ∈ s, |X i ω| ∂μ :=
        integral_mono (integrable_finsetSum _ fun i hi ↦ (hident i hi).integrable_iff.mpr hY).abs
          (integrable_finsetSum _ habs) fun ω ↦ Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, ∫ ω, |X i ω| ∂μ := integral_finset_sum _ habs
    _ = ∑ i ∈ s, ∫ ω, |Y ω| ∂μ :=
        Finset.sum_congr rfl fun i hi ↦ ((hident i hi).comp continuous_abs.measurable).integral_eq
    _ = s.card * ∫ ω, |Y ω| ∂μ := by simp

end ProbabilityTheory
