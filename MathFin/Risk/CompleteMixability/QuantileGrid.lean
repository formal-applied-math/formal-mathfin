/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Risk.CompleteMixability
public import MathFin.Probability.Laws.Quantile

/-!
# The quantile grid

`k` copies of a law `T` whose sum is deterministic up to the length of `T`'s interval: the
values of the quantile function at the `k` points `frac (w + j / k)`, `j < k`, of a rotated
grid. Each point is uniform when `w` is, so each copy has law `T`; and the grid samples one
point in each cell `[j/k, (j+1)/k)`, where the quantile function and its mean over the cell lie
between the same two values, so the errors telescope to at most `Q(1) - Q(0) ≤ L`.

This is Lemma 2.2 of Shmalo, with the uniform random bijection replaced by a rotation.

## Main results

* `MathFin.hasLaw_quantile_fract`: each grid copy has law `T`.
* `MathFin.abs_sum_quantile_fract_sub_le`: the sum is within `L` of `k` times the mean.

## References

* [Y. Shmalo, *Absolutely continuous laws on a bounded interval are completely mixable for all
  large n*][Shmalo2026CompleteMixability], Lemma 2.2

## Tags

complete mixability, quantile coupling, stratified sampling, MSC 60E05
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

variable {T : Measure ℝ} [IsProbabilityMeasure T]

/-- Each copy of the rotated quantile grid has law `T`. -/
theorem hasLaw_quantile_fract {k : ℕ} (hk : 0 < k) (j : ℕ) :
    HasLaw (fun w ↦ quantile T (Int.fract (w + j / k))) T (volume.restrict (Ioo 0 1)) := by
  sorry

/-- **The quantile grid** (Shmalo, Lemma 2.2). If `T` is carried by `[α, α + L]`, the sum of
the `k` grid copies is a.s. within `L` of `k` times the mean of `T`. -/
theorem abs_sum_quantile_fract_sub_le {α L : ℝ} (hT : T (Icc α (α + L))ᶜ = 0) {k : ℕ}
    (hk : 0 < k) : ∀ᵐ w ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      |∑ j ∈ Finset.range k, quantile T (Int.fract (w + j / k)) - k * ∫ x, x ∂T| ≤ L := by
  sorry

end MathFin
