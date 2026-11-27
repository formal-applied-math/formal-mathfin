/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import Mathlib.Probability.Distributions.Gaussian.Real

public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Small-ball bound for the real Gaussian law

The centred Gaussian density `gaussianPDFReal 0 v` is bounded by its value `(√(2πv))⁻¹` at the
origin, so a symmetric interval of half-width `r` carries mass at most `2r/√(2πv)`. With variance
`1/n` and half-width `c/n` this is at most `c/√n`: an increment of Brownian motion over a time
step `1/n` falls in the window `[-c/n, c/n]` with probability at most `c/√n`. This is the
estimate behind the Paley–Wiener–Zygmund argument for nowhere differentiability.

## Main results

* `gaussianReal_abs_le_le`: `N(0, v)(|x| ≤ r) ≤ 2r/√(2πv)`
* `gaussianReal_abs_le_le_inv_sqrt`: `N(0, 1/n)(|x| ≤ c/n) ≤ c/√n`

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Corollary 5.3.4
* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  §2.9

## Tags

Gaussian distribution, small ball probability, density bound, MSC 60G15
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

/-- **Small-ball bound.** The centred Gaussian law of variance `v ≠ 0` gives the window
`{|x| ≤ r}` mass at most `2r/√(2πv)`: the density never exceeds its value at the origin. -/
theorem gaussianReal_abs_le_le {v : ℝ≥0} (hv : v ≠ 0) (r : ℝ) :
    gaussianReal 0 v {x | |x| ≤ r} ≤ ENNReal.ofReal (2 * r / √(2 * π * v)) := by
  have hset : {x : ℝ | |x| ≤ r} = Set.Icc (-r) r := by
    ext x
    simp [abs_le]
  rw [hset, gaussianReal_apply _ hv]
  calc ∫⁻ x in Set.Icc (-r) r, gaussianPDF 0 v x
      ≤ ∫⁻ _ in Set.Icc (-r) r, ENNReal.ofReal (√(2 * π * v))⁻¹ := by
        refine lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_
        rw [gaussianPDFReal_def]
        exact mul_le_of_le_one_right (inv_nonneg.2 (Real.sqrt_nonneg _))
          (Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.2 (sq_nonneg _)) (by positivity)))
    _ = ENNReal.ofReal (2 * r / √(2 * π * v)) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- **Small-ball bound at the Brownian scale.** The Gaussian law of variance `1/n` gives the
window `{|x| ≤ c/n}` mass at most `c/√n`. -/
theorem gaussianReal_abs_le_le_inv_sqrt {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 0 ≤ c) :
    gaussianReal 0 (n : ℝ≥0)⁻¹ {x | |x| ≤ c / n} ≤ ENNReal.ofReal (c / √n) := by
  refine (gaussianReal_abs_le_le (inv_ne_zero (Nat.cast_ne_zero.2 hn.ne')) _).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hss : √(n : ℝ) * √n = n := Real.mul_self_sqrt hn0.le
  have h1 : 2 / √(n : ℝ) ≤ √(2 * π * ((n : ℝ≥0)⁻¹ : ℝ≥0)) := by
    have h4 : (2 : ℝ) / √n = √(4 * (n : ℝ)⁻¹) := by
      rw [Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num), Real.sqrt_inv]
      ring
    rw [h4]
    refine Real.sqrt_le_sqrt ?_
    push_cast
    nlinarith [Real.pi_gt_three, inv_pos.2 hn0]
  have hD : 0 < √(2 * π * ((n : ℝ≥0)⁻¹ : ℝ≥0)) := lt_of_lt_of_le (by positivity) h1
  rw [div_le_iff₀ hD]
  calc 2 * (c / n) = c / √n * (2 / √n) := by
        rw [div_mul_div_comm, hss]
        ring
    _ ≤ c / √n * √(2 * π * ((n : ℝ≥0)⁻¹ : ℝ≥0)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

end MathFin
