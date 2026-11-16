/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Discrete.DoobLpMaximalInequality
public import MathFin.Probability.Gaussian.GaussianMoments
public import BrownianMotion.Gaussian.BrownianMotion
public import BrownianMotion.Auxiliary.Martingale

/-!
# Doob's `L²` maximal inequality for Brownian motion on a finite grid

A filtered pre-Brownian motion sampled along a monotone schedule `t₀ ≤ t₁ ≤ …` is a discrete-time
martingale of the sampled filtration (`Martingale.indexComap`), so Doob's `Lᵖ` maximal inequality
for discrete martingales (`Probability/Discrete/DoobLpMaximalInequality`) bounds the running
maximum of `|B|` over the grid in `L²` by twice the `L²` norm of the last value, which is
`√(t_n)`.

## Main results

* `ProbabilityTheory.IsFilteredPreBrownian.eLpNorm_two_eq`: `‖B_t‖_{L²} = √t`
* `ProbabilityTheory.IsFilteredPreBrownian.eLpNorm_runMax_le`:
  `‖max_{k ≤ n} |B_{t_k}|‖_{L²} ≤ 2 √(t_n)`

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 2.4.6

## Tags

Doob maximal inequality, Brownian motion, running maximum, discrete grid, MSC 60G42, MSC 60J65
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- **The `L²` norm of Brownian motion at time `t` is `√t`.** -/
theorem IsFilteredPreBrownian.eLpNorm_two_eq (hB : IsFilteredPreBrownian B 𝓕 P) (s : ℝ≥0) :
    eLpNorm (B s) 2 P = ENNReal.ofReal (√s) := by
  have hmem : MemLp (B s) 2 P := (hB.hasLaw_eval s).memLp (memLp_id_gaussianReal 2)
  have hint : ∫ ω, B s ω ^ 2 ∂P = s := by
    have h := (hB.hasLaw_eval s).integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    simpa only [Function.comp_def, MathFin.integral_sq_gaussianReal] using h
  have hnorm : ∫ ω, ‖B s ω‖ ^ (2 : ℝ) ∂P = s := by
    rw [← hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    show ‖B s ω‖ ^ (2 : ℝ) = B s ω ^ 2
    rw [Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
      sq_abs]
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), ENNReal.toReal_ofNat,
    ← one_div, ← Real.sqrt_eq_rpow, hnorm]

/-- **Doob's `L²` maximal inequality for Brownian motion on a finite grid.** For a filtered
pre-Brownian motion `B` and a monotone schedule `t`, the running maximum of `|B|` over the first
`n + 1` grid times satisfies `‖max_{k ≤ n} |B_{t_k}|‖_{L²} ≤ 2 √(t_n)`: Doob's inequality
(`maximal_ineq_Lp` through `Martingale.eLpNorm_norm_runMax_le`) for the sampled martingale
`k ↦ B_{t_k}` of the sampled filtration, whose last `L²` norm is `√(t_n)`. -/
theorem IsFilteredPreBrownian.eLpNorm_runMax_le [IsProbabilityMeasure P]
    (hB : IsFilteredPreBrownian B 𝓕 P) {t : ℕ → ℝ≥0} (ht : Monotone t) (n : ℕ) :
    eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ |B (t k) ω|)) 2 P ≤ 2 * ENNReal.ofReal (√(t n)) := by
  have hM : Martingale (B ∘ t) (𝓕.indexComap ht) P :=
    (IsPreBrownianReal.isMartingale B 𝓕 P).indexComap ht
  have h : eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ |B (t k) ω|)) (ENNReal.ofReal 2) P
      ≤ ENNReal.ofReal (2 / (2 - 1)) * eLpNorm (B (t n)) (ENNReal.ofReal 2) P :=
    hM.eLpNorm_norm_runMax_le one_lt_two n
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  have h3 : ENNReal.ofReal (2 / (2 - 1)) = 2 := by norm_num
  rw [h2, h3, hB.eLpNorm_two_eq] at h
  exact h

end ProbabilityTheory
