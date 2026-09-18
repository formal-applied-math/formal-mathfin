/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.DoobLpMaximalInequality
public import BrownianMotion.StochasticIntegral.UniformIntegrable

/-!
# L²-bounded discrete martingales converge in L²

Mathlib's martingale convergence theory gives, for an L¹-bounded
submartingale, almost-everywhere convergence to `ℱ.limitProcess f μ`
(`Submartingale.ae_tendsto_limitProcess`), membership of the limit in `Lᵖ`
under an `Lᵖ` bound (`Submartingale.memLp_limitProcess`), and **L¹**-norm
convergence under uniform integrability
(`Submartingale.tendsto_eLpNorm_one_limitProcess`). It does **not** contain
the classical L² statement: an L²-bounded martingale converges in L²-norm.

This file proves it, and the route is the point: the uniform-integrability
input is manufactured from this library's own **Doob L² maximal inequality**
(`MeasureTheory.Martingale.eLpNorm_norm_runMax_le`,
`Foundations/DoobLpMaximalInequality.lean`):

1. the running maxima `ω ↦ max_{k ≤ n} ‖f k ω‖` are uniformly L²-bounded by
   `2R` (Doob at `p = 2`);
2. by monotone convergence the all-time envelope `ω ↦ ⨆ n ‖f n ω‖` is
   square-integrable, and it dominates every `f n` — steps 1–2 are the `p = 2`
   case of `MeasureTheory.LpDominator`, shared with
   `LpContinuousMartingaleConvergence`;
3. a single L² dominator makes the family uniformly integrable in L²
   (Degenne's `uniformIntegrable_of_dominated_singleton`);
4. Vitali (`tendsto_Lp_finite_of_tendsto_ae`) upgrades the a.e. convergence
   to L²-norm convergence.

## Main result

* `martingale_ae_tendsto_and_eLpNorm_two_tendsto` — for a martingale `f`
  with `eLpNorm (f n) 2 μ ≤ R` for all `n`: a.e. convergence to
  `ℱ.limitProcess f μ` **and** `eLpNorm (f n − ℱ.limitProcess f μ) 2 μ → 0`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

/-- **L² martingale convergence** (Saporito, Theorem 2.5.1, L² form). A
martingale bounded in L² converges to `ℱ.limitProcess f μ` almost everywhere
**and** in L²-norm. The a.e. half is Mathlib's upcrossing-based convergence;
the L² half is new: this library's Doob L² maximal inequality supplies an L²
envelope dominating every `f n` (`MeasureTheory.LpDominator`), that single
dominator makes the family uniformly integrable in L², and Vitali's convergence
theorem closes the argument. -/
theorem martingale_ae_tendsto_and_eLpNorm_two_tendsto
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {R : ℝ≥0}
    (hf : Martingale f ℱ μ) (hbdd : ∀ n, eLpNorm (f n) 2 μ ≤ R) :
    (∀ᵐ ω ∂μ, Filter.Tendsto (fun n ↦ f n ω) Filter.atTop
      (nhds (ℱ.limitProcess f μ ω))) ∧
    Filter.Tendsto (fun n ↦ eLpNorm (f n - ℱ.limitProcess f μ) 2 μ)
      Filter.atTop (nhds 0) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (f n) μ :=
    ((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable
  -- L¹ bound from the L² bound on a finite measure
  have hbdd1 : ∃ R₁ : ℝ≥0, ∀ n, eLpNorm (f n) 1 μ ≤ (R₁ : ℝ≥0∞) := by
    set c : ℝ≥0∞ := μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
      with hc_def
    have hc_ne : c ≠ ∞ := by
      rw [hc_def]
      exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ _)).ne
    refine ⟨((R : ℝ≥0∞) * c).toNNReal, fun n ↦ ?_⟩
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (p := 1) (q := 2)
      one_le_two (hmeas n)
    rw [ENNReal.coe_toNNReal (by finiteness)]
    exact h.trans (mul_le_mul_left (hbdd n) _)
  obtain ⟨R₁, hR₁⟩ := hbdd1
  have h_ae := hf.submartingale.ae_tendsto_limitProcess hR₁
  -- Doob's L² maximal inequality: the envelope `⨆ n ‖f n‖` is in L² and dominates every `f n`
  have hb (n : ℕ) : eLpNorm (f n) (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal R := by
    simpa using hbdd n
  have hdom : MemLp (LpDominator.dominator f) 2 μ := by
    simpa using LpDominator.dominator_memLp one_lt_two hf hb
  exact ⟨h_ae, tendsto_Lp_finite_of_tendsto_ae one_le_two ENNReal.ofNat_ne_top hmeas
    (hf.submartingale.memLp_limitProcess hbdd)
    (uniformIntegrable_of_dominated_singleton one_le_two ENNReal.ofNat_ne_top hdom hmeas
      (LpDominator.norm_le_dominator one_lt_two hf hb)).unifIntegrable h_ae⟩

end MathFin
