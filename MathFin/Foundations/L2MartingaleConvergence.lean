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
2. by monotone convergence the all-time envelope `G ω = ⨆ n ‖f n ω‖ₑ` is
   square-integrable, and it dominates every `f n`;
3. a single L² dominator makes the family uniformly integrable in L²
   (Chebyshev shrinks the tail sets `{C ≤ ‖f n‖}` uniformly; absolute
   continuity of the indicator seminorm, `MemLp.eLpNorm_indicator_le`,
   converts small measure into small L² mass);
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

namespace L2MartingaleConvergence

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {R : ℝ≥0}

/-- The real-valued envelope, in `L²` and dominating all `f n`. The `p = 2` case of
`MeasureTheory.LpDominator.dominator`: Doob's maximal inequality plus monotone convergence
give an all-time envelope `⨆ₙ ‖fₙ‖` that is itself `L²` and dominates every `fₙ`. -/
private lemma exists_dominator [IsFiniteMeasure μ]
    (hf : Martingale f ℱ μ) (hmeas : ∀ n, Measurable (f n))
    (hbdd : ∀ n, eLpNorm (f n) 2 μ ≤ R) :
    ∃ g : Ω → ℝ, Measurable g ∧ MemLp g 2 μ ∧ ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ g ω := by
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by simp
  have hb : ∀ n, eLpNorm (f n) (ENNReal.ofReal (2 : ℝ)) μ ≤ ENNReal.ofReal (R : ℝ) := by
    intro n; rw [htwo, ENNReal.ofReal_coe_nnreal]; exact hbdd n
  refine ⟨MeasureTheory.LpDominator.dominator f,
    MeasureTheory.LpDominator.measurable_dominator hf, ?_,
    fun n ↦ MeasureTheory.LpDominator.norm_le_dominator one_lt_two hf hb n⟩
  simpa only [htwo] using
    MeasureTheory.LpDominator.dominator_memLp (p := (2 : ℝ)) one_lt_two hf hb

/-- A single L² dominator makes the family uniformly integrable in L² — this is
Degenne's `uniformIntegrable_of_dominated_singleton` projected to `UnifIntegrable`
via `.unifIntegrable`, superseding a hand-rolled Chebyshev tail argument. -/
private lemma unifIntegrable_of_dominator [IsFiniteMeasure μ]
    (hmeas : ∀ n, Measurable (f n)) {g : Ω → ℝ} (_hgm : Measurable g)
    (hg : MemLp g 2 μ) (hdom : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ g ω) :
    UnifIntegrable f 2 μ :=
  (uniformIntegrable_of_dominated_singleton one_le_two (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    hg (fun n ↦ (hmeas n).aestronglyMeasurable) hdom).unifIntegrable

end L2MartingaleConvergence

open L2MartingaleConvergence in
/-- **L² martingale convergence** (Saporito, Theorem 2.5.1, L² form). A
martingale bounded in L² converges to `ℱ.limitProcess f μ` almost everywhere
**and** in L²-norm. The a.e. half is Mathlib's upcrossing-based convergence;
the L² half is new: uniform integrability in L² is produced by this library's
Doob L² maximal inequality (envelope dominator + Chebyshev), and Vitali's
convergence theorem closes the argument. -/
theorem martingale_ae_tendsto_and_eLpNorm_two_tendsto
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {R : ℝ≥0}
    (hf : Martingale f ℱ μ) (hbdd : ∀ n, eLpNorm (f n) 2 μ ≤ R) :
    (∀ᵐ ω ∂μ, Filter.Tendsto (fun n ↦ f n ω) Filter.atTop
      (nhds (ℱ.limitProcess f μ ω))) ∧
    Filter.Tendsto (fun n ↦ eLpNorm (f n - ℱ.limitProcess f μ) 2 μ)
      Filter.atTop (nhds 0) := by
  have hmeas : ∀ n, Measurable (f n) := fun n ↦
    ((hf.stronglyMeasurable n).mono (ℱ.le n)).measurable
  -- L¹ bound from the L² bound on a finite measure
  have hbdd1 : ∃ R₁ : ℝ≥0, ∀ n, eLpNorm (f n) 1 μ ≤ (R₁ : ℝ≥0∞) := by
    set c : ℝ≥0∞ := μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
      with hc_def
    have hc_ne : c ≠ ∞ := by
      rw [hc_def]
      exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ _)).ne
    refine ⟨((R : ℝ≥0∞) * c).toNNReal, fun n ↦ ?_⟩
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (p := 1) (q := 2)
      one_le_two (hmeas n).aestronglyMeasurable
    rw [ENNReal.coe_toNNReal (by finiteness)]
    exact h.trans (mul_le_mul_left (hbdd n) _)
  obtain ⟨R₁, hR₁⟩ := hbdd1
  have h_ae := hf.submartingale.ae_tendsto_limitProcess hR₁
  have h_memLp : MemLp (ℱ.limitProcess f μ) 2 μ :=
    hf.submartingale.memLp_limitProcess hbdd
  obtain ⟨g, hgm, hg, hdom⟩ := exists_dominator hf hmeas hbdd
  exact ⟨h_ae, tendsto_Lp_finite_of_tendsto_ae one_le_two (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun n ↦ (hmeas n).aestronglyMeasurable) h_memLp
    (unifIntegrable_of_dominator hmeas hgm hg hdom) h_ae⟩

end MathFin
