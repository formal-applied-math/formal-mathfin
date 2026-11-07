/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Actuarial.CompoundPoissonMGF
public import MathFin.RiskMeasures.ExpectedShortfall

/-!
# Expected shortfall of a compound-Poisson aggregate loss

The aggregate loss `L = ∑_{i<N} Xᵢ` of the collective risk model has a Poisson(λ) claim count `N`
independent of i.i.d. integrable claim sizes `Xᵢ`. Its risk is computed by the
Rockafellar–Uryasev theorem, once `L` is known to be integrable:

* `integrable_compoundPoisson` is the Wald-type bound. The count is integrated out with the
  freezing lemma for a countable variable (`Foundations/IndepFreezing.lean`), and the `n`-claim
  sums are dominated by `𝔼|X₀|·2ⁿ`, integrable against the Poisson law
  (`Foundations/PoissonPgf.lean`).
* `isLeast_rockafellarUryasev_compoundPoisson` and `expectedShortfall_compoundPoisson_eq` are the
  library's Rockafellar–Uryasev theorem (`RiskMeasures/ExpectedShortfall.lean`) for `L`: `ES_α(L)`
  is the least value of `c ↦ c + (1 − α)⁻¹ 𝔼[(L − c)⁺]`, attained at `c = VaR_α(L)`.
* `integral_max_sub_compoundPoisson` is the Poisson-mixture expansion of the objective's
  expectation, `𝔼[(L − c)⁺] = ∫ n, 𝔼[(∑_{i<n} Xᵢ − c)⁺] dPoisson(λ)`, so the objective is
  computed from the laws of the fixed-size sums alone.

## Main results

* `integrable_compoundPoisson` — the aggregate loss is integrable.
* `isLeast_rockafellarUryasev_compoundPoisson` — `ES_α(L)` is the least value of the objective.
* `expectedShortfall_compoundPoisson_eq` — `ES_α(L) = VaR_α(L) + (1 − α)⁻¹ 𝔼[(L − VaR_α(L))⁺]`.
* `integral_max_sub_compoundPoisson` — the Poisson-mixture expansion of `𝔼[(L − c)⁺]`.
* `integral_max_sub_compoundPoisson_eq_tsum` — the same as a series over the claim count.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Section 8.2
* [Rockafellar and Uryasev (2000)][RockafellarUryasev2000]
* [Rockafellar and Uryasev (2002)][RockafellarUryasev2002]
* [Klugman, Panjer and Willmot, *Loss Models*][KlugmanPanjerWillmot], Thm 9.3

## Tags

compound Poisson, aggregate loss, expected shortfall, conditional VaR, Rockafellar-Uryasev,
Wald bound, Poisson mixture, collective risk model, MSC 91G70, MSC 60G50, JEL G22, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {lam : ℝ≥0} {N : Ω → ℕ} {X : ℕ → Ω → ℝ}

private lemma natCast_le_two_pow (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  exact_mod_cast (Nat.lt_two_pow_self (n := n)).le

section Wald

variable (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hX : Integrable (X 0) μ)
include hident hX

private lemma integrable_range_sum (n : ℕ) :
    Integrable (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) μ :=
  integrable_finset_sum _ fun i _ ↦ (hident i).integrable_iff.mpr hX

/-- Wald's bound for a fixed number of claims: `𝔼|∑_{i<n} Xᵢ| ≤ n·𝔼|X₀|`. -/
private lemma integral_abs_range_sum_le (n : ℕ) :
    ∫ ω, |∑ i ∈ Finset.range n, X i ω| ∂μ ≤ n * ∫ ω, |X 0 ω| ∂μ := by
  have hi (i : ℕ) : Integrable (fun ω ↦ |X i ω|) μ := ((hident i).integrable_iff.mpr hX).abs
  calc ∫ ω, |∑ i ∈ Finset.range n, X i ω| ∂μ
      ≤ ∫ ω, ∑ i ∈ Finset.range n, |X i ω| ∂μ :=
        integral_mono (integrable_range_sum hident hX n).abs
          (integrable_finset_sum _ fun i _ ↦ hi i) fun ω ↦ Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range n, ∫ ω, |X i ω| ∂μ := integral_finset_sum _ fun i _ ↦ hi i
    _ = n * ∫ ω, |X 0 ω| ∂μ := by
        have h (i : ℕ) : ∫ ω, |X i ω| ∂μ = ∫ ω, |X 0 ω| ∂μ :=
          ((hident i).comp continuous_abs.measurable).integral_eq
        simp [h]

omit hX in
private lemma aemeasurable_claims : AEMeasurable (fun ω i ↦ X i ω) μ :=
  .of_eval fun i ↦ (hident i).aemeasurable_fst

variable (hN : HasLaw N (poissonMeasure lam) μ) (hNX : IndepFun N (fun ω i ↦ X i ω) μ)
include hN hNX

/-- **The compound-Poisson aggregate loss is integrable** (Wald-type bound). For a claim count
`N ∼ Poisson(λ)` independent of i.i.d. integrable claims, `∑_{i<N} Xᵢ` is integrable. -/
theorem integrable_compoundPoisson :
    Integrable (fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω) μ := by
  have hgm (n : ℕ) : Measurable fun x : ℕ → ℝ ↦ ∑ i ∈ Finset.range n, x i := by fun_prop
  have hY := aemeasurable_claims hident
  refine (integrable_comp_prodMk_iff_of_indepFun (g := fun p ↦ ∑ i ∈ Finset.range p.1, p.2 i)
    hNX hN.aemeasurable hY
    (measurable_from_prod_countable_right hgm).aestronglyMeasurable).mpr
    (integrable_prod_map_of_countable hY hgm (integrable_range_sum hident hX) ?_)
  rw [hN.map_eq]
  have hC : 0 ≤ ∫ ω, |X 0 ω| ∂μ := integral_nonneg fun _ ↦ abs_nonneg _
  refine ((PoissonPgf.integrable_pow_poissonMeasure lam 2).const_mul (∫ ω, |X 0 ω| ∂μ)).mono'
    Measurable.of_discrete.aestronglyMeasurable (ae_of_all _ fun n ↦ ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
  simp only [Real.norm_eq_abs]
  exact (integral_abs_range_sum_le hident hX n).trans <| by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left (natCast_le_two_pow n) hC

/-- **The Poisson-mixture expansion of the Rockafellar–Uryasev expectation.** For a claim count
`N ∼ Poisson(λ)` independent of i.i.d. integrable claims, `𝔼[(L − c)⁺]` is the Poisson(λ)
average of the `n`-claim expectations `𝔼[(∑_{i<n} Xᵢ − c)⁺]`. -/
theorem integral_max_sub_compoundPoisson (c : ℝ) :
    ∫ ω, max (∑ i ∈ Finset.range (N ω), X i ω - c) 0 ∂μ
      = ∫ n, ∫ ω, max (∑ i ∈ Finset.range n, X i ω - c) 0 ∂μ ∂(poissonMeasure lam) := by
  have hC : 0 ≤ ∫ ω, |X 0 ω| ∂μ := integral_nonneg fun _ ↦ abs_nonneg _
  refine integral_comp_of_hasLaw_of_countable
    (F := fun n x ↦ max (∑ i ∈ Finset.range n, x i - c) 0) (c := fun n ↦ ∫ ω,
      max (∑ i ∈ Finset.range n, X i ω - c) 0 ∂μ) hN (aemeasurable_claims hident) hNX
    (fun n ↦ by fun_prop) (fun _ _ ↦ le_max_right _ _)
    (fun n ↦ ((integrable_range_sum hident hX n).sub (integrable_const c)).pos_part)
    (fun _ ↦ rfl) ?_
  refine ((PoissonPgf.integrable_pow_poissonMeasure lam 2).const_mul
    (∫ ω, |X 0 ω| ∂μ + |c|)).mono' Measurable.of_discrete.aestronglyMeasurable
    (ae_of_all _ fun n ↦ ?_)
  have hn := natCast_le_two_pow n
  have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
  rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ le_max_right _ _)]
  calc ∫ ω, max (∑ i ∈ Finset.range n, X i ω - c) 0 ∂μ
      ≤ ∫ ω, (|∑ i ∈ Finset.range n, X i ω| + |c|) ∂μ :=
        integral_mono (((integrable_range_sum hident hX n).sub (integrable_const c)).pos_part)
          ((integrable_range_sum hident hX n).abs.add (integrable_const _)) fun ω ↦
          max_le (by linarith [le_abs_self (∑ i ∈ Finset.range n, X i ω), neg_le_abs c])
            (by positivity)
    _ ≤ n * ∫ ω, |X 0 ω| ∂μ + |c| := by
        rw [integral_add (integrable_range_sum hident hX n).abs (integrable_const _),
          integral_const, probReal_univ, one_smul]
        exact add_le_add_left (integral_abs_range_sum_le hident hX n) _
    _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_right hn hC,
          mul_le_mul_of_nonneg_left h1 (abs_nonneg c)]

/-- The Poisson-mixture expansion as a series over the claim count:
`𝔼[(L − c)⁺] = ∑ₙ P(N = n)·𝔼[(∑_{i<n} Xᵢ − c)⁺]`, with `P(N = n) = e^{−λ} λⁿ / n!`. -/
theorem integral_max_sub_compoundPoisson_eq_tsum (c : ℝ) :
    ∫ ω, max (∑ i ∈ Finset.range (N ω), X i ω - c) 0 ∂μ
      = ∑' n : ℕ, Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / n.factorial *
          ∫ ω, max (∑ i ∈ Finset.range n, X i ω - c) 0 ∂μ := by
  rw [integral_max_sub_compoundPoisson hident hX hN hNX, integral_poissonMeasure]
  rfl

/-- **The Rockafellar–Uryasev theorem for the compound-Poisson loss**: for `α ∈ (0, 1)`,
`ES_α(L)` is the least value of `c ↦ c + (1 − α)⁻¹ 𝔼[(L − c)⁺]`. -/
theorem isLeast_rockafellarUryasev_compoundPoisson {α : ℝ} (hα : α ∈ Ioo 0 1) :
    IsLeast (range (rockafellarUryasev (fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω) μ α))
      (expectedShortfall (fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω) μ α) :=
  isLeast_rockafellarUryasev (integrable_compoundPoisson hident hX hN hNX) hα

/-- **The minimizer is the value-at-risk**: for `α ∈ (0, 1)`,
`ES_α(L) = VaR_α(L) + (1 − α)⁻¹ 𝔼[(L − VaR_α(L))⁺]`. -/
theorem expectedShortfall_compoundPoisson_eq {α : ℝ} (hα : α ∈ Ioo 0 1) :
    expectedShortfall (fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω) μ α
      = valueAtRisk (fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω) μ α
        + (1 - α)⁻¹ * ∫ ω, max (∑ i ∈ Finset.range (N ω), X i ω
            - valueAtRisk (fun ω ↦ ∑ i ∈ Finset.range (N ω), X i ω) μ α) 0 ∂μ :=
  (rockafellarUryasev_valueAtRisk (integrable_compoundPoisson hident hX hN hNX) hα).symm

end Wald

end MathFin
