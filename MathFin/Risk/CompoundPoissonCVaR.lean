/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Analysis.IdentDistribSum
public import MathFin.Probability.Jumps.CompoundPoissonMGF
public import MathFin.Risk.ExpectedShortfall
public import MathFin.Risk.StopLossGap

/-!
# Expected shortfall of a compound-Poisson aggregate loss

The aggregate loss `L = ∑_{i<N} Xᵢ` of the collective risk model has a Poisson(λ) claim count `N`
independent of the claim sizes `Xᵢ`, which are identically distributed and integrable. No
independence between the claims is assumed: Wald's bound does not need it. Its risk is computed
by the Rockafellar–Uryasev theorem, once `L` is known to be integrable:

* `integrable_compoundPoisson` is the Wald-type bound. Each `n`-claim sum obeys
  `𝔼|∑_{i<n} Xᵢ| ≤ n·𝔼|X₀|` (`integral_abs_sum_le_of_identDistrib`, for any finite index set;
  `Probability/Analysis/IdentDistribSum.lean`);
  the count is integrated out with the freezing lemma for a countable variable
  (`Probability/Analysis/IndepFreezing.lean`), against the domination `n·𝔼|X₀|`, integrable
  under the Poisson law because its mean exists (`Probability/Jumps/PoissonPgf.lean`).
* `isLeast_rockafellarUryasev_compoundPoisson` and `expectedShortfall_compoundPoisson_eq` are the
  library's Rockafellar–Uryasev theorem (`Risk/ExpectedShortfall.lean`) for `L`: `ES_α(L)`
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
* `ae_lattice_compoundPoisson` — lattice claims have a lattice aggregate.
* `integral_max_sub_succ_mul_compoundPoisson` — the stop-loss recursion for lattice claims.
* `isLeast_rockafellarUryasev_compoundPoisson_lattice` — `ES_α(L)` is the least objective value over
  the lattice retentions.

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

omit [IsProbabilityMeasure μ] in
/-- **A compound-Poisson aggregate of lattice claims is a lattice variable**: if every claim `Xᵢ`
lies in `hℤ` almost surely, so does `∑_{i<N} Xᵢ`. -/
theorem ae_lattice_compoundPoisson {h : ℝ} (hlat : ∀ i, ∀ᵐ ω ∂μ, ∃ k : ℤ, X i ω = k * h) :
    ∀ᵐ ω ∂μ, ∃ n : ℤ, compoundSum N X ω = n * h := by
  filter_upwards [ae_all_iff.2 hlat] with ω hω
  have (m : ℕ) : ∃ n : ℤ, ∑ i ∈ Finset.range m, X i ω = n * h := by
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨k, hk⟩ := hω m
      exact ⟨n + k, by rw [Finset.sum_range_succ, hn, hk]; push_cast; ring⟩
  exact this (N ω)

section Wald

variable (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (hX : Integrable (X 0) μ)
include hident hX

variable (hN : HasLaw N (poissonMeasure lam) μ) (hNX : IndepFun N (fun ω i ↦ X i ω) μ)
include hN hNX

/-- **The compound-Poisson aggregate loss is integrable** (Wald-type bound). For a claim count
`N ∼ Poisson(λ)` independent of identically distributed integrable claims, `∑_{i<N} Xᵢ` is
integrable. -/
theorem integrable_compoundPoisson :
    Integrable (compoundSum N X) μ := by
  have hgm (n : ℕ) : Measurable fun x : ℕ → ℝ ↦ ∑ i ∈ Finset.range n, x i := by fun_prop
  have hY : AEMeasurable (fun ω i ↦ X i ω) μ := .of_eval fun i ↦ (hident i).aemeasurable_fst
  have hS (n : ℕ) : Integrable (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) μ :=
    integrable_finsetSum _ fun i _ ↦ (hident i).integrable_iff.mpr hX
  refine (integrable_comp_prodMk_iff_of_indepFun (g := fun p ↦ ∑ i ∈ Finset.range p.1, p.2 i)
    hNX hN.aemeasurable hY
    (measurable_from_prod_countable_right hgm).aestronglyMeasurable).mpr
    (integrable_prod_map_of_countable hY hgm hS ?_)
  rw [hN.map_eq]
  refine ((PoissonPgf.integrable_natCast_poissonMeasure lam).mul_const
    (∫ ω, |X 0 ω| ∂μ)).mono' Measurable.of_discrete.aestronglyMeasurable
    (ae_of_all _ fun n ↦ ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
  simp only [Real.norm_eq_abs]
  have hW := integral_abs_sum_le_of_identDistrib (s := Finset.range n) (fun i _ ↦ hident i) hX
  rwa [Finset.card_range] at hW

/-- **The Poisson-mixture expansion of the Rockafellar–Uryasev expectation.** For a claim count
`N ∼ Poisson(λ)` independent of identically distributed integrable claims, `𝔼[(L − c)⁺]` is
the Poisson(λ) average of the `n`-claim expectations `𝔼[(∑_{i<n} Xᵢ − c)⁺]`. -/
theorem integral_max_sub_compoundPoisson (c : ℝ) :
    ∫ ω, max (compoundSum N X ω - c) 0 ∂μ
      = ∫ n, ∫ ω, max (∑ i ∈ Finset.range n, X i ω - c) 0 ∂μ ∂(poissonMeasure lam) := by
  have hS (n : ℕ) : Integrable (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) μ :=
    integrable_finsetSum _ fun i _ ↦ (hident i).integrable_iff.mpr hX
  refine integral_comp_of_hasLaw_of_countable
    (F := fun n x ↦ max (∑ i ∈ Finset.range n, x i - c) 0) (c := fun n ↦ ∫ ω,
      max (∑ i ∈ Finset.range n, X i ω - c) 0 ∂μ) hN
    (.of_eval fun i ↦ (hident i).aemeasurable_fst) hNX
    (fun n ↦ by fun_prop) (fun _ _ ↦ le_max_right _ _)
    (fun n ↦ ((hS n).sub (integrable_const c)).pos_part)
    (fun _ ↦ rfl) ?_
  refine (((PoissonPgf.integrable_natCast_poissonMeasure lam).mul_const
    (∫ ω, |X 0 ω| ∂μ)).add (integrable_const |c|)).mono'
    Measurable.of_discrete.aestronglyMeasurable (ae_of_all _ fun n ↦ ?_)
  have h0 : 0 ≤ ∫ ω, max (∑ i ∈ Finset.range n, X i ω - c) 0 ∂μ :=
    integral_nonneg fun _ ↦ le_max_right _ _
  rw [Real.norm_of_nonneg h0]
  calc ∫ ω, max (∑ i ∈ Finset.range n, X i ω - c) 0 ∂μ
      ≤ ∫ ω, (|∑ i ∈ Finset.range n, X i ω| + |c|) ∂μ :=
        integral_mono (((hS n).sub (integrable_const c)).pos_part)
          ((hS n).abs.add (integrable_const _)) fun ω ↦
          max_le (by linarith [le_abs_self (∑ i ∈ Finset.range n, X i ω), neg_le_abs c])
            (by positivity)
    _ ≤ n * ∫ ω, |X 0 ω| ∂μ + |c| := by
        rw [integral_add (hS n).abs (integrable_const _),
          integral_const, probReal_univ, one_smul]
        have hW := integral_abs_sum_le_of_identDistrib (s := Finset.range n)
          (fun i _ ↦ hident i) hX
        rw [Finset.card_range] at hW
        exact add_le_add_left hW _
    _ ≤ _ := le_rfl

/-- The Poisson-mixture expansion as a series over the claim count:
`𝔼[(L − c)⁺] = ∑ₙ P(N = n)·𝔼[(∑_{i<n} Xᵢ − c)⁺]`, with `P(N = n) = e^{−λ} λⁿ / n!`. -/
theorem integral_max_sub_compoundPoisson_eq_tsum (c : ℝ) :
    ∫ ω, max (compoundSum N X ω - c) 0 ∂μ
      = ∑' n : ℕ, Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ n / n.factorial *
          ∫ ω, max (∑ i ∈ Finset.range n, X i ω - c) 0 ∂μ := by
  rw [integral_max_sub_compoundPoisson hident hX hN hNX, integral_poissonMeasure]
  rfl

/-- **The Rockafellar–Uryasev theorem for the compound-Poisson loss**: for `α ∈ (0, 1)`,
`ES_α(L)` is the least value of `c ↦ c + (1 − α)⁻¹ 𝔼[(L − c)⁺]`. -/
theorem isLeast_rockafellarUryasev_compoundPoisson {α : ℝ} (hα : α ∈ Ioo 0 1) :
    IsLeast (range (rockafellarUryasev (compoundSum N X) μ α))
      (expectedShortfall (compoundSum N X) μ α) :=
  isLeast_rockafellarUryasev (integrable_compoundPoisson hident hX hN hNX) hα

/-- **The minimizer is the value-at-risk**: for `α ∈ (0, 1)`,
`ES_α(L) = VaR_α(L) + (1 − α)⁻¹ 𝔼[(L − VaR_α(L))⁺]`. -/
theorem expectedShortfall_compoundPoisson_eq {α : ℝ} (hα : α ∈ Ioo 0 1) :
    expectedShortfall (compoundSum N X) μ α
      = valueAtRisk (compoundSum N X) μ α
        + (1 - α)⁻¹ * ∫ ω, max (compoundSum N X ω
            - valueAtRisk (compoundSum N X) μ α) 0 ∂μ :=
  (rockafellarUryasev_valueAtRisk (integrable_compoundPoisson hident hX hN hNX) hα).symm

/-- **The stop-loss recursion of a compound-Poisson aggregate of lattice claims.** If the claims
lie in `hℤ` almost surely, `0 ≤ h`, then for every integer retention level `j`,
`𝔼[(L − (j + 1)h)⁺] = 𝔼[(L − jh)⁺] − h · P(L > jh)`
(`integral_max_sub_succ_mul_of_lattice`, for the integrable aggregate `L`). -/
theorem integral_max_sub_succ_mul_compoundPoisson {h : ℝ} (hh : 0 ≤ h)
    (hlat : ∀ i, ∀ᵐ ω ∂μ, ∃ k : ℤ, X i ω = k * h) (j : ℤ) :
    ∫ ω, max (compoundSum N X ω - (j + 1) * h) 0 ∂μ =
      ∫ ω, max (compoundSum N X ω - j * h) 0 ∂μ - h * μ.real {ω | j * h < compoundSum N X ω} :=
  integral_max_sub_succ_mul_of_lattice (integrable_compoundPoisson hident hX hN hNX).aemeasurable
    (integrable_compoundPoisson hident hX hN hNX) hh (ae_lattice_compoundPoisson hlat) j

/-- **Expected shortfall of a compound-Poisson aggregate of lattice claims is the least
Rockafellar–Uryasev value on the lattice**: if the claims lie in `hℤ` almost surely with `h > 0`
and `α ∈ (0, 1)`, then `ES_α(L)` is the least of `c + (1 − α)⁻¹ 𝔼[(L − c)⁺]` over `c = jh`, the
values the stop-loss recursion computes (`isLeast_rockafellarUryasev_lattice`). -/
theorem isLeast_rockafellarUryasev_compoundPoisson_lattice {h : ℝ} (hh : 0 < h)
    (hlat : ∀ i, ∀ᵐ ω ∂μ, ∃ k : ℤ, X i ω = k * h) {α : ℝ} (hα : α ∈ Ioo 0 1) :
    IsLeast (range fun j : ℤ ↦
        rockafellarUryasev (compoundSum N X) μ α (j * h))
      (expectedShortfall (compoundSum N X) μ α) :=
  isLeast_rockafellarUryasev_lattice (integrable_compoundPoisson hident hX hN hNX).aemeasurable
    (integrable_compoundPoisson hident hX hN hNX) hh (ae_lattice_compoundPoisson hlat) hα

end Wald

end MathFin
