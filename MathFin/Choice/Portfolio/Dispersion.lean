/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Choice.Portfolio.Equicorrelation
public import MathFin.Choice.Portfolio.MarkowitzNAsset
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul

/-!
# Implied correlation and dispersion

An index replicates its components: with weights `w`, component volatilities `σ` and a common
pairwise correlation `ρ`, the replicated index's variance is the equicorrelation quadratic form
`(1 − ρ)·∑ wᵢ²σᵢ² + ρ·(∑ wᵢσᵢ)²` (`indexVar_equicorrelation`). Everything in this module is that
identity and what it lets one solve for.

* The **implied correlation** `impliedCorrelation` is the common correlation that reproduces an
  observed index variance: the equicorrelation identity is affine in `ρ`, so for a squared
  weighted-volatility sum different from the weighted variance sum the observation determines `ρ`
  uniquely (`indexVar_impliedCorrelation`, `impliedCorrelation_unique`). Where the two agree,
  every common correlation reproduces the same variance and the observation identifies none
  (`indexVar_const_of_sq_sum_eq`); there the solved value carries no meaning.
* The **Bossu proxy** `bossuProxy` divides the observed variance by the squared weighted sum of
  volatilities. It is not the implied correlation: for the equicorrelated index at a nonzero
  squared weighted-volatility sum it is the common correlation plus
  `(1 − ρ)·∑ wᵢ²σᵢ² / (∑ wᵢσᵢ)²` (`bossuProxy_eq_add_gap`), the idiosyncratic share, and at
  nonnegative weights and volatilities with `ρ ≤ 1` it sits between the correlation and one
  (`bossuProxy_between`). The
  variance-denominated variant of the proxy that the source prints for the realised correlation
  is a lower bound for it at nonnegative weights summing to one, nonnegative volatilities and a
  nonnegative observed variance, by Jensen's inequality (`jensenProxy_le_bossuProxy`).
* A **correlation swap** pays the pairwise correlations averaged over the pairwise weight
  products `wᵢwⱼ` (an average where the normalisation is positive — nonnegative at nonnegative
  index weights, and the theorem's gate excludes the zero case). The source's §3.2
  payoff normalises over the unordered pairs, half this mass; the factor cancels in the
  average, and both read the common correlation under equicorrelation. Under equicorrelation
  that ratio, read off the dispersion identity as the off-diagonal share of the portfolio
  variance, is the common correlation
  (`realisedCorrelation_equicorrelation`).
* The **dispersion P&L** of holding the components' variance at weight `wᵢ²` against the index
  variance is `ρ·(∑ wᵢ²σᵢ² − (∑ wᵢσᵢ)²)` (`dispersionPnL_eq`): its sign is that of the common
  correlation times the negative of the off-diagonal share. At the flat weights `wᵢ = 1/d` the index
  variance is the diversification form `((1 − ρ)·∑ σᵢ² + ρ·(∑ σᵢ)²)/d²`
  (`indexVar_equicorrelation_flat_weights`), the heterogeneous-volatility generalisation of
  `portfolioVarN_equicorrelation_equal_weights`.

## Main definitions

* `impliedCorrelation`: the common correlation that reproduces an observed index variance.
* `bossuProxy`: the observed index variance over the squared weighted sum of volatilities.

## Main results

* `indexVar_equicorrelation`: the index variance under equicorrelation, the quadratic form
  `(1 − ρ)·∑ wᵢ²σᵢ² + ρ·(∑ wᵢσᵢ)²`.
* `indexVar_impliedCorrelation` / `impliedCorrelation_unique`: the observed variance determines
  the implied correlation, and it reproduces the observation.
* `indexVar_const_of_sq_sum_eq`: at the boundary the observation identifies no correlation.
* `bossuProxy_eq_add_gap` / `bossuProxy_between`: the proxy and its exact gap.
* `jensenProxy_le_bossuProxy`: the variance-denominated proxy understates the Bossu proxy.
* `realisedCorrelation_equicorrelation`: the correlation swap's floating leg under equicorrelation.
* `dispersionPnL_eq`: the dispersion P&L identity.
* `indexVar_equicorrelation_flat_weights`: the flat-weight form.

## References

* [A. Jacquier and S. Slaoui, *Variance Dispersion and Correlation Swaps*][JacquierSlaoui],
  §3.1, §3.2 (the static identities; the dynamic P&L and weighting schemes of §5.1–§5.4 and
  Appendix D are out of scope)

## Tags

implied correlation, dispersion trading, correlation swap, Bossu proxy, equicorrelation,
index variance, MSC 91G10, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **implied correlation** of an index with weights `w` and component volatilities `σ` at
observed index variance `V`: the common correlation that reproduces `V` in the equicorrelation
identity (`indexVar_impliedCorrelation`). It is junk when the squared weighted sum
`∑ wᵢσᵢ` squared equals the weighted variance sum `∑ wᵢ²σᵢ²`: there the observation identifies no
correlation (`indexVar_const_of_sq_sum_eq`). -/
noncomputable def impliedCorrelation (w σ : n → ℝ) (V : ℝ) : ℝ :=
  (V - ∑ i, w i ^ 2 * σ i ^ 2) / ((∑ i, w i * σ i) ^ 2 - ∑ i, w i ^ 2 * σ i ^ 2)

/-- The **Bossu proxy** for the implied correlation: the observed index variance `V` divided by
the squared weighted sum of volatilities. For the equicorrelated index at a nonzero squared
weighted-volatility sum it is the common correlation plus the idiosyncratic share
(`bossuProxy_eq_add_gap`). It is junk when the squared
weighted sum `∑ wᵢσᵢ` vanishes: there the division returns `0`, which is not a correlation
(`bossuProxy_junk_at_zero`). -/
noncomputable def bossuProxy (w σ : n → ℝ) (V : ℝ) : ℝ :=
  V / (∑ i, w i * σ i) ^ 2

omit [DecidableEq n] in
/-- The Bossu proxy's junk corner: at a vanishing weighted-volatility sum the total division
returns `0`, which is not a correlation. -/
private theorem bossuProxy_junk_at_zero (w σ : n → ℝ) (V : ℝ) (h : ∑ i, w i * σ i = 0) :
    bossuProxy w σ V = 0 := by
  rw [bossuProxy, h, zero_pow two_ne_zero, div_zero]

/-- The equicorrelation index variance in the affine form: the weighted variance sum plus the
common correlation times the off-diagonal share. -/
private theorem indexVar_eq_add_mul_sub (w σ : n → ℝ) (ρ : ℝ) :
    portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j)
      = ∑ i, w i ^ 2 * σ i ^ 2 + ρ * ((∑ i, w i * σ i) ^ 2 - ∑ i, w i ^ 2 * σ i ^ 2) := by
  have h : portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j)
      = portfolioVarN univ (fun i ↦ w i * σ i) (equicorrelationMatrix n ρ) := by
    simp only [portfolioVarN]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  rw [h, portfolioVarN_equicorrelation]
  have hsq : ∑ i, (w i * σ i) ^ 2 = ∑ i, w i ^ 2 * σ i ^ 2 :=
    sum_congr rfl fun i _ ↦ by ring
  rw [hsq]
  ring

/-- **Index variance under equicorrelation**: with weights `w`, component volatilities `σ` and a
common pairwise correlation `ρ`, the replicated index's variance is the equicorrelation quadratic
form `(1 − ρ)·∑ wᵢ²σᵢ² + ρ·(∑ wᵢσᵢ)²`. -/
theorem indexVar_equicorrelation (w σ : n → ℝ) (ρ : ℝ) :
    portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j)
      = (1 - ρ) * ∑ i, w i ^ 2 * σ i ^ 2 + ρ * (∑ i, w i * σ i) ^ 2 := by
  rw [indexVar_eq_add_mul_sub]
  ring

/-- **The implied correlation reproduces the observation**: for a squared weighted-volatility
sum different from the weighted variance sum, the equicorrelated index variance at
`impliedCorrelation w σ V` is the observed variance `V`. -/
theorem indexVar_impliedCorrelation (w σ : n → ℝ) (V : ℝ)
    (hSW : (∑ i, w i * σ i) ^ 2 ≠ ∑ i, w i ^ 2 * σ i ^ 2) :
    portfolioVarN univ w
        (fun i j ↦ σ i * σ j * equicorrelationMatrix n (impliedCorrelation w σ V) i j) = V := by
  rw [indexVar_eq_add_mul_sub, impliedCorrelation]
  field_simp
  ring

/-- **The observation determines the implied correlation**: two common correlations reproducing
the same index variance coincide whenever the squared weighted-volatility sum differs from the
weighted variance sum. -/
theorem impliedCorrelation_unique (w σ : n → ℝ) {ρ ρ' : ℝ}
    (h : portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j)
      = portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ' i j))
    (hSW : (∑ i, w i * σ i) ^ 2 ≠ ∑ i, w i ^ 2 * σ i ^ 2) : ρ = ρ' := by
  rw [indexVar_eq_add_mul_sub, indexVar_eq_add_mul_sub] at h
  have hsub : (∑ i, w i * σ i) ^ 2 - ∑ i, w i ^ 2 * σ i ^ 2 ≠ 0 := sub_ne_zero.2 hSW
  have h2 : ((∑ i, w i * σ i) ^ 2 - ∑ i, w i ^ 2 * σ i ^ 2) * ρ
      = ((∑ i, w i * σ i) ^ 2 - ∑ i, w i ^ 2 * σ i ^ 2) * ρ' := by
    linarith [h, mul_comm ρ ((∑ i, w i * σ i) ^ 2 - ∑ i, w i ^ 2 * σ i ^ 2),
      mul_comm ρ' ((∑ i, w i * σ i) ^ 2 - ∑ i, w i ^ 2 * σ i ^ 2)]
  exact mul_left_cancel₀ hsub h2

/-- **The boundary**: when the squared weighted-volatility sum equals the weighted variance sum,
every common correlation reproduces the same index variance, and the observation identifies no
correlation. There `impliedCorrelation` carries no meaning. -/
theorem indexVar_const_of_sq_sum_eq (w σ : n → ℝ) (ρ : ℝ)
    (h : (∑ i, w i * σ i) ^ 2 = ∑ i, w i ^ 2 * σ i ^ 2) :
    portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j)
      = ∑ i, w i ^ 2 * σ i ^ 2 := by
  rw [indexVar_eq_add_mul_sub, h]
  ring

/-- **The Bossu proxy and its exact gap**: for the equicorrelated index at a nonzero squared
weighted-volatility sum, the proxy equals the common correlation plus
`(1 − ρ)·∑ wᵢ²σᵢ² / (∑ wᵢσᵢ)²` — the idiosyncratic share. -/
theorem bossuProxy_eq_add_gap (w σ : n → ℝ) (ρ : ℝ) (hS : (∑ i, w i * σ i) ^ 2 ≠ 0) :
    bossuProxy w σ (portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j))
      = ρ + (1 - ρ) * (∑ i, w i ^ 2 * σ i ^ 2) / (∑ i, w i * σ i) ^ 2 := by
  rw [bossuProxy, indexVar_eq_add_mul_sub]
  have hne : ∑ i, w i * σ i ≠ 0 := fun h => hS (by rw [h]; norm_num)
  field_simp [hne]
  ring

/-- **The proxy sits between the correlation and one**: at nonnegative weights and volatilities,
a nonzero weighted-volatility sum, and a common correlation `ρ ≤ 1`, the Bossu proxy of the
equicorrelated index variance is at least the common correlation and at most one. -/
theorem bossuProxy_between (w σ : n → ℝ) (ρ : ℝ) (hS : (∑ i, w i * σ i) ^ 2 ≠ 0)
    (hρ : ρ ≤ 1) (hw : ∀ i, 0 ≤ w i) (hσ : ∀ i, 0 ≤ σ i) :
    ρ ≤ bossuProxy w σ (portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j))
      ∧ bossuProxy w σ (portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j))
        ≤ 1 := by
  have hWpos : 0 ≤ ∑ i, w i ^ 2 * σ i ^ 2 :=
    sum_nonneg fun i _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hSpos : 0 < (∑ i, w i * σ i) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hS)
  rw [bossuProxy_eq_add_gap w σ ρ hS]
  refine ⟨le_add_of_nonneg_right
    (div_nonneg (mul_nonneg (by linarith) hWpos) hSpos.le), ?_⟩
  have hWS : ∑ i, w i ^ 2 * σ i ^ 2 ≤ (∑ i, w i * σ i) ^ 2 := by
    have hle : ∀ i, w i * σ i ≤ ∑ j, w j * σ j :=
      fun i ↦ Finset.single_le_sum (f := fun j ↦ w j * σ j)
        (fun j _ ↦ mul_nonneg (hw j) (hσ j)) (Finset.mem_univ i)
    have hstep : ∑ i, w i ^ 2 * σ i ^ 2 ≤ ∑ i, (w i * σ i) * ∑ j, w j * σ j := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have h2 : w i ^ 2 * σ i ^ 2 = (w i * σ i) * (w i * σ i) := by ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left (hle i) (mul_nonneg (hw i) (hσ i))
    have hfin : ∑ i, (w i * σ i) * ∑ j, w j * σ j
        = (∑ j, w j * σ j) * ∑ i, w i * σ i := by
      rw [Finset.mul_sum]
      exact sum_congr rfl fun i _ ↦ mul_comm _ _
    calc ∑ i, w i ^ 2 * σ i ^ 2 ≤ ∑ i, (w i * σ i) * ∑ j, w j * σ j := hstep
      _ = (∑ i, w i * σ i) ^ 2 := by rw [hfin, sq, mul_comm]
  have hgap : 0 ≤ (1 - ρ) * ((∑ i, w i * σ i) ^ 2 - ∑ i, w i ^ 2 * σ i ^ 2) :=
    mul_nonneg (by linarith) (sub_nonneg.2 hWS)
  have key : ρ * (∑ i, w i * σ i) ^ 2 + (1 - ρ) * ∑ i, w i ^ 2 * σ i ^ 2
      ≤ (∑ i, w i * σ i) ^ 2 := by
    nlinarith [hρ, hgap]
  have hne : ∑ i, w i * σ i ≠ 0 := fun h => hS (by rw [h]; norm_num)
  have hrw : ρ + ((1 - ρ) * ∑ i, w i ^ 2 * σ i ^ 2) / (∑ i, w i * σ i) ^ 2
      = (ρ * (∑ i, w i * σ i) ^ 2 + (1 - ρ) * ∑ i, w i ^ 2 * σ i ^ 2)
        / (∑ i, w i * σ i) ^ 2 := by
    field_simp [hne]
  rw [hrw, div_le_one hSpos]
  exact key

/-- **The variance-denominated proxy is a lower bound**: at nonnegative weights summing to
one, nonnegative volatilities and a nonnegative observed variance, the observed variance
divided by the weighted variance sum `∑ wᵢσᵢ²` understates the Bossu proxy, which divides by
the squared weighted-volatility sum instead. The source prints this
variant for the realised correlation and notes the bound is Jensen's. When every `wᵢσᵢ`
vanishes both denominators are zero and both sides are the junk `0`; no correlation is at
issue there. -/
theorem jensenProxy_le_bossuProxy (w σ : n → ℝ) (ρ : ℝ) (hflat : ∑ i, w i = 1)
    (hw : ∀ i, 0 ≤ w i) (hσ : ∀ i, 0 ≤ σ i)
    (hV : 0 ≤ portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j)) :
    portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j)
        / (∑ i, w i * σ i ^ 2)
      ≤ bossuProxy w σ
        (portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j)) := by
  have hJ : (∑ i, w i * σ i) ^ 2 ≤ ∑ i, w i * σ i ^ 2 := by
    have h := ConvexOn.map_sum_le (p := σ) (convexOn_pow (𝕜 := ℝ) 2)
      (fun i _ ↦ hw i) hflat (fun i _ ↦ Set.mem_Ici.2 (hσ i))
    simpa using h
  by_cases hS : (∑ i, w i * σ i) ^ 2 = 0
  · have hsum : ∑ j, w j * σ j = 0 := sq_eq_zero_iff.1 hS
    have h0 : ∀ i, w i * σ i = 0 := fun i ↦ le_antisymm (by
      have := Finset.single_le_sum (f := fun j ↦ w j * σ j)
        (fun j _ ↦ mul_nonneg (hw j) (hσ j)) (Finset.mem_univ i)
      rw [hsum] at this
      linarith)
      (mul_nonneg (hw i) (hσ i))
    have hQ : ∑ i, w i * σ i ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ ↦ by
        rw [show w i * σ i ^ 2 = σ i * (w i * σ i) from by ring, h0 i, mul_zero]
    simp only [bossuProxy]
    rw [hQ, hS]
  · refine div_le_div_of_nonneg_left hV
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hS)) ?_
    exact hJ

/-- **The dispersion P&L**: holding the components' variance at weights `wᵢ²` against the index
variance realises `ρ·(∑ wᵢ²σᵢ² − (∑ wᵢσᵢ)²)` — the common correlation times the weighted
variance sum less the squared weighted-volatility sum. -/
theorem dispersionPnL_eq (w σ : n → ℝ) (ρ : ℝ) :
    ∑ i, w i ^ 2 * σ i ^ 2
        - portfolioVarN univ w (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j)
      = ρ * (∑ i, w i ^ 2 * σ i ^ 2 - (∑ i, w i * σ i) ^ 2) := by
  rw [indexVar_eq_add_mul_sub]
  ring

/-- **The flat-weight index variance**: at the equal weights `wᵢ = 1/d` the equicorrelated index
variance is `((1 − ρ)·∑ σᵢ² + ρ·(∑ σᵢ)²)/d²`, the heterogeneous-volatility generalisation of the
equal-weight diversification floor `portfolioVarN_equicorrelation_equal_weights`. -/
theorem indexVar_equicorrelation_flat_weights (σ : n → ℝ) (ρ : ℝ) :
    portfolioVarN univ (fun _ ↦ (Fintype.card n : ℝ)⁻¹)
        (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j)
      = ((1 - ρ) * ∑ i, σ i ^ 2 + ρ * (∑ i, σ i) ^ 2) / (Fintype.card n : ℝ) ^ 2 := by
  have hscale : portfolioVarN univ (fun _ ↦ (Fintype.card n : ℝ)⁻¹)
      (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j)
      = ((Fintype.card n : ℝ)⁻¹) ^ 2 * portfolioVarN univ σ (equicorrelationMatrix n ρ) := by
    have h1 : portfolioVarN univ (fun i ↦ (Fintype.card n : ℝ)⁻¹ * σ i)
        (equicorrelationMatrix n ρ)
        = ((Fintype.card n : ℝ)⁻¹) ^ 2 * portfolioVarN univ σ (equicorrelationMatrix n ρ) :=
      portfolioVarN_smul univ σ (equicorrelationMatrix n ρ) _
    have h2 : portfolioVarN univ (fun i ↦ (Fintype.card n : ℝ)⁻¹ * σ i)
        (equicorrelationMatrix n ρ)
        = portfolioVarN univ (fun _ ↦ (Fintype.card n : ℝ)⁻¹)
            (fun i j ↦ σ i * σ j * equicorrelationMatrix n ρ i j) := by
      simp only [portfolioVarN]
      exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
    rw [← h2, h1]
  rw [hscale, portfolioVarN_equicorrelation]
  have hinv : ((Fintype.card n : ℝ)⁻¹) ^ 2 = 1 / (Fintype.card n : ℝ) ^ 2 := by
    rw [inv_pow, inv_eq_one_div]
  rw [hinv, div_mul_eq_mul_div, one_mul]

/-- **The correlation swap's floating leg under equicorrelation**: the ratio of the
off-diagonal share of the equicorrelated portfolio variance to the off-diagonal weight mass
`∑ wᵢwⱼ` — the pairwise correlations averaged over the weight products where that
normalisation is positive (nonnegative at nonnegative index weights, positive once two or
more components carry weight) — realises the common correlation. The source's printed payoff
normalises over the unordered pairs, half this mass; the factor cancels in the average. A
swap struck at the common correlation therefore pays nothing. -/
theorem realisedCorrelation_equicorrelation (w : n → ℝ) (ρ : ℝ)
    (hW : (∑ i, w i) ^ 2 ≠ ∑ i, w i ^ 2) :
    (portfolioVarN univ w (equicorrelationMatrix n ρ) - ∑ i, w i ^ 2)
        / ((∑ i, w i) ^ 2 - ∑ i, w i ^ 2) = ρ := by
  rw [portfolioVarN_equicorrelation]
  field_simp
  ring

end MathFin
