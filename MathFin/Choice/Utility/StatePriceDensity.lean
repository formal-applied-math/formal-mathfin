/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Choice.Utility.VonNeumannMorgenstern
public import MathFin.Pricing.FTAP.FTAPMultiState
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Marginal utility is a state-price density

An expected-utility maximiser in a finite-state market prices every traded asset with her
marginal utility. The market is a payoff matrix `A : Fin M → Fin N → ℝ` (`A k ω` is what asset `k`
pays in state `ω`) and a price vector `pr : Fin M → ℝ`. A portfolio `θ : Fin M → ℝ` costs
`∑ k, θ k * pr k` and pays `∑ k, θ k * A k ω` in state `ω`. The agent has the probability weights
`p ω > 0`, a utility `u : ℝ → ℝ` and the budget `w₀`.

If a portfolio `θ` is a local maximum of `∑ ω, p ω * u (payoff θ ω)` on the budget set
`{θ' | cost θ' = w₀}` (Fermat applied to every budget-neutral direction `d`, `cost d = 0`), the
vector `(p ω * u'(W ω))ω` annihilates the payoff of every such `d`; hence it is proportional to
the price vector in the sense that `∑ ω, p ω * u'(W ω) * A k ω = μ * pr k` for every asset `k`,
with `μ * w₀ = ∑ ω, p ω * u'(W ω) * W ω`. When wealth `W` and the budget `w₀` are positive and
`u' > 0` at the optimum, `μ > 0`, so

  `q ω = p ω * u'(W ω) / μ`

is a strictly positive state-price vector pricing every asset (`statePricePricing`), and after
the normalisation by `∑ q` it is an equivalent martingale measure for the excess returns
(`HasEMMMultiState`). For the logarithmic utility `u' = x⁻¹`, `μ = 1 / w₀` and the density is
`w₀ * p ω / W ω`: the growth-optimal portfolio is the numéraire (Long 1990), and the Kelly
two-state market of `Choice/Performance/KellyNumeraire` is its instance.

Concavity of `u` is not used: the first-order condition is necessary for any local maximum.
Differentiability of `u` at the optimal wealths is implied by `deriv u (W ω) > 0`.

## Main definitions

* `portfolioPayoff`: the payoff `∑ k, θ k * A k ω` of a portfolio in state `ω`.
* `portfolioCost`: the cost `∑ k, θ k * pr k` of a portfolio.
* `portfolioUtility`: the expected utility `∑ ω, p ω * u (portfolioPayoff A θ ω)`.

## Main results

* `hasDerivAt_portfolioUtility_line`: the derivative of the expected utility along a line of
  portfolios is `∑ ω, p ω * u'(W ω) * (payoff of d)`.
* `sum_marginalUtility_mul_payoff_eq_zero_of_isLocalMaxOn`: at a local maximum on the budget
  set the marginal-utility vector annihilates the payoff of every budget-neutral direction.
* `exists_pos_smul_eq_of_stationary`: the marginal-utility vector prices every asset up to a
  factor `μ > 0`.
* `exists_statePrices_of_isLocalMaxOn`: marginal utility, normalised, is a strictly positive
  state-price vector.
* `exists_hasEMMMultiState_of_isLocalMaxOn`: the optimum defines a pricing measure.
* `exists_isEMM_of_isLocalMaxOn`: the same as a measure `Q` with `OnePeriodVector.IsEMM`.
* `hasEMMMultiState_of_statePrices`: strictly positive state prices give `HasEMMMultiState`.
* `logUtility_statePrices_of_stationary`: for `u = log`, the density is `w₀ * p / W`.

## References

* [Long (1990)][Long1990]
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §1.2

## Tags

state-price density, stochastic discount factor, marginal utility, first-order condition,
expected utility, pricing kernel, growth-optimal portfolio, JEL D81, JEL G12, MSC 91B16,
MSC 91G10
-/

@[expose] public section

namespace MathFin

open MeasureTheory Filter Topology

variable {N M : ℕ}

/-- The payoff of the portfolio `θ` in state `ω`, in the market with payoff matrix `A`. -/
def portfolioPayoff (A : Fin M → Fin N → ℝ) (θ : Fin M → ℝ) (ω : Fin N) : ℝ :=
  ∑ k, θ k * A k ω

/-- The cost of the portfolio `θ` at the prices `pr`. -/
def portfolioCost (pr θ : Fin M → ℝ) : ℝ :=
  ∑ k, θ k * pr k

/-- The expected utility `∑ ω, p ω * u (W ω)` of the terminal wealth `W = portfolioPayoff A θ`. -/
def portfolioUtility (p : Fin N → ℝ) (u : ℝ → ℝ) (A : Fin M → Fin N → ℝ) (θ : Fin M → ℝ) : ℝ :=
  expectedUtility Finset.univ (fun ω ↦ u (portfolioPayoff A θ ω)) p

lemma portfolioPayoff_add_smul (A : Fin M → Fin N → ℝ) (θ d : Fin M → ℝ) (t : ℝ) (ω : Fin N) :
    portfolioPayoff A (θ + t • d) ω = portfolioPayoff A θ ω + t * portfolioPayoff A d ω := by
  unfold portfolioPayoff
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma portfolioCost_add_smul (pr θ d : Fin M → ℝ) (t : ℝ) :
    portfolioCost pr (θ + t • d) = portfolioCost pr θ + t * portfolioCost pr d := by
  unfold portfolioCost
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- A weighted sum of payoffs is the portfolio-weighted sum of the weighted asset payoffs. -/
lemma sum_mul_portfolioPayoff (l : Fin N → ℝ) (A : Fin M → Fin N → ℝ) (d : Fin M → ℝ) :
    ∑ ω, l ω * portfolioPayoff A d ω = ∑ k, d k * ∑ ω, l ω * A k ω := by
  simp only [portfolioPayoff, Finset.mul_sum]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun ω _ ↦ by ring)

/-- **The derivative of expected utility along a line of portfolios**: at `θ`, in the direction
`d`, it is the marginal-utility-weighted payoff `∑ ω, p ω * u'(W ω) * (payoff of d)`. -/
theorem hasDerivAt_portfolioUtility_line (p : Fin N → ℝ) (u : ℝ → ℝ) (A : Fin M → Fin N → ℝ)
    (θ d : Fin M → ℝ) (hu : ∀ ω, DifferentiableAt ℝ u (portfolioPayoff A θ ω)) :
    HasDerivAt (fun t : ℝ ↦ portfolioUtility p u A (θ + t • d))
      (∑ ω, p ω * deriv u (portfolioPayoff A θ ω) * portfolioPayoff A d ω) 0 := by
  have hfun : (fun t : ℝ ↦ portfolioUtility p u A (θ + t • d)) =
      fun t ↦ ∑ ω, p ω * u (portfolioPayoff A θ ω + t * portfolioPayoff A d ω) := by
    funext t
    simp only [portfolioUtility, expectedUtility, portfolioPayoff_add_smul]
  rw [hfun]
  refine HasDerivAt.fun_sum fun ω _ ↦ ?_
  have hin : HasDerivAt (fun t : ℝ ↦ portfolioPayoff A θ ω + t * portfolioPayoff A d ω)
      (portfolioPayoff A d ω) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const (portfolioPayoff A d ω)).const_add
      (portfolioPayoff A θ ω)
  exact ((((hu ω).hasDerivAt).comp_of_eq (x := 0) hin (by simp)).const_mul (p ω)).congr_deriv
    (by ring)

/-- **Fermat for the budget-constrained problem.** If `θ` is a local maximum of the expected
utility on the budget set `{θ' | cost θ' = w₀}`, then for every budget-neutral direction `d`
(`cost d = 0`) the marginal-utility vector `(p ω * u'(W ω))ω` annihilates the payoff of `d`. -/
theorem sum_marginalUtility_mul_payoff_eq_zero_of_isLocalMaxOn {p : Fin N → ℝ} {u : ℝ → ℝ}
    {A : Fin M → Fin N → ℝ} {pr : Fin M → ℝ} {w₀ : ℝ} {θ : Fin M → ℝ}
    (hmax : IsLocalMaxOn (portfolioUtility p u A) {θ' | portfolioCost pr θ' = w₀} θ)
    (hθ : portfolioCost pr θ = w₀) (hu : ∀ ω, DifferentiableAt ℝ u (portfolioPayoff A θ ω))
    {d : Fin M → ℝ} (hd : portfolioCost pr d = 0) :
    ∑ ω, p ω * deriv u (portfolioPayoff A θ ω) * portfolioPayoff A d ω = 0 := by
  have h0 : ∀ᶠ θ' in 𝓝[{θ' | portfolioCost pr θ' = w₀}] θ,
      portfolioUtility p u A θ' ≤ portfolioUtility p u A θ := hmax
  have h1 := eventually_nhdsWithin_iff.mp h0
  have hc : Continuous fun t : ℝ ↦ θ + t • d := by fun_prop
  have ht : Tendsto (fun t : ℝ ↦ θ + t • d) (𝓝 0) (𝓝 θ) := by
    simpa using hc.tendsto 0
  have hmem (t : ℝ) : θ + t • d ∈ {θ' | portfolioCost pr θ' = w₀} := by
    show portfolioCost pr (θ + t • d) = w₀
    rw [portfolioCost_add_smul, hθ, hd, mul_zero, add_zero]
  have hg : IsLocalMax (fun t : ℝ ↦ portfolioUtility p u A (θ + t • d)) 0 := by
    unfold IsLocalMax IsMaxFilter
    filter_upwards [ht.eventually h1] with t ht'
    simpa using ht' (hmem t)
  exact hg.hasDerivAt_eq_zero (hasDerivAt_portfolioUtility_line p u A θ d hu)

/-- A vector `l` that annihilates the payoff of every budget-neutral direction is proportional to
the prices: `∑ ω, l ω * A k ω = μ * pr k` for every asset `k`, as soon as some asset has a nonzero
price. -/
lemma exists_eq_smul_of_forall_cost_eq_zero {A : Fin M → Fin N → ℝ} {pr : Fin M → ℝ}
    (l : Fin N → ℝ) (h : ∀ d, portfolioCost pr d = 0 → ∑ ω, l ω * portfolioPayoff A d ω = 0)
    {k₀ : Fin M} (hk₀ : pr k₀ ≠ 0) : ∃ μ : ℝ, ∀ k, ∑ ω, l ω * A k ω = μ * pr k := by
  refine ⟨(∑ ω, l ω * A k₀ ω) / pr k₀, fun k ↦ ?_⟩
  have hcost : portfolioCost pr
      (fun j ↦ (if j = k then pr k₀ else 0) - (if j = k₀ then pr k else 0)) = 0 := by
    simp [portfolioCost, sub_mul, Finset.sum_sub_distrib, ite_mul] <;> ring
  have key : pr k₀ * ∑ ω, l ω * A k ω - pr k * ∑ ω, l ω * A k₀ ω = 0 := by
    have := h _ hcost
    rw [sum_mul_portfolioPayoff] at this
    simpa [sub_mul, Finset.sum_sub_distrib, ite_mul] using this
  rw [div_mul_eq_mul_div, eq_div_iff hk₀]
  linarith

/-- **The marginal-utility vector prices every asset.** Suppose the portfolio `θ` costs `w₀ > 0`,
has positive payoffs `W` and positive marginal utility `u' (W ω) > 0`, and is stationary: the
marginal-utility vector annihilates the payoff of every budget-neutral direction. Then there is
`μ > 0` with `μ * w₀ = ∑ ω, p ω * u'(W ω) * W ω` and
`∑ ω, p ω * u'(W ω) * A k ω = μ * pr k` for every asset `k`. -/
theorem exists_pos_smul_eq_of_stationary [NeZero N] {p : Fin N → ℝ} {u : ℝ → ℝ}
    {A : Fin M → Fin N → ℝ} {pr : Fin M → ℝ} {w₀ : ℝ} {θ : Fin M → ℝ}
    (hθ : portfolioCost pr θ = w₀) (hw₀ : 0 < w₀) (hp : ∀ ω, 0 < p ω)
    (hW : ∀ ω, 0 < portfolioPayoff A θ ω) (hu : ∀ ω, 0 < deriv u (portfolioPayoff A θ ω))
    (hfoc : ∀ d, portfolioCost pr d = 0 →
      ∑ ω, p ω * deriv u (portfolioPayoff A θ ω) * portfolioPayoff A d ω = 0) :
    ∃ μ : ℝ, 0 < μ ∧
      μ * w₀ = ∑ ω, p ω * deriv u (portfolioPayoff A θ ω) * portfolioPayoff A θ ω ∧
      ∀ k, ∑ ω, p ω * deriv u (portfolioPayoff A θ ω) * A k ω = μ * pr k := by
  have hne : ∑ k, θ k * pr k ≠ 0 := by
    have : portfolioCost pr θ ≠ 0 := by rw [hθ]; exact hw₀.ne'
    exact this
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨μ, hμ⟩ := exists_eq_smul_of_forall_cost_eq_zero
    (fun ω ↦ p ω * deriv u (portfolioPayoff A θ ω)) hfoc (right_ne_zero_of_mul hk₀)
  have hmw : ∑ ω, p ω * deriv u (portfolioPayoff A θ ω) * portfolioPayoff A θ ω = μ * w₀ := by
    rw [sum_mul_portfolioPayoff (fun ω ↦ p ω * deriv u (portfolioPayoff A θ ω)), ← hθ,
      portfolioCost, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [hμ k]; ring
  have hpos : 0 < μ * w₀ := by
    rw [← hmw]
    exact Finset.sum_pos (fun ω _ ↦ mul_pos (mul_pos (hp ω) (hu ω)) (hW ω))
      Finset.univ_nonempty
  refine ⟨μ, ?_, hmw.symm, hμ⟩
  by_contra h
  nlinarith [not_lt.mp h]

/-- **Marginal utility is a state-price density.** Under the hypotheses of
`exists_pos_smul_eq_of_stationary`, the normalised marginal utility `p ω * u'(W ω) / μ` is a
strictly positive state-price vector that prices every traded asset. -/
theorem exists_statePrices_of_stationary [NeZero N] {p : Fin N → ℝ} {u : ℝ → ℝ}
    {A : Fin M → Fin N → ℝ} {pr : Fin M → ℝ} {w₀ : ℝ} {θ : Fin M → ℝ}
    (hθ : portfolioCost pr θ = w₀) (hw₀ : 0 < w₀) (hp : ∀ ω, 0 < p ω)
    (hW : ∀ ω, 0 < portfolioPayoff A θ ω) (hu : ∀ ω, 0 < deriv u (portfolioPayoff A θ ω))
    (hfoc : ∀ d, portfolioCost pr d = 0 →
      ∑ ω, p ω * deriv u (portfolioPayoff A θ ω) * portfolioPayoff A d ω = 0) :
    ∃ μ : ℝ, 0 < μ ∧ (∀ ω, 0 < p ω * deriv u (portfolioPayoff A θ ω) / μ) ∧
      ∀ k, statePricePricing Finset.univ
        (fun ω ↦ p ω * deriv u (portfolioPayoff A θ ω) / μ) (A k) = pr k := by
  obtain ⟨μ, hμ, -, hk⟩ := exists_pos_smul_eq_of_stationary hθ hw₀ hp hW hu hfoc
  have hμ0 : μ ≠ 0 := hμ.ne'
  refine ⟨μ, hμ, fun ω ↦ div_pos (mul_pos (hp ω) (hu ω)) hμ, fun k ↦ ?_⟩
  calc statePricePricing Finset.univ (fun ω ↦ p ω * deriv u (portfolioPayoff A θ ω) / μ) (A k)
      = (∑ ω, p ω * deriv u (portfolioPayoff A θ ω) * A k ω) / μ := by
        rw [statePricePricing, Finset.sum_div]
        exact Finset.sum_congr rfl fun ω _ ↦ by ring
    _ = pr k := by rw [hk k]; field_simp

/-- **Strictly positive state prices give an equivalent martingale measure.** If `q` is a strictly
positive vector with `∑ ω, q ω * A k ω = pr k` for every asset, then the excess returns
`A k ω - pr k / ∑ q` of the assets over the riskless growth `1 / ∑ q` have the equivalent martingale
measure `q / ∑ q`. -/
theorem hasEMMMultiState_of_statePrices [NeZero N] {A : Fin M → Fin N → ℝ} {pr : Fin M → ℝ}
    {q : Fin N → ℝ} (hq : ∀ ω, 0 < q ω)
    (hprice : ∀ k, statePricePricing Finset.univ q (A k) = pr k) :
    HasEMMMultiState fun k ω ↦ A k ω - pr k / ∑ ω', q ω' := by
  have hD : 0 < ∑ ω, q ω := Finset.sum_pos (fun ω _ ↦ hq ω) Finset.univ_nonempty
  have hD0 : ∑ ω, q ω ≠ 0 := hD.ne'
  refine hasEMM_multi_of_pos_dual hq fun k ↦ ?_
  have h := hprice k
  rw [statePricePricing] at h
  simp only [mul_sub, Finset.sum_sub_distrib, h, ← Finset.sum_mul]
  rw [sub_eq_zero]
  field_simp

/-- **Marginal utility at a constrained optimum is a state-price density.** Let `θ` be a local
maximum of the expected utility `∑ ω, p ω * u (W ω)` (`W = portfolioPayoff A θ`) on the budget
set `{θ' | cost θ' = w₀}`, with `w₀ > 0`, positive probabilities, positive wealth and positive
marginal utility `u' (W ω) > 0` (so `u` is differentiable at each `W ω`). Then
`p ω * u'(W ω) / μ` is a strictly positive state-price vector pricing every asset, for some
`μ > 0`. -/
theorem exists_statePrices_of_isLocalMaxOn [NeZero N] {p : Fin N → ℝ} {u : ℝ → ℝ}
    {A : Fin M → Fin N → ℝ} {pr : Fin M → ℝ} {w₀ : ℝ} {θ : Fin M → ℝ}
    (hmax : IsLocalMaxOn (portfolioUtility p u A) {θ' | portfolioCost pr θ' = w₀} θ)
    (hθ : portfolioCost pr θ = w₀) (hw₀ : 0 < w₀) (hp : ∀ ω, 0 < p ω)
    (hW : ∀ ω, 0 < portfolioPayoff A θ ω) (hu : ∀ ω, 0 < deriv u (portfolioPayoff A θ ω)) :
    ∃ μ : ℝ, 0 < μ ∧ (∀ ω, 0 < p ω * deriv u (portfolioPayoff A θ ω) / μ) ∧
      ∀ k, statePricePricing Finset.univ
        (fun ω ↦ p ω * deriv u (portfolioPayoff A θ ω) / μ) (A k) = pr k :=
  exists_statePrices_of_stationary hθ hw₀ hp hW hu fun _ hd ↦
    sum_marginalUtility_mul_payoff_eq_zero_of_isLocalMaxOn hmax hθ
      (fun ω ↦ differentiableAt_of_deriv_ne_zero (hu ω).ne') hd

/-- **The optimum defines a pricing measure.** Under the hypotheses of
`exists_statePrices_of_isLocalMaxOn`, the strictly positive state prices
`q ω = p ω * u'(W ω) / μ` price every asset, and the excess returns `A k ω - pr k / ∑ q` have the
equivalent martingale measure `q / ∑ q` (`HasEMMMultiState`). -/
theorem exists_hasEMMMultiState_of_isLocalMaxOn [NeZero N] {p : Fin N → ℝ} {u : ℝ → ℝ}
    {A : Fin M → Fin N → ℝ} {pr : Fin M → ℝ} {w₀ : ℝ} {θ : Fin M → ℝ}
    (hmax : IsLocalMaxOn (portfolioUtility p u A) {θ' | portfolioCost pr θ' = w₀} θ)
    (hθ : portfolioCost pr θ = w₀) (hw₀ : 0 < w₀) (hp : ∀ ω, 0 < p ω)
    (hW : ∀ ω, 0 < portfolioPayoff A θ ω) (hu : ∀ ω, 0 < deriv u (portfolioPayoff A θ ω)) :
    ∃ q : Fin N → ℝ, (∀ ω, 0 < q ω) ∧ (∃ μ : ℝ, 0 < μ ∧
        ∀ ω, q ω = p ω * deriv u (portfolioPayoff A θ ω) / μ) ∧
      (∀ k, statePricePricing Finset.univ q (A k) = pr k) ∧
      HasEMMMultiState fun k ω ↦ A k ω - pr k / ∑ ω', q ω' := by
  obtain ⟨μ, hμ, hpos, hprice⟩ := exists_statePrices_of_isLocalMaxOn hmax hθ hw₀ hp hW hu
  exact ⟨_, hpos, ⟨μ, hμ, fun _ ↦ rfl⟩, hprice, hasEMMMultiState_of_statePrices hpos hprice⟩

/-- **The optimum defines a pricing measure on the state space.** For a probability `P` on the
states charging every state, the optimum of `exists_hasEMMMultiState_of_isLocalMaxOn` gives
strictly positive state prices `q = p u'(W)/μ`, for some `μ > 0`, and a measure `Q` that is an
equivalent martingale measure (`OnePeriodVector.IsEMM`) for the excess-return vector
`A k ω - pr k / ∑ q`. -/
theorem exists_isEMM_of_isLocalMaxOn [NeZero N] (P : Measure (Fin N)) [IsProbabilityMeasure P]
    (hP : ∀ i, P {i} ≠ 0) {p : Fin N → ℝ} {u : ℝ → ℝ} {A : Fin M → Fin N → ℝ}
    {pr : Fin M → ℝ} {w₀ : ℝ} {θ : Fin M → ℝ}
    (hmax : IsLocalMaxOn (portfolioUtility p u A) {θ' | portfolioCost pr θ' = w₀} θ)
    (hθ : portfolioCost pr θ = w₀) (hw₀ : 0 < w₀) (hp : ∀ ω, 0 < p ω)
    (hW : ∀ ω, 0 < portfolioPayoff A θ ω) (hu : ∀ ω, 0 < deriv u (portfolioPayoff A θ ω)) :
    ∃ q : Fin N → ℝ, (∀ ω, 0 < q ω) ∧ (∃ μ : ℝ, 0 < μ ∧
        ∀ ω, q ω = p ω * deriv u (portfolioPayoff A θ ω) / μ) ∧
      (∀ k, statePricePricing Finset.univ q (A k) = pr k) ∧
      ∃ Q, OnePeriodVector.IsEMM P
        (multiStateReturn fun k ω ↦ A k ω - pr k / ∑ ω', q ω') Q := by
  obtain ⟨q, hq, hμ, hprice, hemm⟩ := exists_hasEMMMultiState_of_isLocalMaxOn hmax hθ hw₀ hp hW hu
  exact ⟨q, hq, hμ, hprice, (hasEMMMultiState_iff_exists_isEMM _ P hP).mp hemm⟩

/-- **Logarithmic utility: the density is the reciprocal of the optimal wealth.** For `u = log`
and probabilities summing to one, a stationary portfolio of positive wealth `W` and budget
`w₀ > 0` has the state-price vector `w₀ * p ω / W ω`: the growth-optimal portfolio is the
numéraire. -/
theorem logUtility_statePrices_of_stationary [NeZero N] {p : Fin N → ℝ}
    {A : Fin M → Fin N → ℝ} {pr : Fin M → ℝ} {w₀ : ℝ} {θ : Fin M → ℝ}
    (hθ : portfolioCost pr θ = w₀) (hw₀ : 0 < w₀) (hp : ∀ ω, 0 < p ω) (hp1 : ∑ ω, p ω = 1)
    (hW : ∀ ω, 0 < portfolioPayoff A θ ω)
    (hfoc : ∀ d, portfolioCost pr d = 0 →
      ∑ ω, p ω * (portfolioPayoff A θ ω)⁻¹ * portfolioPayoff A d ω = 0) :
    (∀ ω, 0 < w₀ * p ω / portfolioPayoff A θ ω) ∧
      ∀ k, statePricePricing Finset.univ
        (fun ω ↦ w₀ * p ω / portfolioPayoff A θ ω) (A k) = pr k := by
  have hu (ω : Fin N) : 0 < deriv Real.log (portfolioPayoff A θ ω) := by
    rw [Real.deriv_log]; exact inv_pos.mpr (hW ω)
  have hfoc' : ∀ d, portfolioCost pr d = 0 →
      ∑ ω, p ω * deriv Real.log (portfolioPayoff A θ ω) * portfolioPayoff A d ω = 0 := by
    simpa only [Real.deriv_log] using hfoc
  obtain ⟨μ, -, hμw, hk⟩ := exists_pos_smul_eq_of_stationary hθ hw₀ hp hW hu hfoc'
  have hμ1 : μ * w₀ = 1 := by
    calc μ * w₀ = ∑ ω, p ω * deriv Real.log (portfolioPayoff A θ ω) * portfolioPayoff A θ ω := hμw
      _ = ∑ ω, p ω :=
        Finset.sum_congr rfl fun ω _ ↦ by rw [Real.deriv_log]; field_simp [(hW ω).ne']
      _ = 1 := hp1
  refine ⟨fun ω ↦ div_pos (mul_pos hw₀ (hp ω)) (hW ω), fun k ↦ ?_⟩
  have h := hk k
  simp only [Real.deriv_log] at h
  calc statePricePricing Finset.univ (fun ω ↦ w₀ * p ω / portfolioPayoff A θ ω) (A k)
      = w₀ * ∑ ω, p ω * (portfolioPayoff A θ ω)⁻¹ * A k ω := by
        rw [statePricePricing, Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ ↦ by ring
    _ = pr k := by rw [h]; linear_combination pr k * hμ1

end MathFin
