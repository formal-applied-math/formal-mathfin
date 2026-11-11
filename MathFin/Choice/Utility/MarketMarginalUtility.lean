/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Choice.Portfolio.MarketSDF
public import MathFin.Choice.Utility.StatePriceDensity

/-!
# Marginal utility is the market's stochastic discount factor

`Choice/Utility/StatePriceDensity` proves the Euler equation on a finite sample space: at a
stationary portfolio the marginal-utility vector `(p ω * u'(W ω))ω` prices every asset up to a
factor `μ > 0`. This file reads it in a `Market` on a finite sample space. When the market is
complete (no non-zero state vector annihilates every terminal payoff), the state prices are
unique, so the marginal utility is the market's own stochastic discount factor up to the constant
`μ`: `u'(W ω) = μ * sdf ω` (`exists_deriv_eq_mul_sdf_of_stationary`). For the logarithmic utility
this is the numéraire-portfolio identity, `sdf = w₀ / W*`: the density of the pricing measure is
the reciprocal of the growth-optimal wealth (`sdf_eq_div_of_logOptimal`), so deflating by the
growth-optimal portfolio prices the assets under the physical measure.

## Main results

* `Market.IsPricingMeasure.exists_deriv_eq_mul_sdf_of_stationary`: in a complete market on a finite
  sample space, at a stationary portfolio of an increasing utility, `u'(W) = μ * sdf` for some
  `μ > 0`, and `μ * w₀ = E_P[u'(W) W]`.
* `Market.IsPricingMeasure.exists_deriv_eq_mul_sdf_of_isLocalMaxOn`: the same at a local maximum of
  the expected utility `∫ u(W) ∂P` on the budget set.
* `Market.IsPricingMeasure.sdf_eq_div_of_logOptimal`: for `u = log`, `sdf ω = w₀ / W ω`.
* `Market.IsPricingMeasure.integral_div_logOptimal_mul`: the prices deflated by the log-optimal
  wealth are `P`-martingales in one period, `E_P[S_k(T) / W] = S_k(0) / w₀`.

The initial prices `pr k` are deterministic. Completeness of the market is a hypothesis.

## References

* [Long (1990)][Long1990]
* [J. L. Kelly, *A new interpretation of information rate*][Kelly1956]
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §1.2
* [J. H. Cochrane, *Asset Pricing*][Cochrane2005], §1.2

## Tags

marginal utility, stochastic discount factor, state-price density, Euler equation, complete
market, log-optimal portfolio, numéraire portfolio, JEL D81, JEL G12, MSC 91B16, MSC 91G10
-/

@[expose] public section

open MeasureTheory MathFin.Contracts
open scoped NNReal

namespace MathFin.Market

variable {N K : ℕ} [NeZero N] {M : Market (Fin K) (Fin N)} {T : ℝ≥0} {Q : Measure (Fin N)}

/-- **Marginal utility is the stochastic discount factor.** In a market on a finite sample space
with a pricing measure `Q` up to `T`, a probability measure `P` charging every state and
deterministic initial prices `pr`, suppose the terminal payoffs span the states (no non-zero
`x : Fin N → ℝ` has `∑ ω, x ω * S_k(T) ω = 0` for every asset `k`). At a portfolio `θ` of cost
`w₀ > 0`, with positive terminal wealth `W`, positive marginal utility `u'(W) > 0` and stationary
expected utility on the budget set (the marginal-utility vector annihilates the payoff of every
budget-neutral direction), there is `μ > 0` with `μ * w₀ = E_P[u'(W) W]` and
`u'(W ω) = μ * sdf ω` in every state. -/
theorem IsPricingMeasure.exists_deriv_eq_mul_sdf_of_stationary [IsProbabilityMeasure M.P]
    (hP : ∀ ω, 0 < M.P.real {ω}) (hQ : M.IsPricingMeasure T Q) {n₀ : ℝ}
    (hN₀ : ∀ ω, M.numeraire 0 ω = n₀) {pr : Fin K → ℝ} (hpr : ∀ k ω, M.asset k 0 ω = pr k)
    (hcomplete : ∀ x : Fin N → ℝ, (∀ k, ∑ ω, x ω * M.asset k T ω = 0) → x = 0) {u : ℝ → ℝ}
    {w₀ : ℝ} {θ : Fin K → ℝ} (hθ : portfolioCost pr θ = w₀) (hw₀ : 0 < w₀)
    (hW : ∀ ω, 0 < portfolioPayoff (fun j ↦ M.asset j T) θ ω)
    (hu : ∀ ω, 0 < deriv u (portfolioPayoff (fun j ↦ M.asset j T) θ ω))
    (hfoc : ∀ d, portfolioCost pr d = 0 →
      ∑ ω, M.P.real {ω} * deriv u (portfolioPayoff (fun j ↦ M.asset j T) θ ω) *
        portfolioPayoff (fun j ↦ M.asset j T) d ω = 0) :
    ∃ μ : ℝ, 0 < μ ∧
      μ * w₀ = ∑ ω, M.P.real {ω} * deriv u (portfolioPayoff (fun j ↦ M.asset j T) θ ω) *
        portfolioPayoff (fun j ↦ M.asset j T) θ ω ∧
      ∀ ω, deriv u (portfolioPayoff (fun j ↦ M.asset j T) θ ω) = μ * M.sdf Q T ω := by
  obtain ⟨μ, hμ, hμw, hk⟩ := exists_pos_smul_eq_of_stationary (p := fun ω ↦ M.P.real {ω})
    (A := fun j ↦ M.asset j T) hθ hw₀ hP hW hu hfoc
  have hm (k : Fin K) : ∑ ω, M.P.real {ω} * M.sdf Q T ω * M.asset k T ω = pr k := by
    have h := hQ.integral_sdf_mul_asset hN₀ k (hpr k)
    rw [integral_fintype Integrable.of_finite] at h
    simpa only [smul_eq_mul, mul_assoc] using h
  have hx (k : Fin K) : ∑ ω, (M.P.real {ω} *
      (deriv u (portfolioPayoff (fun j ↦ M.asset j T) θ ω) - μ * M.sdf Q T ω)) *
        M.asset k T ω = 0 := by
    calc _ = (∑ ω, M.P.real {ω} * deriv u (portfolioPayoff (fun j ↦ M.asset j T) θ ω) *
            M.asset k T ω) - μ * ∑ ω, M.P.real {ω} * M.sdf Q T ω * M.asset k T ω := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun ω _ ↦ by ring
      _ = 0 := by linear_combination hk k - μ * hm k
  have h0 := hcomplete _ hx
  refine ⟨μ, hμ, hμw, fun ω ↦ ?_⟩
  have h1 : M.P.real {ω} *
      (deriv u (portfolioPayoff (fun j ↦ M.asset j T) θ ω) - μ * M.sdf Q T ω) = 0 :=
    congrFun h0 ω
  have h2 := (mul_eq_zero.mp h1).resolve_left (hP ω).ne'
  linarith

/-- **Marginal utility is the stochastic discount factor at a local optimum.** Under the
hypotheses of `exists_deriv_eq_mul_sdf_of_stationary`, with stationarity replaced by `θ` being a
local maximum on the budget set `{θ' | cost θ' = w₀}` of the expected utility `∫ u(W) ∂P` (the
integral against the reference measure), `u'(W ω) = μ * sdf ω` for some `μ > 0`. -/
theorem IsPricingMeasure.exists_deriv_eq_mul_sdf_of_isLocalMaxOn [IsProbabilityMeasure M.P]
    (hP : ∀ ω, 0 < M.P.real {ω}) (hQ : M.IsPricingMeasure T Q) {n₀ : ℝ}
    (hN₀ : ∀ ω, M.numeraire 0 ω = n₀) {pr : Fin K → ℝ} (hpr : ∀ k ω, M.asset k 0 ω = pr k)
    (hcomplete : ∀ x : Fin N → ℝ, (∀ k, ∑ ω, x ω * M.asset k T ω = 0) → x = 0) {u : ℝ → ℝ}
    {w₀ : ℝ} {θ : Fin K → ℝ}
    (hmax : IsLocalMaxOn (fun θ' ↦ ∫ ω, u (portfolioPayoff (fun j ↦ M.asset j T) θ' ω) ∂M.P)
      {θ' | portfolioCost pr θ' = w₀} θ)
    (hθ : portfolioCost pr θ = w₀) (hw₀ : 0 < w₀)
    (hW : ∀ ω, 0 < portfolioPayoff (fun j ↦ M.asset j T) θ ω)
    (hu : ∀ ω, 0 < deriv u (portfolioPayoff (fun j ↦ M.asset j T) θ ω)) :
    ∃ μ : ℝ, 0 < μ ∧
      ∀ ω, deriv u (portfolioPayoff (fun j ↦ M.asset j T) θ ω) = μ * M.sdf Q T ω := by
  have hobj : (fun θ' ↦ ∫ ω, u (portfolioPayoff (fun j ↦ M.asset j T) θ' ω) ∂M.P) =
      portfolioUtility (fun ω ↦ M.P.real {ω}) u (fun j ↦ M.asset j T) := by
    funext θ'
    exact (expectedUtility_univ_real_eq_integral M.P _).symm
  rw [hobj] at hmax
  obtain ⟨μ, hμ, -, h⟩ := hQ.exists_deriv_eq_mul_sdf_of_stationary hP hN₀ hpr hcomplete hθ hw₀ hW
    hu fun _ hd ↦ sum_marginalUtility_mul_payoff_eq_zero_of_isLocalMaxOn hmax hθ
      (fun ω ↦ differentiableAt_of_deriv_ne_zero (hu ω).ne') hd
  exact ⟨μ, hμ, h⟩

/-- **The log-optimal portfolio is the numéraire portfolio.** In the market of
`exists_deriv_eq_mul_sdf_of_stationary` with `u = log`, a stationary portfolio of cost `w₀ > 0` and
positive terminal wealth `W` has `sdf ω = w₀ / W ω`: the density of the pricing measure is the
reciprocal of the growth-optimal wealth, scaled by its initial value. -/
theorem IsPricingMeasure.sdf_eq_div_of_logOptimal [IsProbabilityMeasure M.P]
    (hP : ∀ ω, 0 < M.P.real {ω}) (hQ : M.IsPricingMeasure T Q) {n₀ : ℝ}
    (hN₀ : ∀ ω, M.numeraire 0 ω = n₀) {pr : Fin K → ℝ} (hpr : ∀ k ω, M.asset k 0 ω = pr k)
    (hcomplete : ∀ x : Fin N → ℝ, (∀ k, ∑ ω, x ω * M.asset k T ω = 0) → x = 0)
    {w₀ : ℝ} {θ : Fin K → ℝ} (hθ : portfolioCost pr θ = w₀) (hw₀ : 0 < w₀)
    (hW : ∀ ω, 0 < portfolioPayoff (fun j ↦ M.asset j T) θ ω)
    (hfoc : ∀ d, portfolioCost pr d = 0 →
      ∑ ω, M.P.real {ω} * (portfolioPayoff (fun j ↦ M.asset j T) θ ω)⁻¹ *
        portfolioPayoff (fun j ↦ M.asset j T) d ω = 0) (ω : Fin N) :
    M.sdf Q T ω = w₀ / portfolioPayoff (fun j ↦ M.asset j T) θ ω := by
  have hu (ω : Fin N) : 0 < deriv Real.log (portfolioPayoff (fun j ↦ M.asset j T) θ ω) := by
    rw [Real.deriv_log]
    exact inv_pos.mpr (hW ω)
  obtain ⟨μ, hμ, hμw, h⟩ := hQ.exists_deriv_eq_mul_sdf_of_stationary hP hN₀ hpr hcomplete hθ hw₀
    hW hu (by simpa only [Real.deriv_log] using hfoc)
  have hp1 : ∑ ω, M.P.real {ω} = 1 := by
    have := integral_fintype (f := fun _ : Fin N ↦ (1 : ℝ)) (μ := M.P) Integrable.of_finite
    simpa using this.symm
  have hμ1 : μ * w₀ = 1 := by
    rw [hμw, ← hp1]
    exact Finset.sum_congr rfl fun ω _ ↦ by
      rw [Real.deriv_log]
      field_simp [(hW ω).ne']
  have h1 := h ω
  rw [Real.deriv_log] at h1
  calc M.sdf Q T ω = (μ * w₀) * M.sdf Q T ω := by rw [hμ1, one_mul]
    _ = w₀ * (μ * M.sdf Q T ω) := by ring
    _ = w₀ / portfolioPayoff (fun j ↦ M.asset j T) θ ω := by rw [← h1, div_eq_mul_inv]

/-- **Prices deflated by the log-optimal wealth are martingales under `P` in one period.** In the
market of `sdf_eq_div_of_logOptimal`, `E_P[S_k(T) / W] = S_k(0) / w₀` for every asset `k`:
the deflated price has the same mean at `T` as at `0`, where the log-optimal wealth is `w₀`. -/
theorem IsPricingMeasure.integral_div_logOptimal_mul [IsProbabilityMeasure M.P]
    (hP : ∀ ω, 0 < M.P.real {ω}) (hQ : M.IsPricingMeasure T Q) {n₀ : ℝ}
    (hN₀ : ∀ ω, M.numeraire 0 ω = n₀) {pr : Fin K → ℝ} (hpr : ∀ k ω, M.asset k 0 ω = pr k)
    (hcomplete : ∀ x : Fin N → ℝ, (∀ k, ∑ ω, x ω * M.asset k T ω = 0) → x = 0)
    {w₀ : ℝ} {θ : Fin K → ℝ} (hθ : portfolioCost pr θ = w₀) (hw₀ : 0 < w₀)
    (hW : ∀ ω, 0 < portfolioPayoff (fun j ↦ M.asset j T) θ ω)
    (hfoc : ∀ d, portfolioCost pr d = 0 →
      ∑ ω, M.P.real {ω} * (portfolioPayoff (fun j ↦ M.asset j T) θ ω)⁻¹ *
        portfolioPayoff (fun j ↦ M.asset j T) d ω = 0) (k : Fin K) :
    ∫ ω, M.asset k T ω / portfolioPayoff (fun j ↦ M.asset j T) θ ω ∂M.P = pr k / w₀ := by
  have e (ω : Fin N) : M.asset k T ω / portfolioPayoff (fun j ↦ M.asset j T) θ ω =
      w₀⁻¹ * (M.sdf Q T ω * M.asset k T ω) := by
    rw [hQ.sdf_eq_div_of_logOptimal hP hN₀ hpr hcomplete hθ hw₀ hW hfoc ω]
    field_simp [hw₀.ne', (hW ω).ne']
  simp_rw [e]
  rw [integral_const_mul, hQ.integral_sdf_mul_asset hN₀ k (hpr k), inv_mul_eq_div]
