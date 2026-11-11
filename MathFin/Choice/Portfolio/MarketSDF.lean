/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Choice.Portfolio.StochasticDiscountFactor
public import MathFin.Pricing.Market
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The stochastic discount factor of a market with a pricing measure

`Choice/Portfolio/StochasticDiscountFactor` proves the Hansen–Jagannathan bound and the
security market line for a discount factor `m` on a probability space. This file shows that every
`Market` with a pricing measure has one. The **stochastic discount factor** of a pricing measure
`Q` up to `T` is the density of `Q` with respect to the reference measure `P` on the events known
at `T`, times the deflator `N 0 / N T`:

  `M.sdf Q T ω = (d(Q|𝓕 T) / d(P|𝓕 T)) (ω) * (N 0 / N T) (ω)`.

Changing measure turns the `Q`-price of a cash flow known at `T` into a `P`-expectation against
`sdf` (`IsPricingMeasure.integral_sdf_mul`); with a deterministic initial price `c` this says
`E_P[sdf * S_i(T)] = c` (`IsPricingMeasure.integral_sdf_mul_asset`), that is `E_P[sdf * R] = 1` for
the gross return `R = S_i(T) / S_i(0)` (`integral_sdf_mul_grossReturn`). So the two theorems of
`StochasticDiscountFactor` apply to the market.

## Main definitions

* `Market.sdf`: the stochastic discount factor of a pricing measure.
* `Market.grossReturn`: the gross return `S_i(T) / S_i(0)` of asset `i` up to `T`.

## Main results

* `Market.IsPricingMeasure.integral_rnDeriv_mul`: the change of measure on `𝓕 T`, an instance of
  `integral_rnDeriv_trim_mul`.
* `Market.IsPricingMeasure.integral_sdf_mul`: `E_P[sdf * X] = E_Q[(N 0 / N T) X]` for a payoff `X`
  known at `T`.
* `Market.IsPricingMeasure.sdf_mul_real_singleton`: `sdf(ω) * P{ω} = (N 0 / N T)(ω) * Q{ω}`, the
  state price (`Market.statePrice`), when the singletons are known at `T`.
* `Market.IsPricingMeasure.integral_sdf_mul_grossReturn`: `E_P[sdf * R_i] = 1` for the gross
  return of an asset with a deterministic initial price.
* `Market.IsPricingMeasure.abs_sharpeRatio_le`: the Hansen–Jagannathan bound,
  `|sharpeRatio (E R_i) r_f σ(R_i)| ≤ σ(sdf) / E[sdf]`, for every asset of a market with a pricing
  measure, an instance of `abs_sharpeRatio_le_of_discountFactor`.
* `Market.IsPricingMeasure.capm_of_affine_sdf`: the security market line for a market whose `sdf`
  is affine in the return of one of its assets, an instance of `capm_of_affine_discountFactor`.

The moments are taken under the reference measure `P`. The riskless return `r_f` is a number with
`r_f * E[sdf] = 1`: the market need not contain a riskless asset. That the `sdf` is square
integrable is a hypothesis.

## References

* [L. P. Hansen and R. Jagannathan, *Implications of security market data for models of dynamic
  economies*][HansenJagannathan1991]
* [J. H. Cochrane, *Asset Pricing*][Cochrane2005], §1.2, §6.3 and §9.1
* [Sharpe, *Capital asset prices*][Sharpe1964]
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §5.2

## Tags

stochastic discount factor, pricing kernel, Radon–Nikodym density, Hansen–Jagannathan bound,
security market line, pricing measure, JEL G12, MSC 91G20, MSC 91G10
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathFin.Contracts
open scoped NNReal

namespace MathFin.Market

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} (M : Market ι Ω)

/-- **The stochastic discount factor of the pricing measure `Q` up to `T`**: the density of `Q`
with respect to the reference measure `P` on `𝓕 T`, times the deflator `N 0 / N T`. -/
noncomputable def sdf (Q : Measure Ω) (T : ℝ≥0) (ω : Ω) : ℝ :=
  ((Q.trim (M.𝓕.le T)).rnDeriv (M.P.trim (M.𝓕.le T)) ω).toReal * M.deflator T ω

/-- **The gross return of asset `i` up to `T`**: `S_i(T) / S_i(0)`. -/
noncomputable def grossReturn (i : ι) (T : ℝ≥0) (ω : Ω) : ℝ :=
  M.asset i T ω / M.asset i 0 ω

variable {M} {T : ℝ≥0} {Q : Measure Ω}

theorem sdf_nonneg (ω : Ω) : 0 ≤ M.sdf Q T ω :=
  mul_nonneg ENNReal.toReal_nonneg (M.deflator_pos T ω).le

/-- **Change of measure on `𝓕 T`.** For a pricing measure `Q` up to `T`, a payoff `g` known at `T`
has `P`-expectation against the density of `Q` equal to its `Q`-expectation. -/
theorem IsPricingMeasure.integral_rnDeriv_mul [IsFiniteMeasure M.P] (hQ : M.IsPricingMeasure T Q)
    {g : Ω → ℝ} (hg : StronglyMeasurable[M.𝓕 T] g) :
    ∫ ω, ((Q.trim (M.𝓕.le T)).rnDeriv (M.P.trim (M.𝓕.le T)) ω).toReal * g ω ∂M.P
      = ∫ ω, g ω ∂Q :=
  integral_rnDeriv_trim_mul (M.𝓕.le T) hQ.ac hg

/-- **The `sdf` prices every payoff known at `T`**: `E_P[sdf * X] = E_Q[(N 0 / N T) X]`. -/
theorem IsPricingMeasure.integral_sdf_mul [IsFiniteMeasure M.P] (hQ : M.IsPricingMeasure T Q)
    {X : Ω → ℝ} (hX : StronglyMeasurable[M.𝓕 T] X) :
    ∫ ω, M.sdf Q T ω * X ω ∂M.P = ∫ ω, M.deflator T ω * X ω ∂Q := by
  have h := hQ.integral_rnDeriv_mul ((M.stronglyMeasurable_deflator T).mul hX)
  simp only [Pi.mul_apply, ← mul_assoc] at h
  exact h

/-- **The `sdf` is the state-price density.** When the singletons are known at `T`
(`{ω} ∈ 𝓕 T`, as on a finite sample space with `𝓕 T = ⊤`), `sdf(ω) * P{ω}` is the state price
`(N 0 / N T)(ω) * Q{ω}` of `ω`. -/
theorem IsPricingMeasure.sdf_mul_real_singleton [IsFiniteMeasure M.P] [MeasurableSingletonClass Ω]
    (hQ : M.IsPricingMeasure T Q) (hT : ∀ ω, MeasurableSet[M.𝓕 T] {ω}) (ω : Ω) :
    M.sdf Q T ω * M.P.real {ω} = M.statePrice Q T ω := by
  have h := integral_rnDeriv_trim_mul (M.𝓕.le T) hQ.ac
    (stronglyMeasurable_const.indicator (hT ω) : StronglyMeasurable[M.𝓕 T]
      (({ω} : Set Ω).indicator fun _ ↦ (1 : ℝ)))
  have e (x : Ω) : ((Q.trim (M.𝓕.le T)).rnDeriv (M.P.trim (M.𝓕.le T)) x).toReal *
      ({ω} : Set Ω).indicator (fun _ ↦ (1 : ℝ)) x =
      ({ω} : Set Ω).indicator
        (fun _ ↦ ((Q.trim (M.𝓕.le T)).rnDeriv (M.P.trim (M.𝓕.le T)) ω).toReal) x := by
    by_cases hx : x = ω
    · subst hx
      simp [Set.indicator_apply]
    · simp [Set.indicator_apply, hx]
  simp_rw [e] at h
  rw [integral_indicator_const _ (measurableSet_singleton ω),
    integral_indicator_const _ (measurableSet_singleton ω)] at h
  simp only [smul_eq_mul, mul_one] at h
  simp only [sdf, statePrice]
  linear_combination M.deflator T ω * h

/-- **An asset with a deterministic initial price `c` is priced by the `sdf`**:
`E_P[sdf * S_i(T)] = c`. -/
theorem IsPricingMeasure.integral_sdf_mul_asset [IsFiniteMeasure M.P] (hQ : M.IsPricingMeasure T Q)
    {n₀ : ℝ} (hN₀ : ∀ ω, M.numeraire 0 ω = n₀) (i : ι) {c : ℝ} (hc : ∀ ω, M.asset i 0 ω = c) :
    ∫ ω, M.sdf Q T ω * M.asset i T ω ∂M.P = c := by
  have := hQ.isProb
  have h : ∫ ω, M.deflator T ω * M.asset i T ω ∂Q = ∫ ω, M.asset i 0 ω ∂Q := by
    rw [← hQ.price_pay_obs hN₀ i le_rfl, Market.price, Contract.value_pay]
    simp [Payoff.eval, scenarioAt]
  rw [hQ.integral_sdf_mul (M.asset_adapted i T), h]
  simp [hc]

/-- **The `sdf` prices the gross return of an asset with a deterministic initial price**:
`E_P[sdf * R_i] = 1` for `R_i = S_i(T) / S_i(0)` with `S_i(0) = c ≠ 0`. -/
theorem IsPricingMeasure.integral_sdf_mul_grossReturn [IsFiniteMeasure M.P]
    (hQ : M.IsPricingMeasure T Q) {n₀ : ℝ} (hN₀ : ∀ ω, M.numeraire 0 ω = n₀) (i : ι) {c : ℝ}
    (hc0 : c ≠ 0) (hc : ∀ ω, M.asset i 0 ω = c) :
    ∫ ω, M.sdf Q T ω * M.grossReturn i T ω ∂M.P = 1 := by
  have h := hQ.integral_sdf_mul_asset hN₀ i hc
  have e : ∀ ω, M.sdf Q T ω * M.grossReturn i T ω = c⁻¹ * (M.sdf Q T ω * M.asset i T ω) :=
    fun ω ↦ by simp only [grossReturn, hc]; ring
  simp_rw [e]
  rw [integral_const_mul, h, inv_mul_cancel₀ hc0]

/-- **The Hansen–Jagannathan bound for a market with a pricing measure.** Let `Q` price the market
up to `T`, and let asset `i` have a deterministic initial price `c ≠ 0` and a square-integrable
gross return `R_i` with positive variance under `P`. If the `sdf` is square integrable and `r_f` is
a riskless return, `r_f * E_P[sdf] = 1`, then
`|sharpeRatio (E R_i) r_f σ(R_i)| ≤ σ(sdf) / E[sdf]`, the moments taken under `P`. -/
theorem IsPricingMeasure.abs_sharpeRatio_le [IsProbabilityMeasure M.P]
    (hQ : M.IsPricingMeasure T Q) {n₀ : ℝ} (hN₀ : ∀ ω, M.numeraire 0 ω = n₀) (i : ι) {c : ℝ}
    (hc0 : c ≠ 0) (hc : ∀ ω, M.asset i 0 ω = c) {rf : ℝ} (hm : MemLp (M.sdf Q T) 2 M.P)
    (hR : MemLp (M.grossReturn i T) 2 M.P) (hR0 : 0 < Var[M.grossReturn i T; M.P])
    (hrf : rf * ∫ ω, M.sdf Q T ω ∂M.P = 1) :
    |sharpeRatio (∫ ω, M.grossReturn i T ω ∂M.P) rf √(Var[M.grossReturn i T; M.P])|
      ≤ √(Var[M.sdf Q T; M.P]) / ∫ ω, M.sdf Q T ω ∂M.P := by
  have hm0 : 0 < ∫ ω, M.sdf Q T ω ∂M.P := by
    refine lt_of_le_of_ne (integral_nonneg fun ω ↦ sdf_nonneg ω) fun h ↦ ?_
    rw [← h, mul_zero] at hrf
    exact zero_ne_one hrf
  exact abs_sharpeRatio_le_of_discountFactor hm hR hm0 hR0 hrf
    (hQ.integral_sdf_mul_grossReturn hN₀ i hc0 hc)

/-- **The security market line for a market with a pricing measure.** Let `Q` price the market up
to `T`, let assets `i` and `j` have deterministic nonzero initial prices, and let `R_i`, `R_j` be
their square-integrable gross returns. If the `sdf` is affine in the return of `j`,
`sdf = a - b R_j`, if `r_f` is a riskless return (`r_f * E_P[sdf] = 1`) and `Var R_j ≠ 0`, then
`E[R_i] = r_f + β (E[R_j] - r_f)` with `β = Cov(R_i, R_j) / Var R_j`, the moments taken under
`P`. -/
theorem IsPricingMeasure.capm_of_affine_sdf [IsProbabilityMeasure M.P]
    (hQ : M.IsPricingMeasure T Q) {n₀ : ℝ} (hN₀ : ∀ ω, M.numeraire 0 ω = n₀) (i j : ι) {ci cj : ℝ}
    (hci0 : ci ≠ 0) (hci : ∀ ω, M.asset i 0 ω = ci) (hcj0 : cj ≠ 0)
    (hcj : ∀ ω, M.asset j 0 ω = cj) {a b rf : ℝ}
    (hm : ∀ ω, M.sdf Q T ω = a - b * M.grossReturn j T ω)
    (hRj : MemLp (M.grossReturn j T) 2 M.P) (hRi : MemLp (M.grossReturn i T) 2 M.P)
    (hrf : rf * ∫ ω, M.sdf Q T ω ∂M.P = 1) (hvar : Var[M.grossReturn j T; M.P] ≠ 0) :
    ∫ ω, M.grossReturn i T ω ∂M.P = securityMarketLine rf
      (beta cov[M.grossReturn i T, M.grossReturn j T; M.P] Var[M.grossReturn j T; M.P])
      (∫ ω, M.grossReturn j T ω ∂M.P) :=
  capm_of_affine_discountFactor hm hRj hRi hrf
    (hQ.integral_sdf_mul_grossReturn hN₀ i hci0 hci)
    (hQ.integral_sdf_mul_grossReturn hN₀ j hcj0 hcj) hvar

end MathFin.Market
