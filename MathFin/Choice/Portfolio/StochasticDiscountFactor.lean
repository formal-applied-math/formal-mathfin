/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Choice.Performance.Ratios
public import MathFin.Choice.Portfolio.CAPMEquilibrium
public import MathFin.Choice.Utility.StatePriceDensity
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# The stochastic discount factor: Hansen–Jagannathan and the CAPM

A stochastic discount factor (SDF) `m` prices a gross return `R` when `E[m R] = 1`, and an excess
return `x` when `E[m x] = 0`. Two classical consequences follow from the covariance of `m` with
the returns.

* **Hansen–Jagannathan.** From `E[m x] = 0` one gets `Cov(m, x) = -E[m] E[x]`, and the
  Cauchy–Schwarz inequality `Cov(m, x)² ≤ Var m · Var x` bounds every Sharpe ratio:
  `|E[x]| / σ(x) ≤ σ(m) / E[m]`. For gross returns priced by `m`, with the riskless return
  `r_f = 1 / E[m]`, this is `|sharpeRatio (E R) r_f σ(R)| ≤ σ(m) / E[m]`.
* **CAPM.** If `m = a - b R_m` is affine in the return `R_m` of the market, every priced return
  has `E[R] - r_f = r_f b Cov(R, R_m)`; applied to `R_m` itself this fixes `r_f b`, and the
  security market line `E[R] = r_f + β (E[R_m] - r_f)` with `β = Cov(R, R_m) / Var R_m` follows.
  With a market portfolio `R_m = ∑ w_k R_k` of finitely many priced assets, the relation
  `E[R_k] - r_f = r_f b (Σ w)_k` is the tangent-portfolio cross-product condition, so
  `CAPM_from_market_equilibrium` applies: its equilibrium hypothesis is a consequence of
  discount-factor pricing.

The moments are those of Mathlib (`ProbabilityTheory.covariance`, `variance`) on a probability
space. Cauchy–Schwarz for the covariance is proved from the non-negativity of
`Var(X + t Y)` (`covariance_sq_le_variance_mul`).

## Main results

* `covariance_sq_le_variance_mul`: `Cov(X, Y)² ≤ Var X · Var Y` for square-integrable `X, Y`.
* `hansenJagannathan_sq`: `(E[m] E[x])² ≤ Var m · Var x` when `E[m x] = 0`.
* `hansenJagannathan_bound`: `|E[x]| / √Var x ≤ √Var m / E[m]` for an excess return `x`.
* `abs_sharpeRatio_le_of_discountFactor`: the same for a gross return `R` priced by `m`, as a
  bound on `sharpeRatio (E R) r_f σ(R)`.
* `integral_sub_eq_of_affine_discountFactor`: `E[R] - r_f = r_f b Cov(R, R_m)` when
  `m = a - b R_m` prices `R`.
* `capm_of_affine_discountFactor`: the security market line from an SDF affine in the market
  return.
* `capm_from_market_equilibrium_of_discountFactor`: `CAPM_from_market_equilibrium` for a market
  portfolio of priced assets, its cross-product hypothesis derived from the discount factor.
* `integral_discountFactor_mul`, `integral_marginalUtility_mul_eq`: on a finite sample space the
  SDF `q / p` of a state-price vector `q`, and the marginal utility `u'(W) / μ` at an
  expected-utility optimum, price the assets (`Choice/Utility/StatePriceDensity`).

## References

* [L. P. Hansen and R. Jagannathan, *Implications of security market data for models of dynamic
  economies*][HansenJagannathan1991]
* [J. H. Cochrane, *Asset Pricing*][Cochrane2005], §6.3 and §5.1
* [Sharpe, *Capital asset prices*][Sharpe1964]

## Tags

stochastic discount factor, Hansen–Jagannathan bound, Sharpe ratio, pricing kernel, CAPM,
security market line, beta pricing, Cauchy–Schwarz, JEL G12, JEL D81, MSC 91G10
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Cauchy–Schwarz for the covariance**: `Cov(X, Y)² ≤ Var X · Var Y` for square-integrable
`X` and `Y`. The quadratic `t ↦ Var(X + t Y) = Var Y t² + 2 Cov(X, Y) t + Var X` is non-negative,
so its discriminant is non-positive. -/
lemma covariance_sq_le_variance_mul [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) : cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ] := by
  have h (t : ℝ) : 0 ≤ Var[Y; μ] * (t * t) + 2 * cov[X, Y; μ] * t + Var[X; μ] := by
    have := variance_nonneg (X + t • Y) μ
    rw [variance_add hX (hY.const_smul t), covariance_smul_right, variance_smul] at this
    nlinarith [this]
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith [this]

/-- **Hansen–Jagannathan, moment form.** If the discount factor `m` prices the excess return `x`
(`E[m x] = 0`), then `(E[m] E[x])² ≤ Var m · Var x`: the covariance `Cov(m, x) = -E[m] E[x]`
is bounded by Cauchy–Schwarz. -/
theorem hansenJagannathan_sq [IsProbabilityMeasure μ] {m x : Ω → ℝ} (hm : MemLp m 2 μ)
    (hx : MemLp x 2 μ) (hprice : ∫ ω, m ω * x ω ∂μ = 0) :
    ((∫ ω, m ω ∂μ) * ∫ ω, x ω ∂μ) ^ 2 ≤ Var[m; μ] * Var[x; μ] := by
  have h0 : ∫ ω, (m * x) ω ∂μ = 0 := hprice
  have h := covariance_sq_le_variance_mul hm hx
  rwa [covariance_eq_sub hm hx, h0, zero_sub, neg_sq] at h

/-- **The Hansen–Jagannathan bound.** A strictly positive-mean discount factor `m` that prices an
excess return `x` with positive variance bounds its Sharpe ratio:
`|E[x]| / σ(x) ≤ σ(m) / E[m]`. -/
theorem hansenJagannathan_bound [IsProbabilityMeasure μ] {m x : Ω → ℝ} (hm : MemLp m 2 μ)
    (hx : MemLp x 2 μ) (hm0 : 0 < ∫ ω, m ω ∂μ) (hx0 : 0 < Var[x; μ])
    (hprice : ∫ ω, m ω * x ω ∂μ = 0) :
    |∫ ω, x ω ∂μ| / √(Var[x; μ]) ≤ √(Var[m; μ]) / ∫ ω, m ω ∂μ := by
  have hσ : 0 < √(Var[x; μ]) := Real.sqrt_pos.mpr hx0
  have h := Real.abs_le_sqrt (hansenJagannathan_sq hm hx hprice)
  rw [Real.sqrt_mul (variance_nonneg m μ), abs_mul, abs_of_pos hm0] at h
  rw [div_le_div_iff₀ hσ hm0]
  linarith

/-- **The Hansen–Jagannathan bound on the Sharpe ratio.** If the discount factor `m` prices the
gross return `R` (`E[m R] = 1`) and the riskless gross return `r_f` (`r_f E[m] = 1`), then the
Sharpe ratio of `R` is bounded by the volatility of the discount factor per unit of its mean:
`|sharpeRatio (E R) r_f σ(R)| ≤ σ(m) / E[m]`. -/
theorem abs_sharpeRatio_le_of_discountFactor [IsProbabilityMeasure μ] {m R : Ω → ℝ} {rf : ℝ}
    (hm : MemLp m 2 μ) (hR : MemLp R 2 μ) (hm0 : 0 < ∫ ω, m ω ∂μ) (hR0 : 0 < Var[R; μ])
    (hrf : rf * ∫ ω, m ω ∂μ = 1) (hprice : ∫ ω, m ω * R ω ∂μ = 1) :
    |sharpeRatio (∫ ω, R ω ∂μ) rf √(Var[R; μ])| ≤ √(Var[m; μ]) / ∫ ω, m ω ∂μ := by
  have hR1 : Integrable R μ := hR.integrable one_le_two
  have hm1 : Integrable m μ := hm.integrable one_le_two
  have hx : MemLp (fun ω ↦ R ω - rf) 2 μ := hR.sub (memLp_const rf)
  have hvar : Var[fun ω ↦ R ω - rf; μ] = Var[R; μ] :=
    variance_sub_const hR.aestronglyMeasurable rf
  have hmean : ∫ ω, (R ω - rf) ∂μ = (∫ ω, R ω ∂μ) - rf := by
    rw [integral_sub hR1 (integrable_const rf), integral_const, probReal_univ, one_smul]
  have hmR : Integrable (fun ω ↦ m ω * R ω) μ := hm.integrable_mul hR
  have hzero : ∫ ω, m ω * (R ω - rf) ∂μ = 0 := by
    simp_rw [mul_sub]
    rw [integral_sub hmR (hm1.mul_const rf), integral_mul_const, hprice]
    linarith
  have h := hansenJagannathan_bound hm hx hm0 (by rw [hvar]; exact hR0) hzero
  rw [hmean, hvar] at h
  unfold sharpeRatio
  rwa [abs_div, abs_of_pos (Real.sqrt_pos.mpr hR0)]

/-- **A priced return, against an affine discount factor.** If `m = a - b R_m` prices `R`
(`E[m R] = 1`) and the riskless return (`r_f E[m] = 1`), then
`E[R] - r_f = r_f b Cov(R, R_m)`. -/
lemma integral_sub_eq_of_affine_discountFactor [IsProbabilityMeasure μ] {m Rm R : Ω → ℝ}
    {a b rf : ℝ} (hm : ∀ ω, m ω = a - b * Rm ω) (hRm : MemLp Rm 2 μ) (hR : MemLp R 2 μ)
    (hrf : rf * ∫ ω, m ω ∂μ = 1) (hprice : ∫ ω, m ω * R ω ∂μ = 1) :
    ∫ ω, R ω ∂μ - rf = rf * b * cov[R, Rm; μ] := by
  obtain rfl : m = fun ω ↦ a - b * Rm ω := funext hm
  have hR1 : Integrable R μ := hR.integrable one_le_two
  have hRm1 : Integrable Rm μ := hRm.integrable one_le_two
  have hRmR : Integrable (fun ω ↦ Rm ω * R ω) μ := hRm.integrable_mul hR
  have e1 : ∫ ω, (a - b * Rm ω) ∂μ = a - b * ∫ ω, Rm ω ∂μ := by
    rw [integral_sub (integrable_const a) (hRm1.const_mul b), integral_const_mul,
      integral_const, probReal_univ, one_smul]
  have e2 : ∫ ω, (a - b * Rm ω) * R ω ∂μ = a * ∫ ω, R ω ∂μ - b * ∫ ω, Rm ω * R ω ∂μ := by
    have : ∀ ω, (a - b * Rm ω) * R ω = a * R ω - b * (Rm ω * R ω) := fun ω ↦ by ring
    simp_rw [this]
    rw [integral_sub (hR1.const_mul a) (hRmR.const_mul b), integral_const_mul,
      integral_const_mul]
  have hrf' : rf * (a - b * ∫ ω, Rm ω ∂μ) = 1 := by rw [← e1]; exact hrf
  have hpi : a * ∫ ω, R ω ∂μ - b * ∫ ω, Rm ω * R ω ∂μ = 1 := by rw [← e2]; exact hprice
  have hcov : cov[R, Rm; μ] = (∫ ω, Rm ω * R ω ∂μ) - (∫ ω, Rm ω ∂μ) * ∫ ω, R ω ∂μ := by
    rw [covariance_comm]
    exact covariance_eq_sub hRm hR
  rw [hcov]
  linear_combination rf * hpi - (∫ ω, R ω ∂μ) * hrf'

/-- **CAPM from a discount factor affine in the market return.** If `m = a - b R_m` prices the
return `R_i`, the market return `R_m` and the riskless return `r_f`, and `R_m` has nonzero
variance, then `E[R_i]` is on the security market line, `E[R_i] = r_f + β_i (E[R_m] - r_f)` with
`β_i = Cov(R_i, R_m) / Var R_m`. -/
theorem capm_of_affine_discountFactor [IsProbabilityMeasure μ] {m Rm Ri : Ω → ℝ} {a b rf : ℝ}
    (hm : ∀ ω, m ω = a - b * Rm ω) (hRm : MemLp Rm 2 μ) (hRi : MemLp Ri 2 μ)
    (hrf : rf * ∫ ω, m ω ∂μ = 1) (hpi : ∫ ω, m ω * Ri ω ∂μ = 1)
    (hpm : ∫ ω, m ω * Rm ω ∂μ = 1) (hvar : Var[Rm; μ] ≠ 0) :
    ∫ ω, Ri ω ∂μ =
      securityMarketLine rf (beta cov[Ri, Rm; μ] Var[Rm; μ]) (∫ ω, Rm ω ∂μ) := by
  have hi := integral_sub_eq_of_affine_discountFactor hm hRm hRi hrf hpi
  have hmk := integral_sub_eq_of_affine_discountFactor hm hRm hRm hrf hpm
  rw [covariance_self hRm.aemeasurable] at hmk
  unfold securityMarketLine beta
  rw [hmk]
  calc ∫ ω, Ri ω ∂μ = rf + rf * b * cov[Ri, Rm; μ] := by linarith
    _ = rf + cov[Ri, Rm; μ] / Var[Rm; μ] * (rf * b * Var[Rm; μ]) := by field_simp

section MarketPortfolio

variable {ι : Type*}

/-- The marginal variance `(Σ w)_i` of the market portfolio `∑ w_k R_k` is the covariance
`Cov(R_i, R_m)`, when `Σ` is the covariance matrix of the returns. -/
lemma marginalVariance_eq_covariance [IsFiniteMeasure μ] (s : Finset ι) (R : ι → Ω → ℝ)
    (hR : ∀ i, MemLp (R i) 2 μ) (w : ι → ℝ) (i : ι) :
    marginalVariance s (fun j k ↦ cov[R j, R k; μ]) w i = cov[R i, ∑ k ∈ s, w k • R k; μ] := by
  rw [covariance_sum_right' (fun k _ ↦ (hR k).const_smul (w k)) (hR i)]
  simp only [marginalVariance]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [covariance_smul_right]; ring

/-- **`CAPM_from_market_equilibrium` from a discount factor.** Let `m = a - b R_m` be a discount
factor affine in the return `R_m = ∑ w_k R_k` of a market portfolio of assets `R_k`, `k ∈ s`,
that prices every asset (`E[m R_k] = 1`) and the riskless return (`r_f E[m] = 1`). Then the
excess expected returns satisfy the tangent-portfolio cross-product condition (they are
`r_f b` times the marginal variances), so `CAPM_from_market_equilibrium` gives
`E[R_i] - r_f = β_i · (w · (E[R] - r_f))` with `β_i = (Σ w)_i / w ⬝ Σ w`, for the covariance
matrix `Σ` of the returns, whenever `w ⬝ Σ w ≠ 0`. -/
theorem capm_from_market_equilibrium_of_discountFactor [IsProbabilityMeasure μ] (s : Finset ι)
    (R : ι → Ω → ℝ) (hR : ∀ i, MemLp (R i) 2 μ) (w : ι → ℝ) {m : Ω → ℝ} {a b rf : ℝ}
    (hm : ∀ ω, m ω = a - b * (∑ k ∈ s, w k • R k) ω)
    (hrf : rf * ∫ ω, m ω ∂μ = 1) (hprice : ∀ i ∈ s, ∫ ω, m ω * R i ω ∂μ = 1) {i : ι}
    (hi : i ∈ s) (hvar : portfolioVarN s w (fun j k ↦ cov[R j, R k; μ]) ≠ 0) :
    (∫ ω, R i ω ∂μ) - rf =
      beta (marginalVariance s (fun j k ↦ cov[R j, R k; μ]) w i)
          (portfolioVarN s w (fun j k ↦ cov[R j, R k; μ])) *
        portfolioReturn s w (fun k ↦ (∫ ω, R k ω ∂μ) - rf) := by
  have hRm : MemLp (∑ k ∈ s, w k • R k) 2 μ :=
    memLp_finsetSum' s fun k _ ↦ (hR k).const_smul (w k)
  have hex (k : ι) (hk : k ∈ s) : (∫ ω, R k ω ∂μ) - rf
      = rf * b * marginalVariance s (fun j k ↦ cov[R j, R k; μ]) w k := by
    rw [marginalVariance_eq_covariance s R hR w k]
    exact integral_sub_eq_of_affine_discountFactor hm hRm (hR k) hrf (hprice k hk)
  exact CAPM_from_market_equilibrium s w (fun k ↦ (∫ ω, R k ω ∂μ) - rf)
    (fun j k ↦ cov[R j, R k; μ]) i hi hvar fun j hj k hk ↦ by
      rw [hex j hj, hex k hk]; ring

end MarketPortfolio

section FiniteStates

/-- **On a finite sample space the discount factor `q / p` of a state-price vector `q` prices by
state prices**: `E_P[(q / p) X] = ∑ ω, q ω X ω`. -/
theorem integral_discountFactor_mul {N : ℕ} (P : Measure (Fin N)) [IsProbabilityMeasure P]
    (hP : ∀ ω, 0 < P.real {ω}) (q X : Fin N → ℝ) :
    ∫ ω, (q ω / P.real {ω}) * X ω ∂P = statePricePricing Finset.univ q X := by
  rw [integral_fintype Integrable.of_finite, statePricePricing]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [smul_eq_mul]
  field_simp [(hP ω).ne']

/-- **Marginal utility is a stochastic discount factor.** At a local optimum of the expected
utility `∑ ω, P{ω} u(W ω)` on the budget set (`Choice/Utility/StatePriceDensity`), the random
variable `u'(W) / μ'` (for some `μ' > 0`) prices every asset: `E_P[(u'(W) / μ') A_k] = pr_k`. -/
theorem integral_marginalUtility_mul_eq {N M : ℕ} [NeZero N] (P : Measure (Fin N))
    [IsProbabilityMeasure P] (hP : ∀ ω, 0 < P.real {ω}) {u : ℝ → ℝ} {A : Fin M → Fin N → ℝ}
    {pr : Fin M → ℝ} {w₀ : ℝ} {θ : Fin M → ℝ}
    (hmax : IsLocalMaxOn (portfolioUtility (fun ω ↦ P.real {ω}) u A)
      {θ' | portfolioCost pr θ' = w₀} θ)
    (hθ : portfolioCost pr θ = w₀) (hw₀ : 0 < w₀)
    (hW : ∀ ω, 0 < portfolioPayoff A θ ω) (hu : ∀ ω, 0 < deriv u (portfolioPayoff A θ ω)) :
    ∃ μ' : ℝ, 0 < μ' ∧
      ∀ k, ∫ ω, (deriv u (portfolioPayoff A θ ω) / μ') * A k ω ∂P = pr k := by
  obtain ⟨μ', hμ', -, hprice⟩ := exists_statePrices_of_isLocalMaxOn hmax hθ hw₀ hP hW hu
  refine ⟨μ', hμ', fun k ↦ ?_⟩
  rw [← hprice k, ← integral_discountFactor_mul P hP]
  congr 1
  funext ω
  have := (hP ω).ne'
  field_simp

end FiniteStates

end MathFin
