/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.PDE

/-!
# Spatial and time-volatility scaling of the Black–Scholes call

Two invariances of `bsd1`, `bsd2` and `bsV` that follow from the formulas alone.

* Spatial homogeneity: scaling spot and strike by `c > 0` leaves `d₁`, `d₂` fixed and scales the
  price by `c`.
* Time-volatility scaling: `(r, σ, τ) ↦ (c r, σ√c, τ/c)` fixes `r τ`, `σ² τ` and `σ √τ`, hence
  `d₁`, `d₂` and the price. For zero rates and `c = τ` the scaling gives the dependence on
  `σ² τ` alone, of which `bsV_eq_totalVarianceCall`
  (`Models/ModelFree/CalendarArbitrage.lean`) is the `r = 0`, `c = τ` instance.

## Main results

* `bsd1_scale`, `bsd2_scale`, `bsV_scale`: spatial homogeneity.
* `bsd1_timeScale`, `bsd2_timeScale`, `bsV_timeScale`: time-volatility scaling.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull] (10th ed., Pearson, 2018), ch. 15

## Tags

Black–Scholes, scaling, homogeneity, total variance, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

/-- `d₁` is unchanged when spot and strike are scaled together by `c > 0`, for positive spot and
strike (where `log (S / K)` is the log-moneyness); the positivity hypotheses are guards for that
meaning, not used by the algebra. -/
theorem bsd1_scale {S K r σ τ c : ℝ} (hc : 0 < c) (_hS : 0 < S) (_hK : 0 < K) :
    bsd1 (c * S) (c * K) r σ τ = bsd1 S K r σ τ := by
  simp [bsd1, mul_div_mul_left _ _ hc.ne']

/-- `d₂` is unchanged when spot and strike are scaled together by `c > 0`, for positive spot and
strike; the positivity hypotheses are guards for that meaning, not used by the algebra. -/
theorem bsd2_scale {S K r σ τ c : ℝ} (hc : 0 < c) (_hS : 0 < S) (_hK : 0 < K) :
    bsd2 (c * S) (c * K) r σ τ = bsd2 S K r σ τ := by
  simp [bsd2, bsd1_scale hc _hS _hK]

/-- **Spatial homogeneity**: `bsV (c K) r σ (c S) τ = c · bsV K r σ S τ` for `c > 0` and positive
spot and strike. The positivity hypotheses are guards for the price reading (the logarithm of the
moneyness off its junk value) that the algebra does not use. -/
theorem bsV_scale {K r σ S τ c : ℝ} (hc : 0 < c) (_hS : 0 < S) (_hK : 0 < K) :
    bsV (c * K) r σ (c * S) τ = c * bsV K r σ S τ := by
  unfold bsV
  rw [bsd1_scale hc _hS _hK, bsd2_scale hc _hS _hK]
  ring

/-- `d₁` is unchanged under `(r, σ, τ) ↦ (c r, σ √c, τ / c)` for `c > 0`: the map fixes
`σ² τ`, `r τ` and `σ √τ`. Stated for positive spot, strike, volatility and maturity, where `d₁`
is the usual parameter; at `σ = 0` or `τ ≤ 0` the denominator `σ √τ` is `0` and `d₁` is a junk
value. The positivity hypotheses are guards for that meaning, not used by the algebra. -/
theorem bsd1_timeScale {S K r σ τ c : ℝ} (hc : 0 < c) (_hS : 0 < S) (_hK : 0 < K)
    (_hσ : 0 < σ) (_hτ : 0 < τ) :
    bsd1 S K (c * r) (σ * Real.sqrt c) (τ / c) = bsd1 S K r σ τ := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hv : Real.sqrt (τ / c) = Real.sqrt τ / Real.sqrt c := Real.sqrt_div' τ hc.le
  have hnum : (c * r + (σ * Real.sqrt c) ^ 2 / 2) * (τ / c) = (r + σ ^ 2 / 2) * τ := by
    rw [mul_pow, hsq]; field_simp
  have hden : σ * Real.sqrt c * Real.sqrt (τ / c) = σ * Real.sqrt τ := by
    rw [hv]; field_simp
  unfold bsd1
  rw [hnum, hden]

/-- `d₂` is unchanged under `(r, σ, τ) ↦ (c r, σ √c, τ / c)` for `c > 0`, for positive spot, strike,
volatility and maturity; the positivity hypotheses are guards, not used by the algebra. -/
theorem bsd2_timeScale {S K r σ τ c : ℝ} (hc : 0 < c) (_hS : 0 < S) (_hK : 0 < K) (_hσ : 0 < σ)
    (_hτ : 0 < τ) :
    bsd2 S K (c * r) (σ * Real.sqrt c) (τ / c) = bsd2 S K r σ τ := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hv : Real.sqrt (τ / c) = Real.sqrt τ / Real.sqrt c := Real.sqrt_div' τ hc.le
  have hden : σ * Real.sqrt c * Real.sqrt (τ / c) = σ * Real.sqrt τ := by
    rw [hv]; field_simp
  rw [bsd2, bsd2, bsd1_timeScale hc _hS _hK _hσ _hτ, hden]

/-- **Time-volatility scaling**: `bsV K (c r) (σ √c) S (τ / c) = bsV K r σ S τ` for `c > 0` and
positive spot, strike, volatility and maturity.
For `r = 0` and `c = τ` this gives the dependence of the call on `σ² τ` alone, of which
`bsV_eq_totalVarianceCall` is the instance; here the rate is scaled with it so that `r τ` is
fixed too. The positivity hypotheses are guards for the price reading (`σ √τ` and the logarithm
off their junk values) that the algebra does not use. -/
theorem bsV_timeScale {K r σ S τ c : ℝ} (hc : 0 < c) (_hS : 0 < S) (_hK : 0 < K) (_hσ : 0 < σ)
    (_hτ : 0 < τ) :
    bsV K (c * r) (σ * Real.sqrt c) S (τ / c) = bsV K r σ S τ := by
  have hexp : c * r * (τ / c) = r * τ := by field_simp
  unfold bsV
  rw [bsd1_timeScale hc _hS _hK _hσ _hτ, bsd2_timeScale hc _hS _hK _hσ _hτ, hexp]

end MathFin
