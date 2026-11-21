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

* Spatial homogeneity: scaling spot and strike by a nonzero `c` leaves `d₁`, `d₂` fixed, and
  scales the closed form `bsV` by `c` for every real `c`.
* Time-volatility scaling: `(r, σ, τ) ↦ (c r, σ√c, τ/c)` fixes `r τ`, `σ² τ` and `σ √τ`, hence
  `d₁`, `d₂` and the closed form `bsV`. For zero rates and `c = τ` the scaling gives the
  dependence on `σ² τ` alone; `bsV_eq_totalVarianceCall`
  (`Models/ModelFree/CalendarArbitrage.lean`) is the corresponding statement through the
  definition of `totalVarianceCall`, for `σ, τ > 0`.

These are identities of the closed forms (the time-volatility rescaling for `c > 0`, the spatial
homogeneity of `bsV` for every real `c` and of `d₁`, `d₂` for `c ≠ 0`). They hold at every
input, including the junk corners (division by zero at `σ = 0` or `K = 0`, `√` of a negative,
`log` of a nonpositive), because both sides are the same expression of the junk value, up to the
factor `c` for the homogeneity statements; they are not claims that the value is a price, which
needs `σ > 0`, `0 < τ` and `0 < S, K`.

## Main results

* `bsd1_scale`, `bsd2_scale`, `bsV_scale`: spatial homogeneity.
* `bsd1_timeScale`, `bsd2_timeScale`, `bsV_timeScale`: time-volatility scaling, with the shared
  step `vol_sqrt_timeScale`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull] (10th ed., Pearson, 2018), ch. 15
  (the Black–Scholes closed form)

## Tags

Black–Scholes, scaling, homogeneity, total variance, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

/-- `d₁` is unchanged when spot and strike are scaled together by a nonzero `c`. -/
theorem bsd1_scale {S K r σ τ c : ℝ} (hc : c ≠ 0) :
    bsd1 (c * S) (c * K) r σ τ = bsd1 S K r σ τ := by
  simp [bsd1, mul_div_mul_left _ _ hc]

/-- `d₂` is unchanged when spot and strike are scaled together by a nonzero `c`. -/
theorem bsd2_scale {S K r σ τ c : ℝ} (hc : c ≠ 0) :
    bsd2 (c * S) (c * K) r σ τ = bsd2 S K r σ τ := by
  simp [bsd2, bsd1_scale hc]

/-- **Spatial homogeneity**: `bsV (c K) r σ (c S) τ = c · bsV K r σ S τ` for every real `c`. -/
theorem bsV_scale {K r σ S τ c : ℝ} :
    bsV (c * K) r σ (c * S) τ = c * bsV K r σ S τ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [bsV]
  unfold bsV
  rw [bsd1_scale hc, bsd2_scale hc]
  ring

/-- The volatility factor `σ √τ` is unchanged under `(σ, τ) ↦ (σ √c, τ / c)` for `c > 0`. -/
theorem vol_sqrt_timeScale {σ τ c : ℝ} (hc : 0 < c) :
    σ * Real.sqrt c * Real.sqrt (τ / c) = σ * Real.sqrt τ := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  rw [Real.sqrt_div' τ hc.le]; field_simp

/-- `d₁` is unchanged under `(r, σ, τ) ↦ (c r, σ √c, τ / c)` for `c > 0`: the map fixes
`σ² τ`, `r τ` and `σ √τ`. -/
theorem bsd1_timeScale {S K r σ τ c : ℝ} (hc : 0 < c) :
    bsd1 S K (c * r) (σ * Real.sqrt c) (τ / c) = bsd1 S K r σ τ := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hnum : (c * r + (σ * Real.sqrt c) ^ 2 / 2) * (τ / c) = (r + σ ^ 2 / 2) * τ := by
    rw [mul_pow, hsq]; field_simp
  unfold bsd1
  rw [hnum, vol_sqrt_timeScale hc]

/-- `d₂` is unchanged under `(r, σ, τ) ↦ (c r, σ √c, τ / c)` for `c > 0`. -/
theorem bsd2_timeScale {S K r σ τ c : ℝ} (hc : 0 < c) :
    bsd2 S K (c * r) (σ * Real.sqrt c) (τ / c) = bsd2 S K r σ τ := by
  rw [bsd2, bsd2, bsd1_timeScale hc, vol_sqrt_timeScale hc]

/-- **Time-volatility scaling**: `bsV K (c r) (σ √c) S (τ / c) = bsV K r σ S τ` for `c > 0`.
For `r = 0`, `c = τ` and `τ > 0` this gives the dependence of the call on `σ² τ` alone, from
which `bsV_eq_totalVarianceCall` (for `σ > 0`) follows together with the definition of
`totalVarianceCall`; here the rate is scaled with it so that `r τ` is fixed too. -/
theorem bsV_timeScale {K r σ S τ c : ℝ} (hc : 0 < c) :
    bsV K (c * r) (σ * Real.sqrt c) S (τ / c) = bsV K r σ S τ := by
  have hexp : c * r * (τ / c) = r * τ := by field_simp
  unfold bsV
  rw [bsd1_timeScale hc, bsd2_timeScale hc, hexp]

end MathFin
