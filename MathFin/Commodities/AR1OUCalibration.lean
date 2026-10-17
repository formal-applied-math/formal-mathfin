/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.FixedIncome.VasicekSDE
public import MathFin.FixedIncome.Vasicek

/-!
# AR(1) ↔ OU parameter inversion

A discretely-sampled Ornstein-Uhlenbeck (Vasicek) process observed on a grid
of spacing `Δt` is exactly an AR(1) process `x_{n+1} = φ x_n + ε_n`. This
file records the standard dictionary between the AR(1) fit `(φ, Var(resid))`
and the continuous-time OU parameters `(k, σ)`:

  `φ = e^{−kΔt}`                        (mean-reversion discount)
  `k = −ln(φ)/Δt`                       (inverse: mean-reversion speed)
  `σ² = 2k·Var(resid) / (1 − e^{−2kΔt})`  (diffusion coefficient)
  `half-life = ln 2 / k`

This is pure algebra given the existing closed-form Vasicek/OU terminal-law
substrate (`FixedIncome/VasicekSDE.lean`): `ouPhiFromK` is literally the decay
factor appearing in `vasicekSDEMean`, and `ouSigmaSqFromVar` inverts
`vasicekSDEVariance` for `σ²` given an observed residual variance.

## Main results

* `ouPhiFromK`, `kFromPhi` : the `φ ↔ k` dictionary, mutually inverse on
  `Δt ≠ 0` (`kFromPhi_ouPhiFromK`) and on `φ > 0` (`ouPhiFromK_kFromPhi`).
* `ouSigmaSqFromVar` : the implied diffusion coefficient from a fitted AR(1)
  residual variance.
* `ouPhiFromK_halfLife` : `FixedIncome.Vasicek`'s existing `meanReversionHalfLife`
  (`ln 2 / k`) is indeed the time at which the decay factor hits `1/2`.
* `ouSigmaSqFromVar_vasicekSDEVariance` : `ouSigmaSqFromVar` genuinely inverts
  `vasicekSDEVariance`, closing the round-trip the module docstring claims.
-/

@[expose] public section

namespace MathFin

/-! ### The `φ ↔ k` dictionary -/

/-- **AR(1) discount factor from OU speed**: `φ = e^{−kΔt}`. -/
noncomputable def ouPhiFromK (k Δt : ℝ) : ℝ := Real.exp (-(k * Δt))

/-- **OU mean-reversion speed from AR(1) discount factor**: `k = −ln(φ)/Δt`. -/
noncomputable def kFromPhi (φ Δt : ℝ) : ℝ := -Real.log φ / Δt

/-- **Diffusion coefficient from fitted residual variance**:
`σ² = 2k·Var(resid) / (1 − e^{−2kΔt})`, inverting `vasicekSDEVariance` for
`σ²` given the AR(1) fit's residual variance at spacing `Δt`. -/
noncomputable def ouSigmaSqFromVar (k residVar Δt : ℝ) : ℝ :=
  2 * k * residVar / (1 - Real.exp (-(2 * k * Δt)))

/-- **`ouSigmaSqFromVar` genuinely inverts `vasicekSDEVariance`**: feeding it
the exact Vasicek/OU variance at spacing `Δt` recovers the diffusion
coefficient `σ²` it came from, for `k ≠ 0` and `1 − e^{−2kΔt} ≠ 0` (e.g.
`k, Δt` both nonzero). -/
theorem ouSigmaSqFromVar_vasicekSDEVariance (σ k Δt : ℝ) (hk : k ≠ 0)
    (hden : 1 - Real.exp (-(2 * k * Δt)) ≠ 0) :
    ouSigmaSqFromVar k (vasicekSDEVariance σ k Δt) Δt = σ ^ 2 := by
  unfold ouSigmaSqFromVar vasicekSDEVariance
  field_simp

/-- Recovering `k` from the `φ` it generates: `kFromPhi (ouPhiFromK k Δt) Δt = k`,
for any `Δt ≠ 0`. -/
theorem kFromPhi_ouPhiFromK (k Δt : ℝ) (hΔt : Δt ≠ 0) :
    kFromPhi (ouPhiFromK k Δt) Δt = k := by
  unfold kFromPhi ouPhiFromK
  rw [Real.log_exp]
  field_simp

/-- Recovering `φ` from the `k` it generates: `ouPhiFromK (kFromPhi φ Δt) Δt = φ`,
for `φ > 0` and `Δt ≠ 0`. -/
theorem ouPhiFromK_kFromPhi (φ Δt : ℝ) (hφ : 0 < φ) (hΔt : Δt ≠ 0) :
    ouPhiFromK (kFromPhi φ Δt) Δt = φ := by
  unfold ouPhiFromK kFromPhi
  rw [neg_div, neg_mul, neg_neg, div_mul_cancel₀ _ hΔt, Real.exp_log hφ]

/-- The decay factor at `FixedIncome.Vasicek`'s existing `meanReversionHalfLife`
is exactly `1/2`, for `k ≠ 0`. -/
theorem ouPhiFromK_halfLife (k : ℝ) (hk : k ≠ 0) :
    ouPhiFromK k (meanReversionHalfLife k) = 1 / 2 := by
  unfold ouPhiFromK meanReversionHalfLife
  rw [mul_div_cancel₀ _ hk, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2), one_div]

end MathFin
