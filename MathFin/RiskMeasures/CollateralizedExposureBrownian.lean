/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.BlackScholes.MertonModel
public import MathFin.FixedIncome.CVA
public import MathFin.Foundations.GaussianMoments

/-!
# Collateralized exposure under a Brownian-driven process

Collateral is modelled as an actual composition of the exposure process — `C t := V (t - Δ)`,
the process itself evaluated `Δ` earlier — never an opaque scalar.

* `collateralizedExposure V Δ t ω = max (V t ω - V (t - Δ) ω) 0`, time indexed by `ℝ≥0` to match
  `IsPreBrownianReal`. The lag `t - Δ` is `ℝ≥0` truncated subtraction, so for `Δ > t` it collapses
  to `0` (i.e. `C_t` would silently become `V_0`); the theorem below guards this with `Δ ≤ t`, so
  no junk value is ever read off by a proved result.
* `collateralizedExposure_brownian_gaussian`: for `V t = m + σ B t` with `B` an actual pre-Brownian
  motion (`IsPreBrownianReal`), `0 < Δ ≤ t`, `σ > 0`, the collateralized exposure has closed form
  `E[(V_t - V_{t-Δ})⁺] = σ√Δ · φ(0)`. The law of the increment `B_t - B_{t-Δ}` is derived
  (not hypothesized) from the Brownian finite-dimensional laws (`MathFin.hasLaw_increment`, over
  Mathlib's `IsPreBrownianReal.hasLaw_sub`), standardized to a driver `Z ~ N(0,1)` by
  `hasLaw_sub_div_of_gaussianReal`, so that `V_t - V_{t-Δ} = σ√Δ · Z` with the σ-scale entering
  as the volatility parameter of `CVA.expectedExposure_gaussian` — the same machinery as
  `ExposureMeasures.lean`'s Gaussian exposure measures. The mean is `0` (an increment
  of a driftless driver), so the standardized argument `d = a/(b√s)` collapses to `0` and the
  answer is the bare Gaussian density `φ(0)` scaled by the volatility of the increment.

## References

* J. C. Hull, *Options, Futures, and Other Derivatives* (collateralized exposure / CSAs).
-/

@[expose] public section

namespace MathFin.CVA

open MeasureTheory Real ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Collateralized exposure at time `t` with lag `Δ`: `max(V_t - C_t, 0)` with the lagged
collateral `C_t := V_{t-Δ}` substituted as an actual earlier value of the same process. -/
noncomputable def collateralizedExposure (V : ℝ≥0 → Ω → ℝ) (Δ t : ℝ≥0) (ω : Ω) : ℝ :=
  max (V t ω - V (t - Δ) ω) 0

/-- **Collateralized exposure under a Brownian-driven process, in closed form**: for
`V_t = m + σ B_t` with `B` an actual pre-Brownian motion, `σ > 0` and `0 < Δ ≤ t`,
`E[(V_t - V_{t-Δ})⁺] = σ√Δ · φ(0)`. The law of the collateralized difference is derived from
`MathFin.hasLaw_increment` (over Mathlib's `IsPreBrownianReal.hasLaw_sub`), not hypothesized. -/
theorem collateralizedExposure_brownian_gaussian [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (m σ : ℝ) (hσ : 0 < σ) {Δ t : ℝ≥0} (hΔpos : 0 < Δ)
    (hΔt : Δ ≤ t) :
    ∫ ω, collateralizedExposure (fun t ω ↦ m + σ * B t ω) Δ t ω ∂P
      = σ * √(Δ : ℝ) * gaussianPDFReal 0 1 0 := by
  have hΔ : (0 : ℝ) < Δ := hΔpos
  have hinc : HasLaw (fun ω ↦ B t ω - B (t - Δ) ω) (gaussianReal 0 Δ) P := by
    simpa [tsub_tsub_cancel_of_le hΔt] using hasLaw_increment hB (tsub_le_self (a := t) (b := Δ))
  have hZ : HasLaw (fun ω ↦ (B t ω - B (t - Δ) ω) / √(Δ : ℝ)) (gaussianReal 0 1) P := by
    simpa using hasLaw_sub_div_of_gaussianReal hinc (Real.sqrt_pos.mpr hΔ) (Real.sq_sqrt hΔ.le).symm
  have hΔne : √(Δ : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hΔ).ne'
  have hpt (ω : Ω) : collateralizedExposure (fun t ω ↦ m + σ * B t ω) Δ t ω
      = max (0 + σ * √(Δ : ℝ) * ((B t ω - B (t - Δ) ω) / √(Δ : ℝ))) 0 := by
    rw [collateralizedExposure, zero_add, mul_assoc, mul_div_cancel₀ _ hΔne]
    congr 1
    ring
  simp_rw [hpt]
  rw [expectedExposure_gaussian hZ hσ hΔ]
  simp

end MathFin.CVA
