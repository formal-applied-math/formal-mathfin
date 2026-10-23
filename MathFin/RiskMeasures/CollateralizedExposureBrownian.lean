/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.FixedIncome.CVA
public import MathFin.Foundations.GaussianMoments

/-!
# Collateralized exposure under a Brownian-driven process

Collateral is modelled as an actual composition of the exposure process — `C t := V (t - Δ)`,
the process itself evaluated `Δ` earlier — never an opaque scalar (contrast the deleted
`CollateralizedExposure.lean` of #272, whose `laggedCollateral` was the identity function on a
free real variable).

* `collateralizedExposure V Δ t ω = max (V t ω - V (t - Δ) ω) 0`, time indexed by `ℝ≥0` to match
  `IsPreBrownianReal`.
* `collateralizedExposure_brownian_gaussian`: for `V t = m + σ B t` with `B` an actual pre-Brownian
  motion (`IsPreBrownianReal`), `0 < Δ ≤ t`, `σ > 0`, the collateralized exposure has closed form
  `E[(V_t - V_{t-Δ})⁺] = σ√Δ · φ(0)`. The law of `V_t - V_{t-Δ} = σ(B_t - B_{t-Δ})` is derived
  (not hypothesized) from the Brownian increment's law `hasLaw_increment` (stationary/independent
  increments) via the Gaussian-scaling lemma `gaussianReal_const_mul`, standardized to a driver
  `Z ~ N(0,1)` and fed into `CVA.expectedExposure_gaussian` — the same machinery as
  `ExposureMeasures.lean`'s Gaussian exposure measures. The mean is `0` (an increment of a driftless
  driver), so the usual `d = a/(b√s)` quantile collapses to `0` and the answer is the bare Gaussian
  density `φ(0)` scaled by the volatility of the increment.

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

/-- Standardizing a mean-zero Gaussian law: if `Y ~ N(0, v)` with `v > 0`, then `Y / √v ~ N(0,1)`.
A genuine derivation from Mathlib's `gaussianReal_div_const`, not a hypothesis. -/
private lemma hasLaw_standard_of_hasLaw_gaussianReal_zero {Y : Ω → ℝ} {v : ℝ≥0}
    (hY : HasLaw Y (gaussianReal 0 v) P) (hv : 0 < v) :
    HasLaw (fun ω ↦ Y ω / √(v : ℝ)) (gaussianReal 0 1) P := by
  have hv' : (0:ℝ) < (v:ℝ) := NNReal.coe_pos.mpr hv
  have hc := gaussianReal_div_const hY √(v:ℝ)
  have hveq : v / NNReal.mk ((√(v:ℝ)) ^ 2) (sq_nonneg _) = 1 := by
    apply NNReal.coe_injective
    push_cast
    rw [Real.sq_sqrt hv'.le, div_self hv'.ne']
  rwa [zero_div, hveq] at hc

/-- **Collateralized exposure under a Brownian-driven process, in closed form**: for
`V_t = m + σ B_t` with `B` an actual pre-Brownian motion, `σ > 0` and `0 < Δ ≤ t`,
`E[(V_t - V_{t-Δ})⁺] = σ√Δ · φ(0)`. The law of the collateralized difference is derived from
`hasLaw_increment` (stationary/independent increments of `B`), not hypothesized. -/
theorem collateralizedExposure_brownian_gaussian [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (m σ : ℝ) (hσ : 0 < σ) {Δ t : ℝ≥0} (hΔpos : 0 < Δ)
    (hΔt : Δ ≤ t) :
    ∫ ω, collateralizedExposure (fun t ω ↦ m + σ * B t ω) Δ t ω ∂P
      = σ * √(Δ : ℝ) * gaussianPDFReal 0 1 0 := by
  have hinc : HasLaw (fun ω ↦ B t ω - B (t - Δ) ω) (gaussianReal 0 Δ) P := by
    have h := hasLaw_increment hB (tsub_le_self (a := t) (b := Δ))
    rwa [tsub_tsub_cancel_of_le hΔt] at h
  have hZ : HasLaw (fun ω ↦ (B t ω - B (t - Δ) ω) / √(Δ : ℝ)) (gaussianReal 0 1) P :=
    hasLaw_standard_of_hasLaw_gaussianReal_zero hinc hΔpos
  have hΔne : √(Δ : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (NNReal.coe_pos.mpr hΔpos)
  have hpt : ∀ ω, collateralizedExposure (fun t ω ↦ m + σ * B t ω) Δ t ω
      = max (0 + σ * √(Δ : ℝ) * ((B t ω - B (t - Δ) ω) / √(Δ : ℝ))) 0 := fun ω ↦ by
    unfold collateralizedExposure
    rw [zero_add, mul_assoc, mul_div_cancel₀ _ hΔne]
    congr 1
    ring
  simp_rw [hpt]
  rw [expectedExposure_gaussian hZ hσ (NNReal.coe_pos.mpr hΔpos)]
  simp

end MathFin.CVA
