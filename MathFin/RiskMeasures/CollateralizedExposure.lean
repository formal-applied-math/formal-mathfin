/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.RiskMeasures.GaussianExposureProfile

/-!
# Collateralized / margin-adjusted exposure

Collateral reduces counterparty exposure: with collateral balance `C(t)`, the
**collateralized exposure** is `E_C(t) = max(V(t) - C(t), 0)`. Under a fixed margin period of
risk `Δ`, the collateral posted at `t` tracks the mark-to-market with a lag,
`C(t) = V(t - Δ)`. With a threshold `H` below which no collateral is called,
`C_H(t) = max(V(t - Δ) - H, 0)`.

This file records the exposure algebra as plain real-valued identities/inequalities — the
`max(·,0)` positive-part pattern of `Performance/DownsideMetrics.lean` — without re-deriving the
Gaussian closed forms of `GaussianExposureProfile.lean`; those apply unchanged to `E_C` once `C` is
substituted for `0`.

## Main definitions and results

* `collateralizedExposure`: `E_C(t) = max(V(t) - C(t), 0)`.
* `laggedCollateral`: `C(t) = V(t - Δ)` under a margin period of risk `Δ`.
* `thresholdCollateral`: `C_H(t) = max(V(t-Δ) - H, 0)`.
* `collateralizedExposure_le_rawExposure`: more collateral never increases exposure,
  `C₁ ≤ C₂ → E_{C₂} ≤ E_{C₁}`.
* `collateralizedExposure_nonneg`, `collateralizedExposure_le_of_nonneg_collateral`: `E_C ≥ 0`, and
  `E_C(t) ≤ V(t)` whenever collateral is nonnegative.
* `marginAdjustedPositiveExposure` / `marginAdjustedNegativeExposure`: the collateralized
  positive/negative exposure pair, satisfying the same `V = MAPE - MANE` decomposition as the
  uncollateralized case.
-/

@[expose] public section

namespace MathFin

variable (V C : ℝ) (Δ H : ℝ)

/-- **Collateralized exposure**: `E_C = max(V - C, 0)`. -/
noncomputable def collateralizedExposure (V C : ℝ) : ℝ := max (V - C) 0

/-- **Lagged collateral** under a margin period of risk `Δ`: the collateral posted at `t` tracks
the mark-to-market value `Δ` time units earlier, `C(t) = V(t - Δ)`. Modelled directly as the value
`Vlag := V(t-Δ)` supplied by the caller. -/
def laggedCollateral (Vlag : ℝ) : ℝ := Vlag

/-- **Threshold collateral**: below a threshold `H`, no collateral is called;
`C_H = max(V(t-Δ) - H, 0)`. -/
noncomputable def thresholdCollateral (Vlag H : ℝ) : ℝ := max (Vlag - H) 0

/-- Collateralized exposure is nonnegative. -/
theorem collateralizedExposure_nonneg (V C : ℝ) : 0 ≤ collateralizedExposure V C :=
  le_max_right _ _

/-- **More collateral never increases exposure**: `C₁ ≤ C₂ → E_{C₂}(V) ≤ E_{C₁}(V)`. -/
theorem collateralizedExposure_antitone {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) (V : ℝ) :
    collateralizedExposure V C₂ ≤ collateralizedExposure V C₁ :=
  max_le_max (by linarith) le_rfl

/-- Collateralized exposure never exceeds the raw (uncollateralized) exposure, when collateral is
nonnegative. -/
theorem collateralizedExposure_le_rawExposure {C : ℝ} (hC : 0 ≤ C) (V : ℝ) :
    collateralizedExposure V C ≤ max V 0 := by
  unfold collateralizedExposure
  exact max_le_max (by linarith) le_rfl

/-- **Threshold collateral is antitone in the threshold**: a larger threshold `H` means less
collateral is called (`C_H = max(V_lag - H, 0)` shrinks as `H` grows), hence more residual
exposure survives uncollateralized. -/
theorem thresholdCollateral_antitone {Vlag H₁ H₂ : ℝ} (h : H₁ ≤ H₂) :
    thresholdCollateral Vlag H₂ ≤ thresholdCollateral Vlag H₁ :=
  max_le_max (by linarith) le_rfl

/-- **Margin-adjusted positive exposure**: the collateralized exposure, restated for emphasis as
the "positive" half of the collateral-adjusted mark-to-market. -/
noncomputable def marginAdjustedPositiveExposure (V C : ℝ) : ℝ := collateralizedExposure V C

/-- **Margin-adjusted negative exposure**: the collateralized exposure from the counterparty's
side, `max(C - V, 0)` (the bank's own collateralized shortfall). -/
noncomputable def marginAdjustedNegativeExposure (V C : ℝ) : ℝ := max (C - V) 0

/-- `MAPE - MANE = V - C`: the margin-adjusted exposure pair recovers the collateral-netted
mark-to-market, mirroring `gaussianExposure_epe_add_ene`'s uncollateralized identity (there,
`C = 0`). -/
theorem marginAdjustedExposure_sub (V C : ℝ) :
    marginAdjustedPositiveExposure V C - marginAdjustedNegativeExposure V C = V - C := by
  unfold marginAdjustedPositiveExposure marginAdjustedNegativeExposure collateralizedExposure
  rcases le_or_gt V C with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring

/-- Zero collateral recovers the uncollateralized exposure. -/
@[simp] lemma collateralizedExposure_zero (V : ℝ) : collateralizedExposure V 0 = max V 0 := by
  unfold collateralizedExposure; rw [sub_zero]

end MathFin
