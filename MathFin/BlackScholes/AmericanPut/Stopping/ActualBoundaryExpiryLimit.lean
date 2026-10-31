/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualBoundaryContinuity
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualBoundaryNormalization

/-! # The actual exercise boundary tends to the strike at expiry

For `0 < r` and `0 ≤ q ≤ r`, the optimal-stopping exercise boundary of the American put
converges to the strike as time to expiry decreases to zero: `B(τ) → K` as `τ ↓ 0`.

On this parameter cell the boundary-at-expiry value `K * min 1 (r / q)` used by
fixed-point American-put engines equals `K`. Only this cell is covered. The cells
`q > r > 0`, `q < 0`, and negative rates (including the double-boundary case) are not
treated here, because the underlying boundary theory assumes `0 < r` and `0 ≤ q ≤ r`.

## Result

`tendsto_brownianUsualExerciseBoundary_expiry`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Filter Boundary
open scoped Topology

/-- The actual exercise boundary of the American put converges to the strike `K` at
expiry, `lim_{τ ↓ 0} B(τ) = K`, when `0 < r` and `0 ≤ q ≤ r`. -/
theorem tendsto_brownianUsualExerciseBoundary_expiry {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ) :
    Tendsto (fun τ : ℝ ↦ brownianUsualExerciseBoundary K r q σ τ.toNNReal)
      (𝓝[>] 0) (𝓝 K) := by
  obtain ⟨hk, hh, hhk⟩ := normalized_rates_admissible hr hq hqr hσ
  have hcont : ContinuousAt
      (fun τ : ℝ ↦ K * canonicalStockBoundary (normalizedRate r σ) (normalizedRate q σ)
        (σ ^ 2 / 2 * τ)) 0 := by
    refine continuousAt_const.mul (ContinuousAt.comp (g := canonicalStockBoundary _ _) ?_ ?_)
    · simpa using canonicalStockBoundary_continuousAt hk hh hhk le_rfl
    · fun_prop
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [mul_zero, canonicalStockBoundary_initial hk.le, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact (brownianUsualExerciseBoundary_eq_scaled_canonical hK hr hq hqr hσ hτ).symm

end MathFin.BlackScholes.AmericanPut.Stopping
