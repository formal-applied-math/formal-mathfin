/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Mathlib

/-!
# Coordinates in Chen–Chadam–Jiang–Zheng (2008), Section 1

The paper uses `t = σ² (T_F - T) / 2` and `S_f(T) = E exp(s(t))`.
These are generic change-of-variable results for an arbitrary function `s`.
They do NOT establish that `s` is an optimal exercise boundary or that it is convex.
The positive interest-rate assumption belongs to the outstanding PDE theorem;
the coordinate change itself does not involve the rate.

## Result

Public entry points include `normalizedTime`, `stockBoundary`, `normalizedTime_pos`,
`stockBoundary_expiry`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

/-- Dimensionless time remaining. `T` is calendar time, `expiry` is maturity. -/
noncomputable def normalizedTime (σ expiry T : ℝ) : ℝ :=
  σ ^ 2 / 2 * (expiry - T)

/-- Stock-price boundary reconstructed from a candidate log-boundary. -/
noncomputable def stockBoundary (E σ expiry : ℝ) (s : ℝ → ℝ) (T : ℝ) : ℝ :=
  E * Real.exp (s (normalizedTime σ expiry T))

theorem normalizedTime_pos {σ expiry T : ℝ} (hσ : 0 < σ) (hT : T < expiry) :
    0 < normalizedTime σ expiry T := by
  exact mul_pos (div_pos (sq_pos_of_pos hσ) (by norm_num)) (sub_pos.mpr hT)

/-- At expiry the convention `s(0) = 0` gives `S_f(T_F) = E`. -/
theorem stockBoundary_expiry (E σ expiry : ℝ) {s : ℝ → ℝ} (hs : s 0 = 0) :
    stockBoundary E σ expiry s expiry = E := by
  simp [stockBoundary, normalizedTime, hs]

theorem hasDerivAt_normalizedTime (σ expiry T : ℝ) :
    HasDerivAt (normalizedTime σ expiry) (-(σ ^ 2 / 2)) T := by
  change HasDerivAt (fun U : ℝ => σ ^ 2 / 2 * (expiry - U)) (-(σ ^ 2 / 2)) T
  convert! ((hasDerivAt_id T).const_sub expiry).const_mul (σ ^ 2 / 2) using 1
  ring

/-- The first derivative under the paper's time reversal and exponential map. -/
theorem hasDerivAt_stockBoundary (E σ expiry T : ℝ) {s : ℝ → ℝ} {ds : ℝ}
    (hs : HasDerivAt s ds (normalizedTime σ expiry T)) :
    HasDerivAt (stockBoundary E σ expiry s)
      (-(σ ^ 2 / 2) * (E * Real.exp (s (normalizedTime σ expiry T))) * ds) T := by
  convert ((hs.comp T (hasDerivAt_normalizedTime σ expiry T)).exp).const_mul E using 1 <;>
    first | rfl | (simp only [Function.comp_apply]; ring)

/-- Equation following Theorem 1.1, with differentiability assumptions explicit.

No assertion about convexity or optimal stopping is hidden in these hypotheses.
The derivative of `s` is needed on positive times to identify the derivative of
`stockBoundary` in a neighbourhood of `T`; the second derivative is local.
-/
theorem deriv2_stockBoundary (E σ expiry : ℝ) {s ds : ℝ → ℝ} {dds T : ℝ}
    (hσ : 0 < σ) (hT : T < expiry)
    (hs : ∀ t, 0 < t → HasDerivAt s (ds t) t)
    (hds : HasDerivAt ds dds (normalizedTime σ expiry T)) :
    deriv (deriv (stockBoundary E σ expiry s)) T =
      σ ^ 4 / 4 * (E * Real.exp (s (normalizedTime σ expiry T))) *
        (dds + (ds (normalizedTime σ expiry T)) ^ 2) := by
  let c := σ ^ 2 / 2
  have htime := hasDerivAt_normalizedTime σ expiry T
  have hsT := hs _ (normalizedTime_pos hσ hT)
  have hprice := hasDerivAt_stockBoundary E σ expiry T hsT
  have hslope := ((hprice.const_mul (-c)).mul (hds.comp T htime))
  have heq : deriv (stockBoundary E σ expiry s) =ᶠ[nhds T]
      (fun U => -c * stockBoundary E σ expiry s U * ds (normalizedTime σ expiry U)) := by
    filter_upwards [isOpen_Iio.mem_nhds hT] with U hU
    exact (hasDerivAt_stockBoundary E σ expiry U (hs _ (normalizedTime_pos hσ hU))).deriv
  rw [(hslope.congr_of_eventuallyEq heq).deriv]
  dsimp [c, stockBoundary]
  ring

/-- Strict positivity of log-boundary curvature implies stock-boundary curvature.
This is only the coordinate implication, not a proof of the hypothesis `0 < dds`.
-/
theorem deriv2_stockBoundary_pos {E σ expiry T dds : ℝ} {s ds : ℝ → ℝ}
    (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry)
    (hs : ∀ t, 0 < t → HasDerivAt s (ds t) t)
    (hds : HasDerivAt ds dds (normalizedTime σ expiry T)) (hdds : 0 < dds) :
    0 < deriv (deriv (stockBoundary E σ expiry s)) T := by
  rw [deriv2_stockBoundary E σ expiry hσ hT hs hds]
  positivity

/-- Weak log curvature plus nonzero log-boundary speed gives STRICT stock
curvature. This is the coordinate implication used by the proposed extension;
it does not strengthen weak log curvature to strict log curvature. -/
theorem deriv2_stockBoundary_pos_of_nonneg {E σ expiry T dds : ℝ} {s ds : ℝ → ℝ}
    (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry)
    (hs : ∀ t, 0 < t → HasDerivAt s (ds t) t)
    (hds : HasDerivAt ds dds (normalizedTime σ expiry T)) (hdds : 0 ≤ dds)
    (hspeed : ds (normalizedTime σ expiry T) ≠ 0) :
    0 < deriv (deriv (stockBoundary E σ expiry s)) T := by
  rw [deriv2_stockBoundary E σ expiry hσ hT hs hds]
  have hsum : 0 < dds + ds (normalizedTime σ expiry T) ^ 2 :=
    add_pos_of_nonneg_of_pos hdds (sq_pos_of_ne_zero hspeed)
  positivity

/-- Ordinary convexity is preserved by the coordinate change, including expiry
if the candidate log-boundary is convex on the closed nonnegative half-line.
This does not assume differentiability at expiry, where the paper has a singularity.
-/
theorem stockBoundary_convexOn {E σ expiry : ℝ} {s : ℝ → ℝ}
    (hE : 0 ≤ E) (hs : ConvexOn ℝ (Set.Ici 0) s) :
    ConvexOn ℝ (Set.Iic expiry) (stockBoundary E σ expiry s) := by
  refine ⟨convex_Iic expiry, ?_⟩
  intro T₁ hT₁ T₂ hT₂ a b ha hb hab
  have ht₁ : normalizedTime σ expiry T₁ ∈ Set.Ici 0 :=
    mul_nonneg (div_nonneg (sq_nonneg σ) (by norm_num)) (sub_nonneg.mpr hT₁)
  have ht₂ : normalizedTime σ expiry T₂ ∈ Set.Ici 0 :=
    mul_nonneg (div_nonneg (sq_nonneg σ) (by norm_num)) (sub_nonneg.mpr hT₂)
  have htime : normalizedTime σ expiry (a • T₁ + b • T₂) =
      a • normalizedTime σ expiry T₁ + b • normalizedTime σ expiry T₂ := by
    simp only [normalizedTime, smul_eq_mul]
    linear_combination -(σ ^ 2 / 2 * expiry) * hab
  have hlog := hs.2 ht₁ ht₂ ha hb hab
  have hexp := convexOn_exp.2 (Set.mem_univ (s (normalizedTime σ expiry T₁)))
    (Set.mem_univ (s (normalizedTime σ expiry T₂))) ha hb hab
  have h := mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr hlog).trans hexp) hE
  simp only [stockBoundary]
  rw [htime]
  simpa only [smul_eq_mul, mul_add, mul_left_comm] using h

end MathFin.BlackScholes.AmericanPut.Boundary
