/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualSmoothFit
public import MathFin.BlackScholes.AmericanPut.Stopping.ConvexDerivativeTrace

/-! # Continuation-side gradient trace for the actual stopping price

Convexity in stock price, smooth fit and interior differentiability imply the
stock gradient trace. The exponential coordinate change gives the log-price
trace required by the classical pricing contract. Boundary smoothness is not
assumed here.

## Result

Public entry points include `canonicalStockPrice`, `canonicalStockPrice_exp`,
`canonicalStockPrice_eq_log`, `canonicalStockPrice_convexOn`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology ContDiff

/-- The same actual stopping value, in normalized stock rather than log spot. -/
noncomputable def canonicalStockPrice (k h S t : ℝ) : ℝ :=
  brownianUsualAmericanPut 1 k h (Real.sqrt 2) S t.toNNReal

theorem canonicalStockPrice_exp (k h x t : ℝ) :
    canonicalStockPrice k h (Real.exp x) t = canonicalPrice k h x t := rfl

theorem canonicalStockPrice_eq_log (k h t : ℝ) {S : ℝ} (hS : 0 < S) :
    canonicalStockPrice k h S t = canonicalPrice k h (Real.log S) t := by
  simp only [canonicalPrice,canonicalStockPrice,Real.exp_log hS]

theorem canonicalStockPrice_convexOn {k h : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    ConvexOn ℝ (Ici 0) (fun S => canonicalStockPrice k h S t) := by
  let μ := completedMeasure gaussianLimit
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  exact value_convexOn_spot (P := μ) (𝓕 := brownianUsualFiltration)
    (q := h) (σ := Real.sqrt 2) (T := t.toNNReal)
    brownian_completed_measurable (by norm_num : (0 : ℝ) ≤ 1) hk

theorem canonicalStockPrice_smooth_fit {k h t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) :
    HasDerivWithinAt (fun S => canonicalStockPrice k h S t) (-1)
      (Ici (canonicalStockBoundary k h t)) (canonicalStockBoundary k h t) := by
  have hB := canonicalStockBoundary_pos hk hh hhk ht.le
  have hfit := canonicalPrice_smooth_fit hk hh hhk ht
  have hmap : MapsTo Real.log (Ici (canonicalStockBoundary k h t))
      (Ici (canonicalLogBoundary k h t)) := by
    intro S hS
    exact Real.log_le_log hB hS
  have hc := hfit.comp (canonicalStockBoundary k h t)
    (Real.hasDerivAt_log hB.ne').hasDerivWithinAt hmap
  have he : -Real.exp (canonicalLogBoundary k h t) * (canonicalStockBoundary k h t)⁻¹ = -1 := by
    rw [exp_canonicalLogBoundary hk hh hhk ht.le]
    field_simp
  rw [he] at hc
  apply hc.congr_of_mem _ (by simp)
  intro S hS
  exact canonicalStockPrice_eq_log k h t (hB.trans_le hS)

theorem canonicalPrice_differentiableAt_continuation {k h x t : ℝ} (hk : 0 ≤ k)
    (ht : 0 < t) (hx : canonicalStockBoundary k h t < Real.exp x) :
    DifferentiableAt ℝ (fun y => canonicalPrice k h y t) x := by
  have hz : (x,t) ∈ canonicalContinuationRegion k h :=
    ⟨ht,(canonicalPrice_strict_continuation_iff hk x ht).mpr hx⟩
  have hp := (canonicalPrice_contDiffAt hk hz).differentiableAt (by simp)
  exact hp.comp (f := fun y : ℝ => (y,t)) x (differentiableAt_id.prodMk (differentiableAt_const t))

theorem canonicalStockPrice_differentiableAt_continuation {k h S t : ℝ} (hk : 0 ≤ k)
    (ht : 0 < t) (hS : 0 < S) (hx : canonicalStockBoundary k h t < S) :
    DifferentiableAt ℝ (fun R => canonicalStockPrice k h R t) S := by
  have hp := canonicalPrice_differentiableAt_continuation (h := h) hk ht
    (show canonicalStockBoundary k h t < Real.exp (Real.log S) by rwa [Real.exp_log hS])
  have hc := hp.hasDerivAt.comp S (Real.hasDerivAt_log hS.ne')
  apply (hc.congr_of_eventuallyEq ?_).differentiableAt
  filter_upwards [Ioi_mem_nhds hS] with R hR
  exact canonicalStockPrice_eq_log k h t hR

theorem canonicalStockPrice_gradient_trace {k h t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) :
    Tendsto (deriv (fun S => canonicalStockPrice k h S t))
      (𝓝[>] canonicalStockBoundary k h t) (𝓝 (-1)) := by
  have hB := canonicalStockBoundary_pos hk hh hhk ht.le
  apply convex_deriv_tendsto_right
    ((canonicalStockPrice_convexOn (h := h) hk.le t).subset
      (fun S hS => hB.le.trans hS) (convex_Ici _))
    (canonicalStockPrice_smooth_fit hk hh hhk ht)
  intro S hS
  exact canonicalStockPrice_differentiableAt_continuation hk.le ht (hB.trans hS) hS

/-- The exact interior-derivative limit required by
`DividendPutSolution.gradient_trace`, without a classical-solution premise. -/
theorem canonicalPrice_gradient_trace {k h t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (ht : 0 < t) :
    Tendsto (fun x => deriv (fun y => canonicalPrice k h y t) x)
      (𝓝[>] canonicalLogBoundary k h t)
      (𝓝 (-Real.exp (canonicalLogBoundary k h t))) := by
  have hexp : Tendsto Real.exp (𝓝[>] canonicalLogBoundary k h t)
      (𝓝[>] canonicalStockBoundary k h t) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · rw [← exp_canonicalLogBoundary hk hh hhk ht.le]
      exact (Real.continuous_exp.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change canonicalStockBoundary k h t < Real.exp x
      rw [← exp_canonicalLogBoundary hk hh hhk ht.le]
      exact Real.exp_lt_exp.mpr hx
  have hs := (canonicalStockPrice_gradient_trace hk hh hhk ht).comp hexp
  have he := (Real.continuous_exp.tendsto (canonicalLogBoundary k h t)).mono_left
    (nhdsWithin_le_nhds (s := Ioi (canonicalLogBoundary k h t)))
  have hlim : Tendsto
      (fun x => deriv (fun S => canonicalStockPrice k h S t) (Real.exp x) * Real.exp x)
      (𝓝[>] canonicalLogBoundary k h t)
      (𝓝 (-Real.exp (canonicalLogBoundary k h t))) := by
    simpa only [Function.comp_def,neg_one_mul] using hs.mul he
  apply hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hS : canonicalStockBoundary k h t < Real.exp x := by
    rw [← exp_canonicalLogBoundary hk hh hhk ht.le]
    exact Real.exp_lt_exp.mpr hx
  have hd := (canonicalStockPrice_differentiableAt_continuation hk.le ht
    (Real.exp_pos x) hS).hasDerivAt.comp x (Real.hasDerivAt_exp x)
  exact hd.deriv.symm

theorem zeroDividend_canonicalPrice_gradient_trace {k t : ℝ} (hk : 0 < k) (ht : 0 < t) :
    Tendsto (fun x => deriv (fun y => canonicalPrice k 0 y t) x)
      (𝓝[>] canonicalLogBoundary k 0 t)
      (𝓝 (-Real.exp (canonicalLogBoundary k 0 t))) :=
  canonicalPrice_gradient_trace hk le_rfl hk.le ht

/-- Liu's stronger normalized parameter range is a separate checked checkpoint. -/
theorem liuRange_canonicalPrice_gradient_trace {k h t : ℝ}
    (hh : 0 ≤ h) (hliu : h + 1 ≤ k) (ht : 0 < t) :
    Tendsto (fun x => deriv (fun y => canonicalPrice k h y t) x)
      (𝓝[>] canonicalLogBoundary k h t)
      (𝓝 (-Real.exp (canonicalLogBoundary k h t))) :=
  canonicalPrice_gradient_trace (by linarith) hh (by linarith) ht

end MathFin.BlackScholes.AmericanPut.Stopping
