/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.OneSidedContact

/-!
# Parabolic test functions at the exercise boundary

At a backward contact maximum, differentiating along the moving exercise
boundary eliminates its speed by smooth fit. Together with the exercise-side
spatial test, this excludes a nonnegative contact maximum of subsolution minus price.
No time derivative or second spatial derivative of the price at contact is
assumed.

## Result

Public entry points include `curve_hasDeriv`, `boundary_test_time_nonneg`,
`boundary_test_residual_pos`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter
open scoped Topology ContDiff

theorem curve_hasDeriv {U : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {t : ℝ}
    (hU : DifferentiableAt ℝ (fun z : ℝ × ℝ => U z.1 z.2) (b t,t))
    (hb : DifferentiableAt ℝ b t) :
    HasDerivAt (fun s => U (b s) s)
      (deriv (U (b t)) t + deriv b t * deriv (fun x => U x t) (b t)) t := by
  let A := fderiv ℝ (fun z : ℝ × ℝ => U z.1 z.2) (b t,t)
  have hA : HasFDerivAt (fun z : ℝ × ℝ => U z.1 z.2) A (b t,t) := hU.hasFDerivAt
  have hx : HasDerivAt (fun x => U x t) (A (1,0)) (b t) := by
    simpa only [Function.comp_def,id_eq] using
      hA.comp_hasDerivAt (b t) ((hasDerivAt_id (b t)).prodMk (hasDerivAt_const (b t) t))
  have hs : HasDerivAt (U (b t)) (A (0,1)) t := by
    simpa only [Function.comp_def,id_eq] using
      hA.comp_hasDerivAt t ((hasDerivAt_const t (b t)).prodMk (hasDerivAt_id t))
  rw [hs.deriv,hx.deriv]
  convert! hA.comp_hasDerivAt (f := fun s => (b s,s)) t
    (hb.hasDerivAt.prodMk (hasDerivAt_id t)) using 1
  rw [show ((deriv b t,1) : ℝ × ℝ) = (0,1) + deriv b t • (1,0) by ext <;> simp]
  simp only [map_add,map_smul,smul_eq_mul]

namespace DividendPutSolution

/-- The time derivative of a smooth spatial test is nonnegative at a
backward maximum along the free boundary, provided it has the payoff slope.
The derivative is of the test, not of the price across the boundary. -/
theorem boundary_test_time_nonneg {k h : ℝ} {p U : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) {t : ℝ} (ht : 0 < t)
    (hU : DifferentiableAt ℝ (fun z : ℝ × ℝ => U z.1 z.2) (b t,t))
    (hslope : deriv (fun x => U x t) (b t) = -Real.exp (b t))
    (hmax : ∀ᶠ s in 𝓝[<] t,
      U (b s) s - p (b s) s ≤ U (b t) t - p (b t) t) :
    0 ≤ deriv (U (b t)) t := by
  have hb : DifferentiableAt ℝ b t :=
    (hp.boundary_smooth.contDiffAt (Ioi_mem_nhds ht)).differentiableAt (by simp)
  have hd := (curve_hasDeriv hU hb).sub ((hb.hasDerivAt.exp).const_sub 1)
  have hderiv : HasDerivAt (fun s => U (b s) s - (1 - Real.exp (b s)))
      (deriv (U (b t)) t) t := by
    convert! hd using 1
    rw [hslope]
    ring
  refine (deriv_nonneg_at_left_max hderiv.differentiableAt ?_).trans_eq hderiv.deriv
  filter_upwards [hmax,nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with s hs hspos
  simpa only [hp.exercise (b s) s hspos le_rfl,hp.exercise (b t) t ht le_rfl] using hs

/-- A smooth function cannot satisfy the pricing subsolution inequality
at an exercise-boundary contact maximum above the price. This is the
boundary-contact case needed for an obstacle comparison principle. -/
theorem boundary_test_residual_pos {k h : ℝ} {p U : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) {t : ℝ} (ht : 0 < t)
    (hU : DifferentiableAt ℝ (fun z : ℝ × ℝ => U z.1 z.2) (b t,t))
    (hspace : ContDiffAt ℝ 2 (fun x => U x t) (b t))
    (hmaxSpace : IsLocalMax (fun x => U x t - p x t) (b t))
    (hmaxTime : ∀ᶠ s in 𝓝[<] t,
      U (b s) s - p (b s) s ≤ U (b t) t - p (b t) t)
    (habove : p (b t) t ≤ U (b t) t) :
    0 < deriv (U (b t)) t - dividendSpatialOperator k h (fun x => U x t) (b t) := by
  obtain ⟨hslope,hcurv⟩ := hp.spatial_test_at_boundary ht hspace hmaxSpace
  have htime := hp.boundary_test_time_nonneg ht hU hslope hmaxTime
  have hforcing := hp.boundary_forcing_pos ht
  rw [hp.exercise (b t) t ht le_rfl] at habove
  unfold dividendSpatialOperator
  rw [hslope]
  nlinarith [hp.rate_pos]

end DividendPutSolution

end MathFin.BlackScholes.AmericanPut.Boundary
