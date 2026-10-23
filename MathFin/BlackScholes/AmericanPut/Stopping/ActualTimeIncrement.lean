/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualStrictSpatialSlope
public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicMaximum

/-! # PDE and maximum principle for actual-price time increments

A positive spatial maximum of a time increment cannot occur where the earlier
price is in exercise: the later continuation slope is strictly greater than
the exercise slope. Both slices are therefore smooth at a candidate positive
space-time maximum, and the pricing PDE excludes it.

## Result

Public entry points include `canonicalTimeIncrement`, `canonicalTimeIncrement_continuous`,
`canonicalTimeIncrement_spatial_deriv`, `canonicalTimeIncrement_contDiffAt`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary
open scoped Topology ContDiff

/-- Increment of the canonical price over a time step `δ`:
`canonicalPrice k h x (t+δ)-canonicalPrice k h x t`. -/
noncomputable def canonicalTimeIncrement (k h δ x t : ℝ) : ℝ :=
  canonicalPrice k h x (t+δ)-canonicalPrice k h x t

theorem canonicalTimeIncrement_continuous {k h : ℝ} (hk : 0 ≤ k) (δ : ℝ) :
    Continuous (fun z : ℝ × ℝ => canonicalTimeIncrement k h δ z.1 z.2) :=
  ((canonicalPrice_continuous hk).comp (show Continuous (fun z : ℝ × ℝ => (z.1,z.2+δ))
    by fun_prop)).sub (canonicalPrice_continuous hk)

theorem canonicalTimeIncrement_spatial_deriv {k h δ x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hδ : 0 ≤ δ) (ht : 0 < t) :
    deriv (fun y => canonicalTimeIncrement k h δ y t) x =
      deriv (fun y => canonicalPrice k h y (t+δ)) x-deriv (fun y => canonicalPrice k h y t) x :=
  deriv_fun_sub (canonicalPrice_differentiableAt_spatial hk hh hhk (by linarith) x)
    (canonicalPrice_differentiableAt_spatial hk hh hhk ht x)

theorem canonicalTimeIncrement_contDiffAt {k h δ x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hδ : 0 ≤ δ) (ht : 0 < t)
    (hx : canonicalLogBoundary k h t < x) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => canonicalTimeIncrement k h δ z.1 z.2) (x,t) := by
  have htδ : 0 < t+δ := by linarith
  have hb := canonicalLogBoundary_antitoneOn hk hh hhk ht.le htδ.le (by linarith : t ≤ t+δ)
  have hz0 : (x,t) ∈ canonicalContinuationRegion k h := by
    rw [canonicalContinuationRegion_eq_logBoundary hk hh hhk]
    exact ⟨ht,hx⟩
  have hz1 : (x,t+δ) ∈ canonicalContinuationRegion k h := by
    rw [canonicalContinuationRegion_eq_logBoundary hk hh hhk]
    exact ⟨htδ,hb.trans_lt hx⟩
  have hp0 : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => canonicalPrice k h z.1 z.2) (x,t) :=
    (canonicalPrice_contDiffAt hk.le hz0).of_le (WithTop.coe_le_coe.mpr le_top)
  have hp1 : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => canonicalPrice k h z.1 z.2) (x,t+δ) :=
    (canonicalPrice_contDiffAt hk.le hz1).of_le (WithTop.coe_le_coe.mpr le_top)
  have hshift : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => canonicalPrice k h z.1 (z.2+δ)) (x,t) :=
    hp1.comp (f := fun z : ℝ × ℝ => (z.1,z.2+δ)) (x,t) (by fun_prop)
  exact hshift.sub hp0

theorem canonicalTimeIncrement_equation {k h δ x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hδ : 0 ≤ δ) (ht : 0 < t)
    (hx : canonicalLogBoundary k h t < x) :
    deriv (canonicalTimeIncrement k h δ x) t =
      deriv (deriv (fun y => canonicalTimeIncrement k h δ y t)) x +
        (k-h-1)*deriv (fun y => canonicalTimeIncrement k h δ y t) x -
        k*canonicalTimeIncrement k h δ x t := by
  have htδ : 0 < t+δ := by linarith
  have hb := canonicalLogBoundary_antitoneOn hk hh hhk ht.le htδ.le (by linarith : t ≤ t+δ)
  have hz0 : (x,t) ∈ canonicalContinuationRegion k h := by
    rw [canonicalContinuationRegion_eq_logBoundary hk hh hhk]
    exact ⟨ht,hx⟩
  have hz1 : (x,t+δ) ∈ canonicalContinuationRegion k h := by
    rw [canonicalContinuationRegion_eq_logBoundary hk hh hhk]
    exact ⟨htδ,hb.trans_lt hx⟩
  have hs0 : ContDiffAt ℝ 2 (fun y => canonicalPrice k h y t) x :=
    ((canonicalPrice_contDiffAt hk.le hz0).of_le (WithTop.coe_le_coe.mpr le_top)).comp
      (f := fun y : ℝ => (y,t)) x (by fun_prop)
  have hs1 : ContDiffAt ℝ 2 (fun y => canonicalPrice k h y (t+δ)) x :=
    ((canonicalPrice_contDiffAt hk.le hz1).of_le (WithTop.coe_le_coe.mpr le_top)).comp
      (f := fun y : ℝ => (y,t+δ)) x (by fun_prop)
  have hd0 : DifferentiableAt ℝ (canonicalPrice k h x) t :=
    ((canonicalPrice_contDiffAt hk.le hz0).comp (f := fun s : ℝ => (x,s)) t
      (by fun_prop)).differentiableAt (by simp)
  have hd1 : DifferentiableAt ℝ (canonicalPrice k h x) (t+δ) :=
    ((canonicalPrice_contDiffAt hk.le hz1).comp (f := fun s : ℝ => (x,s)) (t+δ)
      (by fun_prop)).differentiableAt (by simp)
  have hsecond : deriv (deriv (fun y => canonicalTimeIncrement k h δ y t)) x =
      deriv (deriv (fun y => canonicalPrice k h y (t+δ))) x-
        deriv (deriv (fun y => canonicalPrice k h y t)) x := by
    simpa only [canonicalTimeIncrement,iteratedDeriv_succ,iteratedDeriv_zero] using
      iteratedDeriv_fun_sub (n := 2) hs1 hs0
  have hdt : DifferentiableAt ℝ (fun s => canonicalPrice k h x (s+δ)) t := by
    simpa only [Function.comp_def,id_eq] using hd1.comp t (differentiableAt_id.add_const δ)
  rw [hsecond,canonicalTimeIncrement_spatial_deriv hk hh hhk hδ ht]
  unfold canonicalTimeIncrement
  rw [deriv_fun_sub hdt hd0,deriv_comp_add_const,
    canonicalPrice_continuation_pde hk.le hz1,canonicalPrice_continuation_pde hk.le hz0]
  ring

theorem canonicalTimeIncrement_positive_max_continuation {k h δ x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hδ : 0 ≤ δ) (ht : 0 < t)
    (hm : IsLocalMax (fun y => canonicalTimeIncrement k h δ y t) x)
    (hpos : 0 < canonicalTimeIncrement k h δ x t) : canonicalLogBoundary k h t < x := by
  have htδ : 0 < t+δ := by linarith
  have hstrict : putPayoff x < canonicalPrice k h x (t+δ) :=
    (canonicalPrice_bounds hk.le x t).1.trans_lt (sub_pos.mp hpos)
  have hx1 : canonicalLogBoundary k h (t+δ) < x := by
    by_contra! he
    rw [(canonicalPrice_contact_iff_logBoundary hk hh hhk htδ).mpr he] at hstrict
    exact (lt_irrefl _ hstrict)
  by_contra! hx0
  have hzero := hm.deriv_eq_zero
  rw [canonicalTimeIncrement_spatial_deriv hk hh hhk hδ ht,
    (canonicalPrice_hasDerivAt_exercise hk hh hhk ht hx0).deriv] at hzero
  have hs := canonicalPrice_spatial_deriv_gt_exercise hk hh hhk htδ hx1
  linarith

theorem canonicalTimeIncrement_no_positive_max {k h δ x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hδ : 0 ≤ δ) (ht : 0 < t)
    (hm : IsLocalMax (fun y => canonicalTimeIncrement k h δ y t) x)
    (htm : ∀ᶠ s in 𝓝[<] t, canonicalTimeIncrement k h δ x s ≤ canonicalTimeIncrement k h δ x t)
    (hpos : 0 < canonicalTimeIncrement k h δ x t) : False := by
  have hx := canonicalTimeIncrement_positive_max_continuation hk hh hhk hδ ht hm hpos
  have hc := canonicalTimeIncrement_contDiffAt hk hh hhk hδ ht hx
  have hd : DifferentiableAt ℝ (canonicalTimeIncrement k h δ x) t :=
    (hc.comp (f := fun s : ℝ => (x,s)) t (by fun_prop)).differentiableAt (by norm_num)
  have htime := deriv_nonneg_at_left_max hd htm
  have hspace := second_deriv_nonpos_at_local_max hm
    (hc.continuousAt.comp (f := fun y : ℝ => (y,t)) (by fun_prop))
  have hpde := canonicalTimeIncrement_equation hk hh hhk hδ ht hx
  rw [hm.deriv_eq_zero,mul_zero,add_zero] at hpde
  nlinarith [mul_pos hk hpos]

end MathFin.BlackScholes.AmericanPut.Stopping
