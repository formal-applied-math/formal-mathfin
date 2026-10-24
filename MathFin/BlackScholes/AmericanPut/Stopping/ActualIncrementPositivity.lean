/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.ActualTimeIncrement
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualContinuousContract
public import MathFin.BlackScholes.AmericanPut.Boundary.TimeIncrement
public import MathFin.BlackScholes.AmericanPut.Boundary.StrongPositivity

/-! # Strict positivity of normalized actual-price time increments

These results use the stopping value's proved time monotonicity, continuation
PDE, and spatial smooth fit. No time differentiability of the boundary is
assumed. The stationary positive profile removes the discount term.

## Result

Public entry points include `canonicalIncrementGauge`, `canonicalIncrementGauge_continuous`,
`canonicalIncrementGauge_contDiffAt`, `canonicalIncrementGauge_equation`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary Boundary.Comparison
open scoped Topology ContDiff

/-- The canonical time increment divided by the stationary profile:
`canonicalTimeIncrement k h δ x t / profile (k-h-1) k x`. -/
noncomputable def canonicalIncrementGauge (k h δ x t : ℝ) : ℝ :=
  canonicalTimeIncrement k h δ x t / profile (k-h-1) k x

theorem canonicalIncrementGauge_continuous {k h : ℝ} (hk : 0 < k) (δ : ℝ) :
    Continuous (fun z : ℝ × ℝ => canonicalIncrementGauge k h δ z.1 z.2) := by
  have hf := profile_data (β := k-h-1) hk.le
  exact (canonicalTimeIncrement_continuous hk.le δ).div
    (hf.smooth.continuous.comp continuous_fst) (fun z => (hf.pos z.1).ne')

theorem canonicalIncrementGauge_contDiffAt {k h δ x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hδ : 0 ≤ δ) (ht : 0 < t)
    (hx : canonicalLogBoundary k h t < x) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => canonicalIncrementGauge k h δ z.1 z.2) (x,t) := by
  have hf := profile_data (β := k-h-1) hk.le
  exact (canonicalTimeIncrement_contDiffAt hk hh hhk hδ ht hx).div
    ((hf.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp (x,t) contDiffAt_fst)
    (hf.pos x).ne'

theorem canonicalIncrementGauge_equation {k h δ x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hδ : 0 ≤ δ) (ht : 0 < t)
    (hx : canonicalLogBoundary k h t < x) :
    deriv (canonicalIncrementGauge k h δ x) t =
      deriv (deriv (fun y => canonicalIncrementGauge k h δ y t)) x +
        incrementDrift k h x*deriv (fun y => canonicalIncrementGauge k h δ y t) x := by
  have hs := canonicalTimeIncrement_contDiffAt hk hh hhk hδ ht hx
  have hsx : ContDiffAt ℝ 2 (fun y => canonicalTimeIncrement k h δ y t) x := by
    simpa only [Function.comp_def] using hs.comp x
      (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t)) x by fun_prop)
  have hst : DifferentiableAt ℝ (canonicalTimeIncrement k h δ x) t :=
    (hs.comp t (show ContDiffAt ℝ 2 (fun s : ℝ => (x,s)) t by fun_prop)).differentiableAt
        (by norm_num)
  have hf : ProfileData ((k-h-1)-0) k (profile (k-h-1) k) := by
    simpa only [sub_zero] using profile_data (β := k-h-1) hk.le
  have he := gauge_equation (c := 0) (d := 0) hf hsx hst
    (canonicalTimeIncrement_equation hk hh hhk hδ ht hx)
  have hfun : Comparison.gauge (canonicalTimeIncrement k h δ) (profile (k-h-1) k) 0 0 =
      canonicalIncrementGauge k h δ := by
    funext y s
    simp [Comparison.gauge,canonicalIncrementGauge]
  rw [hfun] at he
  simpa only [zero_mul,add_zero,sub_zero,incrementDrift,logSlope,mul_div_assoc] using he

theorem canonicalIncrementGauge_nonneg {k h δ : ℝ} (hk : 0 < k)
    (hδ : 0 ≤ δ) (x t : ℝ) : 0 ≤ canonicalIncrementGauge k h δ x t :=
  div_nonneg (sub_nonneg.mpr (canonicalPrice_monotone_time hk.le x (by linarith)))
    ((profile_data hk.le).pos x).le

theorem canonicalIncrementGauge_initial_pos {k h δ x : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hδ : 0 < δ) (hx : 0 < x) :
    0 < canonicalIncrementGauge k h δ x 0 := by
  have hp := canonicalPrice_continuousBoundaryPutSolution hk hh hhk
  apply div_pos _ ((profile_data hk.le).pos x)
  unfold canonicalTimeIncrement
  rw [zero_add,hp.initial]
  exact sub_pos.mpr (hp.continuation x δ hδ ((hp.boundary_nonpos hδ).trans_lt hx))

theorem canonicalIncrementGauge_pos_above_strike {k h δ x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hδ : 0 < δ) (hx : 0 < x) (ht : 0 < t) :
    0 < canonicalIncrementGauge k h δ x t := by
  obtain ⟨M,hM⟩ := incrementDrift_bounded (h := h) hk
  apply positive_later_of_positive_point (U := canonicalIncrementGauge k h δ)
    (D := fun x _ => incrementDrift k h x) (β := 0) (a := 0) (x := x) (M := M) ht hx hx
    (canonicalIncrementGauge_continuous hk δ).continuousOn
  · intro z s hz hs _
    exact canonicalIncrementGauge_contDiffAt hk hh hhk hδ.le hs
      ((canonicalLogBoundary_neg hk hh hhk hs).trans hz)
  · intro z s hz hs _
    exact canonicalIncrementGauge_equation hk hh hhk hδ.le hs
      ((canonicalLogBoundary_neg hk hh hhk hs).trans hz)
  · intro z _ _ _ _
    exact hM z
  · intro z s _ _ _
    exact canonicalIncrementGauge_nonneg hk hδ.le z s
  · exact canonicalIncrementGauge_initial_pos hk hh hhk hδ hx

theorem canonicalIncrementGauge_pos_on_flat_tail {k h δ A x t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hδ : 0 < δ) (hA : 0 < A)
    (hflat : ∀ s, A ≤ s → canonicalLogBoundary k h s = canonicalLogBoundary k h A)
    (hx : canonicalLogBoundary k h A < x) (ht : A < t) :
    0 < canonicalIncrementGauge k h δ x t := by
  obtain ⟨M,hM⟩ := incrementDrift_bounded (h := h) hk
  apply positive_later_of_positive_point (U := canonicalIncrementGauge k h δ)
    (D := fun x _ => incrementDrift k h x) (β := canonicalLogBoundary k h A)
    (a := A) (x := 1) (M := M) ht
    (by linarith [canonicalLogBoundary_neg hk hh hhk hA]) hx
    (canonicalIncrementGauge_continuous hk δ).continuousOn
  · intro z s hz hs _
    exact canonicalIncrementGauge_contDiffAt hk hh hhk hδ.le (hA.trans hs)
      (by rwa [hflat s hs.le])
  · intro z s hz hs _
    exact canonicalIncrementGauge_equation hk hh hhk hδ.le (hA.trans hs)
      (by rwa [hflat s hs.le])
  · intro z _ _ _ _
    exact hM z
  · intro z s _ _ _
    exact canonicalIncrementGauge_nonneg hk hδ.le z s
  · exact canonicalIncrementGauge_pos_above_strike hk hh hhk hδ (by norm_num) hA

theorem canonicalIncrementGauge_fit_of_same_boundary {k h δ t : ℝ} (hk : 0 < k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hδ : 0 ≤ δ) (ht : 0 < t)
    (heq : canonicalLogBoundary k h (t + δ) = canonicalLogBoundary k h t) :
    canonicalIncrementGauge k h δ (canonicalLogBoundary k h t) t = 0 ∧
      HasDerivAt (fun x => canonicalIncrementGauge k h δ x t) 0
        (canonicalLogBoundary k h t) := by
  have hp := canonicalPrice_continuousBoundaryPutSolution hk hh hhk
  have htδ := add_pos_of_pos_of_nonneg ht hδ
  have hval : canonicalTimeIncrement k h δ (canonicalLogBoundary k h t) t = 0 := by
    unfold canonicalTimeIncrement
    rw [hp.exercise _ (t+δ) htδ (by rw [heq]),hp.exercise _ t ht le_rfl,sub_self]
  have hd₀ := canonicalPrice_hasDerivAt_boundary hk hh hhk ht
  have hd₁ := canonicalPrice_hasDerivAt_boundary hk hh hhk htδ
  rw [heq] at hd₁
  have hf := profile_data (β := k-h-1) hk.le
  refine ⟨by simp [canonicalIncrementGauge,hval],?_⟩
  have hnum : HasDerivAt (canonicalTimeIncrement k h δ · t) 0
      (canonicalLogBoundary k h t) := by
    convert! hd₁.sub hd₀ using 1
    simp
  convert! hnum.div (hf.hasDeriv (canonicalLogBoundary k h t))
    (hf.pos (canonicalLogBoundary k h t)).ne' using 1
  rw [hval]
  simp

end MathFin.BlackScholes.AmericanPut.Stopping
