/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.BoundaryMonotonicity
public import MathFin.BlackScholes.AmericanPut.Boundary.GaugeTransform
public import MathFin.BlackScholes.AmericanPut.Boundary.ComparisonCoefficients

/-!
# The positive-profile-normalized time increment of the actual price

Both time slices are in continuation whenever the earlier one is. Dividing
their difference by a positive stationary profile removes the discount term.
Nonnegativity follows from the proved price monotonicity, not an assumption.

## Result

Public entry points include `timeIncrement`, `incrementGauge`, `incrementDrift`,
`timeIncrement_continuousOn`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set Filter Comparison
open scoped Topology ContDiff

/-- Increment of the price `p` over a time step `δ`: `p x (t+δ)-p x t`. -/
noncomputable def timeIncrement (p : ℝ → ℝ → ℝ) (δ x t : ℝ) : ℝ := p x (t+δ)-p x t

/-- The time increment divided by the stationary profile:
`timeIncrement p δ x t / profile (k-h-1) k x`. -/
noncomputable def incrementGauge (p : ℝ → ℝ → ℝ) (k h δ x t : ℝ) : ℝ :=
  timeIncrement p δ x t / profile (k-h-1) k x

/-- First-order coefficient of the equation satisfied by `incrementGauge`:
`k-h-1+2*logSlope (profile (k-h-1) k) x`. -/
noncomputable def incrementDrift (k h x : ℝ) : ℝ := k-h-1+2*logSlope (profile (k-h-1) k) x

namespace DividendPutSolution

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem timeIncrement_continuousOn (hp : DividendPutSolution k h p b) {δ : ℝ} (hδ : 0 ≤ δ) :
    ContinuousOn (fun z : ℝ × ℝ => timeIncrement p δ z.1 z.2) {z | 0 ≤ z.2} := by
  exact (hp.price_continuous.comp
    (show ContinuousOn (fun z : ℝ × ℝ => (z.1,z.2+δ)) {z | 0 ≤ z.2} by fun_prop)
    (fun _ hz => add_nonneg hz hδ)).sub hp.price_continuous

theorem timeIncrement_contDiffAt (hp : DividendPutSolution k h p b)
    {δ x t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) (hx : b t < x) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => timeIncrement p δ z.1 z.2) (x,t) := by
  have htδ : 0 < t+δ := add_pos_of_pos_of_nonneg ht hδ
  have hbδ : b (t+δ) ≤ b t := hp.boundary_antitoneOn ht.le htδ.le (by linarith)
  have h₁ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => p z.1 (z.2+δ)) (x,t) := by
    simpa only [Function.comp_def] using
      ((hp.price_contDiffAt htδ (hbδ.trans_lt hx)).of_le (WithTop.coe_le_coe.mpr le_top)).comp (x,t)
      (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ => (z.1,z.2+δ)) (x,t) by fun_prop)
  exact h₁.sub ((hp.price_contDiffAt ht hx).of_le (WithTop.coe_le_coe.mpr le_top))

theorem timeIncrement_equation (hp : DividendPutSolution k h p b)
    {δ x t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) (hx : b t < x) :
    deriv (timeIncrement p δ x) t =
      dividendSpatialOperator k h (fun y => timeIncrement p δ y t) x := by
  have htδ : 0 < t+δ := add_pos_of_pos_of_nonneg ht hδ
  have hbδ : b (t+δ) ≤ b t := hp.boundary_antitoneOn ht.le htδ.le (by linarith)
  have hs₀ := hp.price_contDiffAt ht hx
  have hs₁ := hp.price_contDiffAt htδ (hbδ.trans_lt hx)
  have hd₀ : DifferentiableAt ℝ (p x) t :=
    (hs₀.comp t (show ContDiffAt ℝ ∞ (fun s : ℝ => (x,s)) t by fun_prop)).differentiableAt (by simp)
  have hd₁ : DifferentiableAt ℝ (p x) (t+δ) :=
    (hs₁.comp (t+δ) (show ContDiffAt ℝ ∞ (fun s : ℝ => (x,s)) (t+δ) by fun_prop)).differentiableAt
        (by simp)
  have hsx₀ : ContDiffAt ℝ 2 (fun y => p y t) x := by
    simpa only [Function.comp_def] using
      (hs₀.of_le (WithTop.coe_le_coe.mpr le_top)).comp x
        (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t)) x by fun_prop)
  have hsx₁ : ContDiffAt ℝ 2 (fun y => p y (t+δ)) x := by
    simpa only [Function.comp_def] using
      (hs₁.of_le (WithTop.coe_le_coe.mpr le_top)).comp x
        (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t+δ)) x by fun_prop)
  have hsecond : deriv (deriv (fun y => timeIncrement p δ y t)) x =
      deriv (deriv (fun y => p y (t+δ))) x-deriv (deriv (fun y => p y t)) x := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,timeIncrement] using
      iteratedDeriv_fun_sub (n := 2) hsx₁ hsx₀
  unfold dividendSpatialOperator
  rw [hsecond]
  unfold timeIncrement
  have hdt : DifferentiableAt ℝ (fun s => p x (s+δ)) t := by
    simpa only [Function.comp_def,id_eq] using hd₁.comp t (differentiableAt_id.add_const δ)
  rw [deriv_fun_sub hdt hd₀,
    deriv_comp_add_const, hp.equation x (t+δ) htδ (hbδ.trans_lt hx),hp.equation x t ht hx,
    deriv_fun_sub (hsx₁.differentiableAt (by norm_num)) (hsx₀.differentiableAt (by norm_num))]
  unfold dividendSpatialOperator
  ring

theorem incrementGauge_continuousOn (hp : DividendPutSolution k h p b) {δ : ℝ} (hδ : 0 ≤ δ) :
    ContinuousOn (fun z : ℝ × ℝ => incrementGauge p k h δ z.1 z.2) {z | 0 ≤ z.2} := by
  have hf := profile_data (β := k-h-1) hp.rate_pos.le
  exact (hp.timeIncrement_continuousOn hδ).div
    ((hf.smooth.continuous.comp continuous_fst).continuousOn) (fun z _ => (hf.pos z.1).ne')

theorem incrementGauge_contDiffAt (hp : DividendPutSolution k h p b)
    {δ x t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) (hx : b t < x) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => incrementGauge p k h δ z.1 z.2) (x,t) := by
  have hf := profile_data (β := k-h-1) hp.rate_pos.le
  exact (hp.timeIncrement_contDiffAt hδ ht hx).div
    ((hf.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp (x,t) contDiffAt_fst)
    (hf.pos x).ne'

theorem incrementGauge_equation (hp : DividendPutSolution k h p b)
    {δ x t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) (hx : b t < x) :
    deriv (incrementGauge p k h δ x) t =
      deriv (deriv (fun y => incrementGauge p k h δ y t)) x +
        incrementDrift k h x*deriv (fun y => incrementGauge p k h δ y t) x := by
  have hs := hp.timeIncrement_contDiffAt hδ ht hx
  have hsx : ContDiffAt ℝ 2 (fun y => timeIncrement p δ y t) x := by
    simpa only [Function.comp_def] using hs.comp x
      (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t)) x by fun_prop)
  have hst : DifferentiableAt ℝ (timeIncrement p δ x) t :=
    (hs.comp t (show ContDiffAt ℝ 2 (fun s : ℝ => (x,s)) t by fun_prop)).differentiableAt
        (by norm_num)
  have hf : ProfileData ((k-h-1)-0) k (profile (k-h-1) k) := by
    simpa only [sub_zero] using profile_data (β := k-h-1) hp.rate_pos.le
  have he := gauge_equation (c := 0) (d := 0) hf hsx hst (hp.timeIncrement_equation hδ ht hx)
  have hfun : Comparison.gauge (timeIncrement p δ) (profile (k-h-1) k) 0 0 =
      incrementGauge p k h δ := by
    funext y s
    simp [Comparison.gauge,incrementGauge]
  rw [hfun] at he
  simpa only [zero_mul,add_zero,sub_zero,incrementDrift,logSlope,mul_div_assoc] using he

theorem incrementGauge_nonneg (hp : DividendPutSolution k h p b)
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t) (x : ℝ) : 0 ≤ incrementGauge p k h δ x t :=
  div_nonneg (sub_nonneg.mpr (hp.price_mono_time x ht (by linarith)))
    ((profile_data hp.rate_pos.le).pos x).le

theorem incrementGauge_initial_pos (hp : DividendPutSolution k h p b)
    {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) : 0 < incrementGauge p k h δ x 0 := by
  apply div_pos _ ((profile_data hp.rate_pos.le).pos x)
  unfold timeIncrement
  rw [zero_add,hp.initial]
  exact sub_pos.mpr (hp.continuation x δ hδ ((hp.boundary_nonpos hδ).trans_lt hx))

end DividendPutSolution

theorem incrementDrift_bounded {k h : ℝ} (hk : 0 < k) :
    ∃ M : ℝ, ∀ x, |incrementDrift k h x| ≤ M := by
  obtain ⟨B,_,hB⟩ := profile_slope_and_deriv_bounded (β := k-h-1) hk
  refine ⟨|k-h-1|+2*B,?_⟩
  intro x
  have hh := abs_add_le (k-h-1) (2*logSlope (profile (k-h-1) k) x)
  norm_num only [abs_mul,abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at hh
  dsimp [incrementDrift]
  linarith [(hB x).1]

end MathFin.BlackScholes.AmericanPut.Boundary
