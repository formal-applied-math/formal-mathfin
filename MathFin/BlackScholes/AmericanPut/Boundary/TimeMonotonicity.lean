/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.DelayedPrice
public import MathFin.BlackScholes.AmericanPut.Boundary.LocalizationBarrier

/-!
# More time remaining cannot reduce the price

Compare the price with its clamped time delay minus a small quadratic
localization supersolution. At a positive contact the delayed price is in
continuation, so local obstacle comparison applies. The localization is then
removed pointwise. No time monotonicity is assumed in the pricing contract.

## Result

Public entry points include `dividendSpatialOperator_sub_const_mul`, `penalizedDelay`,
`penalizedDelay_local_subsolution`, `penalizedDelay_le_price`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set
open scoped Topology ContDiff

theorem dividendSpatialOperator_sub_const_mul {F G : ℝ → ℝ} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x) (hG : ContDiffAt ℝ 2 G x) (k h ε : ℝ) :
    dividendSpatialOperator k h (fun y => F y - ε*G y) x =
      dividendSpatialOperator k h F x - ε*dividendSpatialOperator k h G x := by
  have hsecond : deriv (deriv (fun y => F y - ε*G y)) x =
      deriv (deriv F) x - deriv (deriv (fun y => ε*G y)) x := by
    simpa [iteratedDeriv_succ] using iteratedDeriv_fun_sub (n := 2) hF
      (show ContDiffAt ℝ 2 (fun y => ε*G y) x from contDiffAt_const.mul hG)
  have hscale : deriv (deriv (fun y => ε*G y)) x = ε*deriv (deriv G) x := by
    rw [deriv_const_mul_field',deriv_const_mul_field]
  unfold dividendSpatialOperator
  rw [hsecond,hscale,deriv_fun_sub (hF.differentiableAt (by norm_num))
    ((hG.differentiableAt (by norm_num)).const_mul ε),deriv_const_mul_field]
  ring

/-- The price delayed by `a`, penalized by `ε` times the localization barrier:
`delayedPrice p a x t - ε*localizationBarrier k h x t`. -/
noncomputable def penalizedDelay (p : ℝ → ℝ → ℝ) (k h a ε x t : ℝ) : ℝ :=
  delayedPrice p a x t - ε*localizationBarrier k h x t

namespace DividendPutSolution

variable {k h : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}

theorem penalizedDelay_local_subsolution (hp : DividendPutSolution k h p b)
    {a ε x t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (hgt : p x t < penalizedDelay p k h a ε x t) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => penalizedDelay p k h a ε z.1 z.2) (x,t) ∧
      deriv (penalizedDelay p k h a ε x) t ≤
        dividendSpatialOperator k h (fun y => penalizedDelay p k h a ε y t) x := by
  have habove : putPayoff x < delayedPrice p a x t := by
    have hd := hp.dominates x t ht.le
    have hw := localizationBarrier_pos k h x t
    dsimp [penalizedDelay] at hgt
    nlinarith
  obtain ⟨hta,hxb⟩ := hp.delayedPrice_above_payoff habove
  have hD := hp.delayedPrice_contDiffAt hta hxb
  have hW := (localizationBarrier_contDiff k h).contDiffAt (x := (x,t))
  refine ⟨hD.sub (contDiffAt_const.mul hW),?_⟩
  have hDx : ContDiffAt ℝ 2 (fun y => delayedPrice p a y t) x := by
    simpa only [Function.comp_def] using hD.comp x
      (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t)) x by fun_prop)
  have hWx : ContDiffAt ℝ 2 (fun y => localizationBarrier k h y t) x := by
    simpa only [Function.comp_def] using hW.comp x
      (show ContDiffAt ℝ 2 (fun y : ℝ => (y,t)) x by fun_prop)
  have hDt : DifferentiableAt ℝ (delayedPrice p a x) t :=
    (hD.comp t (show ContDiffAt ℝ 2 (fun s : ℝ => (x,s)) t by fun_prop)).differentiableAt
        (by norm_num)
  have hWt := (localizationBarrier_hasDeriv_t k h x t).differentiableAt
  unfold penalizedDelay
  rw [deriv_fun_sub hDt (hWt.const_mul ε),deriv_const_mul_field,
    dividendSpatialOperator_sub_const_mul hDx hWx,
    hp.delayedPrice_equation hta hxb]
  have hsup := localizationBarrier_supersolution (h := h) hp.rate_pos.le x t
  nlinarith

/-- The spatial localization is an implementation device, not a price
assumption. The comparison takes place on a finite rectangle chosen for each
positive penalty and target point. -/
theorem penalizedDelay_le_price (hp : DividendPutSolution k h p b)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (x : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    penalizedDelay p k h a ε x T ≤ p x T := by
  let R := max (|x|+1) (max 1 (1/ε))
  have hR1 : 1 ≤ R := (le_max_left 1 (1/ε)).trans (le_max_right _ _)
  have hRe : 1/ε ≤ R := (le_max_right 1 (1/ε)).trans (le_max_right _ _)
  have hRx : |x| ≤ R := by dsimp [R]; linarith [le_max_left (|x|+1) (max 1 (1/ε))]
  have hεR : 1 ≤ ε*R := by have hh := (div_le_iff₀ hε).mp hRe; nlinarith
  have hquad : 1 ≤ ε*(1+R^2) := by
    have hRR : R ≤ R^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hRR hε.le]
  have hedges (y : ℝ) (hy : y^2 = R^2) (t : ℝ) (ht : 0 ≤ t) :
      penalizedDelay p k h a ε y t ≤ p y t := by
    have hD : delayedPrice p a y t ≤ 1 := hp.bounded y _ (le_max_right _ _)
    have hW := localizationBarrier_ge_quad k h y ht
    rw [hy] at hW
    have hP := hp.nonneg y ht
    unfold penalizedDelay
    nlinarith
  have hcont : Continuous (fun z : ℝ × ℝ => penalizedDelay p k h a ε z.1 z.2) :=
    (hp.delayedPrice_continuous a).sub ((localizationBarrier_contDiff k h).continuous.const_mul ε)
  have hcomp := hp.obstacle_comparison_of_local_tests
    (L := fun _ => -R) (R := fun _ => R) (T := T)
    continuous_const continuous_const
    (twoSidedStrip_isCompact continuous_const continuous_const (fun _ _ => by linarith))
    hcont.continuousOn
    (fun y t ht _ _ _ hgt => (hp.penalizedDelay_local_subsolution hε ht hgt).1)
    (fun y t ht _ _ _ hgt => (hp.penalizedDelay_local_subsolution hε ht hgt).2)
    (by
      intro y _ _
      unfold penalizedDelay
      rw [hp.delayedPrice_initial ha,hp.initial]
      have hw := localizationBarrier_pos k h y 0
      nlinarith)
    (fun t ht _ => hedges (-R) (by ring) t ht)
    (fun t ht _ => hedges R rfl t ht)
  exact hcomp (x,T) ⟨hT,le_rfl,by linarith [neg_abs_le x],(le_abs_self x).trans hRx⟩

theorem delayedPrice_le_price (hp : DividendPutSolution k h p b)
    {a : ℝ} (ha : 0 ≤ a) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    delayedPrice p a x t ≤ p x t := by
  by_contra hn
  have hgap : 0 < delayedPrice p a x t - p x t := sub_pos.mpr (lt_of_not_ge hn)
  let W := localizationBarrier k h x t
  have hW : 0 < W := localizationBarrier_pos k h x t
  let ε := (delayedPrice p a x t-p x t)/(2*W)
  have hε : 0 < ε := div_pos hgap (by positivity)
  have hbound := hp.penalizedDelay_le_price ha hε x ht
  change delayedPrice p a x t-ε*W ≤ p x t at hbound
  have he : ε*W = (delayedPrice p a x t-p x t)/2 := by dsimp [ε]; field_simp
  rw [he] at hbound
  linarith

/-- Time monotonicity is proved from the classical pricing contract, not
assumed through an optimal-stopping representation or a monotone boundary. -/
theorem price_mono_time (hp : DividendPutSolution k h p b) (x : ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : p x s ≤ p x t := by
  have hh := hp.delayedPrice_le_price (sub_nonneg.mpr hst) x (hs.trans hst)
  simpa [delayedPrice,show t-(t-s) = s by ring,max_eq_left hs] using hh

end DividendPutSolution

end MathFin.BlackScholes.AmericanPut.Boundary
