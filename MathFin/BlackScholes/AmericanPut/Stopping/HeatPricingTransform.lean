/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.IntervalHeatBoundary
public import MathFin.BlackScholes.AmericanPut.Stopping.SmoothPricingComparison
public import MathFin.BlackScholes.AmericanPut.Boundary.GaugeTransform

/-! # Fixed-interval heat-to-pricing transformation

An exponential factor removes the drift and discount without moving the
spatial endpoints. Heat time is twice normalized pricing time.

## Result

Public entry points include `pricingGauge`, `priceFromHeat`, `pricingGauge_hasDeriv_space`,
`pricingGauge_hasDeriv_time`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The exponential gauge factor `exp ((-(k-h-1)/2)*(x-L) + (-(k+(k-h-1)^2/4))*(t-a))` of the
heat-to-pricing change of variables. -/
noncomputable def pricingGauge (k h L a x t : ℝ) : ℝ :=
  Real.exp ((-(k-h-1)/2)*(x-L) + (-(k+(k-h-1)^2/4))*(t-a))

/-- A heat solution `V` read as a pricing function: the gauge times `V` at shifted space `z.1-L`
and doubled time `2*(z.2-a)`. -/
noncomputable def priceFromHeat (V : ℝ × ℝ → ℝ) (k h L a : ℝ) (z : ℝ × ℝ) : ℝ :=
  pricingGauge k h L a z.1 z.2 * V (z.1-L,2*(z.2-a))

theorem pricingGauge_hasDeriv_space (k h L a x t : ℝ) :
    HasDerivAt (fun y => pricingGauge k h L a y t)
      ((-(k-h-1)/2)*pricingGauge k h L a x t) x := by
  unfold pricingGauge
  convert! ((((hasDerivAt_id x).sub_const L).const_mul (-(k-h-1)/2)).add_const
    ((-(k+(k-h-1)^2/4))*(t-a))).exp using 1
  simp only [id_eq]
  ring

theorem pricingGauge_hasDeriv_time (k h L a x t : ℝ) :
    HasDerivAt (fun s => pricingGauge k h L a x s)
      ((-(k+(k-h-1)^2/4))*pricingGauge k h L a x t) t := by
  unfold pricingGauge
  convert! ((((hasDerivAt_id t).sub_const a).const_mul (-(k+(k-h-1)^2/4))).const_add
    ((-(k-h-1)/2)*(x-L))).exp using 1
  simp only [id_eq]
  ring

theorem pricingGauge_deriv2_space (k h L a x t : ℝ) :
    deriv (deriv (fun y => pricingGauge k h L a y t)) x =
      (-(k-h-1)/2)^2*pricingGauge k h L a x t := by
  rw [show deriv (fun y => pricingGauge k h L a y t) =
    (fun y => (-(k-h-1)/2)*pricingGauge k h L a y t) from
      funext fun y => (pricingGauge_hasDeriv_space k h L a y t).deriv,
    deriv_const_mul_field,(pricingGauge_hasDeriv_space k h L a x t).deriv]
  ring

theorem priceFromHeat_continuous {V : ℝ × ℝ → ℝ} (hV : Continuous V) (k h L a : ℝ) :
    Continuous (priceFromHeat V k h L a) := by
  exact (show Continuous (fun z : ℝ × ℝ => pricingGauge k h L a z.1 z.2) by
    unfold pricingGauge; fun_prop).mul
    (hV.comp ((continuous_fst.sub continuous_const).prodMk
      (continuous_const.mul (continuous_snd.sub continuous_const))))

theorem priceFromHeat_smoothAt {V : ℝ × ℝ → ℝ} {k h L a x t : ℝ}
    (hV : ContDiffAt ℝ ∞ V (x - L, 2 *(t - a))) :
    ContDiffAt ℝ ∞ (priceFromHeat V k h L a) (x,t) := by
  exact (show ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => pricingGauge k h L a z.1 z.2) (x,t) by
    unfold pricingGauge; fun_prop).mul (hV.comp (x,t)
      (show ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (z.1-L,2*(z.2-a))) (x,t) by fun_prop))

theorem priceFromHeat_pricingOperator {V : ℝ × ℝ → ℝ} {k h L a x t : ℝ}
    (hV : ContDiffAt ℝ 2 V (x - L, 2 *(t - a))) :
    pricingOperator k h (priceFromHeat V k h L a) (x,t) =
      pricingGauge k h L a x t *
        (2*deriv (fun s => V (x-L,s)) (2*(t-a))-
          deriv (deriv (fun y => V (y,2*(t-a)))) (x-L)) := by
  have hvx : ContDiffAt ℝ 2 (fun y => V (y-L,2*(t-a))) x :=
    hV.comp x (show ContDiffAt ℝ 2 (fun y : ℝ => (y-L,2*(t-a))) x by fun_prop)
  have hvs : DifferentiableAt ℝ (fun s => V (x-L,s)) (2*(t-a)) :=
    (hV.comp (2*(t-a))
        (show ContDiffAt ℝ 2 (fun s : ℝ => (x-L,s)) (2*(t-a)) by fun_prop)).differentiableAt
      (by norm_num)
  have hvt : HasDerivAt (fun s => V (x-L,2*(s-a)))
      (2*deriv (fun s => V (x-L,s)) (2*(t-a))) t := by
    convert! hvs.hasDerivAt.comp t (((hasDerivAt_id t).sub_const a).const_mul 2) using 1
    ring
  have hgt := pricingGauge_hasDeriv_time k h L a x t
  have hgx := pricingGauge_hasDeriv_space k h L a x t
  have hgs : ContDiffAt ℝ 2 (fun y => pricingGauge k h L a y t) x := by
    unfold pricingGauge; fun_prop
  have hx2 := Boundary.Comparison.deriv2_mul_at hgs hvx
  have ht1 := (hgt.mul hvt).deriv
  have hx1 := (hgx.mul (hvx.differentiableAt (by norm_num)).hasDerivAt).deriv
  simp only [Pi.mul_def] at ht1 hx1
  have hshift : deriv (deriv (fun y => V (y-L,2*(t-a)))) x =
      deriv (deriv (fun y => V (y,2*(t-a)))) (x-L) := by
    simpa only [show (2 : ℕ) = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] using
      congr_fun (iteratedDeriv_comp_sub_const (n := 2) (f := fun y => V (y,2*(t-a))) (s := L)) x
  have hshift1 : deriv (fun y => V (y-L,2*(t-a))) x =
      deriv (fun y => V (y,2*(t-a))) (x-L) :=
    deriv_comp_sub_const (fun y => V (y,2*(t-a))) L x
  unfold pricingOperator priceFromHeat
  dsimp only
  rw [ht1,hx2,hx1,pricingGauge_deriv2_space,hgx.deriv,hshift,hshift1]
  ring

end MathFin.BlackScholes.AmericanPut.Stopping
