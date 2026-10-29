/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.DelayedGrid

/-! # The deterministic waiting inequality for the actual American value

Optimal delayed-grid rules and dominated convergence prove one direction of
continuous-time dynamic programming, without assuming an optimal continuous rule.

## Result

Public entry points include `brownianAmericanPut_wait_integral`, `brownianLogState_integral`,
`brownianAmericanPut_wait`, `canonicalPrice_wait`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped NNReal Topology

theorem brownianAmericanPut_wait_integral {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (u T : ℝ≥0) (x : ℝ) :
    (∫ ω, Real.exp (-r*(u : ℝ))*brownianAmericanPut K r q σ
      (Real.exp (brownianLogState (r-q-σ^2/2) σ x u ω)) T ∂gaussianLimit) ≤
      brownianAmericanPut K r q σ (Real.exp x) (u+T) := by
  have hX : Measurable (brownianLogState (r-q-σ^2/2) σ x u) :=
    measurable_const.add (measurable_const.mul (measurable_brownian u))
  have hc := tendsto_integral_of_dominated_convergence (μ := gaussianLimit) (fun _ => K)
    (F := fun n ω => Real.exp (-r*(u : ℝ))*brownianGridPrice K r q σ T (gridStep n)
      (brownianLogState (r-q-σ^2/2) σ x u ω))
    (f := fun ω => Real.exp (-r*(u : ℝ))*brownianAmericanPut K r q σ
      (Real.exp (brownianLogState (r-q-σ^2/2) σ x u ω)) T)
    (fun n =>
        (measurable_const.mul
        ((brownianGridPrice_continuous hK hr q σ T (gridStep n)).measurable.comp
        hX)).aestronglyMeasurable)
    (integrable_const K)
    (fun n => Eventually.of_forall (fun ω => by
      have hb := brownianGridMarkovAux_bound
        (fun i y => discountedLogPayoff_bound hK hr (cappedGridTime T (gridStep n) i) y)
        T (gridStep n) (r-q-σ^2/2) σ ⌈T/gridStep n⌉₊ 0
        (brownianLogState (r-q-σ^2/2) σ x u ω)
      have he : Real.exp (-r*(u : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [u.coe_nonneg])
      rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans
        ((mul_le_mul_of_nonneg_right he hK).trans (by simp))))
    (Eventually.of_forall (fun ω => tendsto_const_nhds.mul
      (brownianGridPrice_tendsto hK hr T (brownianLogState (r-q-σ^2/2) σ x u ω))))
  exact le_of_tendsto hc
      (Eventually.of_forall (fun n => delayedGridPrice_le_american hK hr u T (gridStep_pos n) x))

theorem brownianLogState_integral {f : ℝ → ℝ} (hf : Continuous f) (β σ x : ℝ) (u : ℝ≥0) :
    (∫ ω, f (brownianLogState β σ x u ω) ∂gaussianLimit) =
      brownianHeatFlow f (σ^2*(u : ℝ)).toNNReal (x+β*(u : ℝ)) := by
  have he := brownian_scaled_increment_heatFlow hf (show (0 : ℝ≥0) ≤ u from zero_le) σ (x+β*(u : ℝ))
  have hz : (fun ω => f (x+β*(u : ℝ)+σ*(brownian u ω-brownian 0 ω))) =ᵐ[gaussianLimit]
      fun ω => f (brownianLogState β σ x u ω) := by
    filter_upwards [isBrownianReal_brownian.eval_zero_ae_eq_zero] with ω hω
    simp only [hω,sub_zero,brownianLogState]
  simpa only [NNReal.coe_zero,sub_zero,integral_congr_ae hz] using he

theorem brownianAmericanPut_wait {K r q σ : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (u T : ℝ≥0) (x : ℝ) :
    Real.exp (-r*(u : ℝ))*brownianHeatFlow
      (fun y => brownianAmericanPut K r q σ (Real.exp y) T)
      (σ^2*(u : ℝ)).toNNReal (x+(r-q-σ^2/2)*(u : ℝ)) ≤
      brownianAmericanPut K r q σ (Real.exp x) (u+T) := by
  have hf : Continuous (fun y => brownianAmericanPut K r q σ (Real.exp y) T) :=
    (brownianAmericanPut_continuousOn_spot hK hr T).comp_continuous Real.continuous_exp
      (fun y => (Real.exp_pos y).le)
  have he := brownianAmericanPut_wait_integral (q := q) (σ := σ) hK hr u T x
  rw [integral_const_mul,brownianLogState_integral hf] at he
  exact he

theorem canonicalPrice_wait {k h : ℝ} (hk : 0 ≤ k) (u T : ℝ≥0) (x : ℝ) :
    Real.exp (-k*(u : ℝ))*brownianHeatFlow (fun y => canonicalPrice k h y (T : ℝ))
      (2*(u : ℝ)).toNNReal (x+(k-h-1)*(u : ℝ)) ≤ canonicalPrice k h x (u+T : ℝ≥0) := by
  have he := brownianAmericanPut_wait (K := 1) (r := k) (q := h) (σ := Real.sqrt 2)
    (by norm_num) hk u T x
  have hprice (y : ℝ) (t : ℝ≥0) : brownianAmericanPut 1 k h (Real.sqrt 2) (Real.exp y) t =
      canonicalPrice k h y (t : ℝ) := by
    simp only [canonicalPrice,Real.toNNReal_coe]
    exact (brownianUsualAmericanPut_eq_raw_of_pos (by norm_num) hk (Real.exp_pos y) t).symm
  simp only
      [hprice,Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),div_self (show (2 : ℝ) ≠ 0 by norm_num)]
      at he
  exact he

end MathFin.BlackScholes.AmericanPut.Stopping
