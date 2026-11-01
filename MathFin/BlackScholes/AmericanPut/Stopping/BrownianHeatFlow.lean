/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.CompactHeatFlow
public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianModel

/-! # Heat evolution as an actual Brownian expectation, including time zero 
## Result

Public entry points include `brownianHeatFlow`, `brownianHeatFlow_zero`,
`brownianHeatFlow_continuous`, `brownianHeatFlow_bound`, `PutWaiting`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open MathFin.FeynmanKacHeatEquation
open scoped NNReal Topology

/-- Heat evolution as a Brownian expectation: the integral of `f (x+B_t)` under
`gaussianLimit`. -/
noncomputable def brownianHeatFlow (f : ℝ → ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  ∫ ω, f (x+brownian t ω) ∂gaussianLimit

theorem brownianHeatFlow_zero {f : ℝ → ℝ} (x : ℝ) : brownianHeatFlow f 0 x = f x := by
  unfold brownianHeatFlow
  have heq : (fun ω => f (x+brownian 0 ω)) =ᵐ[gaussianLimit] (fun _ => f x) := by
    filter_upwards [isBrownianReal_brownian.eval_zero_ae_eq_zero] with ω hω
    rw [hω,add_zero]
  rw [integral_congr_ae heq]
  simp

theorem brownianHeatFlow_continuous {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, ‖f x‖ ≤ C) :
    Continuous (fun z : ℝ≥0 × ℝ => brownianHeatFlow f z.1 z.2) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro z
    exact (hf.measurable.comp (measurable_const.add (measurable_brownian z.1))).aestronglyMeasurable
  · exact fun z => Eventually.of_forall (fun ω => hbound (z.2+brownian z.1 ω))
  · exact integrable_const C
  · exact Eventually.of_forall
      (fun ω => hf.comp (continuous_snd.add ((continuous_brownian ω).comp continuous_fst)))

theorem brownianHeatFlow_bound {f : ℝ → ℝ} {C : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ C) (t : ℝ≥0) (x : ℝ) : ‖brownianHeatFlow f t x‖ ≤ C := by
  simpa only [brownianHeatFlow,probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ := gaussianLimit)
      (Eventually.of_forall (fun ω => hbound (x+brownian t ω))))

theorem brownianHeatFlow_eq_kernel {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ≥0}
    (ht : 0 < t) (x : ℝ) : brownianHeatFlow f t x = feynmanU f t x := by
  simpa only [brownianHeatFlow,Real.toNNReal_coe] using
    (feynmanU_eq_integral_of_map (B := fun s : ℝ => brownian s.toNNReal) (μ := gaussianLimit)
      (isBrownianReal_brownian.toIsPreBrownianReal.aemeasurable (t : ℝ).toNNReal)
      (isBrownianReal_brownian.toIsPreBrownianReal.hasLaw_eval (t : ℝ).toNNReal).map_eq
      hf (show (0 : ℝ) < t by exact_mod_cast ht) x).symm

/-- The heat flow of `f` over time `(2*(t-a)).toNNReal` from the shifted point
`x+(k-h-1)*(t-a)`, discounted by `exp (-k*(t-a))`. -/
noncomputable def linearPriceEvolution (f : ℝ → ℝ) (k h a x t : ℝ) : ℝ :=
  Real.exp (-k*(t-a))*brownianHeatFlow f (2*(t-a)).toNNReal (x+(k-h-1)*(t-a))

/-- A put price `p` (pairs `(log spot, time remaining)`) *waits* at normalized rates `k`, `h`
if it dominates its own discounted Gaussian evolution: for remaining times `0 ≤ a ≤ t`, the price
at remaining time `t` is at least the discounted expectation of the price at remaining time `a`
after a Brownian wait of length `t-a` (`linearPriceEvolution`). This is the one inequality the
stopping verification needs beyond `PutEnvelope p`. Classical solutions satisfy it by the
parabolic comparison (`DividendPutSolution.putWaiting`); the stopping value satisfies it by
dynamic programming (`canonicalPrice_putWaiting`). -/
structure PutWaiting (k h : ℝ) (p : ℝ → ℝ → ℝ) : Prop where
  evolution_le : ∀ {a t : ℝ}, 0 ≤ a → a ≤ t → ∀ x,
    linearPriceEvolution (fun y ↦ p y a) k h a x t ≤ p x t

theorem linearPriceEvolution_initial (f : ℝ → ℝ) (k h a x : ℝ) :
    linearPriceEvolution f k h a x a = f x := by
  simp [linearPriceEvolution,brownianHeatFlow_zero]

theorem linearPriceEvolution_continuous {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, ‖f x‖ ≤ C) (k h a : ℝ) :
    Continuous (fun z : ℝ × ℝ => linearPriceEvolution f k h a z.1 z.2) :=
  (show Continuous (fun z : ℝ × ℝ => Real.exp (-k*(z.2-a))) by fun_prop).mul
    ((brownianHeatFlow_continuous hf hbound).comp
      (show Continuous (fun z : ℝ × ℝ => ((2*(z.2-a)).toNNReal,z.1+(k-h-1)*(z.2-a))) by fun_prop))

theorem linearPriceEvolution_bound {f : ℝ → ℝ} {C k h a x t : ℝ}
    (hbound : ∀ x, ‖f x‖ ≤ C) (hk : 0 ≤ k) (ht : a ≤ t) :
    linearPriceEvolution f k h a x t ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hbound 0)
  have he : Real.exp (-k*(t-a)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hb := brownianHeatFlow_bound hbound (2*(t-a)).toNNReal (x+(k-h-1)*(t-a))
  have hle : brownianHeatFlow f (2*(t-a)).toNNReal (x+(k-h-1)*(t-a)) ≤ C :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb)
  unfold linearPriceEvolution
  exact (mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le).trans (by nlinarith)

theorem linearPriceEvolution_eq_kernel {f : ℝ → ℝ} (hf : Continuous f) {k h a x t : ℝ}
    (ht : a < t) : linearPriceEvolution f k h a x t =
      Real.exp (-k*(t-a))*feynmanU f (2*(t-a)) (x+(k-h-1)*(t-a)) := by
  have htime : 0 < 2*(t-a) := by linarith
  simp only [linearPriceEvolution,brownianHeatFlow_eq_kernel hf (Real.toNNReal_pos.mpr htime),
    Real.coe_toNNReal _ htime.le]

end MathFin.BlackScholes.AmericanPut.Stopping
