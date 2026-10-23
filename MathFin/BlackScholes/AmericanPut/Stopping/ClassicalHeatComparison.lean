/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.LinearPriceComparison
public import MathFin.BlackScholes.AmericanPut.Stopping.SmoothMinorants

/-! # Gaussian comparison for the actual continuous classical price

Smooth compact minorants and dominated convergence remove the test-payoff
restriction. No smoothness across the exercise boundary is assumed.

## Result

Public entry points include `brownianHeatFlow_tendsto_of_bounded`,
`linearPriceEvolution_le_classical_of_continuous`, `classicalPrice_gaussian_comparison`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory Boundary
open scoped Topology NNReal

theorem brownianHeatFlow_tendsto_of_bounded {f : ℝ → ℝ} {m : ℕ → ℝ → ℝ} {C : ℝ}
    (hm : ∀ n, Continuous (m n)) (hb : ∀ n x, ‖m n x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => m n x) atTop (𝓝 (f x))) (t : ℝ≥0) (x : ℝ) :
    Tendsto (fun n => brownianHeatFlow (m n) t x) atTop (𝓝 (brownianHeatFlow f t x)) := by
  exact tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => ((hm n).measurable.comp
      (measurable_const.add (measurable_brownian t))).aestronglyMeasurable)
    (integrable_const C) (fun n => Eventually.of_forall (fun ω => hb n (x+brownian t ω)))
    (Eventually.of_forall (fun ω => hlim (x+brownian t ω)))

theorem linearPriceEvolution_le_classical_of_continuous
    {k h a T : ℝ} {p : ℝ → ℝ → ℝ} {b f : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) (ha : 0 ≤ a)
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (hinit : ∀ x, f x ≤ p x a) :
    ∀ x t, t ∈ Icc a T → linearPriceEvolution f k h a x t ≤ p x t := by
  obtain ⟨m,hm,hc,hle,hb,hlim⟩ := exists_smooth_compact_minorant_sequence hf hf0
    (fun x => (hinit x).trans (hp.bounded x a ha))
  intro x t ht
  have heach (n : ℕ) : linearPriceEvolution (m n) k h a x t ≤ p x t :=
    linearPriceEvolution_le_classical hp ha (hm n) (hc n)
      (fun y => (hle n y).trans (hinit y)) x t ht
  have hconv : Tendsto (fun n => linearPriceEvolution (m n) k h a x t) atTop
      (𝓝 (linearPriceEvolution f k h a x t)) :=
    tendsto_const_nhds.mul (brownianHeatFlow_tendsto_of_bounded
      (fun n => (hm n).continuous) hb hlim _ _)
  exact le_of_tendsto hconv (Eventually.of_forall heach)

theorem classicalPrice_gaussian_comparison
    {k h a t : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) (ha : 0 ≤ a) (hat : a ≤ t) (x : ℝ) :
    linearPriceEvolution (fun y => p y a) k h a x t ≤ p x t := by
  have hf : Continuous (fun y => p y a) := hp.price_continuous.comp_continuous
    (continuous_id.prodMk continuous_const) (fun _ => ha)
  exact linearPriceEvolution_le_classical_of_continuous hp ha hf
    (fun y => hp.price_nonneg y ha) (fun _ => le_rfl) x t ⟨hat,le_rfl⟩

end MathFin.BlackScholes.AmericanPut.Stopping
