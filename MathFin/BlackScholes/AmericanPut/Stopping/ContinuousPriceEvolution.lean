/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.LinearPriceComparison
public import MathFin.BlackScholes.AmericanPut.Stopping.ActualSmoothComparison

/-! # Constructed smooth evolution for continuous initial price data

This constructs the initial-data part of a local Dirichlet solution. Matching
the two lateral sides is a separate obligation, not claimed here.

## Result

Public entry points include `linearPriceEvolution_smoothAt`, `linearPriceEvolution_pricingOperator`,
`exists_smooth_initial_solution`, `exists_continuous_compact_interval_extension`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open MathFin.FeynmanKacHeatEquation
open scoped Topology ContDiff NNReal

theorem linearPriceEvolution_smoothAt {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) {k h a x t : ℝ} (ht : a < t) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => linearPriceEvolution f k h a z.1 z.2) (x,t) := by
  have hheat : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => feynmanU f z.1 z.2)
      (2*(t-a),x+(k-h-1)*(t-a)) :=
    (compact_continuous_heatFlow_smooth hf hc).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds (by dsimp; linarith))
  have hcomp : ContDiffAt ℝ ∞
      (fun z : ℝ × ℝ => feynmanU f (2*(z.2-a)) (z.1+(k-h-1)*(z.2-a))) (x,t) := by
    simpa only [Function.comp_def] using hheat.comp (x,t)
      (show ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (2*(z.2-a),z.1+(k-h-1)*(z.2-a))) (x,t) by fun_prop)
  have hkern : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => linearPriceKernel f k h a z.1 z.2) (x,t) :=
    (show ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => Real.exp (-k*(z.2-a))) (x,t) by fun_prop).mul hcomp
  exact hkern.congr_of_eventuallyEq (linearPriceEvolution_eventuallyEq_kernel hf ht)

theorem linearPriceEvolution_pricingOperator {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) {k h a x t : ℝ} (ht : a < t) :
    pricingOperator k h (fun z => linearPriceEvolution f k h a z.1 z.2) (x,t) = 0 := by
  have he := linearPriceEvolution_eventuallyEq_kernel (k := k) (h := h) (x := x) hf ht
  have het : linearPriceEvolution f k h a x =ᶠ[𝓝 t] linearPriceKernel f k h a x := by
    simpa only [Function.comp_def,id_eq] using he.comp_tendsto
        (continuousAt_const.prodMk continuousAt_id)
  have hex : (fun y => linearPriceEvolution f k h a y t) =ᶠ[𝓝 x]
      (fun y => linearPriceKernel f k h a y t) := by
    simpa only [Function.comp_def,id_eq] using he.comp_tendsto
        (continuousAt_id.prodMk continuousAt_const)
  have hp := linearPriceKernel_equation (k := k) (h := h) (x := x) hf hc ht
  unfold Boundary.dividendSpatialOperator at hp
  unfold pricingOperator
  rw [het.deriv_eq,hex.deriv_eq,hex.deriv.deriv_eq,he.self_of_nhds]
  linarith

/-- A real construction: Gaussian evolution supplies all four properties. -/
theorem exists_smooth_initial_solution {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (k h a : ℝ) :
    ∃ U : ℝ × ℝ → ℝ, Continuous U ∧
      (∀ x, U (x,a) = f x) ∧ ContDiffOn ℝ ∞ U {z | a < z.2} ∧
      ∀ z, a < z.2 → pricingOperator k h U z = 0 := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hf
  refine ⟨fun z => linearPriceEvolution f k h a z.1 z.2,
    linearPriceEvolution_continuous hf hC k h a,?_,?_,?_⟩
  · exact fun x => linearPriceEvolution_initial f k h a x
  · exact fun z hz => (linearPriceEvolution_smoothAt hf hc hz).contDiffWithinAt
  · exact fun z hz => linearPriceEvolution_pricingOperator hf hc hz

theorem exists_continuous_compact_interval_extension {f : ℝ → ℝ} (hf : Continuous f)
    (L R : ℝ) : ∃ g : ℝ → ℝ, Continuous g ∧ HasCompactSupport g ∧ ∀ x ∈ Icc L R, g x = f x := by
  let χ : ContDiffBump (0 : ℝ) := {
    rIn := |L|+|R|+1
    rOut := |L|+|R|+2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  refine ⟨fun x => χ x*f x,χ.continuous.mul hf,χ.hasCompactSupport.mul_right,?_⟩
  intro x hx
  have hb : x ∈ Metric.closedBall (0 : ℝ) χ.rIn := by
    change dist x 0 ≤ |L|+|R|+1
    rw [Real.dist_eq,sub_zero,abs_le]
    constructor
    · linarith [neg_abs_le L,abs_nonneg R,hx.1]
    · linarith [le_abs_self R,abs_nonneg L,hx.2]
  change χ x*f x = f x
  rw [χ.one_of_mem_closedBall hb,one_mul]

/-- The actual price's continuous initial trace on any finite spatial interval
has a constructed positive-time smooth PDE evolution. Lateral matching is not
among the conclusions. -/
theorem exists_canonicalPrice_initial_solution {k h : ℝ} (hk : 0 ≤ k) (a L R : ℝ) :
    ∃ U : ℝ × ℝ → ℝ, Continuous U ∧
      (∀ x ∈ Icc L R, U (x,a) = canonicalPrice k h x a) ∧
      ContDiffOn ℝ ∞ U {z | a < z.2} ∧
      ∀ z, a < z.2 → pricingOperator k h U z = 0 := by
  have hf : Continuous (fun x => canonicalPrice k h x a) :=
    (canonicalPrice_continuous hk).comp (continuous_id.prodMk continuous_const)
  obtain ⟨g,hg,hgc,hge⟩ := exists_continuous_compact_interval_extension hf L R
  obtain ⟨U,hU,hinit,hUs,hPDE⟩ := exists_smooth_initial_solution hg hgc k h a
  exact ⟨U,hU,fun x hx => (hinit x).trans (hge x hx),hUs,hPDE⟩

end MathFin.BlackScholes.AmericanPut.Stopping
