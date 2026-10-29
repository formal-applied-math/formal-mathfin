/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianHeatFlow
public import MathFin.BlackScholes.AmericanPut.Stopping.ContinuousHeatSmoothing

/-! # Gaussian evolution of a smooth test payoff stays below the classical price 
## Result

Public entry points include `linearPriceKernel`, `linearPriceEvolution_eventuallyEq_kernel`,
`linearPriceKernel_contDiffAt`, `heatFlow_affine_hasDeriv`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory Boundary
open MathFin.FeynmanKacHeatEquation
open scoped Topology ContDiff

/-- `Real.exp (-k*(t-a))` times the heat flow `feynmanU f (2*(t-a))`, evaluated at the drifted
point `x+(k-h-1)*(t-a)`. -/
noncomputable def linearPriceKernel (f : ℝ → ℝ) (k h a x t : ℝ) : ℝ :=
  Real.exp (-k*(t-a))*feynmanU f (2*(t-a)) (x+(k-h-1)*(t-a))

theorem linearPriceEvolution_eventuallyEq_kernel {f : ℝ → ℝ} (hf : Continuous f)
    {k h a x t : ℝ} (ht : a < t) :
    (fun z : ℝ × ℝ => linearPriceEvolution f k h a z.1 z.2) =ᶠ[𝓝 (x,t)]
      (fun z => linearPriceKernel f k h a z.1 z.2) := by
  filter_upwards [continuousAt_const.eventually_lt continuousAt_snd ht] with z hz
  exact linearPriceEvolution_eq_kernel hf hz

theorem linearPriceKernel_contDiffAt {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {k h a x t : ℝ} (ht : a < t) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => linearPriceKernel f k h a z.1 z.2) (x,t) := by
  have hF : ContDiffAt ℝ 2 (fun z : ℝ × ℝ => feynmanU f z.1 z.2)
      (2*(t-a),x+(k-h-1)*(t-a)) :=
    (compact_continuous_heatFlow_contDiff hf hc).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds (by dsimp; linarith))
  have hcomp : ContDiffAt ℝ 2
      (fun z : ℝ × ℝ => feynmanU f (2*(z.2-a)) (z.1+(k-h-1)*(z.2-a))) (x,t) := by
    simpa only [Function.comp_def] using hF.comp (x,t)
      (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ => (2*(z.2-a),z.1+(k-h-1)*(z.2-a))) (x,t) by fun_prop)
  exact (show ContDiffAt ℝ 2 (fun z : ℝ × ℝ => Real.exp (-k*(z.2-a))) (x,t) by fun_prop).mul hcomp

theorem heatFlow_affine_hasDeriv {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {α a x t : ℝ} (ht : a < t) :
    HasDerivAt (fun s => feynmanU f (2*(s-a)) (x+α*(s-a)))
      (2*deriv (fun u => feynmanU f u (x+α*(t-a))) (2*(t-a)) +
        α*deriv (feynmanU f (2*(t-a))) (x+α*(t-a))) t := by
  let u := 2*(t-a)
  let y := x+α*(t-a)
  have hd : DifferentiableAt ℝ (fun z : ℝ × ℝ => feynmanU f z.1 z.2) (u,y) :=
    ((compact_continuous_heatFlow_contDiff hf hc).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds
          (by dsimp [u]; linarith))).differentiableAt (by norm_num)
  let A := fderiv ℝ (fun z : ℝ × ℝ => feynmanU f z.1 z.2) (u,y)
  have hdu : HasDerivAt (fun s => feynmanU f s y) (A (1,0)) u := by
    simpa only [Function.comp_def,id_eq] using hd.hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u y))
  have hdy : HasDerivAt (feynmanU f u) (A (0,1)) y := by
    simpa only [Function.comp_def,id_eq] using hd.hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y u).prodMk (hasDerivAt_id y))
  have hpath : HasDerivAt (fun s => (2*(s-a),x+α*(s-a))) (2,α) t := by
    convert! (((hasDerivAt_id t).sub_const a).const_mul 2).prodMk
      ((((hasDerivAt_id t).sub_const a).const_mul α).const_add x) using 1
    simp
  change HasDerivAt _ (2*deriv (fun s => feynmanU f s y) u+α*deriv (feynmanU f u) y) t
  rw [hdu.deriv,hdy.deriv]
  convert! hd.hasFDerivAt.comp_hasDerivAt t hpath using 1
  rw [show ((2,α) : ℝ × ℝ) = (2 : ℝ) • (1,0)+α • (0,1) by ext <;> simp]
  simp only [map_add,map_smul,smul_eq_mul]
  rfl

theorem linearPriceKernel_equation {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {k h a x t : ℝ} (ht : a < t) :
    deriv (linearPriceKernel f k h a x) t =
      dividendSpatialOperator k h (fun y => linearPriceKernel f k h a y t) x := by
  have hdt : HasDerivAt (linearPriceKernel f k h a x)
      (Real.exp (-k*(t-a))*(2*deriv (fun u => feynmanU f u (x+(k-h-1)*(t-a))) (2*(t-a)) +
        (k-h-1)*deriv (feynmanU f (2*(t-a))) (x+(k-h-1)*(t-a)) -
        k*feynmanU f (2*(t-a)) (x+(k-h-1)*(t-a)))) t := by
    convert! ((((hasDerivAt_id t).sub_const a).const_mul (-k)).exp).mul
      (heatFlow_affine_hasDeriv hf hc ht) using 1
    simp only [id_eq]
    ring
  have hdx : deriv (fun y => linearPriceKernel f k h a y t) = fun y =>
      Real.exp (-k*(t-a))*deriv (feynmanU f (2*(t-a))) (y+(k-h-1)*(t-a)) := by
    funext y
    simp only [linearPriceKernel,deriv_const_mul_field,deriv_comp_add_const]
  have hdxx : deriv (deriv (fun y => linearPriceKernel f k h a y t)) x =
      Real.exp (-k*(t-a))*deriv (deriv (feynmanU f (2*(t-a)))) (x+(k-h-1)*(t-a)) := by
    rw [hdx,deriv_const_mul_field,deriv_comp_add_const]
  unfold dividendSpatialOperator
  rw [hdt.deriv,hdxx,hdx,compact_heatFlow_equation hf hc (by linarith)]
  unfold linearPriceKernel
  ring

theorem linearPriceEvolution_le_classical {k h a T : ℝ} {p : ℝ → ℝ → ℝ} {b f : ℝ → ℝ}
    (hp : DividendPutSolution k h p b) (ha : 0 ≤ a)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (hinit : ∀ x, f x ≤ p x a) :
    ∀ x t, t ∈ Icc a T → linearPriceEvolution f k h a x t ≤ p x t := by
  obtain ⟨C,hC⟩ := (hc.norm.isCompact_range hf.continuous.norm).bddAbove
  have hbound : ∀ x, ‖f x‖ ≤ C := fun x => hC (mem_range_self x)
  apply hp.obstacle_comparison_unbounded_window ha
    (linearPriceEvolution_continuous hf.continuous hbound k h a).continuousOn
    (fun _ _ ht => linearPriceEvolution_bound hbound hp.rate_pos.le ht.1)
  · intro x t ht _ _
    exact (linearPriceKernel_contDiffAt hf.continuous hc ht).congr_of_eventuallyEq
      (linearPriceEvolution_eventuallyEq_kernel hf.continuous ht)
  · intro x t ht _ _
    have he := linearPriceEvolution_eventuallyEq_kernel (k := k) (h := h) (x := x) hf.continuous ht
    have het : linearPriceEvolution f k h a x =ᶠ[𝓝 t] linearPriceKernel f k h a x := by
      simpa only [Function.comp_def,id_eq] using he.comp_tendsto
          (continuousAt_const.prodMk continuousAt_id)
    have hex : (fun y => linearPriceEvolution f k h a y t) =ᶠ[𝓝 x]
        (fun y => linearPriceKernel f k h a y t) := by
      simpa only [Function.comp_def,id_eq] using he.comp_tendsto
          (continuousAt_id.prodMk continuousAt_const)
    unfold dividendSpatialOperator
    rw [het.deriv_eq,hex.deriv_eq,hex.deriv.deriv_eq,he.self_of_nhds]
    exact (linearPriceKernel_equation hf.continuous hc ht).le
  · intro x
    simpa only [linearPriceEvolution_initial] using hinit x

end MathFin.BlackScholes.AmericanPut.Stopping
