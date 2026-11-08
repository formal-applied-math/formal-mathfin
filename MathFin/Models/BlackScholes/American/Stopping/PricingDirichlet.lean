/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.Models.BlackScholes.American.Stopping.PricingBoundaryCorrection
public import MathFin.Models.BlackScholes.American.Stopping.ContinuousPriceEvolution

/-!
# Constructed local pricing Dirichlet solution for continuous data

## Main results

* `pricingOperator_add`: the pricing operator is additive on functions that are `C²` at the point.
* `exists_pricing_dirichlet_solution`: for a continuous `u` on the plane and `L < R`, there is a
  continuous `F` that agrees with `u` on the initial segment `[L,R] × {a}` and on both lateral
  sides over `[a,T]`, is `C^∞` on `(L,R) × (a,T)`, and satisfies `pricingOperator k h F = 0`
  there.

## Tags

Dirichlet problem, local pricing solution, continuous data, pricing operator, existence, MSC 35R35,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem pricingOperator_add {F G : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hF : ContDiffAt ℝ 2 F z) (hG : ContDiffAt ℝ 2 G z) (k h : ℝ) :
    pricingOperator k h (fun w => F w+G w) z = pricingOperator k h F z+pricingOperator k h G z := by
  have hFx : ContDiffAt ℝ 2 (fun x => F (x,z.2)) z.1 :=
    hF.comp z.1 (show ContDiffAt ℝ 2 (fun x : ℝ => (x,z.2)) z.1 by fun_prop)
  have hGx : ContDiffAt ℝ 2 (fun x => G (x,z.2)) z.1 :=
    hG.comp z.1 (show ContDiffAt ℝ 2 (fun x : ℝ => (x,z.2)) z.1 by fun_prop)
  have hFt : DifferentiableAt ℝ (fun t => F (z.1,t)) z.2 :=
    (hF.comp z.2 (show ContDiffAt ℝ 2 (fun t : ℝ => (z.1,t)) z.2 by fun_prop)).differentiableAt
      (by norm_num)
  have hGt : DifferentiableAt ℝ (fun t => G (z.1,t)) z.2 :=
    (hG.comp z.2 (show ContDiffAt ℝ 2 (fun t : ℝ => (z.1,t)) z.2 by fun_prop)).differentiableAt
      (by norm_num)
  have hs : deriv (deriv (fun x => F (x,z.2)+G (x,z.2))) z.1 =
      deriv (deriv (fun x => F (x,z.2))) z.1+deriv (deriv (fun x => G (x,z.2))) z.1 := by
    simpa [iteratedDeriv_succ] using iteratedDeriv_fun_add (n := 2) hFx hGx
  unfold pricingOperator
  rw [deriv_fun_add hFt hGt,hs,
    deriv_fun_add (hFx.differentiableAt (by norm_num)) (hGx.differentiableAt (by norm_num))]
  ring

/-- The boundary data are supplied by an arbitrary continuous function, not by
an already-smooth pricing solution. Both lateral sides and the initial trace
are matched by a constructed smooth interior solution. -/
theorem exists_pricing_dirichlet_solution {u : ℝ × ℝ → ℝ} (hu : Continuous u)
    {L R : ℝ} (hLR : L < R) (k h a T : ℝ) :
    ∃ F : ℝ × ℝ → ℝ, Continuous F ∧
      (∀ x ∈ Icc L R, F (x,a) = u (x,a)) ∧
      (∀ t ∈ Icc a T, F (L,t) = u (L,t)) ∧
      (∀ t ∈ Icc a T, F (R,t) = u (R,t)) ∧
      ContDiffOn ℝ ∞ F (Ioo L R ×ˢ Ioo a T) ∧
      ∀ z ∈ Ioo L R ×ˢ Ioo a T, pricingOperator k h F z = 0 := by
  have hf : Continuous (fun x => u (x,a)) := hu.comp (continuous_id.prodMk continuous_const)
  obtain ⟨f,hf,hfc,hfe⟩ := exists_continuous_compact_interval_extension hf L R
  obtain ⟨U,hU,hinit,hUs,hUpde⟩ := exists_smooth_initial_solution hf hfc k h a
  have hbottom : ∀ x ∈ Icc L R, U (x,a) = u (x,a) :=
    fun x hx => (hinit x).trans (hfe x hx)
  let g₀ : ℝ → ℝ := fun t => u (L,max a t)-U (L,max a t)
  let g₁ : ℝ → ℝ := fun t => u (R,max a t)-U (R,max a t)
  have hg₀ : Continuous g₀ :=
    (hu.comp (continuous_const.prodMk (continuous_const.max continuous_id))).sub
      (hU.comp (continuous_const.prodMk (continuous_const.max continuous_id)))
  have hg₁ : Continuous g₁ :=
    (hu.comp (continuous_const.prodMk (continuous_const.max continuous_id))).sub
      (hU.comp (continuous_const.prodMk (continuous_const.max continuous_id)))
  have hs₀ : ∀ t, t ≤ a → g₀ t = 0 := by
    intro t ht
    simp only [g₀,max_eq_left ht,hbottom L ⟨le_rfl,hLR.le⟩,sub_self]
  have hs₁ : ∀ t, t ≤ a → g₁ t = 0 := by
    intro t ht
    simp only [g₁,max_eq_left ht,hbottom R ⟨hLR.le,le_rfl⟩,sub_self]
  obtain ⟨C,hC,hCstart,hCleft,hCright,hCs,hCpde⟩ :=
    exists_interval_pricing_boundary_solution hg₀ hg₁ hLR hs₀ hs₁ k h T
  have hUa : ∀ z, a < z.2 → ContDiffAt ℝ ∞ U z := fun z hz =>
    hUs.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hz)
  have hCa : ∀ z, L < z.1 → z.1 < R → ContDiffAt ℝ ∞ C z := fun z hx hxR =>
    hCs.contDiffAt (((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)).mem_nhds ⟨hx,hxR⟩)
  refine ⟨fun z => U z+C z,hU.add hC,?_,?_,?_,?_,?_⟩
  · intro x hx
    dsimp only
    rw [hCstart x a le_rfl,add_zero,hbottom x hx]
  · intro t ht
    dsimp only
    rw [hCleft t ht]
    dsimp [g₀]
    rw [max_eq_right ht.1]
    ring
  · intro t ht
    dsimp only
    rw [hCright t ht]
    dsimp [g₁]
    rw [max_eq_right ht.1]
    ring
  · intro z hz
    exact ((hUa z hz.2.1).add (hCa z hz.1.1 hz.1.2)).contDiffWithinAt
  · intro z hz
    rw [pricingOperator_add ((hUa z hz.2.1).of_le (WithTop.coe_le_coe.mpr le_top))
      ((hCa z hz.1.1 hz.1.2).of_le (WithTop.coe_le_coe.mpr le_top)),
      hUpde z hz.2.1,hCpde z hz.1.1 hz.1.2,add_zero]

end MathFin.BlackScholes.AmericanPut.Stopping
