/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.CoupledHeatBoundary
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Two-sided heat boundary correction on a finite interval 
## Result

Public entry points include `exists_boundary_time_cutoff`, `intervalHeatCorrection`,
`intervalHeatCorrection_continuous`, `intervalHeatCorrection_smoothAt`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction

theorem exists_boundary_time_cutoff (a T : ℝ) :
    ∃ (D : ℝ) (χ : ℝ →ᵇ ℝ), 0 ≤ D ∧ HasCompactSupport (χ : ℝ → ℝ) ∧
      (∀ t, ‖χ t‖ ≤ 1) ∧ (∀ t ∈ Icc a T, χ t = 1) ∧
      ∀ t, a+D < t → χ t = 0 := by
  let ψ : ContDiffBump (0 : ℝ) := {
    rIn := max |a| |T|+1
    rOut := max |a| |T|+2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  have hb : ∀ t, ‖ψ t‖ ≤ 1 := fun _ => by
    rw [Real.norm_of_nonneg ψ.nonneg]
    exact ψ.le_one
  let χ : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup ψ ψ.continuous 1 hb
  refine ⟨ψ.rOut+|a|,χ,by dsimp [ψ]; positivity,ψ.hasCompactSupport,hb,?_,?_⟩
  · intro t ht
    change ψ t = 1
    apply ψ.one_of_mem_closedBall
    rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs]
    change |t| ≤ max |a| |T|+1
    have ha : -max |a| |T| ≤ a := (neg_le_neg (le_max_left _ _)).trans (neg_abs_le a)
    have hT : T ≤ max |a| |T| := (le_abs_self T).trans (le_max_right _ _)
    exact (abs_le.mpr ⟨ha.trans ht.1,ht.2.trans hT⟩).trans (by linarith)
  · intro t ht
    change ψ t = 0
    apply ψ.zero_of_le_dist
    rw [dist_zero_right,Real.norm_eq_abs]
    have ha := neg_abs_le a
    exact (show ψ.rOut ≤ t by linarith).trans (le_abs_self t)

/-- The two-sided correction on `[0,L]`: the half-line extension of `f₀` at depth `x` plus that
of `f₁` at depth `L-x`. -/
noncomputable def intervalHeatCorrection (f₀ f₁ : ℝ → ℝ) (L : ℝ) (x t : ℝ) : ℝ :=
  heatBoundaryExtension f₀ x t+heatBoundaryExtension f₁ (L-x) t

theorem intervalHeatCorrection_continuous (f₀ f₁ : ℝ →ᵇ ℝ) (L : ℝ) :
    Continuous (fun z : ℝ × ℝ => intervalHeatCorrection f₀ f₁ L z.1 z.2) :=
  (heatBoundaryExtension_continuous f₀.continuous f₀.norm_coe_le_norm).add
    ((heatBoundaryExtension_continuous f₁.continuous f₁.norm_coe_le_norm).comp
      ((continuous_const.sub continuous_fst).prodMk continuous_snd))

theorem intervalHeatCorrection_smoothAt {f₀ f₁ : ℝ → ℝ}
    (h₀ : Continuous f₀) (hc₀ : HasCompactSupport f₀)
    (h₁ : Continuous f₁) (hc₁ : HasCompactSupport f₁) {L x t : ℝ}
    (hx : 0 < x) (hxL : x < L) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => intervalHeatCorrection f₀ f₁ L z.1 z.2) (x,t) := by
  have h0 := (compact_heatBoundaryExtension_smooth h₀ hc₀).contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds
        (show (x,t) ∈ {z : ℝ × ℝ | 0 < z.1} from hx))
  have h1 := (compact_heatBoundaryExtension_smooth h₁ hc₁).contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds
      (show (L-x,t) ∈ {z : ℝ × ℝ | 0 < z.1} from sub_pos.mpr hxL))
  exact h0.add (h1.comp (x,t) (f := fun z : ℝ × ℝ => (L-z.1,z.2))
    (show ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (L-z.1,z.2)) (x,t) by fun_prop))

theorem intervalHeatCorrection_equation {f₀ f₁ : ℝ → ℝ}
    (h₀ : Continuous f₀) (hc₀ : HasCompactSupport f₀)
    (h₁ : Continuous f₁) (hc₁ : HasCompactSupport f₁) {L x t : ℝ}
    (hx : 0 < x) (hxL : x < L) :
    deriv (fun s => intervalHeatCorrection f₀ f₁ L x s) t =
      (1/2)*deriv (deriv (fun y => intervalHeatCorrection f₀ f₁ L y t)) x := by
  have h0 := (compact_heatBoundaryExtension_smooth h₀ hc₀).contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds
        (show (x,t) ∈ {z : ℝ × ℝ | 0 < z.1} from hx))
  have h1 := (compact_heatBoundaryExtension_smooth h₁ hc₁).contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds
      (show (L-x,t) ∈ {z : ℝ × ℝ | 0 < z.1} from sub_pos.mpr hxL))
  have h0x : ContDiffAt ℝ 2 (fun y => heatBoundaryExtension f₀ y t) x :=
    (h0.comp x (show ContDiffAt ℝ ∞ (fun y : ℝ => (y,t)) x by fun_prop)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have h1x : ContDiffAt ℝ 2 (fun y => heatBoundaryExtension f₁ (L-y) t) x :=
    (h1.comp x (show ContDiffAt ℝ ∞ (fun y : ℝ => (L-y,t)) x by fun_prop)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hs : deriv
      (deriv (fun y => heatBoundaryExtension f₀ y t+heatBoundaryExtension f₁ (L-y) t)) x =
      deriv (deriv (fun y => heatBoundaryExtension f₀ y t)) x+
      deriv (deriv (fun y => heatBoundaryExtension f₁ (L-y) t)) x := by
    simpa only [show (2 : ℕ) = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] using
      iteratedDeriv_fun_add h0x h1x
  have hr : deriv (deriv (fun y => heatBoundaryExtension f₁ (L-y) t)) x =
      deriv (deriv (fun y => heatBoundaryExtension f₁ y t)) (L-x) := by
    simpa only [show (2 : ℕ) = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero,
      show (-1 : ℝ)^(1+1) = 1 by norm_num,one_smul] using congr_fun
      (iteratedDeriv_comp_const_sub (n := 2) (f := fun y => heatBoundaryExtension f₁ y t) (s := L))
          x
  have ht₀ : DifferentiableAt ℝ (fun s => heatBoundaryExtension f₀ x s) t :=
    (h0.comp t (show ContDiffAt ℝ ∞ (fun s : ℝ => (x,s)) t by fun_prop)).differentiableAt (by simp)
  have ht₁ : DifferentiableAt ℝ (fun s => heatBoundaryExtension f₁ (L-x) s) t :=
    (h1.comp t (show ContDiffAt ℝ ∞ (fun s : ℝ => (L-x,s)) t by fun_prop)).differentiableAt
        (by simp)
  unfold intervalHeatCorrection
  rw [deriv_fun_add ht₀ ht₁,hs,hr,
    compact_heatBoundaryExtension_equation h₀ hc₀ hx t,
    compact_heatBoundaryExtension_equation h₁ hc₁ (sub_pos.mpr hxL) t]
  ring

/-- Constructed two-sided boundary correction, with no regularity assumed of the
boundary data beyond continuity and a compatible zero initial trace. -/
theorem exists_interval_heat_boundary_solution {g₀ g₁ : ℝ → ℝ}
    (h₀ : Continuous g₀) (hc₀ : HasCompactSupport g₀)
    (h₁ : Continuous g₁) (hc₁ : HasCompactSupport g₁) {a L : ℝ}
    (hL : 0 < L) (hs₀ : ∀ t, t ≤ a → g₀ t = 0) (hs₁ : ∀ t, t ≤ a → g₁ t = 0) (T : ℝ) :
    ∃ V : ℝ × ℝ → ℝ, Continuous V ∧
      (∀ x t, t ≤ a → V (x,t) = 0) ∧
      (∀ t ∈ Icc a T, V (0,t) = g₀ t) ∧
      (∀ t ∈ Icc a T, V (L,t) = g₁ t) ∧
      ContDiffOn ℝ ∞ V {z | 0 < z.1 ∧ z.1 < L} ∧
      ∀ x, 0 < x → x < L → ∀ t, deriv (fun s => V (x,s)) t =
        (1/2)*deriv (deriv (fun y => V (y,t))) x := by
  obtain ⟨C₀,hC₀⟩ := hc₀.exists_bound_of_continuous h₀
  obtain ⟨C₁,hC₁⟩ := hc₁.exists_bound_of_continuous h₁
  let G₀ : CausalBoundaryData a :=
    ⟨BoundedContinuousFunction.ofNormedAddCommGroup g₀ h₀ C₀ hC₀,hs₀⟩
  let G₁ : CausalBoundaryData a :=
    ⟨BoundedContinuousFunction.ofNormedAddCommGroup g₁ h₁ C₁ hC₁,hs₁⟩
  obtain ⟨D,χ,hD,hcχ,hχ,hone,hstop⟩ := exists_boundary_time_cutoff a T
  obtain ⟨f₀,f₁,hf₀,hf₁,he₀,he₁⟩ :=
    exists_coupled_compact_boundary_inputs hL hD χ hχ hstop hcχ G₀ G₁ hc₀ hc₁
  refine ⟨fun z => intervalHeatCorrection f₀.1 f₁.1 L z.1 z.2,
    intervalHeatCorrection_continuous f₀.1 f₁.1 L,?_,?_,?_,?_,?_⟩
  · intro x t ht
    simp only [intervalHeatCorrection,heatBoundaryExtension_causal f₀.2 x ht,
      heatBoundaryExtension_causal f₁.2 (L-x) ht,add_zero]
  · intro t ht
    have he := he₀ t
    rw [hone t ht,one_mul] at he
    change f₀.1 t+heatBoundaryExtension f₁.1 L t = g₀ t at he
    simpa only [intervalHeatCorrection,sub_zero,heatBoundaryExtension_boundary] using he
  · intro t ht
    have he := he₁ t
    rw [hone t ht,one_mul] at he
    change f₁.1 t+heatBoundaryExtension f₀.1 L t = g₁ t at he
    simpa only [intervalHeatCorrection,sub_self,heatBoundaryExtension_boundary,add_comm] using he
  · intro z hz
    exact (intervalHeatCorrection_smoothAt f₀.1.continuous hf₀ f₁.1.continuous hf₁
      hz.1 hz.2).contDiffWithinAt
  · intro x hx hxL t
    exact intervalHeatCorrection_equation f₀.1.continuous hf₀ f₁.1.continuous hf₁ hx hxL

/-- Compact support is supplied by the construction, not required of the data. -/
theorem exists_interval_heat_boundary_solution_continuous {g₀ g₁ : ℝ → ℝ}
    (h₀ : Continuous g₀) (h₁ : Continuous g₁) {a L : ℝ}
    (hL : 0 < L) (hs₀ : ∀ t, t ≤ a → g₀ t = 0) (hs₁ : ∀ t, t ≤ a → g₁ t = 0) (T : ℝ) :
    ∃ V : ℝ × ℝ → ℝ, Continuous V ∧
      (∀ x t, t ≤ a → V (x,t) = 0) ∧
      (∀ t ∈ Icc a T, V (0,t) = g₀ t) ∧
      (∀ t ∈ Icc a T, V (L,t) = g₁ t) ∧
      ContDiffOn ℝ ∞ V {z | 0 < z.1 ∧ z.1 < L} ∧
      ∀ x, 0 < x → x < L → ∀ t, deriv (fun s => V (x,s)) t =
        (1/2)*deriv (deriv (fun y => V (y,t))) x := by
  obtain ⟨D,χ,_hD,hcχ,_hχ,hone,_hstop⟩ := exists_boundary_time_cutoff a T
  obtain ⟨V,hV,hstart,hleft,hright,hsmooth,hpde⟩ := exists_interval_heat_boundary_solution
    (χ.continuous.mul h₀) hcχ.mul_right (χ.continuous.mul h₁) hcχ.mul_right hL
    (fun t ht => by change χ t*g₀ t = 0; rw [hs₀ t ht,mul_zero])
    (fun t ht => by change χ t*g₁ t = 0; rw [hs₁ t ht,mul_zero]) T
  refine ⟨V,hV,hstart,?_,?_,hsmooth,hpde⟩
  · intro t ht
    simpa only [Pi.mul_apply,hone t ht,one_mul] using hleft t ht
  · intro t ht
    simpa only [Pi.mul_apply,hone t ht,one_mul] using hright t ht

end MathFin.BlackScholes.AmericanPut.Stopping
