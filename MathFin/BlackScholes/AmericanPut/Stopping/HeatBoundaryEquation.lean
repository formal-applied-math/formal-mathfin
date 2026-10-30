/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.CompactKernelDerivative
public import MathFin.BlackScholes.AmericanPut.Stopping.PlanePartial

/-! # Heat equation for the continuous compact-data boundary integral 
## Result

Public entry points include `boundaryKernelPlane_equation`,
`compact_causalBoundaryIntegral_equation`, `exists_halfLine_heat_boundary_solution`; the
directional derivatives are `planePartial` (`PlanePartial`).
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The causal heat boundary kernel as one function of the plane point `z = (t,x)`. -/
noncomputable def boundaryKernelPlane (z : ℝ × ℝ) : ℝ := causalHeatBoundaryKernel z.1 z.2

theorem boundaryKernelPlane_smoothAt {z : ℝ × ℝ} (hx : 0 < z.2) :
    ContDiffAt ℝ ∞ boundaryKernelPlane z := causalHeatBoundaryKernel_smoothAt hx.ne'

theorem boundaryKernelPlane_equation (t : ℝ) {x : ℝ} (hx : 0 < x) :
    planePartial boundaryKernelPlane (1,0) (t,x) =
      (1/2)*planePartial (planePartial boundaryKernelPlane (0,1)) (0,1) (t,x) := by
  have ht :=
      planePartial_hasDeriv_time (t := t) ((boundaryKernelPlane_smoothAt hx).differentiableAt (by simp))
  have hd := planePartial_hasDeriv_space
    ((planePartial_smoothAt (boundaryKernelPlane_smoothAt (z := (t,x)) hx) (0,1)).differentiableAt
        (by simp))
  have he : (fun y => planePartial boundaryKernelPlane (0,1) (t,y)) =ᶠ[𝓝 x]
      deriv (causalHeatBoundaryKernel t) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact (planePartial_hasDeriv_space
        ((boundaryKernelPlane_smoothAt hy).differentiableAt (by simp))).deriv.symm
  rw [← ht.deriv,← hd.deriv,he.deriv_eq]
  exact causalHeatBoundaryKernel_equation t hx

theorem compact_causalBoundaryIntegral_hasDeriv_time {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (fun s => causalBoundaryIntegral g x s)
      (∫ y, planePartial boundaryKernelPlane (1,0) (t-y,x)*g y) t := by
  apply compact_kernelIntegral_hasDeriv hg hc (U := univ)
    (F := fun s y => boundaryKernelPlane (s-y,x))
    (F' := fun s y => planePartial boundaryKernelPlane (1,0) (s-y,x)) isOpen_univ
  · intro z _
    exact ((boundaryKernelPlane_smoothAt hx).continuousAt.comp
      (show ContinuousAt (fun z : ℝ × ℝ => (z.1-z.2,x)) z by fun_prop)).continuousWithinAt
  · intro z _
    exact ((planePartial_smoothAt (boundaryKernelPlane_smoothAt hx) (1,0)).continuousAt.comp
      (show ContinuousAt (fun z : ℝ × ℝ => (z.1-z.2,x)) z by fun_prop)).continuousWithinAt
  · intro s _ y
    convert! (planePartial_hasDeriv_time
      ((boundaryKernelPlane_smoothAt hx).differentiableAt (by simp))).comp s
      ((hasDerivAt_id s).sub_const y) using 1
    simp
  · exact mem_univ _

theorem compact_planeIntegral_hasDeriv_space {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) {F : ℝ × ℝ → ℝ}
    (hF : ∀ z, 0 < z.2 → ContDiffAt ℝ ∞ F z) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (fun x => ∫ y, F (t-y,x)*g y)
      (∫ y, planePartial F (0,1) (t-y,x)*g y) x := by
  apply compact_kernelIntegral_hasDeriv hg hc (U := Ioi 0)
    (F := fun s y => F (t-y,s))
    (F' := fun s y => planePartial F (0,1) (t-y,s)) isOpen_Ioi
  · intro z hz
    exact ((hF (t-z.2,z.1) hz.1).continuousAt.comp (f := fun w : ℝ × ℝ => (t-w.2,w.1))
      (show ContinuousAt (fun z : ℝ × ℝ => (t-z.2,z.1)) z by fun_prop)).continuousWithinAt
  · intro z hz
    exact ((planePartial_smoothAt (hF (t-z.2,z.1) hz.1) (0,1)).continuousAt.comp
      (f := fun w : ℝ × ℝ => (t-w.2,w.1))
      (show ContinuousAt (fun z : ℝ × ℝ => (t-z.2,z.1)) z by fun_prop)).continuousWithinAt
  · intro s hs y
    exact planePartial_hasDeriv_space ((hF (t-y,s) hs).differentiableAt (by simp))
  · exact hx

theorem compact_causalBoundaryIntegral_equation {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    deriv (fun s => causalBoundaryIntegral g x s) t =
      (1/2)*deriv (deriv (fun x => causalBoundaryIntegral g x t)) x := by
  have hF : ∀ z, 0 < z.2 → ContDiffAt ℝ ∞ boundaryKernelPlane z :=
    fun _ hz => boundaryKernelPlane_smoothAt hz
  have hD : ∀ z, 0 < z.2 → ContDiffAt ℝ ∞ (planePartial boundaryKernelPlane (0,1)) z :=
    fun z hz => planePartial_smoothAt (hF z hz) (0,1)
  have he : deriv (fun x => causalBoundaryIntegral g x t) =ᶠ[𝓝 x]
      (fun x => ∫ y, planePartial boundaryKernelPlane (0,1) (t-y,x)*g y) := by
    filter_upwards [lt_mem_nhds hx] with u hu
    exact (compact_planeIntegral_hasDeriv_space hg hc hF hu t).deriv
  rw [(compact_causalBoundaryIntegral_hasDeriv_time hg hc hx t).deriv,he.deriv_eq,
    (compact_planeIntegral_hasDeriv_space hg hc hD hx t).deriv,← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [boundaryKernelPlane_equation (t-y) hx]
  ring

theorem compact_heatBoundaryExtension_equation {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    deriv (fun s => heatBoundaryExtension g x s) t =
      (1/2)*deriv (deriv (fun x => heatBoundaryExtension g x t)) x := by
  have ht : (fun s => heatBoundaryExtension g x s) = fun s => causalBoundaryIntegral g x s :=
    funext fun s => heatBoundaryExtension_eq_causalBoundaryIntegral g hx s
  have hx' : (fun u => heatBoundaryExtension g u t) =ᶠ[𝓝 x]
      (fun u => causalBoundaryIntegral g u t) := by
    filter_upwards [lt_mem_nhds hx] with u hu
    exact heatBoundaryExtension_eq_causalBoundaryIntegral g hu t
  rw [ht,hx'.deriv.deriv_eq]
  exact compact_causalBoundaryIntegral_equation hg hc hx t

/-- Constructed half-line solution for continuous compact boundary data that starts at `a`.
This is not a solution matching both ends of a finite interval. -/
theorem exists_halfLine_heat_boundary_solution {g : ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) {a : ℝ}
    (hstart : ∀ t, t ≤ a → g t = 0) :
    ∃ V : ℝ × ℝ → ℝ, Continuous V ∧
      (∀ t, V (0,t) = g t) ∧
      (∀ x t, t ≤ a → V (x,t) = 0) ∧
      ContDiffOn ℝ ∞ V {z | 0 < z.1} ∧
      ∀ x, 0 < x → ∀ t, deriv (fun s => V (x,s)) t =
        (1/2)*deriv (deriv (fun y => V (y,t))) x := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hg
  exact ⟨fun z => heatBoundaryExtension g z.1 z.2,
    heatBoundaryExtension_continuous hg hC,heatBoundaryExtension_boundary g,
    fun x _ ht => heatBoundaryExtension_causal hstart x ht,
    compact_heatBoundaryExtension_smooth hg hc,
    fun _ hx t => compact_heatBoundaryExtension_equation hg hc hx t⟩

end MathFin.BlackScholes.AmericanPut.Stopping
