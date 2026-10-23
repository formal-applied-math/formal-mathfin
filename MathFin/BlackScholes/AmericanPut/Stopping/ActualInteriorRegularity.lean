/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.PricingDirichlet

/-! # Interior regularity and PDE of the actual American stopping price

Local Dirichlet solutions are constructed from continuous price data and then
identified by comparison. No classical solution or price derivative is assumed.
This does not establish smooth fit or free-boundary regularity.

## Result

Public entry points include `exists_canonicalContinuation_cylinder`,
`canonicalPrice_locally_eq_smooth_solution`, `canonicalPrice_contDiffAt`,
`canonicalPrice_contDiffOn`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem exists_canonicalContinuation_cylinder {k h : ℝ} (hk : 0 ≤ k) {z : ℝ × ℝ}
    (hz : z ∈ canonicalContinuationRegion k h) :
    ∃ L R a T : ℝ, z ∈ Ioo L R ×ˢ Ioo a T ∧
      Ioo L R ×ˢ Ioo a T ⊆ canonicalContinuationRegion k h := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (canonicalContinuationRegion_isOpen hk) z hz
  refine ⟨z.1-ε/2,z.1+ε/2,z.2-ε/2,z.2+ε/2,?_,?_⟩
  · constructor <;> constructor <;> linarith
  · intro y hy
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    apply max_lt
    · apply (abs_lt.mpr ⟨?_,?_⟩ : |y.1-z.1| < ε/2).trans (half_lt_self hε)
      · linarith [hy.1.1]
      · linarith [hy.1.2]
    · apply (abs_lt.mpr ⟨?_,?_⟩ : |y.2-z.2| < ε/2).trans (half_lt_self hε)
      · linarith [hy.2.1]
      · linarith [hy.2.2]

theorem canonicalPrice_locally_eq_smooth_solution {k h : ℝ} (hk : 0 ≤ k) {z : ℝ × ℝ}
    (hz : z ∈ canonicalContinuationRegion k h) :
    ∃ F : ℝ × ℝ → ℝ, ContDiffAt ℝ ∞ F z ∧ pricingOperator k h F z = 0 ∧
      (fun w : ℝ × ℝ => canonicalPrice k h w.1 w.2) =ᶠ[𝓝 z] F := by
  obtain ⟨L,R,a,T,hzQ,hQ⟩ := exists_canonicalContinuation_cylinder hk hz
  obtain ⟨F,hF,hbottom,hleft,hright,hFs,hpde⟩ :=
    exists_pricing_dirichlet_solution (canonicalPrice_continuous hk)
      (hzQ.1.1.trans hzQ.1.2) k h a T
  have he := canonicalPrice_eq_smooth_on_cylinder hk (hzQ.2.1.trans hzQ.2.2) hQ hF.continuousOn
    (hFs.of_le (WithTop.coe_le_coe.mpr le_top)) hpde hbottom hleft hright
  have hnear : Ioo L R ×ˢ Ioo a T ∈ 𝓝 z := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds hzQ
  refine ⟨F,hFs.contDiffAt hnear,hpde z hzQ,?_⟩
  filter_upwards [hnear] with w hw
  exact he w ⟨⟨hw.1.1.le,hw.1.2.le⟩,hw.2.1.le,hw.2.2.le⟩

theorem canonicalPrice_contDiffAt {k h : ℝ} (hk : 0 ≤ k) {z : ℝ × ℝ}
    (hz : z ∈ canonicalContinuationRegion k h) :
    ContDiffAt ℝ ∞ (fun w : ℝ × ℝ => canonicalPrice k h w.1 w.2) z := by
  obtain ⟨F,hF,_hpde,he⟩ := canonicalPrice_locally_eq_smooth_solution hk hz
  exact hF.congr_of_eventuallyEq he

theorem canonicalPrice_contDiffOn {k h : ℝ} (hk : 0 ≤ k) :
    ContDiffOn ℝ ∞ (fun w : ℝ × ℝ => canonicalPrice k h w.1 w.2)
      (canonicalContinuationRegion k h) :=
  fun _ hz => (canonicalPrice_contDiffAt hk hz).contDiffWithinAt

theorem canonicalPrice_pricingOperator {k h : ℝ} (hk : 0 ≤ k) {z : ℝ × ℝ}
    (hz : z ∈ canonicalContinuationRegion k h) :
    pricingOperator k h (fun w => canonicalPrice k h w.1 w.2) z = 0 := by
  obtain ⟨F,_hF,hpde,he⟩ := canonicalPrice_locally_eq_smooth_solution hk hz
  have ht : (fun t => canonicalPrice k h z.1 t) =ᶠ[𝓝 z.2] (fun t => F (z.1,t)) := by
    simpa only [Function.comp_def] using
      he.comp_tendsto (show Tendsto (fun t : ℝ => (z.1,t)) (𝓝 z.2) (𝓝 z) by
        convert! (continuous_const.prodMk continuous_id).tendsto z.2 using 1)
  have hx : (fun x => canonicalPrice k h x z.2) =ᶠ[𝓝 z.1] (fun x => F (x,z.2)) := by
    simpa only [Function.comp_def] using
      he.comp_tendsto (show Tendsto (fun x : ℝ => (x,z.2)) (𝓝 z.1) (𝓝 z) by
        convert! (continuous_id.prodMk continuous_const).tendsto z.1 using 1)
  unfold pricingOperator at hpde ⊢
  simpa only [ht.deriv_eq,hx.deriv.deriv_eq,hx.deriv_eq,he.self_of_nhds] using hpde

theorem canonicalPrice_continuation_pde {k h x t : ℝ} (hk : 0 ≤ k)
    (hz : (x, t) ∈ canonicalContinuationRegion k h) :
    deriv (fun s => canonicalPrice k h x s) t =
      deriv (deriv (fun y => canonicalPrice k h y t)) x +
        (k-h-1) * deriv (fun y => canonicalPrice k h y t) x -
        k * canonicalPrice k h x t := by
  have hpde := canonicalPrice_pricingOperator hk hz
  unfold pricingOperator at hpde
  dsimp only at hpde
  linarith

end MathFin.BlackScholes.AmericanPut.Stopping
