/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.HeatPricingTransform

/-! # Constructed fixed-interval pricing-equation boundary correction 
## Result

Public entry points include `pricingGauge_ne_zero`, `heatBoundaryDatum`,
`heatBoundaryDatum_continuous`, `heatBoundaryDatum_zero`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped Topology ContDiff

theorem pricingGauge_ne_zero (k h L a x t : ℝ) : pricingGauge k h L a x t ≠ 0 :=
  Real.exp_ne_zero _

/-- The boundary datum `g` at time `a+s/2`, divided by the gauge
`pricingGauge k h L a X (a+s/2)`: the datum read in the heat time `s = 2*(t-a)`. -/
noncomputable def heatBoundaryDatum (g : ℝ → ℝ) (k h L a X s : ℝ) : ℝ :=
  g (a+s/2)/pricingGauge k h L a X (a+s/2)

theorem heatBoundaryDatum_continuous {g : ℝ → ℝ} (hg : Continuous g) (k h L a X : ℝ) :
    Continuous (heatBoundaryDatum g k h L a X) := by
  unfold heatBoundaryDatum pricingGauge
  fun_prop (disch := simp [Real.exp_ne_zero])

theorem heatBoundaryDatum_zero {g : ℝ → ℝ} {a : ℝ}
    (hs : ∀ t, t ≤ a → g t = 0) (k h L X : ℝ) {s : ℝ} (ht : s ≤ 0) :
    heatBoundaryDatum g k h L a X s = 0 := by
  unfold heatBoundaryDatum
  rw [hs _ (by linarith),zero_div]

theorem heatBoundaryDatum_rescale (g : ℝ → ℝ) (k h L a X t : ℝ) :
    heatBoundaryDatum g k h L a X (2*(t-a)) = g t/pricingGauge k h L a X t := by
  unfold heatBoundaryDatum
  rw [show a+2*(t-a)/2 = t by ring]

theorem exists_interval_pricing_boundary_solution {g₀ g₁ : ℝ → ℝ}
    (h₀ : Continuous g₀) (h₁ : Continuous g₁) {a L R : ℝ}
    (hLR : L < R) (hs₀ : ∀ t, t ≤ a → g₀ t = 0) (hs₁ : ∀ t, t ≤ a → g₁ t = 0)
    (k h T : ℝ) :
    ∃ C : ℝ × ℝ → ℝ, Continuous C ∧
      (∀ x t, t ≤ a → C (x,t) = 0) ∧
      (∀ t ∈ Icc a T, C (L,t) = g₀ t) ∧
      (∀ t ∈ Icc a T, C (R,t) = g₁ t) ∧
      ContDiffOn ℝ ∞ C {z | L < z.1 ∧ z.1 < R} ∧
      ∀ z, L < z.1 → z.1 < R → pricingOperator k h C z = 0 := by
  obtain ⟨V,hV,hstart,hleft,hright,hsmooth,hpde⟩ :=
    exists_interval_heat_boundary_solution_continuous
      (heatBoundaryDatum_continuous h₀ k h L a L) (heatBoundaryDatum_continuous h₁ k h L a R)
      (sub_pos.mpr hLR)
      (fun s hs => heatBoundaryDatum_zero hs₀ k h L L hs)
      (fun s hs => heatBoundaryDatum_zero hs₁ k h L R hs) (2*(T-a))
  have hVs : ∀ x t, L < x → x < R → ContDiffAt ℝ ∞ V (x-L,2*(t-a)) := by
    intro x t hx hxR
    apply hsmooth.contDiffAt
    apply ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)).mem_nhds
    constructor <;> dsimp <;> linarith
  refine ⟨priceFromHeat V k h L a,priceFromHeat_continuous hV k h L a,?_,?_,?_,?_,?_⟩
  · intro x t ht
    unfold priceFromHeat
    rw [hstart _ _ (by linarith),mul_zero]
  · intro t ht
    have hs : 2*(t-a) ∈ Icc 0 (2*(T-a)) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    simp only [priceFromHeat,sub_self,hleft _ hs,heatBoundaryDatum_rescale]
    field_simp [pricingGauge_ne_zero]
  · intro t ht
    have hs : 2*(t-a) ∈ Icc 0 (2*(T-a)) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    simp only [priceFromHeat,hright _ hs,heatBoundaryDatum_rescale]
    field_simp [pricingGauge_ne_zero]
  · intro z hz
    exact (priceFromHeat_smoothAt (hVs z.1 z.2 hz.1 hz.2)).contDiffWithinAt
  · intro z hx hxR
    rw [priceFromHeat_pricingOperator ((hVs z.1 z.2 hx hxR).of_le (WithTop.coe_le_coe.mpr le_top)),
      hpde (z.1-L) (by linarith) (by linarith) (2*(z.2-a))]
    ring

end MathFin.BlackScholes.AmericanPut.Stopping
