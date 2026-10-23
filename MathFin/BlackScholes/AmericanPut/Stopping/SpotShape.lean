/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.AmericanValue

/-!
# Spot monotonicity and convexity of the actual stopping value

For each stopping rule the discounted put payoff is decreasing and convex in
initial spot. Integration and the supremum preserve these properties. These
results concern price shape in spot, not exercise-boundary curvature in time.

## Result

Public entry points include `putReward_antitone`, `putReward_convex`, `value_antitone_spot`,
`value_convexOn_spot`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open scoped NNReal

variable {Ω : Type*}

theorem putReward_antitone (W : ℝ≥0 → Ω → ℝ) (K r q σ : ℝ) (θ : Ω → ℝ≥0) (ω : Ω) :
    Antitone (fun S => putReward W K r q σ S θ ω) := by
  intro x y hxy
  exact mul_le_mul_of_nonneg_left
    (max_le_max (sub_le_sub_left (mul_le_mul_of_nonneg_right hxy (Real.exp_pos _).le) K) le_rfl)
    (Real.exp_pos _).le

theorem putReward_convex (W : ℝ≥0 → Ω → ℝ) (K r q σ : ℝ) (θ : Ω → ℝ≥0) (ω : Ω)
    (x y : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    putReward W K r q σ (a*x+b*y) θ ω ≤
      a*putReward W K r q σ x θ ω+b*putReward W K r q σ y θ ω := by
  let G := Real.exp (((r-q)-σ^2/2)*(θ ω : ℝ)+σ*W (θ ω) ω)
  let d := Real.exp (-r*(θ ω : ℝ))
  have hd : 0 ≤ d := (Real.exp_pos _).le
  have hmix : a*(K-x*G)+b*(K-y*G) = K-(a*x+b*y)*G := by
    have hh := congrArg (fun z : ℝ => z*K) hab
    nlinarith
  have hmax : max (K-(a*x+b*y)*G) 0 ≤ a*max (K-x*G) 0+b*max (K-y*G) 0 := by
    apply max_le
    · rw [← hmix]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  change d*max (K-(a*x+b*y)*G) 0 ≤ a*(d*max (K-x*G) 0)+b*(d*max (K-y*G) 0)
  calc
    _ ≤ d*(a*max (K-x*G) 0+b*max (K-y*G) 0) := mul_le_mul_of_nonneg_left hmax hd
    _ = _ := by ring

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
  {K r q σ : ℝ} {T : ℝ≥0}

theorem value_antitone_spot (hW : Measurable W.uncurry) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    AntitoneOn (fun S => americanPutValue P 𝓕 W K r q σ S T) (Ici 0) := by
  intro x hx y hy hxy
  apply csSup_le exerciseValues_nonempty
  rintro _ ⟨θ,rfl⟩
  exact (integral_mono (putReward_integrable hW P hK hr hy θ.measurable_time)
    (putReward_integrable hW P hK hr hx θ.measurable_time)
    (fun ω => putReward_antitone W K r q σ θ.time ω hxy)).trans
      (expectedReward_le_value hW hK hr hx θ)

theorem value_convexOn_spot (hW : Measurable W.uncurry) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    ConvexOn ℝ (Ici 0) (fun S => americanPutValue P 𝓕 W K r q σ S T) := by
  refine ⟨convex_Ici 0,?_⟩
  intro x hx y hy a b ha hb hab
  change americanPutValue P 𝓕 W K r q σ (a*x+b*y) T ≤
    a*americanPutValue P 𝓕 W K r q σ x T+b*americanPutValue P 𝓕 W K r q σ y T
  apply csSup_le exerciseValues_nonempty
  rintro _ ⟨θ,rfl⟩
  have hix := putReward_integrable (q := q) (σ := σ) hW P hK hr hx θ.measurable_time
  have hiy := putReward_integrable (q := q) (σ := σ) hW P hK hr hy θ.measurable_time
  have himix := putReward_integrable (q := q) (σ := σ) hW P hK hr
    (add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)) θ.measurable_time
  calc
    _ ≤ ∫ ω, a*putReward W K r q σ x θ.time ω+b*putReward W K r q σ y θ.time ω ∂P :=
      integral_mono himix ((hix.const_mul a).add (hiy.const_mul b))
        (fun ω => putReward_convex W K r q σ θ.time ω x y ha hb hab)
    _ = a*(∫ ω, putReward W K r q σ x θ.time ω ∂P)+
        b*(∫ ω, putReward W K r q σ y θ.time ω ∂P) := by
      rw [integral_add (hix.const_mul a) (hiy.const_mul b),integral_const_mul,integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (expectedReward_le_value hW hK hr hx θ) ha)
      (mul_le_mul_of_nonneg_left (expectedReward_le_value hW hK hr hy θ) hb)

end MathFin.BlackScholes.AmericanPut.Stopping
