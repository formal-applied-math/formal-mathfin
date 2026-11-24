/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.CommonAffineTransform
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import MathFin.Models.StochVol.Heston.RiccatiIdentification
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Log Spot Characteristic

## Main results

* `IsHestonState.charFun_logSpot`
* `exists_hestonState_charFun`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.Heston.CommonAffineTransform
open MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open MathFin.Heston.CommonAffineStopped
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonStopping
      MathFin.Heston.CommonHestonIto MathFin.Heston.CommonAffine
open scoped NNReal

/-- The unconditional characteristic function of terminal log-spot for an actual
Heston state driven by a prescribed independent Brownian pair. -/
theorem IsHestonState.charFun_logSpot
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 mΩ} {B Z : ℝ≥0 → Ω → ℝ} {hP : IndependentPair ℱ B Z μ}
    {T : ℝ≥0} {p : Parameters} {hρ : |p.rho| ≤ 1} {x₀ v₀ : ℝ} {X V : ℝ≥0 → Ω → ℝ}
    (hS : IsHestonState hP T p hρ x₀ v₀ X V)
    (hBc : ∀ ω, Continuous (fun s ↦ B s ω)) (hZc : ∀ ω, Continuous (fun s ↦ Z s ω))
    (hξ : 0 < p.xi) (hκ : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta) (hv : 0 ≤ v₀) (k : ℝ) :
    charFun (μ.map (X T)) k = globalAffineTransform p (Complex.I * k) 0 x₀ v₀ T := by
  have hm : Measurable (X T) :=
    ((MathFin.Heston.CommonYamada.contProcess_of_predictable hS.predX hS.contX).adapted T).mono
          (ℱ.le T) le_rfl
  have hf : Continuous (fun x : ℝ ↦ Complex.exp ((k : ℂ) * x * Complex.I)) := by fun_prop
  rw [charFun_apply_real, integral_map hm.aemeasurable hf.aestronglyMeasurable]
  let u : ℂ := Complex.I * k
  have hu : u.re = 0 := by simp [u, Complex.mul_re]
  have hs : inClosedLaplaceStrip u := ⟨hu.ge, hu.le.trans zero_le_one⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (|x₀| + v₀)
  let F (n : ℕ) (ω : Ω) := affST p u 0 T
    (fun l ↦ hestonY X V l (locTime X V T N n ω) ω)
  have hstop := hS.stopped hBc hZc hξ hs (w := 0) (by simp) hv hN
  have hbd (n : ℕ) : ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ 1 := by
    filter_upwards [hS.nonneg] with ω hnn
    have ht := locTime_le (X := X) (V := V) (T := T) N n ω
    exact globalAffineTransform_norm_le_one p u 0 hξ hρ hu (by simp) hκ hθ _ _ _
      (hnn _ ht) (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht))
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ F n ω) atTop
      (𝓝 (Complex.exp (u * (X T ω : ℂ)))) := by
    filter_upwards [hS.eventually_locTime N] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    change _ = globalAffineTransform p u 0 _ _ ((T : ℝ) - (locTime X V T N n ω : ℝ))
    simp [hn, hestonY, globalAffineTransform_initial]
  have hconv := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ ↦ (1 : ℝ))
    (fun n ↦ (hstop n).1.aestronglyMeasurable) (integrable_const _) hbd hlim
  have e (n : ℕ) : ∫ ω, F n ω ∂μ = affST p u 0 T (hestonY0 x₀ v₀) := (hstop n).2
  change Tendsto (fun n ↦ ∫ ω, F n ω ∂μ) _ _ at hconv
  simp only [e] at hconv
  have he := (tendsto_nhds_unique hconv tendsto_const_nhds)
  simpa [affST, hestonY0, u, mul_comm, mul_left_comm, mul_assoc] using he

/-- Construct the state and identify its terminal log-spot law for every real frequency. -/
theorem exists_hestonState_charFun
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 mΩ} {B Z : ℝ≥0 → Ω → ℝ} (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous (fun s ↦ B s ω)) (hZc : ∀ ω, Continuous (fun s ↦ Z s ω))
    (T : ℝ≥0) (p : Parameters) (hκ : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta) (hξ : 0 < p.xi)
    (hρ : |p.rho| ≤ 1) (x₀ v₀ : ℝ) (hv : 0 ≤ v₀) :
    ∃ X V : ℝ≥0 → Ω → ℝ, IsHestonState hP T p hρ x₀ v₀ X V ∧
      ∀ k : ℝ, charFun (μ.map (X T)) k = globalAffineTransform p (Complex.I * k) 0 x₀ v₀ T := by
  obtain ⟨X, V, hS⟩ := exists_isHestonState hP T hBc hZc p hκ hθ hξ hρ x₀ v₀ hv
  exact ⟨X, V, hS, fun k ↦ hS.charFun_logSpot hBc hZc hξ hκ hθ hv k⟩

end MathFin.Heston.CommonAffineTransform
