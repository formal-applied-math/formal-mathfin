/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.CommonAffineStopped

/-!
# Common Affine Transform

The finite-horizon Heston state and its stopped affine identity.

## Main definitions

* `IsHestonState`
* `locTime`

## Main results

* `IsHestonState.stopped`
* `locTime_le`
* `IsHestonState.eventually_locTime`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open MathFin.FilteredIto
namespace CommonAffineTransform

open MeasureTheory ProbabilityTheory Filter Topology Set
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonPredictable
      MathFin.FilteredIto.CommonIntegral
  MathFin.FilteredIto.CommonProcessGeneral MathFin.FilteredIto.CommonContinuous
        MathFin.FilteredIto.CommonStopping
  MathFin.FilteredIto.CommonCovariation MathFin.FilteredIto.CommonRiemann
        MathFin.FilteredIto.CommonIto MathFin.Heston.CommonYamada
  MathFin.FilteredIto.CommonOptional MathFin.Heston.CommonHestonIto MathFin.Heston.CommonAffine
        MathFin.Heston.CommonAffineStopped
open scoped NNReal ENNReal

local notation "leb" => MathFin.ItoIntegralL2.timeMeasure

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℝ≥0 mΩ} {B Z : ℝ≥0 → Ω → ℝ}

/-- A Heston state on `[0, T]` driven by the independent pair `(B, Z)` on the common
filtration: continuous predictable processes solving the Heston system. -/
structure IsHestonState (hP : IndependentPair ℱ B Z μ) (T : ℝ≥0) (p : Parameters)
    (hρ : |p.rho| ≤ 1) (x₀ v₀ : ℝ) (X V : ℝ≥0 → Ω → ℝ) : Prop where
  predX : IsStronglyPredictable ℱ X
  predV : IsStronglyPredictable ℱ V
  contX : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc 0 T)
  contV : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ V t ω) (Set.Icc 0 T)
  nonneg : ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ V t ω
  kernels : ∃ Hv Hx : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ),
    (⇑Hv =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ p.xi * Real.sqrt (V z.1 z.2)) ∧
    (⇑Hx =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ Real.sqrt (V z.1 z.2)) ∧
    (∀ᵐ ω ∂μ, ∀ t ≤ T, V t ω = v₀
      + (∫ s in Set.Ioc 0 t, p.kappa * (p.theta - V s ω) ∂leb)
      + itoContinuousMod T hP.left.measurable Hv t ω) ∧
    (∀ᵐ ω ∂μ, ∀ t ≤ T, X t ω = x₀
      + (∫ s in Set.Ioc 0 t, (p.r - p.q) - (1 / 2 : ℝ) * V s ω ∂leb)
      + itoContinuousMod T (hP.correlated_brownian hρ).measurable Hx t ω)

/-- Heston states exist (non-vacuity), for every horizon. -/
theorem exists_isHestonState (hP : IndependentPair ℱ B Z μ) (T : ℝ≥0)
    (hBc : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (hZc : ∀ ω, Continuous fun t : ℝ≥0 ↦ Z t ω)
    (p : Parameters) (hκ : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta) (hξ : 0 < p.xi)
    (hρ : |p.rho| ≤ 1) (x₀ v₀ : ℝ) (hv₀ : 0 ≤ v₀) :
    ∃ X V : ℝ≥0 → Ω → ℝ, IsHestonState hP T p hρ x₀ v₀ X V := by
  obtain ⟨X, V, _Gx, Hv, Hx, hpX, hpV, hcX, hcV, hnn, _hG, hHv, hHx, heqV, heqX⟩ :=
    MathFin.Heston.CommonState.exists_heston_state hP T hBc hZc p hκ hθ hξ hρ x₀ v₀ hv₀
  exact ⟨X, V, hpX, hpV, hcX, hcV, hnn, Hv, Hx, hHv, hHx, heqV, heqX⟩

variable {hP : IndependentPair ℱ B Z μ} {T : ℝ≥0} {p : Parameters} {hρ : |p.rho| ≤ 1}
  {x₀ v₀ : ℝ} {X V : ℝ≥0 → Ω → ℝ}

/-- The localization times `σₙ` (rational exit times of `|X| + V`, shifted so that the level
exceeds the initial value). -/
def locTime (X V : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N₀ n : ℕ) : Ω → ℝ≥0 :=
  CommonOptional.exitTime T (locFun X V) ((n + N₀ : ℕ) : ℝ)

theorem IsHestonState.stopped (hS : IsHestonState hP T p hρ x₀ v₀ X V)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    (hξ : 0 < p.xi) {u w : ℂ} (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0) (hv₀ : 0 ≤ v₀)
    {N₀ : ℕ} (hN₀ : |x₀| + v₀ < N₀) (n : ℕ) :
    Integrable (fun ω ↦ affST p u w T
      (fun l ↦ hestonY X V l (locTime X V T N₀ n ω) ω)) μ ∧
      ∫ ω, affST p u w T (fun l ↦ hestonY X V l (locTime X V T N₀ n ω) ω) ∂μ
        = affST p u w T (hestonY0 x₀ v₀) := by
  obtain ⟨Hv, Hx, hHv, hHx, heqV, heqX⟩ := hS.kernels
  have hn : |x₀| + v₀ < ((n + N₀ : ℕ) : ℝ) := by
    push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact stopped_affine hP hBc hZc p hξ hρ hu hw hv₀ hS.predX hS.predV hS.contX hS.contV
    hS.nonneg hHv hHx heqV heqX hn

omit mΩ in
lemma locTime_le (N₀ n : ℕ) (ω : Ω) : locTime X V T N₀ n ω ≤ T := exitTime_le _ _ _ _

/-- Almost surely the localization times are eventually equal to `T`. -/
theorem IsHestonState.eventually_locTime (hS : IsHestonState hP T p hρ x₀ v₀ X V) (N₀ : ℕ) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, locTime X V T N₀ n ω = T := by
  filter_upwards [hS.contX, hS.contV] with ω hx hv
  have hgc : ContinuousOn (fun t ↦ locFun X V t ω) (Set.Icc 0 T) :=
    (continuous_abs.comp_continuousOn hx).add hv
  have h := eventually_exitTime_eq hgc
  have h' := (tendsto_add_atTop_nat N₀).eventually h
  filter_upwards [h'] with n hn
  simpa [locTime] using hn


end CommonAffineTransform
end MathFin.Heston
