/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.CIRRegularity
public import MathFin.Models.StochVol.Heston.CIRApproximation
public import MathFin.Probability.Brownian.Ito.Filtered.LipschitzSDE

/-!
# CIRRegularized

Genuine finite-horizon approximants for CIR. The horizon is strictly
positive and chosen in the Picard contraction regime. No assertion about the
unregularized square-root limit or all finite horizons is made here.

## Main definitions

* `cirRegularizedDiffusion`

## Main results

* `lipschitzWith_cirRegularizedDiffusion`
* `exists_small_sde_horizon`
* `exists_cir_regularized_on_small_horizon`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM
open MathFin.ItoIntegralProcessContinuousModification

/-- CIR volatility with the square-root coefficient regularized at scale ε. -/
def cirRegularizedDiffusion (p : Parameters) (ε x : Real) : Real :=
  p.xi * cirApproxDiff ε x

theorem lipschitzWith_cirDrift (p : Parameters) :
    LipschitzWith ‖p.kappa‖₊ (cirDrift p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, cirDrift]
  have he : p.kappa * (p.theta - x) - p.kappa * (p.theta - y) =
      p.kappa * (-(x - y)) := by ring
  rw [he, abs_mul, abs_neg]

theorem lipschitzWith_cirRegularizedDiffusion (p : Parameters) {ε : Real} (hε : 0 < ε) :
    LipschitzWith (‖p.xi‖₊ * Real.toNNReal (1 / (2 * Real.sqrt ε)))
      (cirRegularizedDiffusion p ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (lipschitzWith_cirApproxDiff hε).dist_le_mul x y
  simp only [Real.dist_eq] at h
  simp only [Real.dist_eq, cirRegularizedDiffusion, ← mul_sub, abs_mul,
    NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
  calc |p.xi| * |cirApproxDiff ε x - cirApproxDiff ε y|
      ≤ |p.xi| * ((Real.toNNReal (1 / (2 * Real.sqrt ε)) : Real) * |x - y|) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

theorem exists_small_sde_horizon (Lb Lσ : ℝ≥0) :
    ∃ T : ℝ≥0, 0 < T ∧ (T : Real) * Lb + Real.sqrt (T : Real) * Lσ < 1 := by
  have hc : Continuous (fun t : ℝ≥0 => (t : Real) * Lb + Real.sqrt (t : Real) * Lσ) := by
    fun_prop
  have he : ∀ᶠ t : ℝ≥0 in 𝓝 0, (t : Real) * Lb + Real.sqrt (t : Real) * Lσ < 1 :=
    (hc.tendsto 0).eventually_lt_const (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  let T : ℝ≥0 := ⟨δ / 2, (half_pos hδ).le⟩
  refine ⟨T, by exact_mod_cast half_pos hδ, hball ?_⟩
  change dist T 0 < δ
  change |δ / 2 - 0| < δ
  simpa only [sub_zero, abs_of_nonneg (half_pos hδ).le] using half_lt_self hδ

/-- A nonzero time horizon and a continuous adapted solution of the regularized
CIR equation are produced on the supplied Brownian space. The diffusion is the
actual Itô integral of `ξ g_ε(X)` in its predictable L² class. -/
theorem exists_cir_regularized_on_small_horizon
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → Real} (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (p : Parameters) {ε : Real} (hε : 0 < ε) (v₀ : Real) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ (V : ℝ≥0 → Ω → Real)
        (H : Lp Real 2 (trimMeasure (μ := μ) T hBmeas)),
      IsStronglyPredictable (natFiltration hBmeas) V ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Set.Icc 0 T)) ∧
      MemLp (Function.uncurry V) 2 (trimMeasure (μ := μ) T hBmeas) ∧
      (⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => cirRegularizedDiffusion p ε (V z.1 z.2)) ∧
      (∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ T →
        V t ω = v₀ + (∫ s in Set.Ioc 0 t, cirDrift p (V s ω) ∂timeMeasure)
          + itoContinuousMod T hBmeas H t ω) := by
  obtain ⟨T, hT, hsmall⟩ := exists_small_sde_horizon ‖p.kappa‖₊
    (‖p.xi‖₊ * Real.toNNReal (1 / (2 * Real.sqrt ε)))
  exact ⟨T, hT, exists_continuous_lipschitz_sde_on_small_horizon hB T hBmeas hBcont
    (lipschitzWith_cirDrift p) (lipschitzWith_cirRegularizedDiffusion p hε) v₀ hsmall⟩

end MathFin.Heston
