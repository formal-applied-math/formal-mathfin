/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.AdaptedQuadraticVariation
public import MathFin.Probability.Brownian.AdaptedRiemannStieltjes
public import MathFin.Probability.Brownian.Ito.AdaptedDrift
public import MathFin.Probability.Brownian.Ito.ItoProcessPredictable

/-! # The Itô process with adapted coefficients, and the convergences behind its Itô formula

Let `B` be a Brownian motion every path of which is continuous, and let `σ` and `b` be bounded
processes, adapted to the natural filtration of `B`, every path of which is continuous. Fix a
horizon `T` and a deterministic starting point `x₀`, and let

`X_t = x₀ + ∫₀ᵗ b_s ds + ∫₀ᵗ σ_s dB_s`

(`adaptedItoProcess`: the pathwise drift integral plus the continuous modification of the
stochastic integral). This module builds the process; the three convergences in measure that
Itô's formula for it is assembled from live beside their ingredients (below); the formula is in
`ItoFormulaAdaptedTD` (`ito_formula_adapted`, `ito_formula_adapted_td_against`), where the
one-variable `f(x)` is the case `f_t = 0` of `f(t, x)`.

`X` is a functional of the path of `B`, not a function of `(t, B_t)`, so the formula does not
reduce to the one for functions of Brownian motion. The classical proof splits `f(X_T) − f(X_0)`
on the uniform partition of `[0, T]` by the discrete formula into sums that converge:

* `∑ f'(X_{tₖ}) ΔAₖ → ∫ f'(X) b ds` on every path where `X` is continuous
  (`tendsto_sum_mul_driftPath_sub`);
* `∑ f'(X_{tₖ}) ΔMₖ → ∫ f'(X) dM` in measure
  (`AdaptedRiemannStieltjes.tendstoInMeasure_riemannStieltjes`, from the mean-square convergence
  `tendsto_itoIntegralAgainst_stepσ`);
* `∑ f''(X_{tₖ}) (ΔXₖ)² → ∫ f''(X) σ² ds` in measure
  (`AdaptedQuadraticVariation.tendstoInMeasure_weighted_qv_adapted`, from the `L¹` convergence
  `tendsto_weighted_qv_adapted`);
* the Taylor remainders, which are controlled by the modulus of continuity of the second
  derivative on the range of the path (`abs_discreteTaylorRemainder_le_of_abs_sub_le`) and the
  uniform smallness of the increments of a continuous path
  (`eventually_abs_sub_unifPart_lt`).

The limits in measure hold almost surely along a common subsequence of partitions.

## Main definitions

* `adaptedItoProcess`: the Itô process `X_t = x₀ + ∫₀ᵗ b ds + ∫₀ᵗ φ dB`, the pathwise drift
  integral plus the continuous modification, at horizon `T`, of the stochastic integral.

## Main results

* `adaptedItoProcess_ae_eq`: for `t ≤ T`, the process equals `x₀ + driftPath b t` plus the Itô
  integral `itoProcessCLM`, almost surely.
* `ae_continuousOn_adaptedItoProcess`: almost every path is continuous on `[0, T]`.
* `adaptedItoProcess_isStronglyPredictable`: the process is predictable for the natural
  filtration of `B`.

## Tags

Itô formula, Itô process, adapted coefficients, Riemann–Stieltjes sums, convergence in measure,
stochastic integral, MSC 60H05, MSC 60H10, MSC 60J60
-/

@[expose] public section

namespace MathFin
namespace ItoFormulaAdapted

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralRiemannBridge
  ItoIntegralBrownian QuadraticVariationL2 ItoIntegralProcessContinuousModification
  AdaptedDrift AdaptedQuadraticVariation AdaptedRiemannStieltjes
  PredictableDensityGeneral StochasticIntegralCharacterisation LpMulIsometry
  AdaptedStochasticIntegralFreezing ItoIntegralAgainstMartingale
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
  {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C)

/-! ### The process -/

variable (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {b : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) {Cb : ℝ} (hb_bdd : ∀ s ω, |b s ω| ≤ Cb) (x₀ : ℝ)

/-- **The Itô process** `X_t = x₀ + ∫₀ᵗ b ds + ∫₀ᵗ φ dB` with drift rate `b` and integrand
class `φ`: the pathwise drift integral plus the continuous modification, at horizon `T`, of the
stochastic integral. It is meant for `t ≤ T`. For a Brownian motion with continuous paths and a
bounded rate with continuous paths, almost every path is continuous on `[0, T]`
(`ae_continuousOn_adaptedItoProcess`). -/
noncomputable def adaptedItoProcess (b : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x₀ + driftPath b t ω + itoContinuousMod T hBmeas φ t ω

include hBcont in
/-- At each time up to `T` the process is `x₀` plus the drift plus the Itô integral, almost
surely. -/
theorem adaptedItoProcess_ae_eq {t : ℝ≥0} (ht : t ≤ T) :
    adaptedItoProcess T hBmeas φ x₀ b t =ᵐ[μ] fun ω ↦ x₀ + driftPath b t ω
      + itoProcessCLM hB T t hBmeas φ ω :=
  (itoContinuousMod_modification hB T hBmeas hBcont φ ht).mono fun ω h ↦
    congrArg (x₀ + driftPath b t ω + ·) h

include hB hBcont in
/-- The process starts at `x₀`, almost surely. -/
theorem adaptedItoProcess_zero : adaptedItoProcess T hBmeas φ x₀ b 0 =ᵐ[μ] fun _ ↦ x₀ := by
  filter_upwards [adaptedItoProcess_ae_eq hB T hBmeas hBcont φ x₀ (b := b) zero_le,
    Lp.coeFn_zero ℝ 2 μ] with ω h h0
  rw [h, itoProcessCLM_zero_time, h0]
  simp [driftPath]

include hB hBcont hb_cont hb_bdd in
/-- Almost every path of the process is continuous on `[0, T]`. -/
theorem ae_continuousOn_adaptedItoProcess :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ adaptedItoProcess T hBmeas φ x₀ b t ω) (Icc 0 T) :=
  (itoContinuousMod_continuousOn hB T hBmeas hBcont φ).mono fun ω h ↦
    (continuous_const.add (continuous_driftPath hb_cont hb_bdd ω)).continuousOn.add h

include hB hBcont hb_adap hb_cont hb_bdd in
/-- The process is predictable for the natural filtration of `B`. -/
theorem adaptedItoProcess_isStronglyPredictable :
    IsStronglyPredictable (natFiltration hBmeas) (adaptedItoProcess T hBmeas φ x₀ b) :=
  StronglyMeasurable.add (stronglyMeasurable_const.add
      (driftPath_isStronglyPredictable hBmeas hb_adap hb_cont hb_bdd))
    (itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ)

include hB hBcont hb_adap hb_cont hb_bdd in
/-- A continuous function of the process is predictable. -/
theorem comp_adaptedItoProcess_isStronglyPredictable {g : ℝ → ℝ} (hg : Continuous g) :
    IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ g (adaptedItoProcess T hBmeas φ x₀ b s ω) :=
  hg.comp_stronglyMeasurable
    (adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hb_adap hb_cont hb_bdd x₀)

include hB hBcont hadap hcont hb_adap hb_cont hb_bdd in
/-- A continuous function of the process, times an adapted process with continuous paths, is
predictable. -/
theorem comp_adaptedItoProcess_mul_isStronglyPredictable {g : ℝ → ℝ} (hg : Continuous g) :
    IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ g (adaptedItoProcess T hBmeas φ x₀ b s ω) * σ s ω :=
  StronglyMeasurable.mul (comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ
      hb_adap hb_cont hb_bdd x₀ hg)
    (StronglyAdapted.isStronglyPredictable_of_leftContinuous hadap
      fun ω _ ↦ (hcont ω).continuousWithinAt)

omit mΩ in
/-- A product of functions bounded by `C₁` and `C` is bounded by `C₁ C`. -/
theorem abs_comp_mul_le {g : ℝ → ℝ} {C₁ C : ℝ} (hg : ∀ x, |g x| ≤ C₁) {σ : ℝ≥0 → Ω → ℝ}
    (hbdd : ∀ t ω, |σ t ω| ≤ C) (X : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) :
    |g (X s ω) * σ s ω| ≤ C₁ * C :=
  (abs_mul _ _).trans_le
    (mul_le_mul (hg _) (hbdd s ω) (abs_nonneg _) ((abs_nonneg _).trans (hg 0)))

end ItoFormulaAdapted
end MathFin
