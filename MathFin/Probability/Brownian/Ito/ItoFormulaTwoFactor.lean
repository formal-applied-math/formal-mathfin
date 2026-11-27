/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.Ito.ItoFormulaTwoFactorTaylor
public import MathFin.Probability.Brownian.Ito.ItoProductRule

/-! # Itô's formula for `f(t, X_t, Y_t)` along two Itô processes driven by one Brownian motion

Let `B` be a Brownian motion with continuous paths, `σ`, `τ`, `b`, `c` bounded, adapted to its
natural filtration, with every path continuous, `X = x₀ + ∫ b ds + σ●B` and
`Y = y₀ + ∫ c ds + τ●B` (`adaptedItoProcess`, both at horizon `T`, both driven by the *same* `B`).
For `f(t, x, y)` with partial derivatives `f_t`, `f_x`, `f_y`, `f_xx`, `f_xy = ∂_y f_x`, `f_yy`,
jointly continuous and bounded, almost surely

`f(T, X_T, Y_T) − f(0, x₀, y₀) = ∫ f_x(·, X, Y) dM^σ + ∫ f_y(·, X, Y) dM^τ
  + ∫₀ᵀ (f_t + f_x b + f_y c + ½ f_xx σ² + f_xy σ τ + ½ f_yy τ²)(s, X_s, Y_s) ds`

(`ito_formula_adapted_two_factor_against`), where `M^σ = σ●B`, `M^τ = τ●B` and `∫ w dM` is the
integral against `M` of a bounded predictable weight (`itoIntegralAgainstCLM`, `weightLp`). The
cross term `f_xy σ τ` is the quadratic covariation `d⟨X, Y⟩ = σ τ dt` of the two martingale parts,
*derived*, not assumed.

The proof follows `ito_formula_adapted_td_against`. Along the uniform partitions the discrete
formula `discrete_ito_formula_3d` splits the increment of `f(t, X_t, Y_t)` into `∑ f_t Δt`,
`∑ f_x ΔX`, `∑ f_y ΔY`, the second-order sums and remainders that vanish pathwise
(`ito_formula_3d_of_tendsto`, in `ItoFormulaTwoFactorTaylor`). The drift and time sums converge
pathwise. The martingale sums `∑ f_x(tₖ, Xₖ, Yₖ) ΔM^σ_k` and `∑ f_y ΔM^τ_k` converge in probability
to the integrals against `M^σ` and `M^τ` (`tendstoInMeasure_riemannStieltjes`). The weighted
quadratic variations `∑ w ΔX²`, `∑ w ΔY²` converge in probability by
`tendstoInMeasure_weighted_qv_adapted`, and the cross sum `∑ w ΔX ΔY` by polarisation: with
`Z = X + Y`, which is the Itô process of the coefficients `σ + τ`, `b + c`
(`processToLp_add`), `ΔX ΔY = ½ (ΔZ² − ΔX² − ΔY²)`. Convergence in probability of finitely many
sequences yields one subsequence along which all converge almost surely
(`tendstoInMeasure_prodMk`), and along it the pathwise formula applies.

This file is the bounded case: `σ`, `τ`, `b`, `c` and the partials of `f` bounded, at the single
time `T`, the stochastic integrals taken against `M^σ`, `M^τ`. The formula without a bound on `f`
is `ito_formula_adapted_two_factor_local` (`ItoFormulaTwoFactorLocal`), and the formula with
unbounded coefficients, as an identity of processes at every `t ≤ T`, is
`ito_formula_adapted_two_factor_process` (`ItoFormulaTwoFactorUnbounded`). Two *independent*
Brownian motions are not covered (neither this library nor BrownianMotion at the pinned version
defines a multi-dimensional Brownian motion); `d⟨X, Y⟩ = σ τ dt` here holds because both martingale
parts are integrals against the same `B`.

## Main results

* `ito_formula_adapted_two_factor_against`: the identity above, for `f` with bounded jointly
  continuous partials.
* `processToLp_add`: the `L²` class of a sum of integrands is the sum of the classes.
* `tendstoInMeasure_prodMk`, `tendstoInMeasure_neg`: convergence in measure of pairs and of
  negatives.
* `integral_two_factor_drift`: the real identity that assembles the drift integrals and the
  polarised covariation integral.
* `ito2Drift`: the drift `f_t + f_x b + f_y c + ½ f_xx σ² + f_xy σ τ + ½ f_yy τ²` of
  `f(t, X_t, Y_t)`.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  Theorem 3.3.6
* [Revuz and Yor, *Continuous Martingales and Brownian Motion*][RevuzYor], Theorem IV.3.3

## Tags

Itô formula, Itô lemma, two-dimensional Itô formula, quadratic covariation, polarisation, Itô
process, stochastic integral, MSC 60H05, MSC 60H10
-/

@[expose] public section

namespace MathFin

/-! ### Convergence in measure of pairs and of negatives -/

namespace LocalisationInMeasure

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Convergence in measure of pairs.** If `g₁ → h₁` and `g₂ → h₂` in measure, then
`(g₁, g₂) → (h₁, h₂)` in measure, for the maximum distance on the product. It lets one subsequence
converge almost surely for finitely many sequences at once. -/
theorem tendstoInMeasure_prodMk {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] {g₁ : ℕ → Ω → E} {h₁ : Ω → E}
    {g₂ : ℕ → Ω → F} {h₂ : Ω → F} (hg₁ : TendstoInMeasure μ g₁ atTop h₁)
    (hg₂ : TendstoInMeasure μ g₂ atTop h₂) :
    TendstoInMeasure μ (fun n ω ↦ (g₁ n ω, g₂ n ω)) atTop fun ω ↦ (h₁ ω, h₂ ω) := by
  intro ε hε
  have h := (hg₁ ε hε).add (hg₂ ε hε)
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n ↦ zero_le _)
    fun n ↦ ?_
  refine le_trans (measure_mono fun ω hω ↦ ?_) (measure_union_le _ _)
  have hω' : ε ≤ edist (g₁ n ω, g₂ n ω) (h₁ ω, h₂ ω) := hω
  rw [Prod.edist_eq, le_max_iff] at hω'
  exact hω'

/-- **Convergence in measure is stable under negation.** -/
theorem tendstoInMeasure_neg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {g : ℕ → Ω → ℝ}
    {g' : Ω → ℝ} (h : TendstoInMeasure μ g atTop g') :
    TendstoInMeasure μ (fun n ω ↦ -g n ω) atTop fun ω ↦ -g' ω := by
  intro ε hε
  simpa only [edist_neg_neg] using h ε hε

end LocalisationInMeasure

namespace ItoFormulaAdapted

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralRiemannBridge
  ItoIntegralBrownian QuadraticVariationL2 ItoIntegralProcessContinuousModification
  AdaptedDrift AdaptedRiemannStieltjes AdaptedQuadraticVariation ItoIntegralAgainstMartingale
  PredictableDensityGeneral StochasticIntegralCharacterisation LpMulIsometry
  AdaptedStochasticIntegralFreezing LocalisationInMeasure
open scoped NNReal ENNReal

/-! ### Real algebra -/

/-- A bound on `z` gives a bound on `½ z`. -/
private theorem abs_half_mul_le {z C : ℝ} (h : |z| ≤ C) : |1 / 2 * z| ≤ 1 / 2 * C := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- **The drift of `f(t, X_t, Y_t)`** at the point `(s, x, y)`, for coefficients `b`, `c` (drifts)
and `σ`, `τ` (volatilities) of the two processes:
`f_t + f_x b + f_y c + ½ f_xx σ² + f_xy σ τ + ½ f_yy τ²`. The term `f_xy σ τ` is the one that
only a second driven process brings: the quadratic covariation of the two martingale parts. -/
def ito2Drift (f_t f_x f_y f_xx f_xy f_yy : ℝ → ℝ → ℝ → ℝ) (b c σ τ s x y : ℝ) : ℝ :=
  f_t s x y + f_x s x y * b + f_y s x y * c + 1 / 2 * (f_xx s x y * σ ^ 2)
    + f_xy s x y * (σ * τ) + 1 / 2 * (f_yy s x y * τ ^ 2)

/-- **Polarisation of a weighted sum.** For increments `Δx = xb − xa` and `Δy = yb − ya` and a
weight `W`, `∑ W Δx Δy = ∑ ½ W (Δx + Δy)² − ∑ ½ W Δx² − ∑ ½ W Δy²`. -/
theorem sum_polarisation (n : ℕ) (W xa xb ya yb : ℕ → ℝ) :
    ∑ k ∈ Finset.range n, W k * ((xb k - xa k) * (yb k - ya k))
      = ∑ k ∈ Finset.range n, 1 / 2 * W k * ((xb k + yb k) - (xa k + ya k)) ^ 2
        + -∑ k ∈ Finset.range n, 1 / 2 * W k * (xb k - xa k) ^ 2
        + -∑ k ∈ Finset.range n, 1 / 2 * W k * (yb k - ya k) ^ 2 := by
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- **The drift and covariation integrals of the two-factor Itô formula, assembled.** For
functions of time continuous on `[0, T]`, the time, drift and second-order integrals, the last one
with the polarised cross term `∫ ½ f_xy (σ + τ)² − ∫ ½ f_xy σ² − ∫ ½ f_xy τ²`, add up to the
integral of the drift of `f(t, X_t, Y_t)`,
`f_t + f_x b + f_y c + ½ f_xx σ² + f_xy σ τ + ½ f_yy τ²`. -/
theorem integral_two_factor_drift {T : ℝ≥0} {ft fx fy fxx fxy fyy b c σ τ : ℝ≥0 → ℝ}
    (hft : ContinuousOn ft (Icc 0 T)) (hfx : ContinuousOn fx (Icc 0 T))
    (hfy : ContinuousOn fy (Icc 0 T)) (hfxx : ContinuousOn fxx (Icc 0 T))
    (hfxy : ContinuousOn fxy (Icc 0 T)) (hfyy : ContinuousOn fyy (Icc 0 T))
    (hb : ContinuousOn b (Icc 0 T)) (hc : ContinuousOn c (Icc 0 T))
    (hσ : ContinuousOn σ (Icc 0 T)) (hτ : ContinuousOn τ (Icc 0 T)) :
    (∫ s in Ioc 0 T, ft s ∂timeMeasure) + (∫ s in Ioc 0 T, fx s * b s ∂timeMeasure)
      + (∫ s in Ioc 0 T, fy s * c s ∂timeMeasure)
      + ((∫ s in Ioc 0 T, 1 / 2 * fxx s * σ s ^ 2 ∂timeMeasure)
        + (∫ s in Ioc 0 T, 1 / 2 * fyy s * τ s ^ 2 ∂timeMeasure)
        + (((∫ s in Ioc 0 T, 1 / 2 * fxy s * (σ s + τ s) ^ 2 ∂timeMeasure)
          + -(∫ s in Ioc 0 T, 1 / 2 * fxy s * σ s ^ 2 ∂timeMeasure))
          + -(∫ s in Ioc 0 T, 1 / 2 * fxy s * τ s ^ 2 ∂timeMeasure)))
      = ∫ s in Ioc 0 T, (ft s + fx s * b s + fy s * c s + 1 / 2 * (fxx s * σ s ^ 2)
          + fxy s * (σ s * τ s) + 1 / 2 * (fyy s * τ s ^ 2)) ∂timeMeasure := by
  have iA1 : IntegrableOn ft (Ioc 0 T) timeMeasure := integrableOn_Ioc_of_continuousOn hft
  have iA2 : IntegrableOn (fun s ↦ fx s * b s) (Ioc 0 T) timeMeasure :=
    integrableOn_Ioc_of_continuousOn (hfx.mul hb)
  have iA3 : IntegrableOn (fun s ↦ fy s * c s) (Ioc 0 T) timeMeasure :=
    integrableOn_Ioc_of_continuousOn (hfy.mul hc)
  have iA4 : IntegrableOn (fun s ↦ 1 / 2 * (fxx s * σ s ^ 2)) (Ioc 0 T) timeMeasure :=
    integrableOn_Ioc_of_continuousOn (continuousOn_const.mul (hfxx.mul (hσ.pow 2)))
  have iA5 : IntegrableOn (fun s ↦ fxy s * (σ s * τ s)) (Ioc 0 T) timeMeasure :=
    integrableOn_Ioc_of_continuousOn (hfxy.mul (hσ.mul hτ))
  have iA6 : IntegrableOn (fun s ↦ 1 / 2 * (fyy s * τ s ^ 2)) (Ioc 0 T) timeMeasure :=
    integrableOn_Ioc_of_continuousOn (continuousOn_const.mul (hfyy.mul (hτ.pow 2)))
  have iG2 : IntegrableOn (fun s ↦ 1 / 2 * fxy s * σ s ^ 2) (Ioc 0 T) timeMeasure :=
    integrableOn_Ioc_of_continuousOn ((continuousOn_const.mul hfxy).mul (hσ.pow 2))
  have iG3 : IntegrableOn (fun s ↦ 1 / 2 * fxy s * τ s ^ 2) (Ioc 0 T) timeMeasure :=
    integrableOn_Ioc_of_continuousOn ((continuousOn_const.mul hfxy).mul (hτ.pow 2))
  have iS1 : IntegrableOn (fun s ↦ ft s + fx s * b s) (Ioc 0 T) timeMeasure := iA1.add iA2
  have iS2 : IntegrableOn (fun s ↦ ft s + fx s * b s + fy s * c s) (Ioc 0 T) timeMeasure :=
    iS1.add iA3
  have iS3 : IntegrableOn (fun s ↦ ft s + fx s * b s + fy s * c s + 1 / 2 * (fxx s * σ s ^ 2))
      (Ioc 0 T) timeMeasure := iS2.add iA4
  have iS4 : IntegrableOn (fun s ↦ ft s + fx s * b s + fy s * c s + 1 / 2 * (fxx s * σ s ^ 2)
      + fxy s * (σ s * τ s)) (Ioc 0 T) timeMeasure := iS3.add iA5
  have iG25 : IntegrableOn (fun s ↦ 1 / 2 * fxy s * σ s ^ 2 + fxy s * (σ s * τ s))
      (Ioc 0 T) timeMeasure := iG2.add iA5
  have hsplit : ∫ s in Ioc 0 T, (ft s + fx s * b s + fy s * c s + 1 / 2 * (fxx s * σ s ^ 2)
          + fxy s * (σ s * τ s) + 1 / 2 * (fyy s * τ s ^ 2)) ∂timeMeasure
      = (∫ s in Ioc 0 T, ft s ∂timeMeasure) + (∫ s in Ioc 0 T, fx s * b s ∂timeMeasure)
        + (∫ s in Ioc 0 T, fy s * c s ∂timeMeasure)
        + (∫ s in Ioc 0 T, 1 / 2 * (fxx s * σ s ^ 2) ∂timeMeasure)
        + (∫ s in Ioc 0 T, fxy s * (σ s * τ s) ∂timeMeasure)
        + (∫ s in Ioc 0 T, 1 / 2 * (fyy s * τ s ^ 2) ∂timeMeasure) := by
    rw [integral_add iS4 iA6, integral_add iS3 iA5, integral_add iS2 iA4, integral_add iS1 iA3,
      integral_add iA1 iA2]
  have hpt (s : ℝ≥0) : 1 / 2 * fxy s * (σ s + τ s) ^ 2
      = 1 / 2 * fxy s * σ s ^ 2 + fxy s * (σ s * τ s) + 1 / 2 * fxy s * τ s ^ 2 := by ring
  have hcross : ∫ s in Ioc 0 T, 1 / 2 * fxy s * (σ s + τ s) ^ 2 ∂timeMeasure
      = (∫ s in Ioc 0 T, 1 / 2 * fxy s * σ s ^ 2 ∂timeMeasure)
        + (∫ s in Ioc 0 T, fxy s * (σ s * τ s) ∂timeMeasure)
        + ∫ s in Ioc 0 T, 1 / 2 * fxy s * τ s ^ 2 ∂timeMeasure := by
    rw [← integral_add iG2 iA5, ← integral_add iG25 iG3]
    exact setIntegral_congr_fun measurableSet_Ioc fun s _ ↦ hpt s
  have e4 : ∫ s in Ioc 0 T, 1 / 2 * fxx s * σ s ^ 2 ∂timeMeasure
      = ∫ s in Ioc 0 T, 1 / 2 * (fxx s * σ s ^ 2) ∂timeMeasure :=
    setIntegral_congr_fun measurableSet_Ioc fun s _ ↦ mul_assoc _ _ _
  have e6 : ∫ s in Ioc 0 T, 1 / 2 * fyy s * τ s ^ 2 ∂timeMeasure
      = ∫ s in Ioc 0 T, 1 / 2 * (fyy s * τ s ^ 2) ∂timeMeasure :=
    setIntegral_congr_fun measurableSet_Ioc fun s _ ↦ mul_assoc _ _ _
  rw [hsplit, e4, e6, hcross]
  ring

/-! ### The `L²` class of a sum of integrands -/

section Linear

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))

/-- **The `L²` class of a sum of integrands is the sum of the classes**: `processToLp` is additive
in the integrand. -/
theorem processToLp_add {σ τ : ℝ≥0 → Ω → ℝ}
    (hσa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hσc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω) {Cσ : ℝ} (hσb : ∀ t ω, |σ t ω| ≤ Cσ)
    (hτa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (τ t))
    (hτc : ∀ ω, Continuous fun t : ℝ≥0 ↦ τ t ω) {Cτ : ℝ} (hτb : ∀ t ω, |τ t ω| ≤ Cτ)
    (hρa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
      (fun ω ↦ σ t ω + τ t ω))
    (hρc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω + τ t ω)
    (hρb : ∀ t ω, |σ t ω + τ t ω| ≤ Cσ + Cτ) :
    processToLp (μ := μ) T hBmeas (σ := fun t ω ↦ σ t ω + τ t ω) hρa hρc hρb
      = processToLp (μ := μ) T hBmeas hσa hσc hσb + processToLp (μ := μ) T hBmeas hτa hτc hτb := by
  refine Lp.ext ?_
  filter_upwards [processToLp_coeFn (μ := μ) T hBmeas (σ := fun t ω ↦ σ t ω + τ t ω) hρa hρc hρb,
    processToLp_coeFn (μ := μ) T hBmeas hσa hσc hσb,
    processToLp_coeFn (μ := μ) T hBmeas hτa hτc hτb,
    Lp.coeFn_add (processToLp (μ := μ) T hBmeas hσa hσc hσb)
      (processToLp (μ := μ) T hBmeas hτa hτc hτb)] with z h1 h2 h3 h4
  have e : Function.uncurry (fun t ω ↦ σ t ω + τ t ω) z
      = Function.uncurry σ z + Function.uncurry τ z := rfl
  rw [h1, h4, Pi.add_apply, h2, h3, e]

end Linear

/-! ### Predictability of a function of the two processes -/

section Predictable

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
  (φ₁ φ₂ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {b c : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) {Cb : ℝ} (hb_bdd : ∀ s ω, |b s ω| ≤ Cb)
  (hc_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (c t))
  (hc_cont : ∀ ω, Continuous fun s ↦ c s ω) {Cc : ℝ} (hc_bdd : ∀ s ω, |c s ω| ≤ Cc)
  (x₀ y₀ : ℝ)

include hB hBcont hb_adap hb_cont hb_bdd hc_adap hc_cont hc_bdd in
/-- **A jointly continuous function of the time and of two Itô processes is predictable.** -/
theorem comp_time_adaptedItoProcess_pair_isStronglyPredictable {g : ℝ → ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ × ℝ ↦ g p.1 p.2.1 p.2.2) :
    IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦
      g s (adaptedItoProcess T hBmeas φ₁ x₀ b s ω) (adaptedItoProcess T hBmeas φ₂ y₀ c s ω) := by
  have ht : IsStronglyPredictable (natFiltration hBmeas) fun (s : ℝ≥0) (_ : Ω) ↦ (s : ℝ) :=
    StronglyAdapted.isStronglyPredictable_of_leftContinuous (fun _ ↦ stronglyMeasurable_const)
      fun _ _ ↦ NNReal.continuous_coe.continuousWithinAt
  exact hg.comp_stronglyMeasurable (StronglyMeasurable.prodMk ht (StronglyMeasurable.prodMk
    (adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ₁ hb_adap hb_cont hb_bdd x₀)
    (adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ₂ hc_adap hc_cont hc_bdd y₀)))

end Predictable

/-! ### The formula with bounded partials -/

section Against

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
  {σ τ : ℝ≥0 → Ω → ℝ}
  (hσa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hσc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω) {Cσ : ℝ} (hσb : ∀ t ω, |σ t ω| ≤ Cσ)
  (hτa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (τ t))
  (hτc : ∀ ω, Continuous fun t : ℝ≥0 ↦ τ t ω) {Cτ : ℝ} (hτb : ∀ t ω, |τ t ω| ≤ Cτ)
  {b c : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) {Cb : ℝ} (hb_bdd : ∀ s ω, |b s ω| ≤ Cb)
  (hc_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (c t))
  (hc_cont : ∀ ω, Continuous fun s ↦ c s ω) {Cc : ℝ} (hc_bdd : ∀ s ω, |c s ω| ≤ Cc)
  (x₀ y₀ : ℝ)
  {f f_t f_x f_y f_xx f_xy f_yy : ℝ → ℝ → ℝ → ℝ}
  (hf_t : ∀ t x y, HasDerivAt (fun s ↦ f s x y) (f_t t x y) t)
  (hf_x : ∀ t x y, HasDerivAt (fun u ↦ f t u y) (f_x t x y) x)
  (hf_y : ∀ t x y, HasDerivAt (fun v ↦ f t x v) (f_y t x y) y)
  (hf_xx : ∀ t x y, HasDerivAt (fun u ↦ f_x t u y) (f_xx t x y) x)
  (hf_xy : ∀ t x y, HasDerivAt (fun v ↦ f_x t x v) (f_xy t x y) y)
  (hf_yy : ∀ t x y, HasDerivAt (fun v ↦ f_y t x v) (f_yy t x y) y)
  (hf_t_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_t p.1 p.2.1 p.2.2)
  (hf_x_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_x p.1 p.2.1 p.2.2)
  (hf_y_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_y p.1 p.2.1 p.2.2)
  (hf_xx_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xx p.1 p.2.1 p.2.2)
  (hf_xy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_xy p.1 p.2.1 p.2.2)
  (hf_yy_cont : Continuous fun p : ℝ × ℝ × ℝ ↦ f_yy p.1 p.2.1 p.2.2)

include hB hBcont hσa hσc hσb hτa hτc hτb hb_adap hb_cont hb_bdd hc_adap hc_cont hc_bdd hf_t hf_x
  hf_y hf_xx hf_xy hf_yy hf_t_cont hf_x_cont hf_y_cont hf_xx_cont hf_xy_cont hf_yy_cont in
/-- **Itô's formula for `f(t, X_t, Y_t)` with bounded partials, along two Itô processes driven by
one Brownian motion, the stochastic integrals taken against `M^σ = σ●B` and `M^τ = τ●B`.** Let
`B` be a Brownian motion with every path continuous, `σ`, `τ`, `b`, `c` bounded, adapted to its
natural filtration, with every path continuous, `X = x₀ + ∫ b ds + M^σ` and
`Y = y₀ + ∫ c ds + M^τ` (`adaptedItoProcess`, horizon `T`), and `f(t, x, y)` with jointly
continuous bounded partials `f_t`, `f_x`, `f_y`, `f_xx`, `f_xy = ∂_y f_x`, `f_yy`. Almost surely

`f(T, X_T, Y_T) − f(0, x₀, y₀) = ∫ f_x(·, X, Y) dM^σ + ∫ f_y(·, X, Y) dM^τ
  + ∫₀ᵀ (f_t + f_x b + f_y c + ½ f_xx σ² + f_xy σ τ + ½ f_yy τ²)(s, X_s, Y_s) ds`,

where `∫ w dM` is the integral against `M` of the class of the bounded predictable weight `w`
(`weightLp`). The covariation term `f_xy σ τ` is derived from the polarisation of the weighted
quadratic variation, not assumed. At the single time `T`; for every `t ≤ T` and unbounded `f` this
is still to do. -/
theorem ito_formula_adapted_two_factor_against {Ct Cx Cy Cxx Cxy Cyy : ℝ}
    (hbt : ∀ t x y, |f_t t x y| ≤ Ct) (hbx : ∀ t x y, |f_x t x y| ≤ Cx)
    (hby : ∀ t x y, |f_y t x y| ≤ Cy) (hbxx : ∀ t x y, |f_xx t x y| ≤ Cxx)
    (hbxy : ∀ t x y, |f_xy t x y| ≤ Cxy) (hbyy : ∀ t x y, |f_yy t x y| ≤ Cyy) :
    (fun ω ↦ f T (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b T ω)
        (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c T ω)
        - f 0 x₀ y₀) =ᵐ[μ] fun ω ↦
      itoIntegralAgainstCLM hB T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb)
          (weightLp T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb)
            (comp_time_adaptedItoProcess_pair_isStronglyPredictable hB T hBmeas hBcont
              (processToLp (μ := μ) T hBmeas hσa hσc hσb)
              (processToLp (μ := μ) T hBmeas hτa hτc hτb) hb_adap hb_cont hb_bdd hc_adap hc_cont
              hc_bdd x₀ y₀ hf_x_cont)
            fun s ω ↦ hbx s
              (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b s ω)
              (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c s ω)) ω
        + itoIntegralAgainstCLM hB T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb)
          (weightLp T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb)
            (comp_time_adaptedItoProcess_pair_isStronglyPredictable hB T hBmeas hBcont
              (processToLp (μ := μ) T hBmeas hσa hσc hσb)
              (processToLp (μ := μ) T hBmeas hτa hτc hτb) hb_adap hb_cont hb_bdd hc_adap hc_cont
              hc_bdd x₀ y₀ hf_y_cont)
            fun s ω ↦ hby s
              (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b s ω)
              (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c s ω)) ω
        + ∫ s in Ioc 0 T, ito2Drift f_t f_x f_y f_xx f_xy f_yy (b s ω) (c s ω) (σ s ω) (τ s ω) s
          (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hσa hσc hσb) x₀ b s ω)
          (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hτa hτc hτb) y₀ c s ω)
          ∂timeMeasure := by
  set φσ := processToLp (μ := μ) T hBmeas hσa hσc hσb
  set φτ := processToLp (μ := μ) T hBmeas hτa hτc hτb
  set X := adaptedItoProcess T hBmeas φσ x₀ b
  set Y := adaptedItoProcess T hBmeas φτ y₀ c
  have hXp : IsStronglyPredictable (natFiltration hBmeas) X :=
    adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φσ hb_adap hb_cont hb_bdd x₀
  have hYp : IsStronglyPredictable (natFiltration hBmeas) Y :=
    adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φτ hc_adap hc_cont hc_bdd y₀
  have hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc 0 T) :=
    ae_continuousOn_adaptedItoProcess hB T hBmeas hBcont φσ hb_cont hb_bdd x₀
  have hYc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Y t ω) (Icc 0 T) :=
    ae_continuousOn_adaptedItoProcess hB T hBmeas hBcont φτ hc_cont hc_bdd y₀
  have hXYc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc 0 T)
      ∧ ContinuousOn (fun t ↦ Y t ω) (Icc 0 T) := by
    filter_upwards [hXc, hYc] with ω h1 h2 using ⟨h1, h2⟩
  have hXae (t : ℝ≥0) (ht : t ≤ T) :=
    adaptedItoProcess_ae_eq hB T hBmeas hBcont φσ x₀ (b := b) ht
  have hYae (t : ℝ≥0) (ht : t ≤ T) :=
    adaptedItoProcess_ae_eq hB T hBmeas hBcont φτ y₀ (b := c) ht
  have hXm (t : ℝ≥0) : AEStronglyMeasurable (X t) μ :=
    ((hXp.stronglyAdapted t).mono ((natFiltration hBmeas).le t)).aestronglyMeasurable
  have hYm (t : ℝ≥0) : AEStronglyMeasurable (Y t) μ :=
    ((hYp.stronglyAdapted t).mono ((natFiltration hBmeas).le t)).aestronglyMeasurable
  -- a jointly continuous function of the time and of the two paths
  have hcomp {g : ℝ → ℝ → ℝ → ℝ} (hg : Continuous fun p : ℝ × ℝ × ℝ ↦ g p.1 p.2.1 p.2.2)
      {ω : Ω} (hx : ContinuousOn (fun t ↦ X t ω) (Icc 0 T))
      (hy : ContinuousOn (fun t ↦ Y t ω) (Icc 0 T)) :
      ContinuousOn (fun s : ℝ≥0 ↦ g s (X s ω) (Y s ω)) (Icc 0 T) :=
    hg.comp_continuousOn (NNReal.continuous_coe.continuousOn.prodMk (hx.prodMk hy))
  have hadapt {g : ℝ → ℝ → ℝ → ℝ} (hg : Continuous fun p : ℝ × ℝ × ℝ ↦ g p.1 p.2.1 p.2.2)
      (s : ℝ≥0) :
      StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)]
        fun ω ↦ g s (X s ω) (Y s ω) :=
    (hg.comp (by fun_prop : Continuous fun p : ℝ × ℝ ↦ ((s : ℝ), p.1, p.2))).comp_stronglyMeasurable
      (StronglyMeasurable.prodMk (hXp.stronglyAdapted s) (hYp.stronglyAdapted s))
  have hwcont {g : ℝ → ℝ → ℝ → ℝ} (hg : Continuous fun p : ℝ × ℝ × ℝ ↦ g p.1 p.2.1 p.2.2) :
      ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ g s (X s ω) (Y s ω)) (Icc 0 T) :=
    hXYc.mono fun ω h ↦ hcomp hg h.1 h.2
  -- the coefficients of `Z = X + Y`
  have hρa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
      (fun ω ↦ σ t ω + τ t ω) := fun t ↦ (hσa t).add (hτa t)
  have hρc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω + τ t ω := fun ω ↦ (hσc ω).add (hτc ω)
  have hρb : ∀ t ω, |σ t ω + τ t ω| ≤ Cσ + Cτ := fun t ω ↦
    (abs_add_le _ _).trans (add_le_add (hσb t ω) (hτb t ω))
  have hAZ : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → ∀ ω,
      |(driftPath b t ω + driftPath c t ω) - (driftPath b s ω + driftPath c s ω)|
        ≤ (Cb + Cc) * ((t : ℝ) - s) := by
    intro s t hst ω
    have h1 := abs_driftPath_sub_le hb_cont hb_bdd hst ω
    have h2 := abs_driftPath_sub_le hc_cont hc_bdd hst ω
    have h3 := abs_add_le (driftPath b t ω - driftPath b s ω) (driftPath c t ω - driftPath c s ω)
    have h4 : (driftPath b t ω + driftPath c t ω) - (driftPath b s ω + driftPath c s ω)
        = (driftPath b t ω - driftPath b s ω) + (driftPath c t ω - driftPath c s ω) := by ring
    rw [h4]
    linarith
  have hZae (t : ℝ≥0) (ht : t ≤ T) : (fun ω ↦ X t ω + Y t ω) =ᵐ[μ]
      fun ω ↦ (x₀ + y₀) + (driftPath b t ω + driftPath c t ω)
        + itoProcessCLM hB T t hBmeas
          (processToLp (μ := μ) T hBmeas (σ := fun t ω ↦ σ t ω + τ t ω) hρa hρc hρb) ω := by
    have hlin : itoProcessCLM hB T t hBmeas
          (processToLp (μ := μ) T hBmeas (σ := fun t ω ↦ σ t ω + τ t ω) hρa hρc hρb)
        = itoProcessCLM hB T t hBmeas φσ + itoProcessCLM hB T t hBmeas φτ := by
      rw [processToLp_add T hBmeas hσa hσc hσb hτa hτc hτb hρa hρc hρb, map_add]
    filter_upwards [hXae t ht, hYae t ht,
      Lp.coeFn_add (itoProcessCLM hB T t hBmeas φσ) (itoProcessCLM hB T t hBmeas φτ)]
      with ω h1 h2 h3
    rw [Pi.add_apply] at h3
    rw [hlin, h3, h1, h2]
    ring
  -- the weighted quadratic variations of `X`, `Y` and `Z`
  have qvX {w : ℝ≥0 → Ω → ℝ}
      (hwa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (w s))
      (hwc : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Icc 0 T)) {Cw : ℝ}
      (hwb : ∀ s ω, |w s ω| ≤ Cw) :=
    tendstoInMeasure_weighted_qv_adapted hB T hBmeas hσa hσc hσb
      (abs_driftPath_sub_le hb_cont hb_bdd) (X₀ := fun _ ↦ x₀) hXae hXm hwa hwc hwb
  have qvY {w : ℝ≥0 → Ω → ℝ}
      (hwa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (w s))
      (hwc : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Icc 0 T)) {Cw : ℝ}
      (hwb : ∀ s ω, |w s ω| ≤ Cw) :=
    tendstoInMeasure_weighted_qv_adapted hB T hBmeas hτa hτc hτb
      (abs_driftPath_sub_le hc_cont hc_bdd) (X₀ := fun _ ↦ y₀) hYae hYm hwa hwc hwb
  have qvZ {w : ℝ≥0 → Ω → ℝ}
      (hwa : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (w s))
      (hwc : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Icc 0 T)) {Cw : ℝ}
      (hwb : ∀ s ω, |w s ω| ≤ Cw) :=
    tendstoInMeasure_weighted_qv_adapted hB T hBmeas (σ := fun t ω ↦ σ t ω + τ t ω) hρa hρc hρb
      (A := fun t ω ↦ driftPath b t ω + driftPath c t ω) (Ca := Cb + Cc) hAZ
      (X := fun t ω ↦ X t ω + Y t ω) (X₀ := fun _ ↦ x₀ + y₀) hZae
      (fun t ↦ (hXm t).add (hYm t)) hwa hwc hwb
  -- the weights
  have hxx := qvX (w := fun s ω ↦ 1 / 2 * f_xx s (X s ω) (Y s ω))
    (fun s ↦ (hadapt hf_xx_cont s).const_mul _)
    ((hwcont hf_xx_cont).mono fun ω h ↦ continuousOn_const.mul h)
    fun s ω ↦ abs_half_mul_le (hbxx s (X s ω) (Y s ω))
  have hyy := qvY (w := fun s ω ↦ 1 / 2 * f_yy s (X s ω) (Y s ω))
    (fun s ↦ (hadapt hf_yy_cont s).const_mul _)
    ((hwcont hf_yy_cont).mono fun ω h ↦ continuousOn_const.mul h)
    fun s ω ↦ abs_half_mul_le (hbyy s (X s ω) (Y s ω))
  have hxyX := qvX (w := fun s ω ↦ 1 / 2 * f_xy s (X s ω) (Y s ω))
    (fun s ↦ (hadapt hf_xy_cont s).const_mul _)
    ((hwcont hf_xy_cont).mono fun ω h ↦ continuousOn_const.mul h)
    fun s ω ↦ abs_half_mul_le (hbxy s (X s ω) (Y s ω))
  have hxyY := qvY (w := fun s ω ↦ 1 / 2 * f_xy s (X s ω) (Y s ω))
    (fun s ↦ (hadapt hf_xy_cont s).const_mul _)
    ((hwcont hf_xy_cont).mono fun ω h ↦ continuousOn_const.mul h)
    fun s ω ↦ abs_half_mul_le (hbxy s (X s ω) (Y s ω))
  have hxyZ := qvZ (w := fun s ω ↦ 1 / 2 * f_xy s (X s ω) (Y s ω))
    (fun s ↦ (hadapt hf_xy_cont s).const_mul _)
    ((hwcont hf_xy_cont).mono fun ω h ↦ continuousOn_const.mul h)
    fun s ω ↦ abs_half_mul_le (hbxy s (X s ω) (Y s ω))
  have hone_X := qvX (w := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const)
    (Eventually.of_forall fun _ ↦ continuousOn_const) (Cw := 1) fun _ _ ↦ abs_one.le
  have hone_Y := qvY (w := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const)
    (Eventually.of_forall fun _ ↦ continuousOn_const) (Cw := 1) fun _ _ ↦ abs_one.le
  -- the two Riemann–Stieltjes sums against `M^σ` and `M^τ`
  have hRSx := tendstoInMeasure_riemannStieltjes hB T hBmeas φσ
    (fun t ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φσ ht)
    (comp_time_adaptedItoProcess_pair_isStronglyPredictable hB T hBmeas hBcont φσ φτ hb_adap
      hb_cont hb_bdd hc_adap hc_cont hc_bdd x₀ y₀ hf_x_cont)
    (hwcont hf_x_cont) fun s ω ↦ hbx s (X s ω) (Y s ω)
  have hRSy := tendstoInMeasure_riemannStieltjes hB T hBmeas φτ
    (fun t ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φτ ht)
    (comp_time_adaptedItoProcess_pair_isStronglyPredictable hB T hBmeas hBcont φσ φτ hb_adap
      hb_cont hb_bdd hc_adap hc_cont hc_bdd x₀ y₀ hf_y_cont)
    (hwcont hf_y_cont) fun s ω ↦ hby s (X s ω) (Y s ω)
  -- one subsequence along which everything converges almost surely
  have hPfull := (((hRSx.add hRSy).add hxx).add hyy).add
    ((hxyZ.add (tendstoInMeasure_neg hxyX)).add (tendstoInMeasure_neg hxyY))
  obtain ⟨ν, hνm, hae⟩ :=
    (tendstoInMeasure_prodMk hPfull (tendstoInMeasure_prodMk hone_X hone_Y)).exists_seq_tendsto_ae
  have hν : Tendsto ν atTop atTop := hνm.tendsto_atTop
  filter_upwards [hae, hXc, hYc, adaptedItoProcess_zero hB T hBmeas hBcont φσ x₀ (b := b),
    adaptedItoProcess_zero hB T hBmeas hBcont φτ y₀ (b := c)] with ω hω hxc hyc h0x h0y
  have h1 := hω.fst_nhds
  have h2 := hω.snd_nhds.fst_nhds
  have h3 := hω.snd_nhds.snd_nhds
  -- the bounds on the squared increments
  obtain ⟨Qx, hQx⟩ : ∃ Qx : ℝ, ∀ᶠ i in atTop, ∑ k ∈ Finset.range (ν i),
      (X (unifPart T (ν i) (k + 1)) ω - X (unifPart T (ν i) k) ω) ^ 2 ≤ Qx :=
    ⟨_, (Tendsto.eventually_lt_const (lt_add_one _) h2).mono fun i hi ↦ by
      simpa only [one_mul] using hi.le⟩
  obtain ⟨Qy, hQy⟩ : ∃ Qy : ℝ, ∀ᶠ i in atTop, ∑ k ∈ Finset.range (ν i),
      (Y (unifPart T (ν i) (k + 1)) ω - Y (unifPart T (ν i) k) ω) ^ 2 ≤ Qy :=
    ⟨_, (Tendsto.eventually_lt_const (lt_add_one _) h3).mono fun i hi ↦ by
      simpa only [one_mul] using hi.le⟩
  -- the time and drift sums, pathwise
  have hE := (tendsto_sum_mul_driftPath_sub (b := fun (_ : ℝ≥0) (_ : Ω) ↦ (1 : ℝ))
    (fun _ ↦ continuous_const) (fun _ _ ↦ abs_one.le) T ω
    (g := fun s ↦ f_t s (X s ω) (Y s ω)) (hcomp hf_t_cont hxc hyc)
    fun s ↦ hbt s (X s ω) (Y s ω)).comp hν
  simp only [driftPath_one, mul_one] at hE
  have hDx := (tendsto_sum_mul_driftPath_sub hb_cont hb_bdd T ω
    (g := fun s ↦ f_x s (X s ω) (Y s ω)) (hcomp hf_x_cont hxc hyc)
    fun s ↦ hbx s (X s ω) (Y s ω)).comp hν
  have hDy := (tendsto_sum_mul_driftPath_sub hc_cont hc_bdd T ω
    (g := fun s ↦ f_y s (X s ω) (Y s ω)) (hcomp hf_y_cont hxc hyc)
    fun s ↦ hby s (X s ω) (Y s ω)).comp hν
  -- the martingale and second-order sums, with the polarised cross term
  have hPs : Tendsto (fun i ↦
      ∑ k ∈ Finset.range (ν i), f_x (unifPart T (ν i) k) (X (unifPart T (ν i) k) ω)
        (Y (unifPart T (ν i) k) ω)
        * (itoContinuousMod T hBmeas φσ (unifPart T (ν i) (k + 1)) ω
          - itoContinuousMod T hBmeas φσ (unifPart T (ν i) k) ω)
      + ∑ k ∈ Finset.range (ν i), f_y (unifPart T (ν i) k) (X (unifPart T (ν i) k) ω)
        (Y (unifPart T (ν i) k) ω)
        * (itoContinuousMod T hBmeas φτ (unifPart T (ν i) (k + 1)) ω
          - itoContinuousMod T hBmeas φτ (unifPart T (ν i) k) ω)
      + ∑ k ∈ Finset.range (ν i), 1 / 2 * f_xx (unifPart T (ν i) k) (X (unifPart T (ν i) k) ω)
        (Y (unifPart T (ν i) k) ω)
        * (X (unifPart T (ν i) (k + 1)) ω - X (unifPart T (ν i) k) ω) ^ 2
      + ∑ k ∈ Finset.range (ν i), f_xy (unifPart T (ν i) k) (X (unifPart T (ν i) k) ω)
        (Y (unifPart T (ν i) k) ω)
        * ((X (unifPart T (ν i) (k + 1)) ω - X (unifPart T (ν i) k) ω)
          * (Y (unifPart T (ν i) (k + 1)) ω - Y (unifPart T (ν i) k) ω))
      + ∑ k ∈ Finset.range (ν i), 1 / 2 * f_yy (unifPart T (ν i) k) (X (unifPart T (ν i) k) ω)
        (Y (unifPart T (ν i) k) ω)
        * (Y (unifPart T (ν i) (k + 1)) ω - Y (unifPart T (ν i) k) ω) ^ 2) atTop (𝓝 _) :=
    h1.congr fun i ↦ by
      have e := sum_polarisation (ν i)
        (fun k ↦ f_xy (unifPart T (ν i) k) (X (unifPart T (ν i) k) ω)
          (Y (unifPart T (ν i) k) ω))
        (fun k ↦ X (unifPart T (ν i) k) ω) (fun k ↦ X (unifPart T (ν i) (k + 1)) ω)
        (fun k ↦ Y (unifPart T (ν i) k) ω) (fun k ↦ Y (unifPart T (ν i) (k + 1)) ω)
      beta_reduce at e
      try dsimp only
      linarith [e]
  have key := ito_formula_3d_of_tendsto T hf_t hf_x hf_y hf_xx hf_xy hf_yy hf_t_cont hf_xx_cont
    hf_xy_cont hf_yy_cont (x := fun t ↦ X t ω) (y := fun t ↦ Y t ω)
    (a := fun t ↦ driftPath b t ω) (a' := fun t ↦ driftPath c t ω)
    (m := fun t ↦ itoContinuousMod T hBmeas φσ t ω) (m' := fun t ↦ itoContinuousMod T hBmeas φτ t ω)
    (cx := x₀) (cy := y₀) (fun _ ↦ rfl) (fun _ ↦ rfl) hxc hyc hν hE hDx hDy hPs hQx hQy
  beta_reduce at key
  rw [h0x, h0y] at key
  have hint := integral_two_factor_drift (T := T)
    (ft := fun s ↦ f_t s (X s ω) (Y s ω)) (fx := fun s ↦ f_x s (X s ω) (Y s ω))
    (fy := fun s ↦ f_y s (X s ω) (Y s ω)) (fxx := fun s ↦ f_xx s (X s ω) (Y s ω))
    (fxy := fun s ↦ f_xy s (X s ω) (Y s ω)) (fyy := fun s ↦ f_yy s (X s ω) (Y s ω))
    (b := fun s ↦ b s ω) (c := fun s ↦ c s ω) (σ := fun s ↦ σ s ω) (τ := fun s ↦ τ s ω)
    (hcomp hf_t_cont hxc hyc) (hcomp hf_x_cont hxc hyc) (hcomp hf_y_cont hxc hyc)
    (hcomp hf_xx_cont hxc hyc) (hcomp hf_xy_cont hxc hyc) (hcomp hf_yy_cont hxc hyc)
    (hb_cont ω).continuousOn (hc_cont ω).continuousOn (hσc ω).continuousOn (hτc ω).continuousOn
  beta_reduce at hint
  unfold ito2Drift
  linarith [key, hint]

end Against

end ItoFormulaAdapted

end MathFin
