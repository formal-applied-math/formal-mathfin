/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import BrownianMotion.Auxiliary.ConvergenceInMeasure
public import MathFin.Foundations.ItoFormulaAdaptedProcess

/-! # The product rule for two Itô processes driven by one Brownian motion

Let `B` be a Brownian motion with continuous paths, `σ`, `τ`, `b`, `c` adapted to its natural
filtration with every path continuous, and
`X = x₀ + ∫ b ds + ∫ σ dB`, `Y = y₀ + ∫ c ds + ∫ τ dB` (`localItoProcess`). Almost surely, at
every `t ∈ [0, T]` at once,

`X_t Y_t = x₀ y₀ + ∫₀ᵗ (X c + Y b + σ τ)(s) ds + (∫ (X τ + Y σ) dB)_t`

(`ito_product_rule_process`), i.e. `d(XY) = X dY + Y dX + σ τ dt`: the integral
`∫₀ᵗ σ τ ds` is the quadratic covariation `⟨X, Y⟩_t`, and it is derived, not assumed. The
stochastic term splits as `∫ X τ dB + ∫ Y σ dB` (`ito_product_rule_process_split`).

The proof is polarisation. Itô's formula for `f(x) = x²/2` (`ito_half_sq_process`, the case
`f_t = 0` of `ito_formula_adapted_unbounded_C2_process`) along `X`, `Y` and `Z = X + Y` gives
`XY = Z²/2 − X²/2 − Y²/2`. `Z` is again an Itô process, with coefficients `σ + τ`, `b + c`
(`ae_localItoProcess_add`): both `localItoIntegral` and `predItoIntegral` are additive up to
indistinguishability on `[0, T]` (`ae_localItoIntegral_add`, `ae_predItoIntegral_add`), being at
each time the limits in probability of Riemann sums that add.

Not here: Itô's formula for a general `f(t, X_t, Y_t)` with the cross term `f_xy σ τ`. Polarisation
reaches the polynomials of degree two in `(X, Y)`; a general `f` needs the Taylor argument of
`ItoFormulaAdaptedTD` carried out in two coordinates. Neither is a vector driver
(`d`-dimensional `B`).

## Main results

* `ito_product_rule_process`: for `X`, `Y` as above, almost surely, for all `t ∈ [0, T]`,
  `X_t Y_t = x₀ y₀ + ∫₀ᵗ (X c + Y b + σ τ) ds + (∫ (X τ + Y σ) dB)_t`.
* `ito_product_rule_process_split`: the same with the stochastic term
  `(∫ X τ dB)_t + (∫ Y σ dB)_t`.
* `ito_half_sq_process`: `X_t²/2 = x₀²/2 + ∫₀ᵗ (X b + ½ σ²) ds + (∫ X σ dB)_t` for all `t ∈ [0, T]`
  at once.
* `ae_localItoIntegral_add`, `ae_localItoProcess_add`, `ae_predItoIntegral_add`: additivity of
  the integral and of the process in the coefficients, up to indistinguishability on `[0, T]`.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  Theorem 3.3.6
* [Revuz and Yor, *Continuous Martingales and Brownian Motion*][RevuzYor], Proposition IV.3.1

## Tags

Itô formula, product rule, integration by parts, quadratic covariation, polarisation, stochastic
integral, two Itô processes, MSC 60H05, MSC 60H10, MSC 60G44
-/

@[expose] public section

namespace MathFin
namespace ItoFormulaAdapted

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralBrownian QuadraticVariationL2 ItoIntegralProcessContinuousModification
  AdaptedDrift ItoIntegralLocalised LocalisationInMeasure ItoIntegralRiemannBridge
open scoped NNReal ENNReal

/-! ### Real and pathwise algebra -/

/-- The polarisation identity `XY = Z²/2 − X²/2 − Y²/2` for `Z = X + Y`, carried through the
three Itô formulas for `x ↦ x²/2`. -/
private theorem product_algebra {X Y Z x₀ y₀ DX DY DZ D IX IY IZ IXY Iθ : ℝ}
    (hZt : Z = X + Y)
    (hX : X * X / 2 = x₀ * x₀ / 2 + DX + IX) (hY : Y * Y / 2 = y₀ * y₀ / 2 + DY + IY)
    (hZ : Z * Z / 2 = (x₀ + y₀) * (x₀ + y₀) / 2 + DZ + IZ)
    (hD : DZ = DX + DY + D) (hI₁ : IXY = IX + IY) (hI₂ : IZ = IXY + Iθ) :
    X * Y = x₀ * y₀ + D + Iθ := by
  subst hZt
  linear_combination hZ - hX - hY + hD + hI₂ + hI₁

/-- A function continuous on `[0, t]` is integrable on `(0, t]`. -/
private theorem integrableOn_Ioc_of_continuousOn {g : ℝ≥0 → ℝ} {t : ℝ≥0}
    (hg : ContinuousOn g (Icc 0 t)) : IntegrableOn g (Ioc 0 t) timeMeasure :=
  (hg.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

/-- The integral over `(0, t]` of a sum of three functions continuous on `[0, t]`. -/
private theorem setIntegral_add_add {A B C : ℝ≥0 → ℝ} {t : ℝ≥0}
    (hf : ContinuousOn A (Icc 0 t)) (hg : ContinuousOn B (Icc 0 t))
    (hh : ContinuousOn C (Icc 0 t)) :
    ∫ s in Ioc 0 t, (A s + B s + C s) ∂timeMeasure = (∫ s in Ioc 0 t, A s ∂timeMeasure)
      + (∫ s in Ioc 0 t, B s ∂timeMeasure) + ∫ s in Ioc 0 t, C s ∂timeMeasure := by
  have hAi := integrableOn_Ioc_of_continuousOn hf
  have hBi := integrableOn_Ioc_of_continuousOn hg
  have hCi := integrableOn_Ioc_of_continuousOn hh
  have hABi : IntegrableOn (fun s ↦ A s + B s) (Ioc 0 t) timeMeasure := hAi.add hBi
  rw [integral_add hABi hCi, integral_add hAi hBi]

/-- **The drift path is additive in the rate** along paths of continuous rates. -/
theorem driftPath_add {Ω : Type*} {b c : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hb : Continuous fun s ↦ b s ω) (hc : Continuous fun s ↦ c s ω) (t : ℝ≥0) :
    driftPath (fun s ω ↦ b s ω + c s ω) t ω = driftPath b t ω + driftPath c t ω := by
  unfold driftPath
  exact integral_add (integrableOn_Ioc_of_continuousOn hb.continuousOn)
    (integrableOn_Ioc_of_continuousOn hc.continuousOn)

/-- The Riemann–Itô sum is additive in the integrand along a path where the integrands add. -/
theorem riemannσ_add_of_eq {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {θ θ₁ θ₂ : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
    {ω : Ω} (h : ∀ s ∈ Icc 0 T, θ s ω = θ₁ s ω + θ₂ s ω) (n : ℕ) :
    riemannσ (B := B) θ T n ω = riemannσ (B := B) θ₁ T n ω + riemannσ (B := B) θ₂ T n ω := by
  simp only [riemannσ]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [h _ ⟨zero_le, unifPart_le_T (Finset.mem_range.1 hk).le⟩]
  ring

/-! ### Additivity of the integral and of the process -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)

include hB hBcont in
/-- **`∫ (σ + τ) dB = ∫ σ dB + ∫ τ dB`**, up to indistinguishability on `[0, T]`: at each time
the three are limits in probability of the Riemann sums, which add; paths are continuous. -/
theorem ae_localItoIntegral_add {σ τ : ℝ≥0 → Ω → ℝ}
    (hσa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hσc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω)
    (hτa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (τ t))
    (hτc : ∀ ω, Continuous fun t : ℝ≥0 ↦ τ t ω)
    (hρa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
      (fun ω ↦ σ t ω + τ t ω))
    (hρc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω + τ t ω) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoIntegral (μ := μ) T hBmeas hρa hρc t ω
        = localItoIntegral (μ := μ) T hBmeas hσa hσc t ω
          + localItoIntegral (μ := μ) T hBmeas hτa hτc t ω := by
  refine ae_forall_eq_of_tendstoInMeasure (T := T)
    (Y := fun t ω ↦ localItoIntegral (μ := μ) T hBmeas hρa hρc t ω)
    (Y' := fun t ω ↦ localItoIntegral (μ := μ) T hBmeas hσa hσc t ω
      + localItoIntegral (μ := μ) T hBmeas hτa hτc t ω)
    (g := fun t n ↦ riemannσ (B := B) (fun s ω ↦ σ s ω + τ s ω) t n)
    (ae_continuousOn_localItoIntegral hB T hBmeas hBcont hρa hρc) ?_ ?_ ?_
  · filter_upwards [ae_continuousOn_localItoIntegral hB T hBmeas hBcont hσa hσc,
      ae_continuousOn_localItoIntegral hB T hBmeas hBcont hτa hτc] with ω h1 h2
    exact h1.add h2
  · intro t ht
    exact tendstoInMeasure_riemannσ_localItoIntegral hB T hBmeas hBcont hρa hρc ht.2
  · intro t ht
    refine (TendstoInMeasure.add
      (tendstoInMeasure_riemannσ_localItoIntegral hB T hBmeas hBcont hσa hσc ht.2)
      (tendstoInMeasure_riemannσ_localItoIntegral hB T hBmeas hBcont hτa hτc ht.2)).congr_left
        fun n ↦ Filter.Eventually.of_forall fun ω ↦ ?_
    exact (riemannσ_add_of_eq (B := B) (T := t) (ω := ω) (θ := fun s ω ↦ σ s ω + τ s ω)
      (θ₁ := σ) (θ₂ := τ) (fun s _ ↦ rfl) n).symm

include hB hBcont in
/-- **The Itô process is additive in its coefficients**, up to indistinguishability on `[0, T]`:
the process with coefficients `(σ + τ, b + c)` and starting point `x₀ + y₀` is, almost surely at
every `t ∈ [0, T]`, the sum of the processes with coefficients `(σ, b)`, `(τ, c)` and starting
points `x₀`, `y₀`. -/
theorem ae_localItoProcess_add {σ τ b c : ℝ≥0 → Ω → ℝ}
    (hσa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hσc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω)
    (hτa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (τ t))
    (hτc : ∀ ω, Continuous fun t : ℝ≥0 ↦ τ t ω)
    (hρa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
      (fun ω ↦ σ t ω + τ t ω))
    (hρc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω + τ t ω)
    (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) (hc_cont : ∀ ω, Continuous fun s ↦ c s ω)
    (x₀ y₀ : ℝ) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hρa hρc (x₀ + y₀) (fun s ω ↦ b s ω + c s ω) t ω
        = localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b t ω
          + localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c t ω := by
  filter_upwards [ae_localItoIntegral_add hB T hBmeas hBcont hσa hσc hτa hτc hρa hρc]
    with ω h t ht
  unfold localItoProcess
  rw [h t ht, driftPath_add (hb_cont ω) (hc_cont ω)]
  ring

include hB hBcont in
/-- **`∫ (θ₁ + θ₂) dB = ∫ θ₁ dB + ∫ θ₂ dB`** for predictable integrands with almost surely
continuous paths, up to indistinguishability on `[0, T]`; the integrand `θ₃` of the left side need
only be almost surely the sum of the other two on `[0, T]`. At each time all three integrals are
limits in probability of Riemann sums, and the sums add. -/
theorem ae_predItoIntegral_add {θ₁ θ₂ θ₃ : ℝ≥0 → Ω → ℝ}
    (hp₁ : IsStronglyPredictable (natFiltration hBmeas) θ₁)
    (hp₂ : IsStronglyPredictable (natFiltration hBmeas) θ₂)
    (hp₃ : IsStronglyPredictable (natFiltration hBmeas) θ₃)
    (hc₁ : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ θ₁ s ω) (Icc 0 T))
    (hc₂ : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ θ₂ s ω) (Icc 0 T))
    (hc₃ : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ θ₃ s ω) (Icc 0 T))
    (h : ∀ᵐ ω ∂μ, ∀ s ∈ Icc 0 T, θ₃ s ω = θ₁ s ω + θ₂ s ω) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      predItoIntegral (μ := μ) T hBmeas hp₃ t ω
        = predItoIntegral (μ := μ) T hBmeas hp₁ t ω + predItoIntegral (μ := μ) T hBmeas hp₂ t ω := by
  refine ae_forall_eq_of_tendstoInMeasure (T := T)
    (Y := fun t ω ↦ predItoIntegral (μ := μ) T hBmeas hp₃ t ω)
    (Y' := fun t ω ↦ predItoIntegral (μ := μ) T hBmeas hp₁ t ω
      + predItoIntegral (μ := μ) T hBmeas hp₂ t ω)
    (g := fun t n ↦ riemannσ (B := B) θ₃ t n)
    (ae_continuousOn_predItoIntegral hB T hBmeas hBcont hp₃ hc₃) ?_ ?_ ?_
  · filter_upwards [ae_continuousOn_predItoIntegral hB T hBmeas hBcont hp₁ hc₁,
      ae_continuousOn_predItoIntegral hB T hBmeas hBcont hp₂ hc₂] with ω h1 h2
    exact h1.add h2
  · intro t ht
    exact tendstoInMeasure_riemannσ_predItoIntegral hB T hBmeas hBcont hp₃ hc₃ ht.2
  · intro t ht
    refine (TendstoInMeasure.add
      (tendstoInMeasure_riemannσ_predItoIntegral hB T hBmeas hBcont hp₁ hc₁ ht.2)
      (tendstoInMeasure_riemannσ_predItoIntegral hB T hBmeas hBcont hp₂ hc₂ ht.2)).congr_left
        fun n ↦ ?_
    filter_upwards [h] with ω hω
    exact (riemannσ_add_of_eq (B := B) (T := t) (ω := ω) (θ := θ₃) (θ₁ := θ₁) (θ₂ := θ₂)
      (fun s hs ↦ hω s ⟨hs.1, hs.2.trans ht.2⟩) n).symm

/-! ### Itô's formula for `x ↦ x²/2` -/

include hB hBcont in
/-- A product of the Itô process with an adapted continuous process is predictable. -/
theorem isStronglyPredictable_localItoProcess_mul {σ b w : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω)
    (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
    (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) (x₀ : ℝ)
    (hw_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (w t))
    (hw_cont : ∀ ω, Continuous fun t : ℝ≥0 ↦ w t ω) :
    IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦
      localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω * w s ω :=
  (isStronglyPredictable_localItoProcess hB T hBmeas hBcont hadap hcont hb_adap hb_cont x₀).mul
    (isStronglyPredictable_of_bdd_adapted_cont hBmeas hw_adap hw_cont)

include hB hBcont in
/-- **Itô's formula for `x ↦ x²/2`**: for `X = x₀ + ∫ b ds + ∫ σ dB` as in
`ito_formula_adapted_unbounded_process`, almost surely, at every `t ∈ [0, T]` at once,
`X_t²/2 = x₀²/2 + ∫₀ᵗ (X b + ½ σ²) ds + (∫ X σ dB)_t`. The case `f(x) = x²/2` of
`ito_formula_adapted_unbounded_C2_process`. -/
theorem ito_half_sq_process {σ b : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω)
    (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
    (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) (x₀ : ℝ) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b t ω
          * localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b t ω / 2
        = x₀ * x₀ / 2
          + ∫ s in Ioc 0 t, (localItoProcess (μ := μ) T hBmeas hadap hcont x₀ b s ω * b s ω
              + 1 / 2 * (1 * σ s ω ^ 2)) ∂timeMeasure
          + predItoIntegral (μ := μ) T hBmeas
              (isStronglyPredictable_localItoProcess_mul hB T hBmeas hBcont hadap hcont hb_adap
                hb_cont x₀ hadap hcont) t ω := by
  have hf (x : ℝ) : HasDerivAt (fun x : ℝ ↦ x * x / 2) x x := by
    convert ((hasDerivAt_id' x).mul (hasDerivAt_id' x)).div_const 2 using 1
    ring
  have h := ito_formula_adapted_unbounded_C2_process hB T hBmeas hBcont hadap hcont hb_adap
    hb_cont x₀ (f := fun x ↦ x * x / 2) (f' := fun x ↦ x) (f'' := fun _ ↦ 1) hf
    (fun x ↦ hasDerivAt_id' x) continuous_const
  filter_upwards [h] with ω hω t ht
  exact hω t ht

/-! ### The product rule -/

include hB hBcont in
/-- **The product rule from three Itô formulas for `x ↦ x²/2`.** Let `X`, `Y`, `Z` be processes
with `Z = X + Y` on `[0, T]` and paths almost surely continuous there, and suppose each satisfies
`ito_half_sq_process` for its own coefficients (`σ, b`; `τ, c`; `σ + τ, b + c`) with predictable
integrands `X σ`, `Y τ`, `Z (σ + τ)`. Then `XY` satisfies the product rule, with the stochastic
integral of the predictable integrand `X τ + Y σ`. Polarisation: `XY = Z²/2 − X²/2 − Y²/2`,
with additivity of the drift integral and of `predItoIntegral`. -/
theorem ito_product_rule_of_half_sq {σ τ b c X Y Z : ℝ≥0 → Ω → ℝ} {x₀ y₀ : ℝ}
    (hσc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω) (hτc : ∀ ω, Continuous fun t : ℝ≥0 ↦ τ t ω)
    (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) (hc_cont : ∀ ω, Continuous fun s ↦ c s ω)
    (hpXσ : IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦ X s ω * σ s ω)
    (hpYτ : IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦ Y s ω * τ s ω)
    (hpZρ : IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦ Z s ω * (σ s ω + τ s ω))
    (hpθ : IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦ X s ω * τ s ω + Y s ω * σ s ω)
    (hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc 0 T))
    (hYc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Y t ω) (Icc 0 T))
    (hZeq : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, Z t ω = X t ω + Y t ω)
    (hXf : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, X t ω * X t ω / 2 = x₀ * x₀ / 2
      + ∫ s in Ioc 0 t, (X s ω * b s ω + 1 / 2 * (1 * σ s ω ^ 2)) ∂timeMeasure
      + predItoIntegral (μ := μ) T hBmeas hpXσ t ω)
    (hYf : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, Y t ω * Y t ω / 2 = y₀ * y₀ / 2
      + ∫ s in Ioc 0 t, (Y s ω * c s ω + 1 / 2 * (1 * τ s ω ^ 2)) ∂timeMeasure
      + predItoIntegral (μ := μ) T hBmeas hpYτ t ω)
    (hZf : ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, Z t ω * Z t ω / 2 = (x₀ + y₀) * (x₀ + y₀) / 2
      + ∫ s in Ioc 0 t, (Z s ω * (b s ω + c s ω) + 1 / 2 * (1 * (σ s ω + τ s ω) ^ 2))
        ∂timeMeasure
      + predItoIntegral (μ := μ) T hBmeas hpZρ t ω) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      X t ω * Y t ω = x₀ * y₀
        + ∫ s in Ioc 0 t, (X s ω * c s ω + Y s ω * b s ω + σ s ω * τ s ω) ∂timeMeasure
        + predItoIntegral (μ := μ) T hBmeas hpθ t ω := by
  have hpXY : IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ X s ω * σ s ω + Y s ω * τ s ω := hpXσ.add hpYτ
  have hZc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Z t ω) (Icc 0 T) := by
    filter_upwards [hXc, hYc, hZeq] with ω h1 h2 h3
    exact (h1.add h2).congr fun t ht ↦ h3 t ht
  have hcXσ : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ X s ω * σ s ω) (Icc 0 T) :=
    hXc.mono fun ω h ↦ h.mul (hσc ω).continuousOn
  have hcYτ : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ Y s ω * τ s ω) (Icc 0 T) :=
    hYc.mono fun ω h ↦ h.mul (hτc ω).continuousOn
  have hcXY : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ X s ω * σ s ω + Y s ω * τ s ω) (Icc 0 T) := by
    filter_upwards [hcXσ, hcYτ] with ω h1 h2
    exact h1.add h2
  have hcθ : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ X s ω * τ s ω + Y s ω * σ s ω) (Icc 0 T) := by
    filter_upwards [hXc, hYc] with ω h1 h2
    exact (h1.mul (hτc ω).continuousOn).add (h2.mul (hσc ω).continuousOn)
  have hcZρ : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ Z s ω * (σ s ω + τ s ω)) (Icc 0 T) :=
    hZc.mono fun ω h ↦ h.mul ((hσc ω).add (hτc ω)).continuousOn
  have pXY := ae_predItoIntegral_add hB T hBmeas hBcont hpXσ hpYτ hpXY hcXσ hcYτ hcXY
    (.of_forall fun ω s _ ↦ rfl)
  have pZ := ae_predItoIntegral_add hB T hBmeas hBcont hpXY hpθ hpZρ hcXY hcθ hcZρ (by
    filter_upwards [hZeq] with ω hω s hs
    simp only [hω s hs]
    ring)
  filter_upwards [hXf, hYf, hZf, hZeq, pXY, pZ, hXc, hYc] with ω hX hY hZ hZe h1 h2 hxc hyc t ht
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have cσ : ContinuousOn (fun s ↦ σ s ω) (Icc 0 T) := (hσc ω).continuousOn
  have cτ : ContinuousOn (fun s ↦ τ s ω) (Icc 0 T) := (hτc ω).continuousOn
  have cb : ContinuousOn (fun s ↦ b s ω) (Icc 0 T) := (hb_cont ω).continuousOn
  have cc : ContinuousOn (fun s ↦ c s ω) (Icc 0 T) := (hc_cont ω).continuousOn
  have cσ2 : ContinuousOn (fun s ↦ 1 / 2 * (1 * σ s ω ^ 2)) (Icc 0 T) :=
    continuousOn_const.mul (continuousOn_const.mul (cσ.pow 2))
  have cτ2 : ContinuousOn (fun s ↦ 1 / 2 * (1 * τ s ω ^ 2)) (Icc 0 T) :=
    continuousOn_const.mul (continuousOn_const.mul (cτ.pow 2))
  have hcA : ContinuousOn (fun s ↦ X s ω * b s ω + 1 / 2 * (1 * σ s ω ^ 2)) (Icc 0 t) :=
    ((hxc.mul cb).add cσ2).mono hsub
  have hcB : ContinuousOn (fun s ↦ Y s ω * c s ω + 1 / 2 * (1 * τ s ω ^ 2)) (Icc 0 t) :=
    ((hyc.mul cc).add cτ2).mono hsub
  have hcC : ContinuousOn (fun s ↦ X s ω * c s ω + Y s ω * b s ω + σ s ω * τ s ω) (Icc 0 t) :=
    (((hxc.mul cc).add (hyc.mul cb)).add (cσ.mul cτ)).mono hsub
  have hD : (∫ s in Ioc 0 t, (Z s ω * (b s ω + c s ω) + 1 / 2 * (1 * (σ s ω + τ s ω) ^ 2))
        ∂timeMeasure)
      = (∫ s in Ioc 0 t, (X s ω * b s ω + 1 / 2 * (1 * σ s ω ^ 2)) ∂timeMeasure)
        + (∫ s in Ioc 0 t, (Y s ω * c s ω + 1 / 2 * (1 * τ s ω ^ 2)) ∂timeMeasure)
        + ∫ s in Ioc 0 t, (X s ω * c s ω + Y s ω * b s ω + σ s ω * τ s ω) ∂timeMeasure := by
    refine Eq.trans ?_ (setIntegral_add_add hcA hcB hcC)
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    simp only [hZe s ⟨zero_le, hs.2.trans ht.2⟩]
    ring
  exact product_algebra (hZe t ht) (hX t ht) (hY t ht) (hZ t ht) hD (h1 t ht) (h2 t ht)

variable {σ τ b c : ℝ≥0 → Ω → ℝ}
  (hσa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hσc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω)
  (hτa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (τ t))
  (hτc : ∀ ω, Continuous fun t : ℝ≥0 ↦ τ t ω)
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω)
  (hc_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (c t))
  (hc_cont : ∀ ω, Continuous fun s ↦ c s ω) (x₀ y₀ : ℝ)

include hB hBcont hσa hσc hτa hτc hb_adap hb_cont hc_adap hc_cont in
/-- **The cross integrand `X τ + Y σ` of the product rule is predictable.** -/
theorem productIntegrand_isStronglyPredictable :
    IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦
      localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b s ω * τ s ω
        + localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c s ω * σ s ω :=
  (isStronglyPredictable_localItoProcess_mul hB T hBmeas hBcont hσa hσc hb_adap hb_cont x₀
    hτa hτc).add
    (isStronglyPredictable_localItoProcess_mul hB T hBmeas hBcont hτa hτc hc_adap hc_cont y₀
    hσa hσc)

include hB hBcont hσa hσc hτa hτc hb_adap hb_cont hc_adap hc_cont in
/-- **The product rule for two Itô processes driven by one Brownian motion, as an identity of
processes.** Let `B` be a Brownian motion with every path continuous, `σ`, `τ`, `b`, `c` adapted
to its natural filtration with every path continuous, `X = x₀ + ∫ b ds + ∫ σ dB` and
`Y = y₀ + ∫ c ds + ∫ τ dB` (`localItoProcess`). Almost surely, for every `t ∈ [0, T]` at once,

`X_t Y_t = x₀ y₀ + ∫₀ᵗ (X c + Y b + σ τ)(s) ds + (∫ (X τ + Y σ) dB)_t`,

the stochastic integral being `predItoIntegral` of the predictable integrand `X τ + Y σ`. In
differential form `d(XY) = X dY + Y dX + σ τ dt`, where `σ τ dt = d⟨X, Y⟩`. No bound on the
coefficients is assumed. -/
theorem ito_product_rule_process :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b t ω
          * localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c t ω
        = x₀ * y₀
          + ∫ s in Ioc 0 t, (localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b s ω * c s ω
              + localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c s ω * b s ω
              + σ s ω * τ s ω) ∂timeMeasure
          + predItoIntegral (μ := μ) T hBmeas
              (productIntegrand_isStronglyPredictable hB T hBmeas hBcont hσa hσc hτa hτc hb_adap
                hb_cont hc_adap hc_cont x₀ y₀) t ω := by
  have hρa : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
      (fun ω ↦ σ t ω + τ t ω) := fun t ↦ (hσa t).add (hτa t)
  have hρc : ∀ ω, Continuous fun t : ℝ≥0 ↦ σ t ω + τ t ω := fun ω ↦ (hσc ω).add (hτc ω)
  have hba : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
      (fun ω ↦ b t ω + c t ω) := fun t ↦ (hb_adap t).add (hc_adap t)
  have hbc : ∀ ω, Continuous fun s : ℝ≥0 ↦ b s ω + c s ω := fun ω ↦ (hb_cont ω).add (hc_cont ω)
  exact ito_product_rule_of_half_sq hB T hBmeas hBcont hσc hτc hb_cont hc_cont
    (isStronglyPredictable_localItoProcess_mul hB T hBmeas hBcont hσa hσc hb_adap hb_cont x₀
      hσa hσc)
    (isStronglyPredictable_localItoProcess_mul hB T hBmeas hBcont hτa hτc hc_adap hc_cont y₀
      hτa hτc)
    (isStronglyPredictable_localItoProcess_mul hB T hBmeas hBcont hρa hρc hba hbc (x₀ + y₀)
      hρa hρc)
    (productIntegrand_isStronglyPredictable hB T hBmeas hBcont hσa hσc hτa hτc hb_adap hb_cont
      hc_adap hc_cont x₀ y₀)
    (ae_continuousOn_localItoProcess hB T hBmeas hBcont hσa hσc hb_cont x₀)
    (ae_continuousOn_localItoProcess hB T hBmeas hBcont hτa hτc hc_cont y₀)
    (ae_localItoProcess_add hB T hBmeas hBcont hσa hσc hτa hτc hρa hρc hb_cont hc_cont x₀ y₀)
    (ito_half_sq_process hB T hBmeas hBcont hσa hσc hb_adap hb_cont x₀)
    (ito_half_sq_process hB T hBmeas hBcont hτa hτc hc_adap hc_cont y₀)
    (ito_half_sq_process hB T hBmeas hBcont hρa hρc hba hbc (x₀ + y₀))

include hB hBcont hσa hσc hτa hτc hb_adap hb_cont hc_adap hc_cont in
/-- **The product rule with the stochastic term split**: `d(XY) = X dY + Y dX + σ τ dt` with
`X dY = X c dt + X τ dB` and `Y dX = Y b dt + Y σ dB`. For `X`, `Y` as in
`ito_product_rule_process`, almost surely, for every `t ∈ [0, T]` at once,

`X_t Y_t = x₀ y₀ + ∫₀ᵗ (X c + Y b + σ τ)(s) ds + (∫ X τ dB)_t + (∫ Y σ dB)_t`. -/
theorem ito_product_rule_process_split :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T,
      localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b t ω
          * localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c t ω
        = x₀ * y₀
          + ∫ s in Ioc 0 t, (localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b s ω * c s ω
              + localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c s ω * b s ω
              + σ s ω * τ s ω) ∂timeMeasure
          + predItoIntegral (μ := μ) T hBmeas
              (isStronglyPredictable_localItoProcess_mul hB T hBmeas hBcont hσa hσc hb_adap
                hb_cont x₀ hτa hτc) t ω
          + predItoIntegral (μ := μ) T hBmeas
              (isStronglyPredictable_localItoProcess_mul hB T hBmeas hBcont hτa hτc hc_adap
                hc_cont y₀ hσa hσc) t ω := by
  have hXc := ae_continuousOn_localItoProcess hB T hBmeas hBcont hσa hσc hb_cont x₀
  have hYc := ae_continuousOn_localItoProcess hB T hBmeas hBcont hτa hτc hc_cont y₀
  have hc₁ : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦
      localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b s ω * τ s ω) (Icc 0 T) :=
    hXc.mono fun ω h ↦ h.mul (hτc ω).continuousOn
  have hc₂ : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦
      localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c s ω * σ s ω) (Icc 0 T) :=
    hYc.mono fun ω h ↦ h.mul (hσc ω).continuousOn
  have hc₃ : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦
      localItoProcess (μ := μ) T hBmeas hσa hσc x₀ b s ω * τ s ω
        + localItoProcess (μ := μ) T hBmeas hτa hτc y₀ c s ω * σ s ω) (Icc 0 T) := by
    filter_upwards [hc₁, hc₂] with ω h1 h2
    exact h1.add h2
  filter_upwards [ito_product_rule_process hB T hBmeas hBcont hσa hσc hτa hτc hb_adap hb_cont
    hc_adap hc_cont x₀ y₀, ae_predItoIntegral_add hB T hBmeas hBcont
    (isStronglyPredictable_localItoProcess_mul hB T hBmeas hBcont hσa hσc hb_adap hb_cont x₀
      hτa hτc)
    (isStronglyPredictable_localItoProcess_mul hB T hBmeas hBcont hτa hτc hc_adap hc_cont y₀
      hσa hσc)
    (productIntegrand_isStronglyPredictable hB T hBmeas hBcont hσa hσc hτa hτc hb_adap hb_cont
      hc_adap hc_cont x₀ y₀) hc₁ hc₂ hc₃ (.of_forall fun ω s _ ↦ rfl)] with ω h1 h2 t ht
  rw [h1 t ht, h2 t ht]
  ring

end ItoFormulaAdapted
end MathFin
