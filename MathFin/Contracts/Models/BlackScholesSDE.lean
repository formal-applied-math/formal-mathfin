/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Models.BlackScholesAsian
public import MathFin.Foundations.ItoFormulaGBM
public import MathFin.Foundations.ItoFormulaUnrestrictedLocMart

/-!
# The Black–Scholes contract model solves `dS = rS dt + σS dB`

Every Black–Scholes contract theorem prices on `BlackScholes.pathAssets`, the geometric Brownian
path `S_u = S₀ exp((r − σ²/2)u + σ B_u)` (`Contracts/Models/BlackScholesAsian.lean`). Here it is
shown to be a solution of the stochastic differential equation the name promises:

  `S_t = S₀ + ∫₀ᵗ r S_s ds + ∫₀ᵗ σ S_s dB_s`

almost surely, for all `t ≤ T` at once, for a pre-Brownian motion `B` with continuous paths. The
stochastic integral is the library's `predItoIntegral` of the predictable integrand `σ S`.

The proof is Itô's formula as an identity of processes
(`ItoFormulaAdapted.ito_formula_adapted_unbounded_process`) for the smooth value function
`gbmValue S₀ r σ t x = S₀ exp((r − σ²/2)t + σ x)` evaluated along the Brownian path
(`B` is the Itô integral of `1`, `ae_localItoIntegral_one_eq`): the drift of the formula,
`f_t + ½ f_xx = (r − σ²/2) f + ½ σ² f = r f`, is exactly `r S`, and the `x`-derivative `σ f` is the
integrand. The same decomposition is `ito_formula_gbm` for a single time; this statement is the
process-level, contract-facing form.

Not proved here: that `pathAssets` is *the* solution (pathwise or `L²` uniqueness through the
Picard fixed point of `SDEExistence`); only that it solves the equation.

## Main results

* `BlackScholes.isStronglyPredictable_diffusion_pathAssets`: the diffusion coefficient `σ S` is a
  predictable process.
* `BlackScholes.pathAssets_solves_sde`: almost surely, for all `t ∈ [0, T]`,
  `S_t = S₀ + ∫₀ᵗ r S_s ds + (∫ σ S dB)_t`.

## References

* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 4.4

## Tags

geometric Brownian motion, stochastic differential equation, Black–Scholes model, Itô formula,
MSC 60H10, MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ItoIntegralL2 ItoFormulaAdapted ItoIntegralLocalised
open scoped NNReal

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The diffusion coefficient `σ S` of the Black–Scholes path is predictable.** It is a jointly
continuous function of time and of the Brownian path, which is predictable (adapted and
left-continuous). -/
theorem isStronglyPredictable_diffusion_pathAssets (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (S_0 r σ : ℝ) :
    IsStronglyPredictable (natFiltration hBmeas)
      fun (s : ℝ≥0) ω ↦ σ * pathAssets S_0 r σ B () s ω := by
  have hBp : IsStronglyPredictable (natFiltration hBmeas) B :=
    StronglyAdapted.isStronglyPredictable_of_leftContinuous (stronglyAdapted_natFiltration hBmeas)
      fun ω _ ↦ (hBcont ω).continuousWithinAt
  have ht : IsStronglyPredictable (natFiltration hBmeas) fun (s : ℝ≥0) (_ : Ω) ↦ (s : ℝ) :=
    StronglyAdapted.isStronglyPredictable_of_leftContinuous (fun _ ↦ stronglyMeasurable_const)
      fun _ _ ↦ NNReal.continuous_coe.continuousWithinAt
  have hg : Continuous fun p : ℝ × ℝ ↦ σ * gbmValue S_0 r σ p.1 p.2 := by
    unfold gbmValue; fun_prop
  exact hg.comp_stronglyMeasurable (StronglyMeasurable.prodMk ht hBp)

/-- **The Black–Scholes contract model solves `dS = rS dt + σS dB`.** For a pre-Brownian motion
`B` with continuous paths, almost surely, for every `t ∈ [0, T]` at once,

  `S_t = S₀ + ∫₀ᵗ r S_s ds + (∫ σ S dB)_t`,

where `S = pathAssets S₀ r σ B ()` and the stochastic integral is `predItoIntegral` of the
predictable integrand `σ S` (`isStronglyPredictable_diffusion_pathAssets`). -/
theorem pathAssets_solves_sde (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (T : ℝ≥0) (S_0 r σ : ℝ) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ≥0) T,
      pathAssets S_0 r σ B () t ω
        = S_0 + ∫ s in Ioc 0 t, r * pathAssets S_0 r σ B () s ω ∂timeMeasure
          + predItoIntegral (μ := μ) T hBmeas
            (isStronglyPredictable_diffusion_pathAssets hBmeas hBcont S_0 r σ) t ω := by
  set f : ℝ → ℝ → ℝ := fun t x ↦ gbmValue S_0 r σ t x with hf
  set f_x : ℝ → ℝ → ℝ := fun t x ↦ σ * gbmValue S_0 r σ t x with hfx
  set f_xx : ℝ → ℝ → ℝ := fun t x ↦ σ ^ 2 * gbmValue S_0 r σ t x with hfxx
  set f_t : ℝ → ℝ → ℝ := fun t x ↦ (r - σ ^ 2 / 2) * gbmValue S_0 r σ t x with hft
  have hf_t (t x : ℝ) : HasDerivAt (fun s ↦ f s x) (f_t t x) t :=
    hasDerivAt_gbmValue_time S_0 r σ t x
  have hf_x (t x : ℝ) : HasDerivAt (fun u ↦ f t u) (f_x t x) x :=
    hasDerivAt_gbmValue_space S_0 r σ t x
  have hf_xx (t x : ℝ) : HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x :=
    hasDerivAt_gbmValue_space_space S_0 r σ t x
  have hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2 := by
    simp only [hft]; unfold gbmValue; fun_prop
  have hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2 := by
    simp only [hfx]; unfold gbmValue; fun_prop
  have hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2 := by
    simp only [hfxx]; unfold gbmValue; fun_prop
  set Xp : ℝ≥0 → Ω → ℝ := localItoProcess (μ := μ) T hBmeas
    (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0
    (fun _ _ ↦ (0 : ℝ)) with hXp
  -- Itô's formula for `B = ∫ 1 dB`
  have hIto := ito_formula_adapted_unbounded_process hB T hBmeas hBcont
    (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
    (b := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0
    hf_t hf_x hf_xx hf_t_cont hf_x_cont hf_xx_cont
  have hX := ae_localItoIntegral_one_eq hB T hBmeas hBcont
  have hXc := ae_continuousOn_localItoProcess hB T hBmeas hBcont
    (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
    (b := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ continuous_const) 0
  have hθX := itoIntegrand_isStronglyPredictable hB T hBmeas hBcont
    (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const)
    (b := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) 0
    hf_x_cont
  have hθXc : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ f_x s (Xp s ω) * 1) (Icc 0 T) :=
    hXc.mono fun ω h ↦ (hf_x_cont.comp_continuousOn
      (NNReal.continuous_coe.continuousOn.prodMk h)).mul continuousOn_const
  have hHc : ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ≥0 ↦ σ * pathAssets S_0 r σ B () s ω) (Icc 0 T) :=
    ae_of_all _ fun ω ↦
      (hf_x_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))).continuousOn
  have hXs (ω : Ω) (hω : ∀ t ∈ Icc (0 : ℝ≥0) T, localItoIntegral (μ := μ) T hBmeas
      (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) t ω
        = B t ω) (s : ℝ≥0) (hs : s ∈ Icc (0 : ℝ≥0) T) : Xp s ω = B s ω := by
    simp [Xp, localItoProcess, AdaptedDrift.driftPath, hω s hs]
  have hcongr := ae_predItoIntegral_congr hB T hBmeas hBcont hθX
    (by simpa only [mul_one] using hθXc)
    (isStronglyPredictable_diffusion_pathAssets hBmeas hBcont S_0 r σ) hHc
    (by
      filter_upwards [hX] with ω hω s hs
      change f_x s (Xp s ω) * 1 = σ * pathAssets S_0 r σ B () s ω
      rw [hXs ω hω s hs, mul_one]
      rfl)
  filter_upwards [hIto, hX, hcongr] with ω h1 hXω hc t ht
  have e2 : f (t : ℝ) (Xp t ω) = pathAssets S_0 r σ B () t ω := by
    rw [hXs ω hXω t ht]
    rfl
  have e3 : f 0 0 = S_0 := by simp [hf, gbmValue]
  have hint : ∫ s in Ioc 0 t, (f_t s (Xp s ω) + f_x s (Xp s ω) * 0
        + 1 / 2 * (f_xx s (Xp s ω) * 1 ^ 2)) ∂timeMeasure
      = ∫ s in Ioc 0 t, r * pathAssets S_0 r σ B () s ω ∂timeMeasure := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    have hsT : s ∈ Icc (0 : ℝ≥0) T := ⟨zero_le, hs.2.trans ht.2⟩
    change (r - σ ^ 2 / 2) * gbmValue S_0 r σ s (Xp s ω) + σ * gbmValue S_0 r σ s (Xp s ω) * 0
        + 1 / 2 * (σ ^ 2 * gbmValue S_0 r σ s (Xp s ω) * 1 ^ 2) = _
    rw [hXs ω hXω s hsT]
    change _ = r * gbmValue S_0 r σ s (B s ω)
    ring
  have key := h1 t ht
  have hc' := hc t ht
  linarith [key, hint, hc', e2, e3]

end MathFin.Contracts.BlackScholes
