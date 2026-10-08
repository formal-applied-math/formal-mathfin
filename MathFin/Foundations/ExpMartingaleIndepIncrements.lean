/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# The exponential martingale of a process with independent increments

Let a real process `X` be adapted to a filtration `𝓕`, with each increment `X_t − X_s` (`s ≤ t`)
independent of `𝓕_s` and with exponential moment `𝔼[e^{X_t − X_s}] = e^{ψ(t) − ψ(s)}` for a
deterministic `ψ`. Then `t ↦ e^{X_t − ψ(t)}` is an `𝓕`-martingale. The increment factor
`e^{ψ(s) − ψ(t)}·e^{X_t − X_s}` is independent of `𝓕_s`, so its conditional expectation is its
mean, `1` (`condExp_indep_eq`); the factor `e^{X_s − ψ(s)}` is known at time `s` and comes out of
the conditional expectation (`condExp_mul_of_stronglyMeasurable_left`).

For a Lévy process `ψ(t) = tκ(1)` is linear in `t`, with `κ` the cumulant generating function of
`X_1`. The Wald martingale of Brownian motion
(`Foundations/BrownianMartingale.waldExponential_isMartingale`) is the case of Gaussian increments;
`BlackScholes/JumpDiffusionProcess.lean` applies the lemma to the log-price of a jump-diffusion.

## Main results

* `martingale_exp_sub_of_indep_increments`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] [Preorder ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → ℝ}

/-- **The exponential martingale of a process with independent increments.** If `X` is adapted
to `𝓕`, each increment `X_t − X_s` (`s ≤ t`) is independent of `𝓕_s` with
`𝔼[e^{X_t − X_s}] = e^{ψ(t) − ψ(s)}`, and each `e^{X_t}` is integrable, then `t ↦ e^{X_t − ψ(t)}`
is an `𝓕`-martingale. -/
theorem martingale_exp_sub_of_indep_increments {ψ : ι → ℝ} (hX : StronglyAdapted 𝓕 X)
    (hindep : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) (𝓕 s) P)
    (hint : ∀ t, Integrable (fun ω ↦ Real.exp (X t ω)) P)
    (hmean : ∀ s t, s ≤ t → ∫ ω, Real.exp (X t ω - X s ω) ∂P = Real.exp (ψ t - ψ s)) :
    Martingale (fun t ω ↦ Real.exp (X t ω - ψ t)) 𝓕 P := by
  refine ⟨fun t ↦ Real.continuous_exp.comp_stronglyMeasurable
    ((hX t).sub stronglyMeasurable_const), fun s t hst ↦ ?_⟩
  have hD : Measurable fun ω ↦ X t ω - X s ω :=
    ((hX t).mono (𝓕.le t)).measurable.sub ((hX s).mono (𝓕.le s)).measurable
  have hD_int : Integrable (fun ω ↦ Real.exp (X t ω - X s ω)) P :=
    Integrable.of_integral_ne_zero (by rw [hmean s t hst]; exact (Real.exp_pos _).ne')
  have hE : StronglyMeasurable[𝓕 s] fun ω ↦ Real.exp (X s ω - ψ s) :=
    Real.continuous_exp.comp_stronglyMeasurable ((hX s).sub stronglyMeasurable_const)
  have hsplit : (fun ω ↦ Real.exp (X t ω - ψ t))
      = (fun ω ↦ Real.exp (X s ω - ψ s))
        * fun ω ↦ Real.exp (ψ s - ψ t) * Real.exp (X t ω - X s ω) := by
    funext ω
    show Real.exp (X t ω - ψ t)
      = Real.exp (X s ω - ψ s) * (Real.exp (ψ s - ψ t) * Real.exp (X t ω - X s ω))
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  -- the increment factor is independent of `𝓕_s`: its conditional expectation is its mean, `1`
  have hG : P[fun ω ↦ Real.exp (ψ s - ψ t) * Real.exp (X t ω - X s ω) | 𝓕 s]
      =ᵐ[P] fun _ ↦ (1 : ℝ) := by
    have hm : StronglyMeasurable[MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance]
        fun ω ↦ Real.exp (ψ s - ψ t) * Real.exp (X t ω - X s ω) :=
      ((measurable_const.mul Real.continuous_exp.measurable).comp
        (Measurable.of_comap_le le_rfl)).stronglyMeasurable
    have h := condExp_indep_eq hD.comap_le (𝓕.le s) hm (hindep s t hst)
    rwa [integral_const_mul, hmean s t hst, ← Real.exp_add,
      show ψ s - ψ t + (ψ t - ψ s) = 0 by ring, Real.exp_zero] at h
  -- `e^{X_s − ψ(s)}` is known at time `s` and comes out
  have hpull := condExp_mul_of_stronglyMeasurable_left hE
    (by rw [← hsplit]; simpa only [Real.exp_sub] using (hint t).div_const (Real.exp (ψ t)))
    (hD_int.const_mul (Real.exp (ψ s - ψ t)))
  show P[fun ω ↦ Real.exp (X t ω - ψ t) | 𝓕 s] =ᵐ[P] fun ω ↦ Real.exp (X s ω - ψ s)
  rw [hsplit]
  filter_upwards [hpull, hG] with ω h1 h2
  rw [h1, Pi.mul_apply, h2, mul_one]

end MathFin
