/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.JumpDiffusionCanonical
public import MathFin.Foundations.ExpMartingaleIndepIncrements

/-!
# The jump-diffusion price process

The other jump-diffusion files model only the price at maturity. Here the log-price is a process
`X` on `[0, ∞)`, adapted to a filtration `𝓕`, starting at `0`, whose increment `X_t − X_s` over
`[s, t]` is independent of `𝓕_s` and has the law of a jump-diffusion log-return over `t − s`: a
drift `b(t − s)`, a Gaussian part of variance `σ²(t − s)` and a compound-Poisson part with
`Poisson(Λ(t − s))` jumps of law `ν` (`JumpDiffusionProcess`); here `Λ` is a jump rate. The
increments are those of a Lévy process with these characteristics; no path regularity is assumed.
Without jumps, Brownian motion with drift is such a process
(`IsFilteredPreBrownian.jumpDiffusionProcess`); with jumps its existence is not proved.

The price `S_t = S₀e^{X_t}` discounted at the rate `r` is a martingale exactly at the compensated
drift `b = r − σ²/2 − Λ(𝔼[e^J] − 1)` (`JumpDiffusionProcess.martingale_iff`). The increment's
exponential moment is `e^{(b + σ²/2 + Λ(𝔼[e^J] − 1))(t − s)}`
(`integral_exp_jumpDiffusionIncrementLaw`, computed on the canonical model), so the exponential
martingale of independent increments (`martingale_exp_sub_of_indep_increments`) gives the "if";
conversely a martingale has constant mean, and the mean at time `1` is
`S₀e^{b + σ²/2 + Λ(𝔼[e^J] − 1) − r}`.

## Main results

* `jumpDiffusionIncrementLaw`, `integral_exp_jumpDiffusionIncrementLaw`: the law of a
  jump-diffusion log-return over a time `τ`, and its exponential moment.
* `JumpDiffusionProcess.martingale_iff`: the discounted price is a martingale if and only if the
  drift is compensated.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-! ### The increment law -/

namespace JumpDiffusionHyp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {Λ : ℝ≥0} {Z : Ω → ℝ}
  {N : Ω → ℕ} {J : ℕ → Ω → ℝ}

/-- **The exponential moment of a jump-diffusion log-return**:
`𝔼[e^{bT + σ√T·Z + ∑_{i<N} Jᵢ}] = e^{(b + σ²/2)T + Λ(𝔼[e^J] − 1)}`. It is the discounted
terminal price (`discounted_terminal`) of the model with spot `1`, rate `b + σ²/2` and no drift
correction, undiscounted. -/
lemma integral_exp_logReturn (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) (b σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, rexp (b * T + σ * Real.sqrt T * Z ω + ∑ i ∈ Finset.range (N ω), J i ω) ∂Q
      = rexp ((b + σ ^ 2 / 2) * T + Λ * (∫ ω, rexp (J 0 ω) ∂Q - 1)) := by
  have hpt (ω : Ω) : rexp (b * T + σ * Real.sqrt T * Z ω + ∑ i ∈ Finset.range (N ω), J i ω)
      = rexp ((b + σ ^ 2 / 2) * T) * (rexp (-(b + σ ^ 2 / 2) * T)
        * jumpDiffusionTerminal 1 (b + σ ^ 2 / 2) σ T 0 (Z ω) (N ω) (fun i ↦ J i ω)) := by
    rw [jumpDiffusionTerminal, one_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc ∫ ω, rexp (b * T + σ * Real.sqrt T * Z ω + ∑ i ∈ Finset.range (N ω), J i ω) ∂Q
      = rexp ((b + σ ^ 2 / 2) * T) * ∫ ω, rexp (-(b + σ ^ 2 / 2) * T)
          * jumpDiffusionTerminal 1 (b + σ ^ 2 / 2) σ T 0 (Z ω) (N ω) (fun i ↦ J i ω) ∂Q := by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ hpt)
    _ = rexp ((b + σ ^ 2 / 2) * T) * (1 * rexp (-0 + Λ * (∫ ω, rexp (J 0 ω) ∂Q - 1))) := by
        rw [h.discounted_terminal hJ 1 (b + σ ^ 2 / 2) σ hT 0]
    _ = rexp ((b + σ ^ 2 / 2) * T + Λ * (∫ ω, rexp (J 0 ω) ∂Q - 1)) := by
        rw [one_mul, neg_zero, zero_add, Real.exp_add]

end JumpDiffusionHyp

/-- The law of a jump-diffusion log-return over a time `τ`: the drift `bτ`, a Gaussian part
`σ√τ·Z` and a compound-Poisson part, a `Poisson(Λτ)` number of independent jumps of law `ν`, all
independent. It is the law of `bτ + σ√τ·ω₁ + ∑_{i<ω₂} ω₃ᵢ` under the canonical model
`jumpDiffusionMeasure (Λτ) ν`. -/
noncomputable def jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) :
    Measure ℝ :=
  (jumpDiffusionMeasure (Λ * τ) ν).map fun ω ↦
    b * τ + σ * Real.sqrt τ * ω.1 + ∑ i ∈ Finset.range ω.2.1, ω.2.2 i

/-- The log-return `bτ + σ√τ·ω₁ + ∑_{i<ω₂} ω₃ᵢ` is measurable on the canonical space. -/
lemma measurable_jumpDiffusionLogReturn (b σ : ℝ) (τ : ℝ≥0) :
    Measurable fun ω : ℝ × ℕ × (ℕ → ℝ) ↦
      b * τ + σ * Real.sqrt τ * ω.1 + ∑ i ∈ Finset.range ω.2.1, ω.2.2 i := by
  have hsum : Measurable fun p : ℕ × (ℕ → ℝ) ↦ ∑ i ∈ Finset.range p.1, p.2 i :=
    measurable_from_prod_countable_right fun n ↦
      show Measurable fun j : ℕ → ℝ ↦ ∑ i ∈ Finset.range n, j i by fun_prop
  exact (measurable_const.add (measurable_const.mul measurable_fst)).add (hsum.comp measurable_snd)

instance isProbabilityMeasure_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (τ : ℝ≥0) :
    IsProbabilityMeasure (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
  Measure.isProbabilityMeasure_map (measurable_jumpDiffusionLogReturn b σ τ).aemeasurable

/-- **The exponential moment of the jump-diffusion increment law**:
`∫ e^x d(law over τ) = e^{(b + σ²/2 + Λ(𝔼[e^J] − 1))τ}` when `𝔼[e^J] < ∞` under the jump law `ν`.
On the canonical model this is `JumpDiffusionHyp.integral_exp_logReturn`. -/
theorem integral_exp_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν) (τ : ℝ≥0) :
    ∫ x, rexp x ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      = rexp ((b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1)) * τ) := by
  have hφ := measurable_jumpDiffusionLogReturn b σ τ
  rw [jumpDiffusionIncrementLaw, integral_map hφ.aemeasurable measurable_exp.aestronglyMeasurable,
    (jumpDiffusionHyp_canonical (Λ * τ) ν).1.integral_exp_logReturn
      (integrable_exp_canonical_jump hν) b σ (NNReal.coe_nonneg τ),
    integral_exp_canonical_jump (Λ * τ) ν, NNReal.coe_mul]
  congr 1
  ring

/-- The exponential of the log-return is integrable when `𝔼[e^J] < ∞`: its integral is
positive. -/
lemma integrable_exp_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν) (τ : ℝ≥0) :
    Integrable rexp (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
  Integrable.of_integral_ne_zero (by
    rw [integral_exp_jumpDiffusionIncrementLaw b σ Λ hν τ]
    exact (Real.exp_pos _).ne')

/-! ### The process -/

/-- **A jump-diffusion log-price process.** `X` is adapted to the filtration `𝓕`, starts at `0`,
and each increment `X_t − X_s` (`s ≤ t`) is independent of `𝓕_s` and has the law of a
jump-diffusion log-return over `t − s` (`jumpDiffusionIncrementLaw`): drift `b(t − s)`, a
Gaussian part of variance `σ²(t − s)`, and a compound-Poisson part with `Poisson(Λ(t − s))` jumps
of law `ν`. The price is `S_t = S₀e^{X_t}`. The structure is a hypothesis: it is satisfied
without jumps (`IsFilteredPreBrownian.jumpDiffusionProcess`), and its existence with jumps is not
proved. -/
structure JumpDiffusionProcess {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) : Prop where
  adapted : StronglyAdapted 𝓕 X
  zero : ∀ᵐ ω ∂P, X 0 ω = 0
  indep : ∀ s t, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) (𝓕 s) P
  law : ∀ s t, s ≤ t →
    HasLaw (fun ω ↦ X t ω - X s ω) (jumpDiffusionIncrementLaw b σ Λ ν (t - s)) P

namespace JumpDiffusionProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b σ : ℝ} {Λ : ℝ≥0} {ν : Measure ℝ}

/-- The increment over `[s, t]` has exponential moment
`e^{(b + σ²/2 + Λ(𝔼[e^J] − 1))(t − s)}`. -/
lemma integral_exp_increment (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν]
    (hν : Integrable rexp ν) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, rexp (X t ω - X s ω) ∂P
      = rexp ((b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1)) * (t - s : ℝ≥0)) := by
  rw [← integral_exp_jumpDiffusionIncrementLaw b σ Λ hν (t - s)]
  exact (h.law s t hst).integral_comp measurable_exp.aestronglyMeasurable

/-- `e^{X_t}` is integrable: `X_t = X_t − X_0` almost surely, and the increment has a finite
exponential moment. -/
lemma integrable_exp (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν]
    (hν : Integrable rexp ν) (t : ℝ≥0) : Integrable (fun ω ↦ rexp (X t ω)) P := by
  have h0 : Integrable (fun ω ↦ rexp (X t ω - X 0 ω)) P :=
    Integrable.of_integral_ne_zero (by
      rw [h.integral_exp_increment hν (zero_le : (0 : ℝ≥0) ≤ t)]
      exact (Real.exp_pos _).ne')
  refine h0.congr ?_
  filter_upwards [h.zero] with ω hω
  rw [hω, sub_zero]

/-- **The discounted jump-diffusion price is a martingale exactly at the compensated drift.** For
a jump law with `𝔼[e^J] < ∞` and `S₀ ≠ 0`, `t ↦ e^{−rt}S₀e^{X_t}` is an `𝓕`-martingale if and
only if `b = r − σ²/2 − Λ(𝔼[e^J] − 1)`. -/
theorem martingale_iff (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν) {S_0 : ℝ} (hS_0 : S_0 ≠ 0) (r : ℝ) :
    Martingale (fun (t : ℝ≥0) ω ↦ rexp (-r * t) * (S_0 * rexp (X t ω))) 𝓕 P ↔
      b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1) := by
  constructor
  · -- a martingale has constant mean; at time `1` it is `S₀e^{b + σ²/2 + Λ(𝔼[e^J] − 1) − r}`
    intro hM
    have hmean : ∫ ω, rexp (-r * ((0 : ℝ≥0) : ℝ)) * (S_0 * rexp (X 0 ω)) ∂P
        = ∫ ω, rexp (-r * ((1 : ℝ≥0) : ℝ)) * (S_0 * rexp (X 1 ω)) ∂P :=
      (integral_congr_ae (hM.2 0 1 zero_le_one)).symm.trans (integral_condExp (𝓕.le 0))
    have h0 : ∫ ω, rexp (-r * ((0 : ℝ≥0) : ℝ)) * (S_0 * rexp (X 0 ω)) ∂P = S_0 := by
      have hS : (fun ω ↦ rexp (-r * ((0 : ℝ≥0) : ℝ)) * (S_0 * rexp (X 0 ω))) =ᵐ[P]
          fun _ ↦ S_0 := by
        filter_upwards [h.zero] with ω hω
        simp [hω]
      rw [integral_congr_ae hS, integral_const, probReal_univ, one_smul]
    have hX1 : ∫ ω, rexp (X 1 ω) ∂P = rexp (b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1)) := by
      have hX : (fun ω ↦ rexp (X 1 ω - X 0 ω)) =ᵐ[P] fun ω ↦ rexp (X 1 ω) := by
        filter_upwards [h.zero] with ω hω
        rw [hω, sub_zero]
      rw [← integral_congr_ae hX, h.integral_exp_increment hν zero_le_one, tsub_zero,
        NNReal.coe_one, mul_one]
    have h1 : ∫ ω, rexp (-r * ((1 : ℝ≥0) : ℝ)) * (S_0 * rexp (X 1 ω)) ∂P
        = S_0 * rexp (b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1) - r) := by
      rw [integral_const_mul, integral_const_mul, hX1, NNReal.coe_one, mul_one, mul_left_comm,
        ← Real.exp_add]
      congr 2
      ring
    rw [h0, h1] at hmean
    have hexp : rexp (b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1) - r) = 1 :=
      mul_left_cancel₀ hS_0 (hmean.symm.trans (mul_one S_0).symm)
    have := (Real.exp_eq_one_iff _).1 hexp
    linarith
  · -- at the compensated drift the increment exponentials have mean `e^{r(t − s)}`
    intro hb
    have hfun : (fun (t : ℝ≥0) ω ↦ rexp (-r * t) * (S_0 * rexp (X t ω)))
        = S_0 • fun (t : ℝ≥0) ω ↦ rexp (X t ω - r * t) := by
      funext t ω
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [hfun]
    refine Martingale.smul S_0 (martingale_exp_sub_of_indep_increments
      (ψ := fun t : ℝ≥0 ↦ r * (t : ℝ)) h.adapted h.indep (h.integrable_exp hν)
      fun s t hst ↦ ?_)
    show ∫ ω, rexp (X t ω - X s ω) ∂P = rexp (r * t - r * s)
    rw [h.integral_exp_increment hν hst, NNReal.coe_sub hst, hb]
    congr 1
    ring

end JumpDiffusionProcess

end MathFin
