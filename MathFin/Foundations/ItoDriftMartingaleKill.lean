/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoDriftIncrementEnergy
public import MathFin.Foundations.ItoDriftGapDecay
public import MathFin.Foundations.ItoDriftMomentBounds

/-! # The martingale kill (the discrete route, stage 5c)

`mul_trueIncr_expect_eq_zero`: the first-order martingale terms of the discrete Itô formula die
exactly, the martingale property of `M` transferred along the a.e. identification `hMeq`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral
  QuadraticVariationL2 ItoIntegralBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! #### Stage 5c — the martingale kill

Toward the integrated Itô–drift identity for `X_t = c + ∫₀ᵗ β + M_t` (`hXrel`) with bounded
adapted path-continuous `β, δ` and the hypothesized `M`. Route of the assembly: the per-path
discrete Itô formula
(`MathFin.discrete_ito_formula`) at the grid values of `X`, integrated over `Ω`; the
first-order martingale terms die **exactly** (the martingale-kill lemma
`mul_trueIncr_expect_eq_zero` below — the discrete-assembly replacement for "the
stochastic integral has zero mean"); the drift block is the pathwise left-endpoint
Riemann–Stieltjes sum (`AdaptedDrift.tendsto_sum_mul_driftPath_sub` along each path at the
weight `f'∘X` + DCT + the stage-1
Fubini `expectation_pathIntegral_eq`); the quadratic block is `quadraticSqSum_tendsto'` at the
weight `f″∘X` plus the drift corrections (`𝔼|ΔM·driftIncr| ≤ 2D_βD_δ·cell^{3/2}`,
`𝔼[driftIncr²] ≤ (D_β·cell)²`, which the proofs sum to `O(√mesh)` and `O(mesh)`); the Taylor
remainder dies by `abs_discreteTaylorRemainder_le` + `trueIncr_pow3_le`
(`taylorRemainderSum_tendsto`). -/

section StageFiveC

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

/-- **The martingale-kill lemma** (the exact first-order cross-term zero of the adapted
assembly): for `h` bounded and `𝓕_u`-measurable, `u ≤ v`,

  `𝔼[h·(M_v − M_u)] = 0`.

Route: the conditional expectation of the increment dies
(`μ[M_v | 𝓕_u] =ᵐ M_u` — the `incrementEnergy` martingale congruence, from
`itoIntegralProcessGen_isMartingale` through the a.e. `hMeq` transfer; `condExp_sub`),
then the tower pull-out `integral_mul_condExp_eq` and the vanishing integrand. -/
theorem mul_trueIncr_expect_eq_zero {u v : ℝ≥0} (huv : u ≤ v)
    {h : Ω → ℝ} {Ch : ℝ}
    (hmadap : StronglyMeasurable[natFiltration hBmeas u] h)
    (hbdd : ∀ ω, |h ω| ≤ Ch) :
    ∫ ω, h ω * (M v ω - M u ω) ∂μ = 0 := by
  -- integrability of the increment and of the bounded product
  have hincr : Integrable (fun ω ↦ M v ω - M u ω) μ :=
    ((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v).sub
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq u)).integrable one_le_two
  have hMu : StronglyMeasurable (M u) :=
    (hMadap u).mono ((natFiltration hBmeas).le u)
  have hMv : StronglyMeasurable (M v) :=
    (hMadap v).mono ((natFiltration hBmeas).le v)
  have hhmeas : AEStronglyMeasurable (fun ω ↦ h ω * (M v ω - M u ω)) μ :=
    (hmadap.mono ((natFiltration hBmeas).le u)).mul (hMv.sub hMu) |>.aestronglyMeasurable
  have hprod : Integrable (fun ω ↦ h ω * (M v ω - M u ω)) μ :=
    Integrable.mono' (hincr.abs.const_mul Ch) hhmeas
      (Eventually.of_forall fun ω ↦ by
        change ‖h ω * (M v ω - M u ω)‖ ≤ Ch * |M v ω - M u ω|
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hbdd ω) (abs_nonneg _))
  -- the martingale congruences: `μ[M v | 𝓕_u] =ᵐ M u` and `μ[M u | 𝓕_u] =ᵐ M u`
  have hmartv : μ[M v | natFiltration hBmeas u] =ᵐ[μ] M u :=
    condExp_congr_ae (hMeq v) |>.trans
      ((itoIntegralProcessGen_isMartingale hB T hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd) huv).trans (hMeq u).symm)
  have hmartu : μ[M u | natFiltration hBmeas u] =ᵐ[μ] M u :=
    condExp_congr_ae (hMeq u) |>.trans
      ((itoIntegralProcessGen_isMartingale hB T hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd) (le_refl u)).trans (hMeq u).symm)
  -- so the conditional expectation of the increment is zero
  have hcond : μ[(M v - M u) | natFiltration hBmeas u]
      =ᵐ[μ] (fun _ ↦ (0 : ℝ)) := by
    have hsub := condExp_sub
      ((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq v).integrable one_le_two)
      ((memLp_M hB hBmeas hδadap hδcont hδbdd hMeq u).integrable one_le_two)
      (natFiltration hBmeas u)
    refine hsub.trans ?_
    filter_upwards [hmartv, hmartu] with ω h1 h2
    change μ[M v | natFiltration hBmeas u] ω - μ[M u | natFiltration hBmeas u] ω = 0
    rw [h1, h2]
    ring
  -- the tower pull-out kills the term
  have hcongr : (fun ω ↦ h ω * μ[(M v - M u) |
        natFiltration hBmeas u] ω) =ᵐ[μ] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hcond] with ω hc
    show h ω * μ[(M v - M u) | natFiltration hBmeas u] ω = 0
    rw [hc]
    ring
  calc ∫ ω, h ω * (M v ω - M u ω) ∂μ
      = ∫ ω, h ω * μ[(M v - M u) | natFiltration hBmeas u] ω ∂μ :=
        integral_mul_condExp_eq ((natFiltration hBmeas).le u) hmadap hprod hincr
    _ = ∫ ω, (fun _ ↦ (0 : ℝ)) ω ∂μ := integral_congr_ae (μ := μ) hcongr
    _ = 0 := by simp

end StageFiveC

end MathFin.ItoDriftConditional
