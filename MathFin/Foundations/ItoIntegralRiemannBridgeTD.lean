/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralRiemannBridgeAdapted

/-! # Riemann ↔ CLM bridge for bounded jointly-continuous time-dependent integrands

Generalizes `ItoIntegralRiemannBridge.itoIntegralCLM_T_of_bdd_cont` (integrand `φ ∘ B`)
to a **time-dependent** integrand `(s, ω) ↦ φ(s, B_s ω)` for bounded jointly continuous
`φ : ℝ → ℝ → ℝ`. The uniform-partition Riemann–Itô sums `∑ φ(tₖ, B_{tₖ})·ΔBₖ` converge
in `L²(μ)` to the genuine continuous Itô integral `itoIntegralCLM_T gφ`, where `gφ` is
the trim-`L²` realization of `s ↦ φ(s, B_s)`.

Like the `φ ∘ B` bridge, this is the adapted bridge (`itoIntegralCLM_T_of_bdd_adapted_cont`)
at the integrand `θ s ω = φ(s, B_s ω)`: the time slot is the *deterministic* node, so `θ` is
adapted and bounded, and `s ↦ φ(s, B_s ω)` is continuous by joint continuity composed with
`s ↦ (s, B_s ω)`. The time-dependent Itô formula consumes this at `φ = f_x`.
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralRiemannBridgeTD

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal
open scoped MeasureTheory NNReal ENNReal InnerProductSpace
open ItoIntegralL2 ItoIntegralCLM ItoIntegralBrownian ItoIntegralRiemannBridge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- **Riemann ↔ CLM bridge, time-dependent integrand.** For bounded jointly continuous
`φ : ℝ → ℝ → ℝ`, the uniform-partition Riemann–Itô sums `∑ φ(tₖ, B_{tₖ})·ΔBₖ` converge
in `L²(μ)` to `itoIntegralCLM_T gφ`, where `gφ` is the trim-`L²` realization of
`s ↦ φ(s, B_s)` (`processToLp` of the adapted continuous bounded process), with
`gφ =ᵐ [φ(·, B_·)]`. -/
theorem itoIntegralCLM_T_of_bdd_cont_td (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ B s ω))
    {φ : ℝ → ℝ → ℝ} (hφ_cont : Continuous fun p : ℝ × ℝ ↦ φ p.1 p.2)
    {C : ℝ} (hφ_bdd : ∀ t x, |φ t x| ≤ C) (T : ℝ≥0) :
    ∃ gφ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (⇑gφ =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun z ↦ φ z.1 (B z.1 z.2)) ∧
      Tendsto (fun n ↦ (memLp_riemannσ (θ := fun s ω ↦ φ s (B s ω)) hB hBmeas
            (fun t ↦ stronglyMeasurable_comp_eval hBmeas
              (hφ_cont.comp (continuous_const.prodMk continuous_id)).measurable t)
            (fun _ _ ↦ hφ_bdd _ _) T n).toLp
          (riemannσ (B := B) (fun s ω ↦ φ s (B s ω)) T n))
        atTop (𝓝 (itoIntegralCLM_T hB T hBmeas gφ)) := by
  have hadap (t : ℝ≥0) : StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
      (fun ω ↦ φ t (B t ω)) :=
    stronglyMeasurable_comp_eval hBmeas
      (hφ_cont.comp (continuous_const.prodMk continuous_id)).measurable t
  have hcont (ω : Ω) : Continuous fun s : ℝ≥0 ↦ φ s (B s ω) :=
    hφ_cont.comp ((NNReal.continuous_coe).prodMk (hBcont ω))
  exact ⟨processToLp (μ := μ) (σ := fun s ω ↦ φ s (B s ω)) T hBmeas hadap hcont
      (fun _ _ ↦ hφ_bdd _ _),
    processToLp_coeFn (σ := fun s ω ↦ φ s (B s ω)) T hBmeas hadap hcont (fun _ _ ↦ hφ_bdd _ _),
    itoIntegralCLM_T_of_bdd_adapted_cont (θ := fun s ω ↦ φ s (B s ω)) hB hBmeas hadap hcont
      (fun _ _ ↦ hφ_bdd _ _) T⟩

end ItoIntegralRiemannBridgeTD
end MathFin
