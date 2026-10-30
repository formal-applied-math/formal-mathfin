/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralRiemannBridgeAdapted

/-! # Riemann ↔ CLM bridge for bounded continuous integrands

Generalizes `ItoIntegralBrownian.itoIntegralCLM_T_brownian` (integrand `s ↦ B_s`) to a
bounded continuous integrand `φ ∘ B`. For bounded continuous `φ`, the uniform-partition
Riemann–Itô sums `∑ φ(B_{tₖ})·ΔBₖ` converge in `L²(μ)` to the genuine continuous Itô
integral `itoIntegralCLM_T gφ`, where `gφ` is the trim-`L²` realization of `s ↦ φ(B_s)`.

This is the adapted bridge (`itoIntegralCLM_T_of_bdd_adapted_cont`) at the integrand
`θ s ω = φ(B_s ω)`: it is adapted (`stronglyMeasurable_comp_eval`), bounded by `C`, and
continuous in `s` for every `ω` because `φ` and the Brownian paths are. The realization `gφ`
is `processToLp θ`, which agrees with `φ ∘ B` a.e.
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralRiemannBridge

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal
open scoped MeasureTheory NNReal ENNReal InnerProductSpace
open ItoIntegralL2 ItoIntegralCLM ItoIntegralBrownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- **Riemann ↔ CLM bridge.** For bounded continuous `φ`, the uniform-partition
Riemann–Itô sums `∑ φ(B_{tₖ})·ΔBₖ` converge in `L²(μ)` to `itoIntegralCLM_T gφ`, with the
integrand **named**: `gφ =ᵐ [φ(B_·)]` (it is `processToLp` of the adapted continuous bounded
process `φ ∘ B`). Carrying the identification here is what lets `ito_formula_L2_bddDeriv` state
which integrand its Itô term integrates. -/
theorem itoIntegralCLM_T_of_bdd_cont (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ B s ω))
    {φ : ℝ → ℝ} (hφ_cont : Continuous φ) {C : ℝ} (hφ_bdd : ∀ x, |φ x| ≤ C) (T : ℝ≥0) :
    ∃ gφ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (⇑gφ =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun z ↦ φ (B z.1 z.2)) ∧
      Tendsto (fun n ↦ (memLp_riemannσ (θ := fun s ω ↦ φ (B s ω)) hB hBmeas
            (fun t ↦ stronglyMeasurable_comp_eval hBmeas hφ_cont.measurable t)
            (fun _ _ ↦ hφ_bdd _) T n).toLp (riemannσ (B := B) (fun s ω ↦ φ (B s ω)) T n))
        atTop (𝓝 (itoIntegralCLM_T hB T hBmeas gφ)) := by
  have hadap (t : ℝ≥0) : StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)]
      (fun ω ↦ φ (B t ω)) := stronglyMeasurable_comp_eval hBmeas hφ_cont.measurable t
  have hcont (ω : Ω) : Continuous fun s : ℝ≥0 ↦ φ (B s ω) := hφ_cont.comp (hBcont ω)
  exact ⟨processToLp (μ := μ) (σ := fun s ω ↦ φ (B s ω)) T hBmeas hadap hcont
      (fun _ _ ↦ hφ_bdd _),
    processToLp_coeFn (σ := fun s ω ↦ φ (B s ω)) T hBmeas hadap hcont (fun _ _ ↦ hφ_bdd _),
    itoIntegralCLM_T_of_bdd_adapted_cont (θ := fun s ω ↦ φ (B s ω)) hB hBmeas hadap hcont
      (fun _ _ ↦ hφ_bdd _) T⟩

end ItoIntegralRiemannBridge
end MathFin
