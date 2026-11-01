/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaTD

/-! # CLM-identified continuous-time Itô formula (L²), time-independent case

For `f ∈ C³` with bounded `f′, f″, f‴`,

  `f(B_T) − f(B_0) =ᵐ[μ] itoIntegralCLM_T gf' + ½∫₀ᵀ f″(B_s) ds`,

where `gf'` is the Itô-`L²` realization of `s ↦ f′(B_s)`. This is the `f(t, x) = f(x)`
(`f_t = 0`) instance of the time-dependent formula `ito_formula_td_L2_bddDeriv`
(`ItoFormulaTD`); there is no separate time-independent proof.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM ItoIntegralBrownian
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- **CLM-identified bounded-derivative Itô formula in `L²`.** For `f ∈ C³` with `|f′| ≤ C₁`,
`|f″| ≤ C₂`, `|f‴| ≤ C₃`, there is an Itô-`L²` integrand `gf'` with

  `gf' =ᵐ [f′(B_·)]`  and  `f(B_T) − f(B_0) =ᵐ[μ] itoIntegralCLM_T gf' + ½∫₀ᵀ f″(B_s) ds`.

The first conjunct is what makes the second the Itô *formula* rather than a decomposition into
some Itô integral. It is the time-independent case of `ito_formula_td_L2_bddDeriv`. -/
theorem ito_formula_L2_bddDeriv
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ B s ω)) (T : ℝ≥0)
    {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 : ℝ} (hf1 : ∀ x, |f' x| ≤ C1) {C2 : ℝ} (hf2 : ∀ x, |f'' x| ≤ C2)
    {C3 : ℝ} (hf3 : ∀ x, |f''' x| ≤ C3) :
    ∃ gf' : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (⇑gf' =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun z ↦ f' (B z.1 z.2)) ∧
      (fun ω ↦ f (B T ω) - f (B 0 ω)) =ᵐ[μ]
        (fun ω ↦ (itoIntegralCLM_T hB T hBmeas gf') ω
          + (1 / 2) * ∫ s in Set.Ioc 0 T, f'' (B s ω) ∂ItoIntegralL2.timeMeasure) := by
  obtain ⟨gf', hname, hae⟩ := ito_formula_td_L2_bddDeriv hB hBmeas hBcont T
    (f := fun _ ↦ f) (f_t := fun _ _ ↦ 0) (f_x := fun _ ↦ f') (f_xx := fun _ ↦ f'')
    (f_tt := fun _ _ ↦ 0) (f_tx := fun _ _ ↦ 0) (f_xxx := fun _ ↦ f''')
    (fun t _ ↦ hasDerivAt_const t _) (fun t _ ↦ hasDerivAt_const t _)
    (fun _ _ ↦ hasDerivAt_const _ _) (fun _ x ↦ hf x) (fun _ x ↦ hf' x) (fun _ x ↦ hf'' x)
    ((continuous_iff_continuousAt.mpr fun x ↦ (hf' x).continuousAt).comp continuous_snd)
    ((continuous_iff_continuousAt.mpr fun x ↦ (hf'' x).continuousAt).comp continuous_snd)
    (Ct := 0) (C1 := C1) (C2 := C2) (Ctt := 0) (Ctx := 0) (Cxxx := C3)
    (by simp) (fun _ x ↦ hf1 x) (fun _ x ↦ hf2 x) (by simp) (by simp) (fun _ x ↦ hf3 x)
  refine ⟨gf', hname, ?_⟩
  filter_upwards [hae] with ω hω
  simp only [zero_add] at hω
  rw [hω, integral_const_mul]

omit hB in
/-- **Continuity discharged.** The bounded-derivative Itô formula for the continuous
modification `IsPreBrownianReal.mk X` of any pre-Brownian `X`: the path-continuity hypothesis is
supplied for free by the Kolmogorov–Chentsov modification (`IsPreBrownianReal.continuous_mk`), so
no separate continuity assumption on the process is needed. -/
theorem ito_formula_L2_bddDeriv_mk {X : ℝ≥0 → Ω → ℝ} (hX : IsPreBrownianReal X μ) (T : ℝ≥0)
    {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 : ℝ} (hf1 : ∀ x, |f' x| ≤ C1) {C2 : ℝ} (hf2 : ∀ x, |f'' x| ≤ C2)
    {C3 : ℝ} (hf3 : ∀ x, |f''' x| ≤ C3) :
    ∃ gf' : Lp ℝ 2 (trimMeasure_T (μ := μ) T (fun t ↦ IsPreBrownianReal.measurable_mk (h := hX) t)),
      (⇑gf' =ᵐ[trimMeasure_T (μ := μ) T (fun t ↦ IsPreBrownianReal.measurable_mk (h := hX) t)]
        fun z ↦ f' (IsPreBrownianReal.mk (h := hX) X z.1 z.2)) ∧
      (fun ω ↦ f (IsPreBrownianReal.mk (h := hX) X T ω) -
          f (IsPreBrownianReal.mk (h := hX) X 0 ω)) =ᵐ[μ]
        (fun ω ↦ (itoIntegralCLM_T (hX.isBrownianReal_mk).toIsPreBrownianReal T
                    (fun t ↦ IsPreBrownianReal.measurable_mk (h := hX) t) gf') ω
          + (1 / 2) * ∫ s in Set.Ioc 0 T,
              f'' (IsPreBrownianReal.mk (h := hX) X s ω) ∂ItoIntegralL2.timeMeasure) :=
  ito_formula_L2_bddDeriv (hB := (hX.isBrownianReal_mk).toIsPreBrownianReal)
    (B := IsPreBrownianReal.mk (h := hX) X)
    (fun t ↦ IsPreBrownianReal.measurable_mk (h := hX) t)
    (fun ω ↦ IsPreBrownianReal.continuous_mk (h := hX) ω) T hf hf' hf'' hf1 hf2 hf3

end MathFin
