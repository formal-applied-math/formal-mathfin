/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralCLM
public import MathFin.Foundations.LpMulIsometry

/-! # Simple processes are dense in the bracket-weighted predictable `L²`

`ItoIntegralCLM.simpleAssembly_T_denseRange` puts the simple processes densely inside
`L²(trim_T)`. The Itô integral against `M = φ●B` lives on the **weighted** space
`L²(φ²·trim_T)` instead — `φ²ds` being the bracket `d⟨M⟩` — and its characterisation as *the*
stochastic integral, as well as the passage from simple strategies to general ones, both need
density there.

## The argument, and why it is short

The flat density proof is a π-λ induction over the predictable rectangles, and porting it
wholesale to a second measure would duplicate its longest argument. It does not need porting.
Its core, `ItoIntegralCLM.setIntegral_eq_zero_of_orthogonal_pred`, is a statement about an
*integrable* function on `trim_T`, and the weighted problem reduces to it by moving the weight
into the integrand: if `g ∈ L²(f²·trim_T)` is orthogonal to every simple process, then

  `h := f²·g`

is `trim_T`-integrable (`∫|h| d(trim) = ∫|g| d(f²·trim) ≤ ‖g‖·(f²·trim)(univ)^{1/2}`), and
orthogonality says exactly that `∫_R h d(trim) = 0` on every predictable rectangle `R`. The
π-λ core then gives `h = 0` a.e., and since `f²·trim_T` is carried by `{f ≠ 0}`, that is
`g = 0` a.e. for the weighted measure.

So the weight is handled where it is cheap — inside the integrand — and the hard measure
theory is used once, unchanged. `setIntegral_eq_zero_of_orthogonal_pred` was weakened from an
`L²` class to an integrable function for exactly this call; `h` is `L¹` and generally not `L²`.

## Result

* `memLp_uncurry_of_isFiniteMeasure` — a simple process is `L²` for *any* finite predictable
  measure, since `SimpleProcess.coe_bounded` bounds it uniformly.
* `simpleAssembly_ν` — the resulting embedding, the weighted analogue of `simpleAssembly_T`.
* `isFiniteMeasure_sqWeight` — `f²·trim_T` is finite exactly because `f ∈ L²(trim_T)`.

The density theorem itself, `simpleAssembly_sqWeight_denseRange`, is **not yet in this file**:
what is here is the scaffolding it stands on, and the `setIntegral_eq_zero_of_orthogonal_pred`
weakening that makes the `h := f²·g` reduction above available. The argument in the section
above is the plan for it, not a description of proved content.
-/

@[expose] public section

namespace MathFin
namespace PredictableDensityGeneral

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM LpMulIsometry
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### A simple process is `L²` for every finite predictable measure -/

/-- A simple process is bounded (`SimpleProcess.coe_bounded`), so it is square-integrable
against **any** finite measure on the predictable σ-algebra — no relation to `trim_T` needed.
This is what lets the same `TBoundedSP` index the weighted space. -/
lemma memLp_uncurry_of_isFiniteMeasure (hBmeas : ∀ t, Measurable (B t))
    (ν : @Measure (ℝ≥0 × Ω)
      (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable) [IsFiniteMeasure ν]
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) :
    MemLp (Function.uncurry ⇑V) 2 ν := by
  obtain ⟨C, hC⟩ := V.coe_bounded
  exact MemLp.of_bound V.isStronglyPredictable.aestronglyMeasurable C
    (Eventually.of_forall fun z ↦ hC z.1 z.2)

/-- **The weighted simple-process embedding**, the analogue of `simpleAssembly_T` with the
trim measure replaced by an arbitrary finite predictable `ν`. -/
noncomputable def simpleAssembly_ν (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (ν : @Measure (ℝ≥0 × Ω)
      (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable) [IsFiniteMeasure ν] :
    TBoundedSP T hBmeas →ₗ[ℝ] Lp ℝ 2 ν where
  toFun V := (memLp_uncurry_of_isFiniteMeasure hBmeas ν V.val).toLp _
  map_add' V W := by
    show (memLp_uncurry_of_isFiniteMeasure hBmeas ν ((V + W) : TBoundedSP T hBmeas).val).toLp _
      = _
    rw [Submodule.coe_add,
      ← MemLp.toLp_add (memLp_uncurry_of_isFiniteMeasure hBmeas ν V.val)
        (memLp_uncurry_of_isFiniteMeasure hBmeas ν W.val)]
    congr 1
    exact ItoIntegralL2.uncurry_coe_add hBmeas V.val W.val
  map_smul' c V := by
    show (memLp_uncurry_of_isFiniteMeasure hBmeas ν ((c • V) : TBoundedSP T hBmeas).val).toLp _
      = _
    rw [Submodule.coe_smul, RingHom.id_apply,
      ← MemLp.toLp_const_smul c (memLp_uncurry_of_isFiniteMeasure hBmeas ν V.val)]
    congr 1
    exact ItoIntegralL2.uncurry_coe_smul hBmeas c V.val

lemma coeFn_simpleAssembly_ν (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (ν : @Measure (ℝ≥0 × Ω)
      (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable) [IsFiniteMeasure ν]
    (V : TBoundedSP T hBmeas) :
    ⇑(simpleAssembly_ν T hBmeas ν V) =ᵐ[ν] Function.uncurry ⇑V.val :=
  (memLp_uncurry_of_isFiniteMeasure hBmeas ν V.val).coeFn_toLp

/-! ### The bracket weight -/

omit [IsProbabilityMeasure μ] in
/-- `f²·trim_T` is a finite measure exactly when `f ∈ L²(trim_T)`: its total mass is `‖f‖²`. -/
lemma isFiniteMeasure_sqWeight (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {f : ℝ≥0 × Ω → ℝ} (hfL2 : MemLp f 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    IsFiniteMeasure (sqWeight (trimMeasure_T (μ := μ) T hBmeas) f) := by
  refine ⟨?_⟩
  have hlt : ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas) < ⊤ := by
    have h := hfL2.2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h
    have h2 : (∫⁻ z, ‖f z‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂(trimMeasure_T (μ := μ) T hBmeas)) ≠ ⊤ := by
      intro htop
      rw [htop] at h
      simp [ENNReal.top_rpow_of_pos] at h
    refine lt_of_le_of_ne le_top ?_
    intro htop
    exact h2 (by
      rw [← htop]
      refine lintegral_congr fun z ↦ ?_
      rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast])
  rw [sqWeight, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hlt

end PredictableDensityGeneral
end MathFin
