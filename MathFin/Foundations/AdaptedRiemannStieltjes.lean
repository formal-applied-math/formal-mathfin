/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.AdaptedStochasticIntegralFreezing
public import MathFin.Foundations.StochasticIntegralCharacterisation

/-! # Riemann–Stieltjes sums against an Itô integral converge

The first-order term of the adapted-coefficient Itô formula
(`docs/specs/2026-07-05-adapted-ito-formula-design.md`, step B5). Let `M = φ●B` for a predictable
`L²` driver `φ`, and let `w` be a bounded predictable weight whose paths are almost surely
continuous on `[0, T]`. Along the uniform partition `tₖ = kT/n` of `[0, T]`,

  `∑ₖ w(tₖ)·(M_{tₖ₊₁} − M_{tₖ}) → ∫ w dM` in `L²(μ)`

(`tendsto_integral_sq_riemannStieltjes_sub`), and `∫ w dM = ∫ χ dB` for the class `χ` of `φ·w`
(`coeFn_mulLI_weightLp`).

The sum is the integral against `M` of the left-endpoint step process of `w`
(`itoIntegralAgainst_stepσ`, the band identity `itoIntegralAgainst_elementary` on each cell). The
step processes converge to `w` in `L²(⟨M⟩)` by dominated convergence
(`tendsto_simpleAssemblyOfMeasure_stepσ`): they converge at every time of `(0, T]` along every
continuous path, which is `⟨M⟩`-almost everywhere, and they are bounded by the bound of `w`. The
Itô isometry against `M` carries that to the integrals. No freezing of `φ` is involved, so `φ`
needs no path regularity.

## Main results

* `tendsto_integral_sq_riemannStieltjes_sub` — the sums converge to `∫ w dM` in mean square.
* `tendsto_itoIntegralAgainst_stepσ` — the same convergence, as `L²(μ)` classes of step integrals.
* `itoIntegralAgainst_stepσ` — the `n`-th step integral is the Riemann–Stieltjes sum, almost
  surely.
* `coeFn_mulLI_weightLp`, `itoIntegralAgainst_weightLp` — the limit is `∫ χ dB`, where `χ` is the
  class of `φ·w`; and any predictable `L²` class equal to `φ·w` almost everywhere will do.
-/

@[expose] public section

namespace MathFin
namespace AdaptedRiemannStieltjes

open MeasureTheory ProbabilityTheory Filter Topology
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralRiemannBridge
  ItoIntegralAgainstMartingale ItoIntegralBrownian QuadraticVariationL2
  AdaptedStochasticIntegralFreezing
  PredictableDensityGeneral StochasticIntegralCharacterisation LpMulIsometry
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {w : ℝ≥0 → Ω → ℝ}
  (hw_pred : IsStronglyPredictable (natFiltration hBmeas) w)
  (hw_cont : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Set.Icc 0 T)) {Cw : ℝ}
  (hw_bdd : ∀ s ω, |w s ω| ≤ Cw)

omit [IsProbabilityMeasure μ] in
include hw_pred hw_bdd in
/-- A bounded predictable weight is square-integrable against the bracket of `M`. -/
theorem memLp_uncurry_bracketMeasure :
    MemLp (Function.uncurry w) 2 (bracketMeasure (μ := μ) T hBmeas φ) :=
  MemLp.of_bound hw_pred.aestronglyMeasurable Cw
    (ae_of_all _ fun z ↦ (Real.norm_eq_abs _).trans_le (hw_bdd z.1 z.2))

/-- The weight as a class of `L²(⟨M⟩)`, the integrand of `∫ w dM`. -/
noncomputable def weightLp : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ) :=
  (memLp_uncurry_bracketMeasure T hBmeas φ hw_pred hw_bdd).toLp (Function.uncurry w)

omit [IsProbabilityMeasure μ] in
/-- The weight's class is the weight, `⟨M⟩`-almost everywhere. -/
theorem coeFn_weightLp : ⇑(weightLp T hBmeas φ hw_pred hw_bdd)
    =ᵐ[bracketMeasure (μ := μ) T hBmeas φ] Function.uncurry w :=
  (memLp_uncurry_bracketMeasure T hBmeas φ hw_pred hw_bdd).coeFn_toLp

include hw_cont in
/-- **The step processes converge to the weight in `L²(⟨M⟩)`.** Dominated convergence: along a
path continuous on `[0, T]` they converge at every time of `(0, T]`, the bracket charges nothing
else, and they are bounded by `C_w`. -/
theorem tendsto_simpleAssemblyOfMeasure_stepσ :
    Tendsto (fun n ↦ simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ)
        (stepσ hBmeas (fun t ↦ hw_pred.stronglyAdapted t) hw_bdd T n)) atTop
      (𝓝 (weightLp T hBmeas φ hw_pred hw_bdd)) := by
  refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n ↦ memLp_uncurry_of_isFiniteMeasure hBmeas
    (bracketMeasure (μ := μ) T hBmeas φ)
    (stepσ hBmeas (fun t ↦ hw_pred.stronglyAdapted t) hw_bdd T n).val) _
    (memLp_uncurry_bracketMeasure T hBmeas φ hw_pred hw_bdd)).2 ?_
  have hsupp : ∀ᵐ z ∂(bracketMeasure (μ := μ) T hBmeas φ), z.1 ∈ Set.Ioc 0 T :=
    ae_fst_mem_Ioc_bracketMeasure
  refine tendsto_eLpNorm_sub_of_dominated_convergence ENNReal.ofNat_ne_top (fun _ ↦ Cw)
    (fun n ↦ (memLp_uncurry_of_isFiniteMeasure hBmeas _ _).aestronglyMeasurable)
    (memLp_const Cw) (fun n ↦ ?_) ?_
  · filter_upwards [hsupp] with z hz
    exact (Real.norm_eq_abs _).trans_le
      (abs_uncurry_stepσ_le hBmeas (fun t ↦ hw_pred.stronglyAdapted t) hw_bdd T n hz z.2)
  · -- convergence on `(0, T]`: a predictable set, containing `(0, T] × {ω}` for almost every `ω`
    have hmeas : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable]
        {z : ℝ≥0 × Ω | z.1 ∈ Set.Ioc 0 T → Tendsto (fun n ↦ Function.uncurry
          ⇑(stepσ hBmeas (fun t ↦ hw_pred.stronglyAdapted t) hw_bdd T n).val z) atTop
            (𝓝 (Function.uncurry w z))} := by
      letI : MeasurableSpace (ℝ≥0 × Ω) := (natFiltration (mΩ := mΩ) hBmeas).predictable
      have h1 : MeasurableSet {z : ℝ≥0 × Ω | z.1 ∈ Set.Ioc 0 T} := by
        convert measurableSet_predictable_Ioc_prod (𝓕 := natFiltration hBmeas) 0 T
          MeasurableSet.univ using 1
        ext z
        simp
      have h2 := measurableSet_tendsto_fun (l := atTop)
        (fun n ↦ (stepσ hBmeas (fun t ↦ hw_pred.stronglyAdapted t) hw_bdd T
          n).val.isStronglyPredictable.measurable) hw_pred.measurable
      exact h1.himp h2
    filter_upwards [ae_bracketMeasure_of_ae_forall T hBmeas φ hmeas
      (hw_cont.mono fun ω hω t ht ↦ tendsto_uncurry_stepσ hBmeas
        (fun t ↦ hw_pred.stronglyAdapted t) hw_bdd T ht (hω t ⟨ht.1.le, ht.2⟩)), hsupp]
      with z hz hzT
    exact hz hzT

include hw_cont in
/-- **Riemann–Stieltjes sums against `M` converge to the integral against `M`**, in `L²(μ)`: the
Itô isometry against `M` applied to `tendsto_simpleAssemblyOfMeasure_stepσ`. -/
theorem tendsto_itoIntegralAgainst_stepσ :
    Tendsto (fun n ↦ itoIntegralAgainstCLM hB T hBmeas φ
        (simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ)
          (stepσ hBmeas (fun t ↦ hw_pred.stronglyAdapted t) hw_bdd T n))) atTop
      (𝓝 (itoIntegralAgainstCLM hB T hBmeas φ (weightLp T hBmeas φ hw_pred hw_bdd))) :=
  ((itoIntegralAgainstCLM hB T hBmeas φ).continuous.tendsto _).comp
    (tendsto_simpleAssemblyOfMeasure_stepσ T hBmeas φ hw_pred hw_cont hw_bdd)

/-- **The integral of the step process is the Riemann–Stieltjes sum**
`∑ₖ w(tₖ)·(M_{tₖ₊₁} − M_{tₖ})`, almost surely: the band identity on each cell. -/
theorem itoIntegralAgainst_stepσ (n : ℕ) :
    ⇑(itoIntegralAgainstCLM hB T hBmeas φ
        (simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ)
          (stepσ hBmeas (fun t ↦ hw_pred.stronglyAdapted t) hw_bdd T n)))
      =ᵐ[μ] fun ω ↦ ∑ k ∈ Finset.range n, w (unifPart T n k) ω
          * (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas φ ω
            - itoProcessCLM hB T (unifPart T n k) hBmeas φ ω) := by
  have hterm (k : {x // x ∈ Finset.range n}) :
      ⇑(itoIntegralAgainstCLM hB T hBmeas φ
          (simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ)
            (cellStep T hBmeas (fun t ↦ hw_pred.stronglyAdapted t) hw_bdd n k)))
        =ᵐ[μ] fun ω ↦ w (unifPart T n k) ω
            * (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas φ ω
              - itoProcessCLM hB T (unifPart T n k) hBmeas φ ω) :=
    itoIntegralAgainst_elementary (hB := hB) T hBmeas φ (unifPart_mono T n (Nat.le_succ k))
      (unifPart_le_T (Finset.mem_range.mp k.2)) (w (unifPart T n k))
      (hw_pred.stronglyAdapted (unifPart T n k)).measurable Cw (hw_bdd (unifPart T n k)) _
      ((coeFn_simpleAssemblyOfMeasure T hBmeas _ _).trans (ae_of_all _ fun z ↦ by
        rw [uncurry_cellStep, elemIntegrand]
        by_cases hz : z.1 ∈ Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) <;> simp [hz]))
  rw [stepσ_eq_sum_cellStep, map_sum, map_sum]
  refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
  filter_upwards [ae_all_iff.2 hterm] with ω hω
  rw [← Finset.sum_attach (Finset.range n) fun k ↦ w (unifPart T n k) ω
    * (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas φ ω
      - itoProcessCLM hB T (unifPart T n k) hBmeas φ ω)]
  exact Finset.sum_congr rfl fun k _ ↦ hω k

include hw_cont in
/-- **Riemann–Stieltjes sums against `M` converge in mean square**:
`𝔼[(∑ₖ w(tₖ)·(M_{tₖ₊₁} − M_{tₖ}) − ∫ w dM)²] → 0`. The `L²` convergence
`tendsto_itoIntegralAgainst_stepσ`, with each step integral read as its sum
(`itoIntegralAgainst_stepσ`). -/
theorem tendsto_integral_sq_riemannStieltjes_sub :
    Tendsto (fun n : ℕ ↦ ∫ ω, (∑ k ∈ Finset.range n, w (unifPart T n k) ω
          * (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas φ ω
            - itoProcessCLM hB T (unifPart T n k) hBmeas φ ω)
        - itoIntegralAgainstCLM hB T hBmeas φ (weightLp T hBmeas φ hw_pred hw_bdd) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have h := (tendsto_iff_norm_sub_tendsto_zero.1
    (tendsto_itoIntegralAgainst_stepσ hB T hBmeas φ hw_pred hw_cont hw_bdd)).pow 2
  rw [zero_pow two_ne_zero] at h
  refine h.congr fun n ↦ ?_
  rw [lp_two_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (itoIntegralAgainstCLM hB T hBmeas φ
      (simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ)
        (stepσ hBmeas (fun t ↦ hw_pred.stronglyAdapted t) hw_bdd T n)))
      (itoIntegralAgainstCLM hB T hBmeas φ (weightLp T hBmeas φ hw_pred hw_bdd)),
    itoIntegralAgainst_stepσ hB T hBmeas φ hw_pred hw_bdd n] with ω h1 h2
  rw [h1, Pi.sub_apply, h2]

omit [IsProbabilityMeasure μ] in
/-- **The integrand of the limit**: `∫ w dM = ∫ χ dB` by definition
(`itoIntegralAgainstCLM_apply`), with `χ` the image of the weight's class under multiplication by
`φ`, and that `χ` is `φ·w` almost everywhere. The weight's class is `w` wherever `φ ≠ 0`. -/
theorem coeFn_mulLI_weightLp :
    ⇑(mulLI (trimMeasure_T (μ := μ) T hBmeas) (Lp.stronglyMeasurable φ).measurable
        (weightLp T hBmeas φ hw_pred hw_bdd))
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun z ↦ (φ : ℝ≥0 × Ω → ℝ) z * w z.1 z.2 := by
  filter_upwards [coeFn_mulLI _ (Lp.stronglyMeasurable φ).measurable
      (weightLp T hBmeas φ hw_pred hw_bdd),
    (ae_withDensity_iff (μ := trimMeasure_T (μ := μ) T hBmeas)
      (measurable_sqDensity (Lp.stronglyMeasurable φ).measurable)).1
      (coeFn_weightLp T hBmeas φ hw_pred hw_bdd)] with z hz hc
  rw [hz]
  by_cases hφz : (φ : ℝ≥0 × Ω → ℝ) z = 0
  · rw [hφz, zero_mul, zero_mul]
  · exact congrArg ((φ : ℝ≥0 × Ω → ℝ) z * ·) (hc (sqDensity_ne_zero hφz))

/-- **The limit is an Itô integral against `B`**: `∫ w dM = ∫ χ dB` for any predictable `L²`
class `χ` equal to `φ·w` almost everywhere. -/
theorem itoIntegralAgainst_weightLp (χ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hχ : ⇑χ =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun z ↦ (φ : ℝ≥0 × Ω → ℝ) z * w z.1 z.2) :
    itoIntegralAgainstCLM hB T hBmeas φ (weightLp T hBmeas φ hw_pred hw_bdd)
      = itoIntegralCLM_T hB T hBmeas χ := by
  rw [itoIntegralAgainstCLM_apply]
  congr 1
  exact Lp.ext ((coeFn_mulLI_weightLp T hBmeas φ hw_pred hw_bdd).trans hχ.symm)

end AdaptedRiemannStieltjes

end MathFin
