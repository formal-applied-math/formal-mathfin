/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedTD
public import MathFin.Probability.Brownian.Ito.Filtered.ContAdaptedDensity
public import MathFin.Probability.Brownian.Ito.ItoFormulaAdapted
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Itô's formula for predictable `L²` integrands

`MathFin.ItoFormulaAdapted.ito_formula_adapted` is stated for integrands that are bounded,
adapted and continuous along every path.  Here it is extended, by `L²` approximation
(`ContAdaptedDensity`) and dominated convergence, to arbitrary predictable integrands
`β, γ ∈ L²((0,T]×Ω)`: for `X = x₀ + ∫ β ds + ∫ γ dB` and `f ∈ C²` with bounded `f', f''`,

`f(X_T) - f(x₀) = ∫₀ᵀ f'(X_s) γ_s dB_s + ∫₀ᵀ (f'(X_s) β_s + ½ f''(X_s) γ_s²) ds` a.s.

## Main definitions

* `l2ItoProcess`
* `l2ItoProcessLp`

## Main results

* `memLp_comp_mul_coeFn`
* `integrable_comp_terminal`
* `ito_formula_L2`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open MathFin MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM MathFin.ItoIntegralProcessGeneral
open MathFin.ItoIntegralProcessContinuousModification MathFin.ItoFormulaAdapted
open MathFin.AdaptedDrift

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

section Tools
variable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))

theorem ae_le_T_timeMeasure_T : ∀ᵐ t ∂(timeMeasureHorizon T), t ≤ T := by
  rw [timeMeasureHorizon]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2

/-- Per-time a.e. equality of two predictable functions gives a.e. equality for the trim. -/
theorem ae_eq_trim_of_slices {f g : ℝ≥0 × Ω → ℝ}
    (hf : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] f)
    (hg : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] g)
    (h : ∀ t ≤ T, ∀ᵐ ω ∂μ, f (t, ω) = g (t, ω)) :
    f =ᵐ[trimMeasure (μ := μ) T hBmeas] g := by
  refine hf.ae_eq_trim_of_stronglyMeasurable (natFiltration hBmeas).predictable_le_prod hg ?_
  have hset : MeasurableSet {z : ℝ≥0 × Ω | f z = g z} :=
    measurableSet_eq_fun (hf.mono (natFiltration hBmeas).predictable_le_prod).measurable
      (hg.mono (natFiltration hBmeas).predictable_le_prod).measurable
  rw [Filter.EventuallyEq, Measure.ae_prod_iff_ae_ae hset]
  filter_upwards [ae_le_T_timeMeasure_T T] with t htT
  exact h t htT

/-- Pathwise a.e. equality on `[0,T]` gives a.e. equality for the trim. -/
theorem ae_eq_trim_of_pathwise {f g : ℝ≥0 × Ω → ℝ}
    (hf : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] f)
    (hg : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] g)
    (h : ∀ᵐ ω ∂μ, ∀ t ≤ T, f (t, ω) = g (t, ω)) :
    f =ᵐ[trimMeasure (μ := μ) T hBmeas] g :=
  ae_eq_trim_of_slices T hBmeas hf hg fun t ht => h.mono fun _ hω => hω t ht

/-- `L¹` bound for pathwise time integrals. -/
theorem integral_abs_setIntegral_le {F : ℝ≥0 × Ω → ℝ}
    (hF : Integrable F ((timeMeasureHorizon T).prod μ)) :
    ∫ ω, |∫ s in Set.Ioc 0 T, F (s, ω) ∂timeMeasure| ∂μ
      ≤ ∫ z, |F z| ∂((timeMeasureHorizon T).prod μ) := by
  rw [integral_prod_symm _ hF.abs]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    hF.abs.integral_prod_right (ae_of_all _ fun _ => ?_)
  exact abs_integral_le_integral_abs

/-- The total mass of the horizon product measure. -/
theorem measureReal_prod_univ : ((timeMeasureHorizon T).prod μ).real Set.univ = (T : ℝ) := by
  rw [measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod, measure_univ (μ := μ), mul_one,
    timeMeasureHorizon, Measure.restrict_apply_univ, timeMeasure_Ioc, NNReal.coe_zero, sub_zero,
    ENNReal.toReal_ofReal T.coe_nonneg]

/-- `L¹ ≤ √T · L²` for elements of the predictable `L²` space. -/
theorem integral_abs_coeFn_le (u : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∫ z, |u z| ∂((timeMeasureHorizon T).prod μ) ≤ Real.sqrt T * ‖u‖ := by
  have hu : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] (⇑u) :=
    Lp.stronglyMeasurable u
  have h1 : ∫ z, |u z| ∂((timeMeasureHorizon T).prod μ)
      = ∫ z, |u z * 1| ∂(trimMeasure (μ := μ) T hBmeas) := by
    simp only [mul_one, ← Real.norm_eq_abs]
    exact integral_trim (natFiltration hBmeas).predictable_le_prod hu.norm
  rw [h1]
  refine (integral_abs_mul_le_sqrt_mul_sqrt (Lp.memLp u) (memLp_const 1)).trans ?_
  rw [← MathFin.lp_two_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have h2 : ∫ _z, (1 : ℝ) ^ 2 ∂(trimMeasure (μ := μ) T hBmeas) = T := by
    simp only [one_pow, integral_const, smul_eq_mul, mul_one]
    change (((timeMeasureHorizon T).prod μ).trim (natFiltration hBmeas).predictable_le_prod).real
      Set.univ = T
    rw [measureReal_def, trim_measurableSet_eq _ MeasurableSet.univ, ← measureReal_def,
      measureReal_prod_univ]
  rw [h2, mul_comm]

end Tools

/-! ### The canonical Itô process with `L²` integrands -/

section Canonical
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

/-- `X_t = x₀ + ∫₀ᵗ β ds + ∫₀ᵗ γ dB` with predictable `L²` integrands. -/
def l2ItoProcess (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (x₀ : ℝ)
    (β γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x₀ + driftContinuousMod T hBmeas β t ω + itoContinuousMod T hBmeas γ t ω

include hB hBcont in
theorem l2ItoProcess_isStronglyPredictable (x₀ : ℝ)
    (β γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    IsStronglyPredictable (natFiltration hBmeas) (l2ItoProcess T hBmeas x₀ β γ) :=
  (stronglyMeasurable_const.add (driftContinuousMod_isStronglyPredictable T hBmeas β)).add
    (itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont γ)

include hB hBcont in
theorem ae_continuousOn_l2ItoProcess (x₀ : ℝ) (β γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t => l2ItoProcess T hBmeas x₀ β γ t ω) (Set.Icc 0 T) := by
  filter_upwards [driftContinuousMod_continuousOn T hBmeas β,
    itoContinuousMod_continuousOn hB T hBmeas hBcont γ] with ω hd hi
  exact (continuousOn_const.add hd).add hi

/-- The class of the canonical process in `E`. -/
def l2ItoProcessLp (x₀ : ℝ) (β γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
  Lp.const 2 (trimMeasure (μ := μ) T hBmeas) x₀ + driftProcessAssembled (μ := μ) T hBmeas β
    + itoProcessAssembled hB T hBmeas hBcont γ

theorem coeFn_l2ItoProcessLp (x₀ : ℝ) (β γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ⇑(l2ItoProcessLp hB T hBmeas hBcont x₀ β γ)
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry (l2ItoProcess T hBmeas x₀ β γ) := by
  have hito : ⇑(itoProcessAssembled hB T hBmeas hBcont γ)
      =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas γ) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont γ).coeFn_toLp
  filter_upwards [Lp.coeFn_add (Lp.const 2 (trimMeasure (μ := μ) T hBmeas) x₀
        + driftProcessAssembled (μ := μ) T hBmeas β) (itoProcessAssembled hB T hBmeas hBcont γ),
    Lp.coeFn_add (Lp.const 2 (trimMeasure (μ := μ) T hBmeas) x₀)
      (driftProcessAssembled (μ := μ) T hBmeas β),
    Lp.coeFn_const (p := 2) (μ := trimMeasure (μ := μ) T hBmeas) (c := x₀),
    driftProcessAssembled_coeFn (μ := μ) T hBmeas β, hito] with z h1 h2 h3 hd hi
  rw [l2ItoProcessLp, h1, Pi.add_apply, h2, Pi.add_apply, hd, hi]
  have h3' : (Lp.const 2 (trimMeasure (μ := μ) T hBmeas) x₀) z = x₀ := h3
  rw [h3']
  rfl

theorem norm_l2ItoProcessLp_sub_le (x₀ : ℝ) (β γ β' γ' : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ‖l2ItoProcessLp hB T hBmeas hBcont x₀ β γ - l2ItoProcessLp hB T hBmeas hBcont x₀ β' γ'‖
      ≤ (T : ℝ) * ‖β - β'‖ + Real.sqrt T * ‖γ - γ'‖ := by
  have heq : l2ItoProcessLp hB T hBmeas hBcont x₀ β γ - l2ItoProcessLp hB T hBmeas hBcont x₀ β' γ'
      = driftProcessAssembled (μ := μ) T hBmeas (β - β')
        + itoProcessAssembled hB T hBmeas hBcont (γ - γ') := by
    rw [map_sub, itoProcessAssembled_sub, l2ItoProcessLp, l2ItoProcessLp]; abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (driftProcessAssembled_norm_le T hBmeas _)
    (itoProcessAssembled_norm_le hB T hBmeas hBcont _))

end Canonical
/-! ### Slices, terminal values and the bounded continuous case -/

section Slices
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

/-- The product-measure version of an `E`-element is square integrable. -/
theorem memLp_prod_coeFn (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    MemLp (⇑φ) 2 ((timeMeasureHorizon T).prod μ) :=
  memLp_prod_of_trim T hBmeas (Lp.stronglyMeasurable φ) (Lp.memLp φ)

theorem integrable_prod_coeFn (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    Integrable (⇑φ) ((timeMeasureHorizon T).prod μ) :=
  (memLp_prod_coeFn T hBmeas φ).integrable one_le_two

theorem integrable_prod_coeFn_sq (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    Integrable (fun z => (φ z) ^ 2) ((timeMeasureHorizon T).prod μ) :=
  (memLp_prod_coeFn T hBmeas φ).integrable_sq

/-- Time slices of the drift are square integrable. -/
theorem memLp_driftContinuousMod_slice (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {t : ℝ≥0} (htT : t ≤ T) :
    MemLp (fun ω => driftContinuousMod T hBmeas φ t ω) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun ω => driftContinuousMod T hBmeas φ t ω) μ :=
    ((driftContinuousMod_stronglyAdapted T hBmeas φ t).mono
      ((natFiltration hBmeas).le t)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hint := integrable_prod_coeFn_sq T hBmeas φ
  have hbound : Integrable (fun ω => (T : ℝ) * ∫ u in Set.Ioc 0 T, (φ (u, ω)) ^ 2 ∂timeMeasure) μ :=
    (Integrable.integral_prod_right hint).const_mul _
  refine hbound.mono' (hmeas.pow 2) ?_
  have hslice : ∀ᵐ ω ∂μ, Integrable (fun u => (φ (u, ω)) ^ 2) (timeMeasureHorizon T) :=
    hint.prod_left_ae
  have hφm : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] (⇑φ) :=
    Lp.stronglyMeasurable φ
  have hmeas_slice : ∀ ω, StronglyMeasurable (fun u => φ (u, ω)) := fun ω =>
    (hφm.mono (natFiltration hBmeas).predictable_le_prod).comp_measurable
      measurable_prodMk_right
  filter_upwards [driftContinuousMod_eq_setIntegral T hBmeas φ htT, hslice] with ω hω hsl
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hω]
  have hmemω : MemLp (fun u => φ (u, ω)) 2 (timeMeasure.restrict (Set.Ioc 0 t)) := by
    rw [memLp_two_iff_integrable_sq (hmeas_slice ω).aestronglyMeasurable]
    rw [← timeMeasure_T_restrict_Ioc T htT]
    exact hsl.restrict
  letI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc 0 t)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hCS := MathFin.sq_integral_le_measureReal_mul hmemω
  rw [Measure.restrict_apply_univ, timeMeasure_Ioc,
    ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact t.coe_nonneg),
    NNReal.coe_zero, sub_zero] at hCS
  refine hCS.trans (mul_le_mul (by exact_mod_cast htT) ?_
    (integral_nonneg fun _ => sq_nonneg _) T.coe_nonneg)
  exact setIntegral_mono_set hsl (ae_of_all _ fun _ => sq_nonneg _)
    (Set.Ioc_subset_Ioc_right htT).eventuallyLE

/-- The drift is linear at a fixed time, almost surely. -/
theorem driftContinuousMod_sub_ae (φ ψ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {t : ℝ≥0} (htT : t ≤ T) :
    ∀ᵐ ω ∂μ, driftContinuousMod T hBmeas (φ - ψ) t ω
      = driftContinuousMod T hBmeas φ t ω - driftContinuousMod T hBmeas ψ t ω := by
  have hsub : ∀ᵐ ω ∂μ, ∀ᵐ u ∂(timeMeasureHorizon T), (φ - ψ) (u, ω) = φ (u, ω) - ψ (u, ω) := by
    have h1 : ⇑(φ - ψ) =ᵐ[(timeMeasureHorizon T).prod μ] ⇑φ - ⇑ψ :=
      ae_eq_of_ae_eq_trim (Lp.coeFn_sub φ ψ)
    have h2 : ∀ᵐ z ∂μ.prod (timeMeasureHorizon T), (φ - ψ) (z.2, z.1) = φ (z.2, z.1) - ψ (z.2,
          z.1) :=
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae h1
    exact Measure.ae_ae_of_ae_prod h2
  filter_upwards [driftContinuousMod_eq_setIntegral T hBmeas (φ - ψ) htT,
    driftContinuousMod_eq_setIntegral T hBmeas φ htT,
    driftContinuousMod_eq_setIntegral T hBmeas ψ htT, hsub,
    (integrable_prod_coeFn T hBmeas φ).prod_left_ae,
    (integrable_prod_coeFn T hBmeas ψ).prod_left_ae] with ω h1 h2 h3 h4 hiφ hiψ
  rw [h1, h2, h3, ← integral_sub]
  · refine integral_congr_ae ?_
    rw [← timeMeasure_T_restrict_Ioc T htT]
    exact ae_restrict_of_ae h4
  · rw [← timeMeasure_T_restrict_Ioc T htT]; exact hiφ.restrict
  · rw [← timeMeasure_T_restrict_Ioc T htT]; exact hiψ.restrict

include hBcont in
/-- The continuous Itô modification at the terminal time is the Itô integral. -/
theorem itoContinuousMod_terminal_ae (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    (fun ω => itoContinuousMod T hBmeas φ T ω) =ᵐ[μ] ⇑(itoIntegralCLM hB T hBmeas φ) := by
  filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont φ le_rfl] with ω hω
  rw [hω, itoProcessCLM_terminal_eq]

include hB hBcont in
/-- **Terminal `L¹` stability** of the canonical Itô process in its integrands. -/
theorem integral_abs_terminal_sub_le (x₀ : ℝ)
    (β γ β' γ' : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∫ ω, |l2ItoProcess T hBmeas x₀ β γ T ω - l2ItoProcess T hBmeas x₀ β' γ' T ω| ∂μ
      ≤ Real.sqrt T * ‖β - β'‖ + ‖γ - γ'‖ := by
  set D := fun ω => driftContinuousMod T hBmeas (β - β') T ω
  set I := ⇑(itoIntegralCLM hB T hBmeas (γ - γ'))
  have hDmem := memLp_driftContinuousMod_slice T hBmeas (β - β') le_rfl
  have hImem : MemLp I 2 μ := Lp.memLp _
  have hae : (fun ω => l2ItoProcess T hBmeas x₀ β γ T ω - l2ItoProcess T hBmeas x₀ β' γ' T ω)
      =ᵐ[μ] fun ω => D ω + I ω := by
    filter_upwards [driftContinuousMod_sub_ae T hBmeas β β' le_rfl,
      itoContinuousMod_terminal_ae hB T hBmeas hBcont γ,
      itoContinuousMod_terminal_ae hB T hBmeas hBcont γ',
      Lp.coeFn_sub (itoIntegralCLM hB T hBmeas γ) (itoIntegralCLM hB T hBmeas γ')]
      with ω hd hi hi' hsub
    simp only [l2ItoProcess, D, I, map_sub, hd, hsub, Pi.sub_apply, ← hi, ← hi']
    ring
  have hae' : (fun ω => |l2ItoProcess T hBmeas x₀ β γ T ω - l2ItoProcess T hBmeas x₀ β' γ' T ω|)
      =ᵐ[μ] fun ω => |D ω + I ω| := hae.mono fun ω hω => congrArg abs hω
  rw [integral_congr_ae hae']
  calc ∫ ω, |D ω + I ω| ∂μ ≤ ∫ ω, (|D ω| + |I ω|) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          ((hDmem.integrable one_le_two).abs.add (hImem.integrable one_le_two).abs)
          (ae_of_all _ fun ω => abs_add_le _ _)
    _ = ∫ ω, |D ω| ∂μ + ∫ ω, |I ω| ∂μ :=
        integral_add (hDmem.integrable one_le_two).abs (hImem.integrable one_le_two).abs
    _ ≤ Real.sqrt T * ‖β - β'‖ + ‖γ - γ'‖ := by
        gcongr
        · refine (integral_abs_le_sqrt_integral_sq hDmem).trans ?_
          have h := integral_driftSlice_sq_le T hBmeas (β - β') (le_refl T)
          rw [bandEnergy_self] at h
          calc Real.sqrt (∫ ω, D ω ^ 2 ∂μ) ≤ Real.sqrt ((T : ℝ) * ‖β - β'‖ ^ 2) :=
                Real.sqrt_le_sqrt h
            _ = Real.sqrt T * ‖β - β'‖ := by
                rw [Real.sqrt_mul T.coe_nonneg, Real.sqrt_sq (norm_nonneg _)]
        · refine (integral_abs_le_sqrt_integral_sq hImem).trans ?_
          rw [← MathFin.lp_two_norm_sq, Real.sqrt_sq (norm_nonneg _), itoIntegralCLM_norm]

end Slices

/-! ### General convergence lemmas on a finite measure space -/

section Convergence
variable {α : Type*} {m : MeasurableSpace α} {ν : Measure α} [IsFiniteMeasure ν]

theorem abs_sub_le_of_deriv_bound {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) {C : ℝ}
    (hC : ∀ x, |f' x| ≤ C) (a b : ℝ) : |f a - f b| ≤ C * |a - b| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := Set.univ)
    (fun x _ => (hf x).differentiableAt) (fun x _ => by rw [(hf x).deriv]; exact hC x)
    convex_univ (Set.mem_univ b) (Set.mem_univ a)
  simpa [Real.norm_eq_abs] using this

/-- `L¹ ≤ √ν(univ) · L²`. -/
theorem integral_abs_le_sqrt_mul_norm (u : Lp ℝ 2 ν) :
    ∫ x, |u x| ∂ν ≤ Real.sqrt (ν.real Set.univ) * ‖u‖ := by
  have h := integral_abs_mul_le_sqrt_mul_sqrt (Lp.memLp u) (memLp_const (1 : ℝ) (μ := ν))
  simp only [mul_one, one_pow, integral_const, smul_eq_mul] at h
  rw [← MathFin.lp_two_norm_sq, Real.sqrt_sq (norm_nonneg _)] at h
  linarith [h]

/-- Dominated convergence for weighted differences. -/
theorem tendsto_integral_abs_sub_mul {g : ℕ → α → ℝ} {g₀ h : α → ℝ} {M : ℝ}
    (hgm : ∀ n, AEStronglyMeasurable (g n) ν) (hg₀m : AEStronglyMeasurable g₀ ν)
    (hh : Integrable h ν) (hbd : ∀ n, ∀ᵐ x ∂ν, |g n x| ≤ M) (hbd₀ : ∀ᵐ x ∂ν, |g₀ x| ≤ M)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => g n x) atTop (𝓝 (g₀ x))) :
    Tendsto (fun n => ∫ x, |g n x - g₀ x| * |h x| ∂ν) atTop (𝓝 0) := by
  have key := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun n x => |g n x - g₀ x| * |h x|) (f := fun _ => (0 : ℝ)) (fun x => 2 * M * |h x|)
    (fun n => ((hgm n).sub hg₀m).norm.mul hh.aestronglyMeasurable.norm)
    (hh.abs.const_mul _)
    (fun n => by
      filter_upwards [hbd n, hbd₀] with x h1 h2
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
      have : |g n x - g₀ x| ≤ 2 * M := by
        calc |g n x - g₀ x| ≤ |g n x| + |g₀ x| := abs_sub _ _
          _ ≤ 2 * M := by linarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _))
    (by
      filter_upwards [hlim] with x hx
      have h0 : Tendsto (fun n => |g n x - g₀ x|) atTop (𝓝 0) := by
        have := (hx.sub_const (g₀ x)).abs
        simpa using this
      simpa using h0.mul_const |h x|)
  simpa using key

theorem tendsto_integral_abs_coeFn_sub {v : ℕ → Lp ℝ 2 ν} {v₀ : Lp ℝ 2 ν}
    (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun k => ∫ x, |v k x - v₀ x| ∂ν) atTop (𝓝 0) := by
  have hn : Tendsto (fun k => Real.sqrt (ν.real Set.univ) * ‖v k - v₀‖) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hv).const_mul (Real.sqrt (ν.real Set.univ))
    simpa using this
  refine squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun k => ?_) hn
  calc ∫ x, |v k x - v₀ x| ∂ν = ∫ x, |(v k - v₀) x| ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_sub (v k) v₀] with x hx
        rw [hx, Pi.sub_apply]
    _ ≤ _ := integral_abs_le_sqrt_mul_norm (v k - v₀)

/-- `L¹` convergence of `g(Y_k) v_k`. -/
theorem tendsto_integral_abs_comp_mul_sub {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) {Y : ℕ → α → ℝ} {Y₀ : α → ℝ}
    (hYm : ∀ k, AEStronglyMeasurable (Y k) ν) (hY₀m : AEStronglyMeasurable Y₀ ν)
    (hY : ∀ᵐ x ∂ν, Tendsto (fun k => Y k x) atTop (𝓝 (Y₀ x)))
    {v : ℕ → Lp ℝ 2 ν} {v₀ : Lp ℝ 2 ν} (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun k => ∫ x, |g (Y k x) * v k x - g (Y₀ x) * v₀ x| ∂ν) atTop (𝓝 0) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  have hv₀i : Integrable (⇑v₀) ν := (Lp.memLp v₀).integrable one_le_two
  have h1 := (tendsto_integral_abs_coeFn_sub hv).const_mul C
  have h2 := tendsto_integral_abs_sub_mul (g := fun k x => g (Y k x)) (g₀ := fun x => g (Y₀ x))
    (h := ⇑v₀) (M := C) (fun k => hg.comp_aestronglyMeasurable (hYm k))
    (hg.comp_aestronglyMeasurable hY₀m) hv₀i (fun k => ae_of_all _ fun x => hgC _)
    (ae_of_all _ fun x => hgC _)
    (by filter_upwards [hY] with x hx using (hg.tendsto _).comp hx)
  have hsum := h1.add h2
  rw [mul_zero, add_zero] at hsum
  refine squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun k => ?_) hsum
  have hvki : Integrable (⇑(v k)) ν := (Lp.memLp (v k)).integrable one_le_two
  have hint1 : Integrable (fun x => C * |v k x - v₀ x|) ν := ((hvki.sub hv₀i).abs).const_mul C
  have hint2 : Integrable (fun x => |g (Y k x) - g (Y₀ x)| * |v₀ x|) ν := by
    refine Integrable.bdd_mul (c := 2 * C) hv₀i.abs ?_ ?_
    · exact ((hg.comp_aestronglyMeasurable (hYm k)).sub
        (hg.comp_aestronglyMeasurable hY₀m)).norm
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_abs]
      calc |g (Y k x) - g (Y₀ x)| ≤ |g (Y k x)| + |g (Y₀ x)| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hgC (Y k x), hgC (Y₀ x)]
  rw [← integral_const_mul, ← integral_add hint1 hint2]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hint1.add hint2)
    (ae_of_all _ fun x => ?_)
  have e : g (Y k x) * v k x - g (Y₀ x) * v₀ x
      = g (Y k x) * (v k x - v₀ x) + (g (Y k x) - g (Y₀ x)) * v₀ x := by ring
  beta_reduce
  rw [e]
  calc |g (Y k x) * (v k x - v₀ x) + (g (Y k x) - g (Y₀ x)) * v₀ x|
      ≤ |g (Y k x) * (v k x - v₀ x)| + |(g (Y k x) - g (Y₀ x)) * v₀ x| := abs_add_le _ _
    _ ≤ C * |v k x - v₀ x| + |g (Y k x) - g (Y₀ x)| * |v₀ x| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hgC _) (abs_nonneg _)) le_rfl

/-- `L¹` convergence of `g(Y_k) v_k²`. -/
theorem tendsto_integral_abs_comp_mul_sq_sub {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) {Y : ℕ → α → ℝ} {Y₀ : α → ℝ}
    (hYm : ∀ k, AEStronglyMeasurable (Y k) ν) (hY₀m : AEStronglyMeasurable Y₀ ν)
    (hY : ∀ᵐ x ∂ν, Tendsto (fun k => Y k x) atTop (𝓝 (Y₀ x)))
    {v : ℕ → Lp ℝ 2 ν} {v₀ : Lp ℝ 2 ν} (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun k => ∫ x, |g (Y k x) * v k x ^ 2 - g (Y₀ x) * v₀ x ^ 2| ∂ν) atTop (𝓝 0) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  have hv₀2 : Integrable (fun x => v₀ x ^ 2) ν := (Lp.memLp v₀).integrable_sq
  -- `∫|v_k² - v₀²| ≤ ‖v_k - v₀‖·‖v_k + v₀‖ → 0`
  have hsq : Tendsto (fun k => ∫ x, |v k x ^ 2 - v₀ x ^ 2| ∂ν) atTop (𝓝 0) := by
    have hb : Tendsto (fun k => ‖v k - v₀‖ * ‖v k + v₀‖) atTop (𝓝 (0 * ‖v₀ + v₀‖)) :=
      (tendsto_iff_norm_sub_tendsto_zero.mp hv).mul
        ((hv.add tendsto_const_nhds).norm)
    rw [zero_mul] at hb
    refine squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun k => ?_) hb
    have hCS := integral_abs_mul_le_sqrt_mul_sqrt (Lp.memLp (v k - v₀)) (Lp.memLp (v k + v₀))
    rw [← MathFin.lp_two_norm_sq, ← MathFin.lp_two_norm_sq, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (norm_nonneg _)] at hCS
    refine le_of_eq_of_le ?_ hCS
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (v k) v₀, Lp.coeFn_add (v k) v₀] with x h1 h2
    rw [h1, h2, Pi.sub_apply, Pi.add_apply]
    congr 1
    ring
  have h1 := hsq.const_mul C
  have h2 := tendsto_integral_abs_sub_mul (g := fun k x => g (Y k x)) (g₀ := fun x => g (Y₀ x))
    (h := fun x => v₀ x ^ 2) (M := C) (fun k => hg.comp_aestronglyMeasurable (hYm k))
    (hg.comp_aestronglyMeasurable hY₀m) hv₀2 (fun k => ae_of_all _ fun x => hgC _)
    (ae_of_all _ fun x => hgC _)
    (by filter_upwards [hY] with x hx using (hg.tendsto _).comp hx)
  have hsum := h1.add h2
  rw [mul_zero, add_zero] at hsum
  refine squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun k => ?_) hsum
  have hvk2 : Integrable (fun x => v k x ^ 2) ν := (Lp.memLp (v k)).integrable_sq
  have hint1 : Integrable (fun x => C * |v k x ^ 2 - v₀ x ^ 2|) ν := ((hvk2.sub
        hv₀2).abs).const_mul C
  have hint2 : Integrable (fun x => |g (Y k x) - g (Y₀ x)| * |v₀ x ^ 2|) ν := by
    refine Integrable.bdd_mul (c := 2 * C) hv₀2.abs ?_ ?_
    · exact ((hg.comp_aestronglyMeasurable (hYm k)).sub
        (hg.comp_aestronglyMeasurable hY₀m)).norm
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_abs]
      calc |g (Y k x) - g (Y₀ x)| ≤ |g (Y k x)| + |g (Y₀ x)| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hgC (Y k x), hgC (Y₀ x)]
  rw [← integral_const_mul, ← integral_add hint1 hint2]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hint1.add hint2)
    (ae_of_all _ fun x => ?_)
  have e : g (Y k x) * v k x ^ 2 - g (Y₀ x) * v₀ x ^ 2
      = g (Y k x) * (v k x ^ 2 - v₀ x ^ 2) + (g (Y k x) - g (Y₀ x)) * v₀ x ^ 2 := by ring
  beta_reduce
  rw [e]
  calc |g (Y k x) * (v k x ^ 2 - v₀ x ^ 2) + (g (Y k x) - g (Y₀ x)) * v₀ x ^ 2|
      ≤ |g (Y k x) * (v k x ^ 2 - v₀ x ^ 2)| + |(g (Y k x) - g (Y₀ x)) * v₀ x ^ 2| :=
        abs_add_le _ _
    _ ≤ C * |v k x ^ 2 - v₀ x ^ 2| + |g (Y k x) - g (Y₀ x)| * |v₀ x ^ 2| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hgC _) (abs_nonneg _)) le_rfl

/-- `L²` convergence of `g(Y_k) v_k`. -/
theorem tendsto_Lp_comp_mul {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) {Y : ℕ → α → ℝ} {Y₀ : α → ℝ}
    (hYm : ∀ k, AEStronglyMeasurable (Y k) ν) (hY₀m : AEStronglyMeasurable Y₀ ν)
    (hY : ∀ᵐ x ∂ν, Tendsto (fun k => Y k x) atTop (𝓝 (Y₀ x)))
    {v : ℕ → Lp ℝ 2 ν} {v₀ : Lp ℝ 2 ν} (hv : Tendsto v atTop (𝓝 v₀))
    {w : ℕ → Lp ℝ 2 ν} {w₀ : Lp ℝ 2 ν} (hw : ∀ k, ⇑(w k) =ᵐ[ν] fun x => g (Y k x) * v k x)
    (hw₀ : ⇑w₀ =ᵐ[ν] fun x => g (Y₀ x) * v₀ x) :
    Tendsto w atTop (𝓝 w₀) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hv₀2 : Integrable (fun x => v₀ x ^ 2) ν := (Lp.memLp v₀).integrable_sq
  have hD := tendsto_integral_abs_sub_mul (g := fun k x => g (Y k x)) (g₀ := fun x => g (Y₀ x))
    (h := fun x => v₀ x ^ 2) (M := C) (fun k => hg.comp_aestronglyMeasurable (hYm k))
    (hg.comp_aestronglyMeasurable hY₀m) hv₀2 (fun k => ae_of_all _ fun x => hgC _)
    (ae_of_all _ fun x => hgC _)
    (by filter_upwards [hY] with x hx using (hg.tendsto _).comp hx)
  have hN := tendsto_iff_norm_sub_tendsto_zero.mp hv
  have hbound : Tendsto (fun k => Real.sqrt (2 * C ^ 2 * ‖v k - v₀‖ ^ 2
      + 4 * C * ∫ x, |g (Y k x) - g (Y₀ x)| * |v₀ x ^ 2| ∂ν)) atTop (𝓝 0) := by
    have : Tendsto (fun k => 2 * C ^ 2 * ‖v k - v₀‖ ^ 2
        + 4 * C * ∫ x, |g (Y k x) - g (Y₀ x)| * |v₀ x ^ 2| ∂ν) atTop (𝓝 0) := by
      have := ((hN.pow 2).const_mul (2 * C ^ 2)).add (hD.const_mul (4 * C))
      simpa using this
    simpa using this.sqrt
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hbound
  rw [← Real.sqrt_sq (norm_nonneg (w k - w₀))]
  refine Real.sqrt_le_sqrt ?_
  have hvk2 : Integrable (fun x => (v k x - v₀ x) ^ 2) ν := by
    have := (Lp.memLp (v k - v₀)).integrable_sq
    refine this.congr ?_
    filter_upwards [Lp.coeFn_sub (v k) v₀] with x hx
    rw [hx, Pi.sub_apply]
  have hint2 : Integrable (fun x => |g (Y k x) - g (Y₀ x)| * |v₀ x ^ 2|) ν := by
    refine Integrable.bdd_mul (c := 2 * C) hv₀2.abs ?_ ?_
    · exact ((hg.comp_aestronglyMeasurable (hYm k)).sub
        (hg.comp_aestronglyMeasurable hY₀m)).norm
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_abs]
      calc |g (Y k x) - g (Y₀ x)| ≤ |g (Y k x)| + |g (Y₀ x)| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hgC (Y k x), hgC (Y₀ x)]
  have hnv : ‖v k - v₀‖ ^ 2 = ∫ x, (v k x - v₀ x) ^ 2 ∂ν := by
    rw [MathFin.lp_two_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (v k) v₀] with x hx
    rw [hx, Pi.sub_apply]
  rw [MathFin.lp_two_norm_sq, hnv, ← integral_const_mul, ← integral_const_mul, ← integral_add
    (hvk2.const_mul _) (hint2.const_mul _)]
  refine integral_mono_ae ((Lp.memLp (w k - w₀)).integrable_sq)
    ((hvk2.const_mul _).add (hint2.const_mul _)) ?_
  filter_upwards [Lp.coeFn_sub (w k) w₀, hw k, hw₀] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  have hb1 : |g (Y k x)| ≤ C := hgC _
  have hb2 : |g (Y k x) - g (Y₀ x)| ≤ 2 * C := by
    calc |g (Y k x) - g (Y₀ x)| ≤ |g (Y k x)| + |g (Y₀ x)| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hgC (Y k x), hgC (Y₀ x)]
  have e : g (Y k x) * v k x - g (Y₀ x) * v₀ x
      = g (Y k x) * (v k x - v₀ x) + (g (Y k x) - g (Y₀ x)) * v₀ x := by ring
  rw [e]
  have hA : (g (Y k x) * (v k x - v₀ x)) ^ 2 ≤ C ^ 2 * (v k x - v₀ x) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (g (Y k x)), sq_abs (g (Y k x))])
      (sq_nonneg _)
  have hB2 : ((g (Y k x) - g (Y₀ x)) * v₀ x) ^ 2
      ≤ 2 * C * (|g (Y k x) - g (Y₀ x)| * |v₀ x ^ 2|) := by
    rw [mul_pow, abs_of_nonneg (sq_nonneg (v₀ x)), ← sq_abs (g (Y k x) - g (Y₀ x))]
    have h0 : 0 ≤ |g (Y k x) - g (Y₀ x)| := abs_nonneg _
    have hprod := mul_nonneg (mul_nonneg h0 (sq_nonneg (v₀ x))) (sub_nonneg.mpr hb2)
    nlinarith [hprod]
  nlinarith [sq_nonneg (g (Y k x) * (v k x - v₀ x) - (g (Y k x) - g (Y₀ x)) * v₀ x)]

end Convergence

/-! ### The bounded continuous adapted case -/

section BaseCase
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

theorem driftPath_eq_driftContinuousMod (sb : ContAdaptedBdd hBmeas) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T,
      driftPath sb.toFun t ω = driftContinuousMod T hBmeas (sb.toLp (μ := μ) T) t ω := by
  have hG : ⇑(sb.toLp (μ := μ) T) =ᵐ[(timeMeasureHorizon T).prod μ] Function.uncurry sb.toFun :=
    ae_eq_of_ae_eq_trim (sb.coeFn_toLp T)
  have hGswap : ∀ᵐ z ∂μ.prod (timeMeasureHorizon T),
      (sb.toLp (μ := μ) T) (z.2, z.1) = sb.toFun z.2 z.1 :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hG
  filter_upwards [Measure.ae_ae_of_ae_prod hGswap,
    driftContinuousMod_eq_setIntegral_all T hBmeas (sb.toLp (μ := μ) T)] with ω hcoeff hdrift
  intro t ht
  rw [hdrift t ht, driftPath]
  apply integral_congr_ae
  exact (hcoeff.filter_mono (ae_mono
    (Measure.restrict_mono (Set.Ioc_subset_Ioc_right ht) le_rfl))).mono fun s hs => hs.symm

include hB hBcont in
/-- Itô's formula for bounded continuous adapted integrands, on the canonical process. -/
theorem ito_formula_contAdapted (sb sσ : ContAdaptedBdd hBmeas) (x₀ : ℝ)
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') {C₁ C₂ : ℝ} (hf1 : ∀ x, |f' x| ≤ C₁) (hf2 : ∀ x, |f'' x| ≤ C₂) :
    ∃ Γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas),
      (⇑Γ =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z =>
        f' (l2ItoProcess T hBmeas x₀ (sb.toLp (μ := μ) T) (sσ.toLp (μ := μ) T) z.1 z.2) *
              sσ.toFun z.1 z.2) ∧
      (fun ω => f (l2ItoProcess T hBmeas x₀ (sb.toLp (μ := μ) T) (sσ.toLp (μ := μ) T) T ω) - f
            x₀) =ᵐ[μ]
        fun ω => itoIntegralCLM hB T hBmeas Γ ω + ∫ s in Set.Ioc 0 T,
          (f' (l2ItoProcess T hBmeas x₀ (sb.toLp (μ := μ) T) (sσ.toLp (μ := μ) T) s ω) *
                sb.toFun s ω
            + 1 / 2 * (f'' (l2ItoProcess T hBmeas x₀ (sb.toLp (μ := μ) T) (sσ.toLp (μ := μ) T) s ω)
              * sσ.toFun s ω ^ 2)) ∂timeMeasure := by
  have hito := ito_formula_adapted hB T hBmeas hBcont sσ.adapted sσ.cont sσ.bdd sb.adapted
    sb.cont sb.bdd x₀ hf hf' hf'' hf1 hf2
  set X' := adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas sσ.adapted sσ.cont sσ.bdd)
    x₀ sb.toFun with hX'
  set X := l2ItoProcess T hBmeas x₀ (sb.toLp (μ := μ) T) (sσ.toLp (μ := μ) T) with hX
  have hpath : ∀ᵐ ω ∂μ, ∀ t ≤ T, X' t ω = X t ω := by
    filter_upwards [driftPath_eq_driftContinuousMod (μ := μ) T hBmeas sb] with ω hω t ht
    simp only [X', X, adaptedItoProcess, l2ItoProcess, hω t ht]
    rfl
  have hf'c : Continuous f' := Differentiable.continuous fun x => (hf' x).differentiableAt
  have hpred' : IsStronglyPredictable (natFiltration hBmeas)
      fun s ω => f' (X' s ω) * sσ.toFun s ω :=
    comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont sσ.adapted sσ.cont
      (processToLp (μ := μ) T hBmeas sσ.adapted sσ.cont sσ.bdd) sb.adapted sb.cont sb.bdd x₀ hf'c
  have hbdd' : ∀ s ω, |f' (X' s ω) * sσ.toFun s ω| ≤ C₁ * sσ.bound :=
    abs_comp_mul_le hf1 sσ.bdd X'
  refine ⟨processToLpPredictable (μ := μ) T hBmeas hpred' hbdd', ?_, ?_⟩
  · have h1 := processToLpPredictable_coeFn (μ := μ) T hBmeas hpred' hbdd'
    have hXpred := l2ItoProcess_isStronglyPredictable hB T hBmeas hBcont x₀
      (sb.toLp (μ := μ) T) (sσ.toLp (μ := μ) T)
    have hσpred := isStronglyPredictable_of_bdd_adapted_cont hBmeas sσ.adapted sσ.cont
    have h2 : (Function.uncurry fun s ω => f' (X' s ω) * sσ.toFun s ω)
        =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => f' (X z.1 z.2) * sσ.toFun z.1 z.2 :=
      ae_eq_trim_of_pathwise T hBmeas hpred'
        ((hf'c.comp_stronglyMeasurable hXpred).mul hσpred)
        (hpath.mono fun ω hω t ht => by simp only [Function.uncurry, hω t ht])
    exact h1.trans h2
  · filter_upwards [hito, hpath] with ω hω hp
    have hT : X' T ω = X T ω := hp T le_rfl
    calc f (X T ω) - f x₀ = f (X' T ω) - f x₀ := by rw [hT]
      _ = itoIntegralCLM hB T hBmeas (processToLpPredictable (μ := μ) T hBmeas hpred' hbdd') ω
          + ∫ s in Set.Ioc 0 T, (f' (X' s ω) * sb.toFun s ω
            + 1 / 2 * (f'' (X' s ω) * sσ.toFun s ω ^ 2)) ∂timeMeasure := hω
      _ = itoIntegralCLM hB T hBmeas (processToLpPredictable (μ := μ) T hBmeas hpred' hbdd') ω
          + ∫ s in Set.Ioc 0 T, (f' (X s ω) * sb.toFun s ω
            + 1 / 2 * (f'' (X s ω) * sσ.toFun s ω ^ 2)) ∂timeMeasure := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
        rw [hp s hs.2]

end BaseCase

/-! ### The general case -/

section General
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

theorem memLp_comp_mul_coeFn {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStronglyPredictable (natFiltration hBmeas) X)
    {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C)
    (γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    MemLp (fun z => g (X z.1 z.2) * γ z) 2 (trimMeasure (μ := μ) T hBmeas) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  refine ((Lp.memLp γ).const_mul C).of_le ?_ (ae_of_all _ fun z => ?_)
  · exact ((hg.comp_stronglyMeasurable hX).mul (Lp.stronglyMeasurable γ)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (hgC _) (abs_nonneg _)

include hB hBcont in
theorem integrable_comp_terminal (x₀ : ℝ) (β γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) {C₁ : ℝ} (hf1 : ∀ x, |f' x| ≤ C₁) :
    Integrable (fun ω => f (l2ItoProcess T hBmeas x₀ β γ T ω) - f x₀) μ := by
  have hfc : Continuous f := Differentiable.continuous fun x => (hf x).differentiableAt
  have hXpred := l2ItoProcess_isStronglyPredictable hB T hBmeas hBcont x₀ β γ
  have hXT : StronglyMeasurable (fun ω => l2ItoProcess T hBmeas x₀ β γ T ω) :=
    (hXpred.stronglyAdapted T).mono ((natFiltration hBmeas).le T)
  have hD := (memLp_driftContinuousMod_slice T hBmeas β (le_refl T)).integrable one_le_two
  have hI : Integrable (⇑(itoIntegralCLM hB T hBmeas γ)) μ := (Lp.memLp _).integrable one_le_two
  refine ((hD.abs.add hI.abs).const_mul C₁).mono'
    ((hfc.comp_stronglyMeasurable hXT).sub stronglyMeasurable_const).aestronglyMeasurable ?_
  filter_upwards [itoContinuousMod_terminal_ae hB T hBmeas hBcont γ] with ω hω
  rw [Real.norm_eq_abs]
  refine (abs_sub_le_of_deriv_bound hf hf1 _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hf1 0))
  simp only [l2ItoProcess, hω]
  rw [show x₀ + driftContinuousMod T hBmeas β T ω + (itoIntegralCLM hB T hBmeas γ) ω - x₀
      = driftContinuousMod T hBmeas β T ω + (itoIntegralCLM hB T hBmeas γ) ω by ring]
  exact abs_add_le _ _

include hB hBcont in
/-- **Itô's formula for predictable `L²` integrands.**  For `β, γ` in the predictable `L²`
space on `(0,T] × Ω`, `X = x₀ + ∫ β ds + ∫ γ dB` and `f ∈ C²` with `f'`, `f''` bounded, almost
surely `f(X_T) - f(x₀) = ∫₀ᵀ f'(X)γ dB + ∫₀ᵀ (f'(X)β + ½ f''(X)γ²) ds`, the stochastic integral
being the Itô integral of the class `Γ` of `f'(X)γ`. -/
theorem ito_formula_L2 (x₀ : ℝ) (β γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') {C₁ C₂ : ℝ} (hf1 : ∀ x, |f' x| ≤ C₁) (hf2 : ∀ x, |f'' x| ≤ C₂) :
    ∃ Γ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas),
      (⇑Γ =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z =>
        f' (l2ItoProcess T hBmeas x₀ β γ z.1 z.2) * γ z) ∧
      (fun ω => f (l2ItoProcess T hBmeas x₀ β γ T ω) - f x₀) =ᵐ[μ] fun ω =>
        itoIntegralCLM hB T hBmeas Γ ω + ∫ s in Set.Ioc 0 T,
          (f' (l2ItoProcess T hBmeas x₀ β γ s ω) * β (s, ω)
            + 1 / 2 * (f'' (l2ItoProcess T hBmeas x₀ β γ s ω) * γ (s, ω) ^ 2)) ∂timeMeasure := by
  set X := l2ItoProcess T hBmeas x₀ β γ with hXdef
  have hXpred : IsStronglyPredictable (natFiltration hBmeas) X :=
    l2ItoProcess_isStronglyPredictable hB T hBmeas hBcont x₀ β γ
  have hf'c : Continuous f' := Differentiable.continuous fun x => (hf' x).differentiableAt
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (hf1 0)
  have hC₂ : 0 ≤ C₂ := (abs_nonneg _).trans (hf2 0)
  have hΓmem := memLp_comp_mul_coeFn T hBmeas hXpred hf'c hf1 γ
  refine ⟨hΓmem.toLp _, hΓmem.coeFn_toLp, ?_⟩
  set Γ := hΓmem.toLp (fun z => f' (X z.1 z.2) * γ z) with hΓdef
  -- approximating sequences and the a.e.-convergent subsequence of processes
  obtain ⟨sb₀, hsb₀⟩ := exists_seq_contAdaptedBdd_tendsto (μ := μ) T hBmeas β
  obtain ⟨sσ₀, hsσ₀⟩ := exists_seq_contAdaptedBdd_tendsto (μ := μ) T hBmeas γ
  have hu : Tendsto (fun n => l2ItoProcessLp hB T hBmeas hBcont x₀ ((sb₀ n).toLp T)
      ((sσ₀ n).toLp T)) atTop (𝓝 (l2ItoProcessLp hB T hBmeas hBcont x₀ β γ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun n => norm_l2ItoProcessLp_sub_le hB T hBmeas hBcont x₀ _ _ _ _) ?_
    have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp hsb₀).const_mul (T : ℝ)
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.mp hsσ₀).const_mul (Real.sqrt T)
    simpa using h1.add h2
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  set sb : ℕ → ContAdaptedBdd hBmeas := fun i => sb₀ (ns i)
  set sσ : ℕ → ContAdaptedBdd hBmeas := fun i => sσ₀ (ns i)
  have hsb : Tendsto (fun i => (sb i).toLp (μ := μ) T) atTop (𝓝 β) :=
    hsb₀.comp hns.tendsto_atTop
  have hsσ : Tendsto (fun i => (sσ i).toLp (μ := μ) T) atTop (𝓝 γ) :=
    hsσ₀.comp hns.tendsto_atTop
  set Xk : ℕ → ℝ≥0 → Ω → ℝ := fun i =>
    l2ItoProcess T hBmeas x₀ ((sb i).toLp (μ := μ) T) ((sσ i).toLp (μ := μ) T)
  have hXkpred : ∀ i, IsStronglyPredictable (natFiltration hBmeas) (Xk i) := fun i =>
    l2ItoProcess_isStronglyPredictable hB T hBmeas hBcont x₀ _ _
  have hY : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas),
      Tendsto (fun i => Xk i z.1 z.2) atTop (𝓝 (X z.1 z.2)) := by
    filter_upwards [hae, coeFn_l2ItoProcessLp hB T hBmeas hBcont x₀ β γ,
      ae_all_iff.mpr fun n => coeFn_l2ItoProcessLp hB T hBmeas hBcont x₀
        ((sb₀ n).toLp (μ := μ) T) ((sσ₀ n).toLp (μ := μ) T)] with z hz h0 hn
    have h0' : l2ItoProcessLp hB T hBmeas hBcont x₀ β γ z = X z.1 z.2 := h0
    rw [← h0']
    refine hz.congr fun i => ?_
    exact hn (ns i)
  have hYm := fun i => (hXkpred i).aestronglyMeasurable (μ := trimMeasure (μ := μ) T hBmeas)
  have hY₀m := hXpred.aestronglyMeasurable (μ := trimMeasure (μ := μ) T hBmeas)
  -- base case along the subsequence
  have hbase := fun i => ito_formula_contAdapted (μ := μ) hB T hBmeas hBcont (sb i) (sσ i) x₀
    hf hf' hf'' hf1 hf2
  choose Γk hΓk hEqk using hbase
  -- (a) convergence of the stochastic integrands
  have hΓconv : Tendsto Γk atTop (𝓝 Γ) := by
    refine tendsto_Lp_comp_mul hf'c hf1 hYm hY₀m hY hsσ (fun i => ?_) hΓmem.coeFn_toLp
    filter_upwards [hΓk i, (sσ i).coeFn_toLp (μ := μ) T] with z h1 h2
    rw [h1, h2]
    rfl
  have hΓ0 := tendsto_iff_norm_sub_tendsto_zero.mp hΓconv
  -- (b), (c) convergence of the drift integrands
  have hdrift := tendsto_integral_abs_comp_mul_sub hf'c hf1 hYm hY₀m hY hsb
  have hqv := tendsto_integral_abs_comp_mul_sq_sub hf'' hf2 hYm hY₀m hY hsσ
  -- (d) terminal values
  have hterm : Tendsto (fun i => C₁ * (Real.sqrt T * ‖(sb i).toLp (μ := μ) T - β‖
      + ‖(sσ i).toLp (μ := μ) T - γ‖)) atTop (𝓝 0) := by
    have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp hsb).const_mul (Real.sqrt T)
    have h2 := tendsto_iff_norm_sub_tendsto_zero.mp hsσ
    simpa using (h1.add h2).const_mul C₁
  -- the total bound tends to zero
  set bnd : ℕ → ℝ := fun i =>
    C₁ * (Real.sqrt T * ‖(sb i).toLp (μ := μ) T - β‖ + ‖(sσ i).toLp (μ := μ) T - γ‖)
      + ‖Γk i - Γ‖
      + ((∫ z, |f' (Xk i z.1 z.2) * ((sb i).toLp (μ := μ) T) z - f' (X z.1 z.2) * β z|
            ∂(trimMeasure (μ := μ) T hBmeas))
        + 1 / 2 * ∫ z, |f'' (Xk i z.1 z.2) * ((sσ i).toLp (μ := μ) T) z ^ 2
            - f'' (X z.1 z.2) * γ z ^ 2| ∂(trimMeasure (μ := μ) T hBmeas))
  have hbnd : Tendsto bnd atTop (𝓝 0) := by
    have := (hterm.add hΓ0).add (hdrift.add (hqv.const_mul (1 / 2)))
    rw [show (0 : ℝ) + 0 + (0 + 1 / 2 * 0) = 0 by norm_num] at this
    exact this
  -- integrability of the limit sides
  set F : ℝ≥0 × Ω → ℝ := fun z => f' (X z.1 z.2) * β z + 1 / 2 * (f'' (X z.1 z.2) * γ z ^ 2)
  have hFm : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] F :=
    ((hf'c.comp_stronglyMeasurable hXpred).mul (Lp.stronglyMeasurable β)).add
      (stronglyMeasurable_const.mul ((hf''.comp_stronglyMeasurable hXpred).mul
        ((Lp.stronglyMeasurable γ).pow 2)))
  have hFint : Integrable F ((timeMeasureHorizon T).prod μ) := by
    refine (((integrable_prod_coeFn T hBmeas β).abs.const_mul C₁).add
      ((integrable_prod_coeFn_sq T hBmeas γ).const_mul (1 / 2 * C₂))).mono'
      (hFm.mono (natFiltration hBmeas).predictable_le_prod).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    calc |F z| ≤ |f' (X z.1 z.2) * β z| + |1 / 2 * (f'' (X z.1 z.2) * γ z ^ 2)| := abs_add_le _ _
      _ ≤ C₁ * |β z| + 1 / 2 * C₂ * γ z ^ 2 := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (γ z)),
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          have e1 := mul_le_mul_of_nonneg_right (hf1 (X z.1 z.2)) (abs_nonneg (β z))
          have e2 := mul_le_mul_of_nonneg_right (hf2 (X z.1 z.2)) (sq_nonneg (γ z))
          nlinarith
  set R : Ω → ℝ := fun ω => itoIntegralCLM hB T hBmeas Γ ω
    + ∫ s in Set.Ioc 0 T, F (s, ω) ∂timeMeasure
  set L : Ω → ℝ := fun ω => f (X T ω) - f x₀
  have hLint : Integrable L μ := integrable_comp_terminal hB T hBmeas hBcont x₀ β γ hf hf1
  have hRint : Integrable R μ :=
    ((Lp.memLp (itoIntegralCLM hB T hBmeas Γ)).integrable one_le_two).add
      (Integrable.integral_prod_right hFint)
  -- the main estimate `∫|L - R| ≤ bnd i`
  have hmain : ∀ i, ∫ ω, |L ω - R ω| ∂μ ≤ bnd i := by
    intro i
    set Fk : ℝ≥0 × Ω → ℝ := fun z => f' (Xk i z.1 z.2) * (sb i).toFun z.1 z.2
      + 1 / 2 * (f'' (Xk i z.1 z.2) * (sσ i).toFun z.1 z.2 ^ 2)
    have hbm := isStronglyPredictable_of_bdd_adapted_cont hBmeas (sb i).adapted (sb i).cont
    have hσm := isStronglyPredictable_of_bdd_adapted_cont hBmeas (sσ i).adapted (sσ i).cont
    have hFkm : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] Fk :=
      ((hf'c.comp_stronglyMeasurable (hXkpred i)).mul hbm).add
        (stronglyMeasurable_const.mul ((hf''.comp_stronglyMeasurable (hXkpred i)).mul
          (hσm.pow 2)))
    have hFkint : Integrable Fk ((timeMeasureHorizon T).prod μ) := by
      refine (integrable_const (C₁ * (sb i).bound + 1 / 2 * C₂ * (sσ i).bound ^ 2)).mono'
        (hFkm.mono (natFiltration hBmeas).predictable_le_prod).aestronglyMeasurable
        (ae_of_all _ fun z => ?_)
      rw [Real.norm_eq_abs]
      have hb := (sb i).bdd z.1 z.2
      have hs := (sσ i).bdd z.1 z.2
      have hs2 : (sσ i).toFun z.1 z.2 ^ 2 ≤ (sσ i).bound ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
      calc |Fk z| ≤ |f' (Xk i z.1 z.2) * (sb i).toFun z.1 z.2|
            + |1 / 2 * (f'' (Xk i z.1 z.2) * (sσ i).toFun z.1 z.2 ^ 2)| := abs_add_le _ _
        _ ≤ C₁ * (sb i).bound + 1 / 2 * C₂ * (sσ i).bound ^ 2 := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ((sσ i).toFun z.1 z.2)),
              abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
            have e1 := mul_le_mul (hf1 (Xk i z.1 z.2)) hb (abs_nonneg _) hC₁
            have e2 := mul_le_mul (hf2 (Xk i z.1 z.2)) hs2 (sq_nonneg _) hC₂
            nlinarith
    set Lk : Ω → ℝ := fun ω => f (Xk i T ω) - f x₀
    set Rk : Ω → ℝ := fun ω => itoIntegralCLM hB T hBmeas (Γk i) ω
      + ∫ s in Set.Ioc 0 T, Fk (s, ω) ∂timeMeasure
    have hLkint : Integrable Lk μ := integrable_comp_terminal hB T hBmeas hBcont x₀ _ _ hf hf1
    have hIint : Integrable (fun ω => itoIntegralCLM hB T hBmeas (Γk i) ω
        - itoIntegralCLM hB T hBmeas Γ ω) μ :=
      ((Lp.memLp _).integrable one_le_two).sub ((Lp.memLp _).integrable one_le_two)
    have hTint : Integrable (fun ω => ∫ s in Set.Ioc 0 T, (Fk (s, ω) - F (s, ω)) ∂timeMeasure) μ :=
      Integrable.integral_prod_right (hFkint.sub hFint)
    -- pointwise estimate
    have hpt : ∀ᵐ ω ∂μ, |L ω - R ω| ≤ |L ω - Lk ω|
        + |itoIntegralCLM hB T hBmeas (Γk i) ω - itoIntegralCLM hB T hBmeas Γ ω|
        + |∫ s in Set.Ioc 0 T, (Fk (s, ω) - F (s, ω)) ∂timeMeasure| := by
      filter_upwards [hEqk i, hFkint.prod_left_ae, hFint.prod_left_ae] with ω hω hk h0
      have hLR : Lk ω = Rk ω := hω
      have hsplit : ∫ s in Set.Ioc 0 T, (Fk (s, ω) - F (s, ω)) ∂timeMeasure
          = (∫ s in Set.Ioc 0 T, Fk (s, ω) ∂timeMeasure)
            - ∫ s in Set.Ioc 0 T, F (s, ω) ∂timeMeasure := integral_sub hk h0
      have e : L ω - R ω = (L ω - Lk ω) + (itoIntegralCLM hB T hBmeas (Γk i) ω
          - itoIntegralCLM hB T hBmeas Γ ω)
          + ∫ s in Set.Ioc 0 T, (Fk (s, ω) - F (s, ω)) ∂timeMeasure := by
        rw [hsplit]
        simp only [R, Rk] at hLR ⊢
        linarith
      rw [e]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    -- integrate the three pieces
    have hP1 : ∫ ω, |L ω - Lk ω| ∂μ
        ≤ C₁ * (Real.sqrt T * ‖(sb i).toLp (μ := μ) T - β‖ + ‖(sσ i).toLp (μ := μ) T - γ‖) := by
      calc ∫ ω, |L ω - Lk ω| ∂μ ≤ ∫ ω, C₁ * |X T ω - Xk i T ω| ∂μ := by
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) ?_
              (ae_of_all _ fun ω => ?_)
            · have hX1 := integrable_comp_terminal hB T hBmeas hBcont x₀ β γ
                (f := id) (f' := fun _ => 1) (fun x => hasDerivAt_id x) (C₁ := 1)
                (fun _ => by norm_num)
              have hX2 := integrable_comp_terminal hB T hBmeas hBcont x₀
                ((sb i).toLp (μ := μ) T) ((sσ i).toLp (μ := μ) T)
                (f := id) (f' := fun _ => 1) (fun x => hasDerivAt_id x) (C₁ := 1)
                (fun _ => by norm_num)
              have hXdiff : Integrable (fun ω => X T ω - Xk i T ω) μ := by
                refine (hX1.sub hX2).congr (ae_of_all _ fun ω => ?_)
                simp only [Pi.sub_apply, id]
                ring
              exact hXdiff.abs.const_mul C₁
            · simp only [L, Lk]
              rw [show f (X T ω) - f x₀ - (f (Xk i T ω) - f x₀) = f (X T ω) - f (Xk i T ω) by ring]
              exact abs_sub_le_of_deriv_bound hf hf1 _ _
        _ = C₁ * ∫ ω, |X T ω - Xk i T ω| ∂μ := integral_const_mul _ _
        _ ≤ C₁ * (Real.sqrt T * ‖β - (sb i).toLp (μ := μ) T‖ + ‖γ - (sσ i).toLp (μ := μ) T‖) :=
            mul_le_mul_of_nonneg_left
              (integral_abs_terminal_sub_le hB T hBmeas hBcont x₀ β γ _ _) hC₁
        _ = _ := by rw [norm_sub_rev β, norm_sub_rev γ]
    have hP2 : ∫ ω, |itoIntegralCLM hB T hBmeas (Γk i) ω - itoIntegralCLM hB T hBmeas Γ ω| ∂μ
        ≤ ‖Γk i - Γ‖ := by
      have hm : MemLp (⇑(itoIntegralCLM hB T hBmeas (Γk i - Γ))) 2 μ := Lp.memLp _
      calc _ = ∫ ω, |itoIntegralCLM hB T hBmeas (Γk i - Γ) ω| ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [Lp.coeFn_sub (itoIntegralCLM hB T hBmeas (Γk i))
              (itoIntegralCLM hB T hBmeas Γ)] with ω hω
            rw [map_sub, hω, Pi.sub_apply]
        _ ≤ Real.sqrt (∫ ω, (itoIntegralCLM hB T hBmeas (Γk i - Γ) ω) ^ 2 ∂μ) :=
            integral_abs_le_sqrt_integral_sq hm
        _ = ‖Γk i - Γ‖ := by
            rw [← MathFin.lp_two_norm_sq, Real.sqrt_sq (norm_nonneg _), itoIntegralCLM_norm]
    have hP3 : ∫ ω, |∫ s in Set.Ioc 0 T, (Fk (s, ω) - F (s, ω)) ∂timeMeasure| ∂μ
        ≤ (∫ z, |f' (Xk i z.1 z.2) * ((sb i).toLp (μ := μ) T) z - f' (X z.1 z.2) * β z|
            ∂(trimMeasure (μ := μ) T hBmeas))
          + 1 / 2 * ∫ z, |f'' (Xk i z.1 z.2) * ((sσ i).toLp (μ := μ) T) z ^ 2
            - f'' (X z.1 z.2) * γ z ^ 2| ∂(trimMeasure (μ := μ) T hBmeas) := by
      refine (integral_abs_setIntegral_le T (hFkint.sub hFint)).trans ?_
      have hDm : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
          (fun z => |(Fk - F) z|) := (hFkm.sub hFm).norm
      rw [integral_trim (natFiltration hBmeas).predictable_le_prod hDm]
      have hA : Integrable (fun z => |f' (Xk i z.1 z.2) * ((sb i).toLp (μ := μ) T) z
          - f' (X z.1 z.2) * β z|) (trimMeasure (μ := μ) T hBmeas) := by
        refine (((Lp.memLp ((sb i).toLp (μ := μ) T)).integrable one_le_two).abs.const_mul C₁
          |>.add (((Lp.memLp β).integrable one_le_two).abs.const_mul C₁)).mono' ?_
          (ae_of_all _ fun z => ?_)
        · exact (((hf'c.comp_aestronglyMeasurable (hYm i)).mul
            (Lp.aestronglyMeasurable _)).sub ((hf'c.comp_aestronglyMeasurable hY₀m).mul
            (Lp.aestronglyMeasurable _))).norm
        · rw [Real.norm_eq_abs, abs_abs]
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right (hf1 _) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (hf1 _) (abs_nonneg _))
      have hB' : Integrable (fun z => |f'' (Xk i z.1 z.2) * ((sσ i).toLp (μ := μ) T) z ^ 2
          - f'' (X z.1 z.2) * γ z ^ 2|) (trimMeasure (μ := μ) T hBmeas) := by
        refine (((Lp.memLp ((sσ i).toLp (μ := μ) T)).integrable_sq.const_mul C₂).add
          ((Lp.memLp γ).integrable_sq.const_mul C₂)).mono' ?_ (ae_of_all _ fun z => ?_)
        · exact (((hf''.comp_aestronglyMeasurable (hYm i)).mul
            ((Lp.aestronglyMeasurable _).pow 2)).sub ((hf''.comp_aestronglyMeasurable hY₀m).mul
            ((Lp.aestronglyMeasurable _).pow 2))).norm
        · rw [Real.norm_eq_abs, abs_abs]
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (((sσ i).toLp (μ := μ) T) z)),
            abs_of_nonneg (sq_nonneg (γ z))]
          exact add_le_add (mul_le_mul_of_nonneg_right (hf2 _) (sq_nonneg _))
            (mul_le_mul_of_nonneg_right (hf2 _) (sq_nonneg _))
      rw [← integral_const_mul, ← integral_add hA (hB'.const_mul _)]
      refine integral_mono_ae ((hFkint.sub hFint).abs.trim
        (natFiltration hBmeas).predictable_le_prod hDm) (hA.add (hB'.const_mul _)) ?_
      filter_upwards [(sb i).coeFn_toLp (μ := μ) T, (sσ i).coeFn_toLp (μ := μ) T] with z hb hs
      have hb' : ((sb i).toLp (μ := μ) T) z = (sb i).toFun z.1 z.2 := hb
      have hs' : ((sσ i).toLp (μ := μ) T) z = (sσ i).toFun z.1 z.2 := hs
      simp only [Pi.sub_apply]
      rw [hb', hs']
      have e : Fk z - F z = (f' (Xk i z.1 z.2) * (sb i).toFun z.1 z.2 - f' (X z.1 z.2) * β z)
          + 1 / 2 * (f'' (Xk i z.1 z.2) * (sσ i).toFun z.1 z.2 ^ 2 - f'' (X z.1 z.2) * γ z ^ 2)
                := by
        simp only [Fk, F]; ring
      rw [e]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc ∫ ω, |L ω - R ω| ∂μ
        ≤ ∫ ω, (|L ω - Lk ω|
          + |itoIntegralCLM hB T hBmeas (Γk i) ω - itoIntegralCLM hB T hBmeas Γ ω|
          + |∫ s in Set.Ioc 0 T, (Fk (s, ω) - F (s, ω)) ∂timeMeasure|) ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (((hLint.sub hLkint).abs.add hIint.abs).add hTint.abs) hpt
      _ = ∫ ω, |L ω - Lk ω| ∂μ
          + ∫ ω, |itoIntegralCLM hB T hBmeas (Γk i) ω - itoIntegralCLM hB T hBmeas Γ ω| ∂μ
          + ∫ ω, |∫ s in Set.Ioc 0 T, (Fk (s, ω) - F (s, ω)) ∂timeMeasure| ∂μ := by
          rw [integral_add (f := fun ω => |L ω - Lk ω|
              + |itoIntegralCLM hB T hBmeas (Γk i) ω - itoIntegralCLM hB T hBmeas Γ ω|)
              (g := fun ω => |∫ s in Set.Ioc 0 T, (Fk (s, ω) - F (s, ω)) ∂timeMeasure|)
              ((hLint.sub hLkint).abs.add hIint.abs) hTint.abs,
            integral_add (f := fun ω => |L ω - Lk ω|)
              (g := fun ω => |itoIntegralCLM hB T hBmeas (Γk i) ω
                - itoIntegralCLM hB T hBmeas Γ ω|) (hLint.sub hLkint).abs hIint.abs]
      _ ≤ bnd i := add_le_add (add_le_add hP1 hP2) hP3
  -- conclude
  have hzero : ∫ ω, |L ω - R ω| ∂μ = 0 := by
    refine le_antisymm ?_ (integral_nonneg fun _ => abs_nonneg _)
    exact ge_of_tendsto' hbnd hmain
  have hae0 := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg (L ω - R ω))
    (hLint.sub hRint).abs).mp hzero
  filter_upwards [hae0] with ω hω
  have : |L ω - R ω| = 0 := hω
  have := abs_eq_zero.mp this
  simp only [L, R, F] at this ⊢
  linarith

end General

end MathFin.FilteredIto
