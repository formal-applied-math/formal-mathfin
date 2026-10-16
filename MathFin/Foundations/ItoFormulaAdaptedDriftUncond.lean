/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Foundations.ItoFormulaAdapted
public import MathFin.Foundations.ItoFormulaTDRemainder

/-! # The unconditional integrated Itô–drift identity (the constructed process)

The #244 review's main request — make the adapted expectation identity unconditional, or derive
it from `ItoFormulaAdapted.ito_formula_adapted` — lands here as the derivation: for the Itô
process the library constructs,

  `X = c + ∫₀• β ds + itoContinuousMod` at the `processToLp` class of `δ`
  (`ItoFormulaAdapted.adaptedItoProcess`, whose `X 0 = c` almost surely),

the integrated Itô–drift identity holds **unconditionally**:

  `𝔼[f(X_T)] = f c + ∫₀ᵀ (𝔼[f'(X_s)·β_s] + ½·𝔼[f''(X_s)·δ_s²]) ds`,

for `B` a pre-Brownian motion with every path continuous, `β, δ` bounded,
`natFiltration`-adapted and path-continuous, and `f` twice differentiable with `f''`
continuous and `f'`, `f''` bounded. No `M` or `X` version is hypothesized — the conditional
packaging of `ItoFormulaAdaptedDrift.itoDrift_expectation_identity_adapted` (a
`natFiltration`-adapted, everywhere-path-continuous version of `δ●B`) is discharged for the
constructed process. This module is separate from `ItoFormulaAdaptedDrift` so that that module
stays free of the `ItoFormulaAdapted` import and its own route (the discrete partition
skeleton) remains self-contained.

Route: `ItoFormulaAdapted.ito_formula_adapted` gives the pathwise a.e. decomposition
`f(X_T) − f c =ᵐ ∫₀ᵀ f'(X)·δ dB + ∫₀ᵀ (f'(X)·β + ½·f''(X)·δ²) ds`; integrating, the stochastic
term dies by centering (`integral_itoIntegralCLM_T` — the Itô integral at any `L²` class has
mean zero), and the drift integral crosses the expectation by a Fubini interchange at the
bounded predictable weight `f'(X)·β + ½·f''(X)·δ²` (`band_fubini` below: predictability gives
product-measurability, boundedness gives band-integrability, and the two iterated integrals of
`integral_prod` / `integral_prod_symm` coincide — no path continuity of `X` is needed, which is
what makes the a.e.-continuous constructed process reachable).

Hypothesis comparison with the conditional theorem (neither statement implies the other):
* weaker on `f`: `f ∈ C²` with continuous `f''` and bounded `f'`, `f''` (no third derivative),
  where the conditional theorem needs `f` three times differentiable with `f'''` bounded;
* no `M` hypotheses (`hMadap`, `hMeq`) and no `hXcont`/`hXrel`, but `X` is not arbitrary: it
  is fixed to the constructed process `adaptedItoProcess … (processToLp δ) c β`, whereas the
  conditional theorem holds for any `X` satisfying its hypotheses;
* stronger on `B`: it adds `hBcont` (every path of `B` continuous), which the conditional
  theorem does not assume (`ito_formula_adapted` and the predictability lemmas for
  `adaptedItoProcess` need it).

## Open question for the maintainer: the conditional route

The #244 review asked to prove the expectation form as a corollary **and retire the
conditional route** (`itoDrift_expectation_identity_adapted`, the roughly 5.7k-line
`ItoFormulaAdaptedDrift`). This module does the first part only; both theorems are kept as
co-headlines. The reason for keeping the conditional one is technical: the library cannot
supply its hypothesized `M` (Route B). `itoContinuousMod` is continuous only almost surely,
modifying it on the null failure set destroys `natFiltration`-adaptedness (the natural
filtration is not complete), and the everywhere-continuous modification is adapted only to
`augFiltration`; so the conditional theorem is the only statement here that covers an `X`
other than the constructed one. Whether that is worth keeping, and whether to demote,
deprecate or delete `ItoFormulaAdaptedDrift`, is left for the maintainer to decide; this
module does not change it.

## Result

* `itoDrift_expectation_identity_adapted_uncond` — the unconditional identity (headline);
* `band_fubini` (private) — band-Fubini for bounded predictable weights.

The constant-coefficient case is `ito_drift_expectation_identity` in `ItoDriftExpectation`;
the conditional version-independent statement is
`itoDrift_expectation_identity_adapted` in `ItoFormulaAdaptedDrift`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoFormulaAdapted
open ItoIntegralProcessContinuousModification
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)

/-- **Fubini for a bounded predictable weight on a time band**: the expectation of
the path integral equals the time-integral of the slice expectations, for `w` strongly
predictable for the natural filtration and bounded. No path continuity is needed (the headline
below applies this at the drift weight of the constructed process, whose paths are continuous
only almost surely): predictability makes the uncurried weight product-measurable
(`predictable_le_prod`), boundedness makes it integrable on the finite band, and the two
iterated integrals of `integral_prod` / `integral_prod_symm` are the same product integral. -/
private theorem band_fubini {w : ℝ≥0 → Ω → ℝ}
    (hw_pred : IsStronglyPredictable (natFiltration hBmeas) w) {Cw : ℝ}
    (hw_bdd : ∀ s ω, |w s ω| ≤ Cw) (u v : ℝ≥0) :
    ∫ ω, (∫ s in Set.Ioc u v, w s ω ∂ItoIntegralL2.timeMeasure) ∂μ
      = ∫ s in Set.Ioc u v, (∫ ω, w s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
  haveI : IsFiniteMeasure (ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hmeas : Measurable (Function.uncurry w) :=
    (show StronglyMeasurable[(natFiltration hBmeas).predictable] (Function.uncurry w) from
        hw_pred).mono (natFiltration hBmeas).predictable_le_prod |>.measurable
  have hint : Integrable (Function.uncurry w)
      ((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) :=
    Integrable.of_bound hmeas.aestronglyMeasurable (max Cw 0)
      (ae_of_all _ fun z ↦ by
        rw [Real.norm_eq_abs]
        exact (hw_bdd z.1 z.2).trans (le_max_left Cw 0))
  calc ∫ ω, (∫ s in Set.Ioc u v, w s ω ∂ItoIntegralL2.timeMeasure) ∂μ
      = ∫ ω, (∫ s, w s ω ∂(ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v))) ∂μ := rfl
    _ = ∫ z, Function.uncurry w z ∂((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) :=
          (MeasureTheory.integral_prod_symm _ hint).symm
    _ = ∫ s, (∫ ω, w s ω ∂μ) ∂(ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) :=
          MeasureTheory.integral_prod _ hint
    _ = ∫ s in Set.Ioc u v, (∫ ω, w s ω ∂μ) ∂ItoIntegralL2.timeMeasure := rfl

/-- **The integrated Itô–drift identity, unconditionally, for the constructed process.** For
`X = adaptedItoProcess T hBmeas (processToLp δ) c β` (so `X 0 = c` almost surely),
`𝔼[f(X_T)] = f c + ∫₀ᵀ (𝔼[f'(X_s)·β_s] + ½·𝔼[f''(X_s)·δ_s²]) ds`, for `B` a pre-Brownian
motion with every path continuous, `β, δ` bounded, `natFiltration`-adapted and path-continuous,
and `f` twice differentiable with `f''` continuous and `f'`, `f''` bounded. No version `M` of
`δ●B` and no hypothesis on `X` is assumed; unlike the conditional
`itoDrift_expectation_identity_adapted`, `X` is fixed to the constructed process and `B` is
assumed path-continuous (`hBcont`). -/
theorem itoDrift_expectation_identity_adapted_uncond (hB : IsPreBrownianReal B μ)
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {β : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (c : ℝ) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''c : Continuous f'')
    {C1 C2 : ℝ} (hg1 : ∀ x, |f' x| ≤ C1) (hg2 : ∀ x, |f'' x| ≤ C2) :
    ∫ ω, f (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β T ω) ∂μ
      = f c + ∫ s in Set.Ioc (0 : ℝ≥0) T,
          ((∫ ω, f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
              c β s ω) * β s ω ∂μ)
            + (1 / 2) * (∫ ω, f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap
              hδcont hδbdd) c β s ω) * (δ s ω * δ s ω) ∂μ))
        ∂ItoIntegralL2.timeMeasure := by
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  -- the process and its regularity
  have hpredX : IsStronglyPredictable (natFiltration hBmeas)
      (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β) :=
    adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) hβadap hβcont hβbdd c
  have hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t]
      (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β t) :=
    fun t ↦ hpredX.stronglyAdapted t
  have hXm : ∀ t, Measurable (adaptedItoProcess T hBmeas
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β t) := fun t ↦
    (hXadap t).measurable.mono ((natFiltration hBmeas).le t) le_rfl
  have hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ adaptedItoProcess T hBmeas
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β t ω) (Set.Icc 0 T) :=
    ae_continuousOn_adaptedItoProcess hB T hBmeas hBcont
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) hβcont hβbdd c
  have hβm : ∀ s, Measurable (β s) := fun s ↦
    (hβadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl
  have hδm : ∀ s, Measurable (δ s) := fun s ↦
    (hδadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl
  -- the drift weight `g := f'(X)·β + ½·f''(X)·δ²` (mul form): sections, paths, bound
  have hg_meas : ∀ s, Measurable (fun ω ↦ f' (adaptedItoProcess T hBmeas
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β s ω) * β s ω
      + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
        c β s ω) * (δ s ω * δ s ω))) := fun s ↦
    ((hf'c.measurable.comp (hXm s)).mul (hβm s)).add
      (((hf''c.measurable.comp (hXm s)).mul ((hδm s).mul (hδm s))).const_mul (1 / 2))
  have hg_cont : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ f' (adaptedItoProcess T hBmeas
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β s ω) * β s ω
      + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
        c β s ω) * (δ s ω * δ s ω))) (Set.Icc 0 T) :=
    hXc.mono fun ω h ↦ ((hf'c.comp_continuousOn h).mul (hβcont ω).continuousOn).add
      (((hf''c.comp_continuousOn h).mul ((hδcont ω).mul (hδcont ω)).continuousOn).const_mul
        (1 / 2))
  have hgd1 : ∀ s ω, |f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
      c β s ω) * β s ω| ≤ C1 * |Db| := by
    intro s ω
    rw [abs_mul]
    exact mul_le_mul (hg1 _) (le_trans (hβbdd s ω) (le_abs_self Db)) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hg1 0))
  have hd2 : ∀ s ω, |δ s ω * δ s ω| ≤ |Dd| * |Dd| := by
    intro s ω
    rw [abs_mul]
    exact mul_le_mul (le_trans (hδbdd s ω) (le_abs_self Dd))
      (le_trans (hδbdd s ω) (le_abs_self Dd)) (abs_nonneg _) (abs_nonneg Dd)
  have hgd2' : ∀ s ω, |f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas
      hδadap hδcont hδbdd) c β s ω) * (δ s ω * δ s ω)| ≤ C2 * (|Dd| * |Dd|) := by
    intro s ω
    rw [abs_mul]
    exact mul_le_mul (hg2 _) (hd2 s ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hg2 0))
  have hgd2 : ∀ s ω, |1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap
      hδcont hδbdd) c β s ω) * (δ s ω * δ s ω))| ≤ 1 / 2 * (C2 * (|Dd| * |Dd|)) := by
    intro s ω
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    exact mul_le_mul_of_nonneg_left (hgd2' s ω) (by norm_num)
  have hg_bdd : ∀ s ω, |f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont
      hδbdd) c β s ω) * β s ω + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas
      hδadap hδcont hδbdd) c β s ω) * (δ s ω * δ s ω))|
      ≤ C1 * |Db| + 1 / 2 * (C2 * (|Dd| * |Dd|)) :=
    fun s ω ↦ (abs_add_le _ _).trans (add_le_add (hgd1 s ω) (hgd2 s ω))
  have hC1 : (0 : ℝ) ≤ C1 := le_trans (abs_nonneg _) (hg1 0)
  have hC2 : (0 : ℝ) ≤ C2 := le_trans (abs_nonneg _) (hg2 0)
  have hCg : (0 : ℝ) ≤ C1 * |Db| + 1 / 2 * (C2 * (|Dd| * |Dd|)) :=
    add_nonneg (mul_nonneg hC1 (abs_nonneg _))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (mul_nonneg hC2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  have hDint : Integrable (fun ω ↦ ∫ s in Set.Ioc 0 T, f' (adaptedItoProcess T hBmeas
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β s ω) * β s ω
      + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
        c β s ω) * (δ s ω * δ s ω)) ∂ItoIntegralL2.timeMeasure) μ :=
    (memLp_pathIntegral_process_of_ae_continuous (w := fun s ω ↦ f' (adaptedItoProcess T hBmeas
        (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β s ω) * β s ω
        + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          c β s ω) * (δ s ω * δ s ω))) hg_meas hCg hg_bdd T hg_cont).integrable one_le_two
  -- the stochastic integrand class and its integrability
  have hsto_int : Integrable (fun ω ↦ (itoIntegralCLM_T hB T hBmeas (processToLpPredictable
      T hBmeas (comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont hδadap
        hδcont (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) hβadap hβcont hβbdd
        c hf'c) (abs_comp_mul_le hg1 hδbdd _)) : Ω → ℝ) ω) μ :=
    (Lp.memLp _).integrable one_le_two
  -- the pathwise formula, mul form
  have hformula' : (fun ω ↦ f (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont
        hδbdd) c β T ω) - f c) =ᵐ[μ] fun ω ↦ (itoIntegralCLM_T hB T hBmeas (processToLpPredictable
      T hBmeas (comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont hδadap
        hδcont (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) hβadap hβcont hβbdd
        c hf'c) (abs_comp_mul_le hg1 hδbdd _)) : Ω → ℝ) ω
      + ∫ s in Set.Ioc 0 T, f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap
          hδcont hδbdd) c β s ω) * β s ω
        + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          c β s ω) * (δ s ω * δ s ω)) ∂ItoIntegralL2.timeMeasure := by
    refine (ito_formula_adapted hB T hBmeas hBcont hδadap hδcont hδbdd hβadap hβcont hβbdd
      c hf hf' hf''c hg1 hg2).trans (ae_of_all _ fun ω ↦ ?_)
    simp only [pow_two]
  -- integrability of `f (X T)`: linear growth of `f` plus the decomposition of `X`
  have hfcont : Continuous f := Differentiable.continuous fun x ↦ (hf x).differentiableAt
  have hf_lin : ∀ x, |f x| ≤ |f 0| + C1 * |x| := by
    intro x
    have hmv : |f x - f 0| ≤ C1 * |x| := by
      have h := abs_sub_le_of_hasDerivAt (g := f) (g' := f') hf hg1 0 x
      simpa using h
    calc |f x| = |f 0 + (f x - f 0)| := by congr 1; ring
      _ ≤ |f 0| + |f x - f 0| := abs_add_le _ _
      _ ≤ |f 0| + C1 * |x| := by linarith
  have hdpb : ∀ t : ℝ≥0, ∀ ω, |AdaptedDrift.driftPath β t ω| ≤ |Db| * (t : ℝ) := by
    intro t ω
    have h0 : AdaptedDrift.driftPath β (0 : ℝ≥0) ω = 0 := by
      simp only [AdaptedDrift.driftPath, Set.Ioc_self, setIntegral_empty]
    have h := AdaptedDrift.abs_driftPath_sub_le hβcont hβbdd
      (show (0 : ℝ≥0) ≤ t from zero_le) ω
    rw [h0, sub_zero, NNReal.coe_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self Db) (NNReal.coe_nonneg t))
  have hMT : MemLp (fun ω ↦ itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas
      hδadap hδcont hδbdd) T ω) 2 μ :=
    (Lp.memLp (itoProcessCLM hB T T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont
      hδbdd))).ae_eq (itoContinuousMod_modification hB T hBmeas hBcont
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) (le_rfl)).symm
  have hint_f : Integrable (fun ω ↦ f (adaptedItoProcess T hBmeas (processToLp (μ := μ)
      T hBmeas hδadap hδcont hδbdd) c β T ω)) μ := by
    have hmeas : AEStronglyMeasurable (fun ω ↦ f (adaptedItoProcess T hBmeas (processToLp
        (μ := μ) T hBmeas hδadap hδcont hδbdd) c β T ω)) μ :=
      (hfcont.measurable.comp (hXm T)).aestronglyMeasurable
    have hintM : Integrable (fun ω ↦ |itoContinuousMod T hBmeas (processToLp (μ := μ)
        T hBmeas hδadap hδcont hδbdd) T ω|) μ :=
      (hMT.norm.integrable one_le_two)
    have hdom : Integrable (fun ω ↦ (|f 0| + C1 * (|c| + |Db| * ((T : ℝ) + 1)))
        + C1 * |itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          T ω|) μ := (integrable_const _).add (hintM.const_mul C1)
    refine Integrable.mono' hdom hmeas (ae_of_all _ fun ω ↦ ?_)
    have hT0 : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg T
    have harg : |adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont
        hδbdd) c β T ω| ≤ |c| + |Db| * ((T : ℝ) + 1)
        + |itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) T ω| := by
      rw [show adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          c β T ω = c + AdaptedDrift.driftPath β T ω
          + itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) T ω
          from rfl]
      have h5 := abs_add_le c (AdaptedDrift.driftPath β T ω)
      have h6 := hdpb T ω
      have h7 : |Db| * (T : ℝ) ≤ |Db| * ((T : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg Db)
      have h8 := abs_add_le (c + AdaptedDrift.driftPath β T ω)
        (itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) T ω)
      linarith
    calc |f (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          c β T ω)|
        ≤ |f 0| + C1 * |adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap
          hδcont hδbdd) c β T ω| := hf_lin _
      _ ≤ |f 0| + C1 * (|c| + |Db| * ((T : ℝ) + 1)
          + |itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) T ω|) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left harg hC1)
      _ = (|f 0| + C1 * (|c| + |Db| * ((T : ℝ) + 1))) + C1 * |itoContinuousMod T hBmeas
          (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) T ω| := by ring
  -- the interchange: predictability of the two weights
  have hp1 : StronglyMeasurable[(natFiltration hBmeas).predictable] (Function.uncurry
      (fun s ω ↦ f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
        c β s ω))) :=
    comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) hβadap hβcont hβbdd c hf'c
  have hp2 : StronglyMeasurable[(natFiltration hBmeas).predictable] (Function.uncurry
      (fun s ω ↦ f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
        c β s ω))) :=
    comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) hβadap hβcont hβbdd c hf''c
  have hpβ : StronglyMeasurable[(natFiltration hBmeas).predictable] (Function.uncurry β) :=
    isStronglyPredictable_of_bdd_adapted_cont hBmeas hβadap hβcont
  have hpδ : StronglyMeasurable[(natFiltration hBmeas).predictable] (Function.uncurry δ) :=
    isStronglyPredictable_of_bdd_adapted_cont hBmeas hδadap hδcont
  have hpredg : IsStronglyPredictable (natFiltration hBmeas)
      (fun s ω ↦ f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
        c β s ω) * β s ω
        + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          c β s ω) * (δ s ω * δ s ω))) :=
    (hp1.mul hpβ).add ((hp2.mul (hpδ.mul hpδ)).const_mul (1 / 2))
  -- the Fubini interchange at the mul-form weight
  have hfub : ∫ ω, (∫ s in Set.Ioc (0 : ℝ≥0) T, f' (adaptedItoProcess T hBmeas
        (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β s ω) * β s ω
        + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          c β s ω) * (δ s ω * δ s ω)) ∂ItoIntegralL2.timeMeasure) ∂μ
      = ∫ s in Set.Ioc (0 : ℝ≥0) T, (∫ ω, f' (adaptedItoProcess T hBmeas
          (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β s ω) * β s ω
          + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
            c β s ω) * (δ s ω * δ s ω)) ∂μ) ∂ItoIntegralL2.timeMeasure :=
    band_fubini hBmeas hpredg hg_bdd 0 T
  -- per-slice integrability of the two pieces
  have hAs : ∀ s, Integrable (fun ω ↦ f' (adaptedItoProcess T hBmeas
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β s ω) * β s ω) μ := fun s ↦
    Integrable.of_bound (((hf'c.measurable.comp (hXm s)).mul (hβm s)).aestronglyMeasurable)
      (C1 * |Db|) (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs]
        exact hgd1 s ω)
  have hBs : ∀ s, Integrable (fun ω ↦ f'' (adaptedItoProcess T hBmeas
      (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β s ω) * (δ s ω * δ s ω)) μ := fun s ↦
    Integrable.of_bound (((hf''c.measurable.comp (hXm s)).mul
      ((hδm s).mul (hδm s))).aestronglyMeasurable) (C2 * (|Dd| * |Dd|)) (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs]
        exact hgd2' s ω)
  -- the master identity
  have hmain : ∫ ω, f (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
        c β T ω) ∂μ - f c
      = ∫ s in Set.Ioc (0 : ℝ≥0) T, (∫ ω, f' (adaptedItoProcess T hBmeas
          (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β s ω) * β s ω
          + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
            c β s ω) * (δ s ω * δ s ω)) ∂μ) ∂ItoIntegralL2.timeMeasure := by
    calc ∫ ω, f (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          c β T ω) ∂μ - f c
        = ∫ ω, (f (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          c β T ω) - f c) ∂μ := by
          rw [integral_sub hint_f (integrable_const (f c)), integral_const]
          simp
      _ = ∫ ω, ((itoIntegralCLM_T hB T hBmeas (processToLpPredictable T hBmeas
            (comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont hδadap
              hδcont (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) hβadap hβcont
              hβbdd c hf'c) (abs_comp_mul_le hg1 hδbdd _)) : Ω → ℝ) ω
          + ∫ s in Set.Ioc 0 T, f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap
              hδcont hδbdd) c β s ω) * β s ω
            + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont
              hδbdd) c β s ω) * (δ s ω * δ s ω)) ∂ItoIntegralL2.timeMeasure) ∂μ :=
          integral_congr_ae hformula'
      _ = ∫ ω, (itoIntegralCLM_T hB T hBmeas (processToLpPredictable T hBmeas
            (comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont hδadap
              hδcont (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) hβadap hβcont
              hβbdd c hf'c) (abs_comp_mul_le hg1 hδbdd _)) : Ω → ℝ) ω ∂μ
          + ∫ ω, (∫ s in Set.Ioc 0 T, f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas
              hδadap hδcont hδbdd) c β s ω) * β s ω
            + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont
              hδbdd) c β s ω) * (δ s ω * δ s ω)) ∂ItoIntegralL2.timeMeasure) ∂μ :=
          integral_add hsto_int hDint
      _ = 0 + ∫ ω, (∫ s in Set.Ioc 0 T, f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas
            hδadap hδcont hδbdd) c β s ω) * β s ω
            + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont
              hδbdd) c β s ω) * (δ s ω * δ s ω)) ∂ItoIntegralL2.timeMeasure) ∂μ := by
          rw [integral_itoIntegralCLM_T hB T hBmeas (processToLpPredictable T hBmeas
            (comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont hδadap
              hδcont (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) hβadap hβcont
              hβbdd c hf'c) (abs_comp_mul_le hg1 hδbdd _))]
      _ = ∫ ω, (∫ s in Set.Ioc 0 T, f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas
            hδadap hδcont hδbdd) c β s ω) * β s ω
            + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont
              hδbdd) c β s ω) * (δ s ω * δ s ω)) ∂ItoIntegralL2.timeMeasure) ∂μ :=
          zero_add _
      _ = ∫ s in Set.Ioc (0 : ℝ≥0) T, (∫ ω, f' (adaptedItoProcess T hBmeas
          (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd) c β s ω) * β s ω
          + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
            c β s ω) * (δ s ω * δ s ω)) ∂μ) ∂ItoIntegralL2.timeMeasure := hfub
  -- split the inner expectation and the time integral
  have hper : ∀ s ∈ Set.Ioc (0 : ℝ≥0) T,
      (∫ ω, f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          c β s ω) * β s ω
          + 1 / 2 * (f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          c β s ω) * (δ s ω * δ s ω)) ∂μ)
        = (∫ ω, f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd)
          c β s ω) * β s ω ∂μ)
          + (1 / 2) * (∫ ω, f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap
              hδcont hδbdd) c β s ω) * (δ s ω * δ s ω) ∂μ) := by
    intro s _
    rw [integral_add (hAs s) ((hBs s).const_mul (1 / 2)), integral_const_mul]
  -- conclude
  have hfin : ∫ ω, f (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hδadap
        hδcont hδbdd) c β T ω) ∂μ - f c
      = ∫ s in Set.Ioc (0 : ℝ≥0) T, ((∫ ω, f' (adaptedItoProcess T hBmeas (processToLp (μ := μ)
          T hBmeas hδadap hδcont hδbdd) c β s ω) * β s ω ∂μ)
          + (1 / 2) * (∫ ω, f'' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas
          hδadap hδcont hδbdd) c β s ω) * (δ s ω * δ s ω) ∂μ)) ∂ItoIntegralL2.timeMeasure := by
    rw [hmain]
    exact setIntegral_congr_fun measurableSet_Ioc hper
  linarith

end MathFin
