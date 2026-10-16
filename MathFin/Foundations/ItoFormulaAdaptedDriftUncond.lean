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
packaging of `itoDrift_expectation_identity_adapted` in `ItoFormulaAdaptedDrift` (a
`natFiltration`-adapted, everywhere-path-continuous version of `δ●B`) is bypassed, not
discharged: the identity is derived directly for the constructed process, without any version
`M`. This module is separate from `ItoFormulaAdaptedDrift` so that that module
stays free of the `ItoFormulaAdapted` import and its own route (the discrete partition
skeleton) remains self-contained.

Route: `ItoFormulaAdapted.ito_formula_adapted` gives the pathwise a.e. decomposition
`f(X_T) − f c =ᵐ ∫₀ᵀ f'(X)·δ dB + ∫₀ᵀ (f'(X)·β + ½·f''(X)·δ²) ds`; integrating, the stochastic
term dies by centering (`integral_itoIntegralCLM_T` — the Itô integral at any `L²` class has
mean zero), and the drift integral crosses the expectation by a Fubini interchange at the
bounded predictable weight `f'(X)·β + ½·f''(X)·δ²` (`band_fubini` below: predictability gives
product-measurability, boundedness gives band-integrability, and `integral_integral_swap`
exchanges the two iterated integrals — no path continuity of `X` is needed, which is
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
modifying it on the null failure set need not preserve `natFiltration`-adaptedness (the natural
filtration is not complete), and the everywhere-continuous modification is adapted only to
`augFiltration`; so the conditional theorem is the only adapted-coefficient statement here that covers an
`X` other than the constructed one. Whether that is worth keeping, and whether to demote,
deprecate or delete `ItoFormulaAdaptedDrift`, is left for the maintainer to decide; this
module does not change it.

## Result

* `itoDrift_expectation_identity_adapted_uncond` — the unconditional identity (headline);
* `band_fubini` (private) — band-Fubini for bounded predictable weights.

The constant-coefficient case is `ito_drift_expectation_identity` in `ItoDriftExpectation`;
the conditional statement (for any `X` satisfying its hypotheses on a version `M`) is
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
(`predictable_le_prod`), boundedness makes it integrable on the finite band, and
`integral_integral_swap` exchanges the two iterated integrals. -/
private theorem band_fubini {w : ℝ≥0 → Ω → ℝ}
    (hw_pred : IsStronglyPredictable (natFiltration hBmeas) w) {Cw : ℝ}
    (hw_bdd : ∀ s ω, |w s ω| ≤ Cw) (u v : ℝ≥0) :
    ∫ ω, (∫ s in Set.Ioc u v, w s ω ∂ItoIntegralL2.timeMeasure) ∂μ
      = ∫ s in Set.Ioc u v, (∫ ω, w s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
  have : IsFiniteMeasure (ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)) :=
    ⟨by simp [ItoIntegralL2.timeMeasure_Ioc]⟩
  have hint : Integrable (Function.uncurry w)
      ((ItoIntegralL2.timeMeasure.restrict (Set.Ioc u v)).prod μ) :=
    .of_bound ((hw_pred.mono (natFiltration hBmeas).predictable_le_prod).aestronglyMeasurable)
      Cw (ae_of_all _ fun z ↦ (Real.norm_eq_abs _).trans_le (hw_bdd z.1 z.2))
  exact integral_integral_swap hint.swap

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
  set φ := processToLp (μ := μ) T hBmeas hδadap hδcont hδbdd
  set X := adaptedItoProcess T hBmeas φ c β
  set g : ℝ≥0 → Ω → ℝ := fun s ω ↦ f' (X s ω) * β s ω + 1 / 2 * (f'' (X s ω) * (δ s ω * δ s ω))
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  have hfcont : Continuous f := Differentiable.continuous fun x ↦ (hf x).differentiableAt
  have hC1 : 0 ≤ C1 := (abs_nonneg _).trans (hg1 0)
  have hC2 : 0 ≤ C2 := (abs_nonneg _).trans (hg2 0)
  have hXm : ∀ t, Measurable (X t) := fun t ↦
    ((adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hβadap hβcont hβbdd
      c).stronglyAdapted t).measurable.mono ((natFiltration hBmeas).le t) le_rfl
  have hβm : ∀ s, Measurable (β s) := fun s ↦
    (hβadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl
  have hδm : ∀ s, Measurable (δ s) := fun s ↦
    (hδadap s).measurable.mono ((natFiltration hBmeas).le s) le_rfl
  -- bounds on the two pieces of the drift weight `g`
  have hgd1 (s ω) : |f' (X s ω) * β s ω| ≤ C1 * |Db| := by
    rw [abs_mul]
    exact mul_le_mul (hg1 _) ((hβbdd s ω).trans (le_abs_self Db)) (abs_nonneg _) hC1
  have hgd2 (s ω) : |f'' (X s ω) * (δ s ω * δ s ω)| ≤ C2 * (|Dd| * |Dd|) := by
    have hδ := (hδbdd s ω).trans (le_abs_self Dd)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (hg2 _) (mul_le_mul hδ hδ (abs_nonneg _) (abs_nonneg Dd))
      (by positivity) hC2
  have hg_bdd : ∀ s ω, |g s ω| ≤ C1 * |Db| + 1 / 2 * (C2 * (|Dd| * |Dd|)) := fun s ω ↦
    (abs_add_le _ _).trans (add_le_add (hgd1 s ω) (by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (hgd2 s ω) (by norm_num)))
  have hAs : ∀ s, Integrable (fun ω ↦ f' (X s ω) * β s ω) μ := fun s ↦
    .of_bound ((hf'c.measurable.comp (hXm s)).mul (hβm s)).aestronglyMeasurable _
      (ae_of_all _ fun ω ↦ (Real.norm_eq_abs _).trans_le (hgd1 s ω))
  have hBs : ∀ s, Integrable (fun ω ↦ f'' (X s ω) * (δ s ω * δ s ω)) μ := fun s ↦
    .of_bound ((hf''c.measurable.comp (hXm s)).mul ((hδm s).mul (hδm s))).aestronglyMeasurable _
      (ae_of_all _ fun ω ↦ (Real.norm_eq_abs _).trans_le (hgd2 s ω))
  have hDint : Integrable (fun ω ↦ ∫ s in Set.Ioc 0 T, g s ω ∂ItoIntegralL2.timeMeasure) μ :=
    (memLp_pathIntegral_process_of_ae_continuous (w := g)
      (fun s ↦ ((hf'c.measurable.comp (hXm s)).mul (hβm s)).add
        (((hf''c.measurable.comp (hXm s)).mul ((hδm s).mul (hδm s))).const_mul (1 / 2)))
      (by positivity) hg_bdd T
      ((ae_continuousOn_adaptedItoProcess hB T hBmeas hBcont φ hβcont hβbdd c).mono fun ω h ↦
        ((hf'c.comp_continuousOn h).mul (hβcont ω).continuousOn).add
          (((hf''c.comp_continuousOn h).mul ((hδcont ω).mul (hδcont ω)).continuousOn).const_mul
            (1 / 2)))).integrable one_le_two
  -- the stochastic integrand class
  set ψ := processToLpPredictable (μ := μ) T hBmeas
    (comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont hδadap hδcont φ hβadap
      hβcont hβbdd c hf'c) (abs_comp_mul_le hg1 hδbdd _)
  -- the pathwise formula, mul form
  have hformula : (fun ω ↦ f (X T ω) - f c) =ᵐ[μ] fun ω ↦ (itoIntegralCLM_T hB T hBmeas ψ : Ω → ℝ) ω
      + ∫ s in Set.Ioc 0 T, g s ω ∂ItoIntegralL2.timeMeasure :=
    (ito_formula_adapted hB T hBmeas hBcont hδadap hδcont hδbdd hβadap hβcont hβbdd
      c hf hf' hf''c hg1 hg2).trans (ae_of_all _ fun ω ↦ by simp only [pow_two]; rfl)
  -- integrability of `f (X T)`: linear growth of `f` plus the decomposition of `X`
  have hf_lin (x : ℝ) : |f x| ≤ |f 0| + C1 * |x| := by
    have := abs_sub_le_of_hasDerivAt (g := f) (g' := f') hf hg1 0 x
    simp only [sub_zero] at this
    linarith [abs_sub_abs_le_abs_sub (f x) (f 0)]
  have hMT : MemLp (itoContinuousMod T hBmeas φ T) 2 μ :=
    (Lp.memLp (itoProcessCLM hB T T hBmeas φ)).ae_eq
      (itoContinuousMod_modification hB T hBmeas hBcont φ le_rfl).symm
  have hint_f : Integrable (fun ω ↦ f (X T ω)) μ := by
    refine (((integrable_const (|f 0| + C1 * (|c| + |Db| * T))).add
      ((hMT.norm.integrable one_le_two).const_mul C1))).mono'
      (hfcont.measurable.comp (hXm T)).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
    have hA : |AdaptedDrift.driftPath β T ω| ≤ |Db| * T := by
      have h := AdaptedDrift.abs_driftPath_sub_le hβcont hβbdd (zero_le : 0 ≤ T) ω
      simp only [AdaptedDrift.driftPath, Set.Ioc_self, setIntegral_empty, sub_zero,
        NNReal.coe_zero] at h ⊢
      exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self Db) T.2)
    have h1 := abs_add_le c (AdaptedDrift.driftPath β T ω)
    have h2 := abs_add_le (c + AdaptedDrift.driftPath β T ω) (itoContinuousMod T hBmeas φ T ω)
    have h3 := hf_lin (X T ω)
    have h4 : C1 * |X T ω| ≤ C1 * (|c| + |Db| * T + ‖itoContinuousMod T hBmeas φ T ω‖) :=
      mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact h2.trans (by linarith)) hC1
    simp only [Real.norm_eq_abs, Pi.add_apply] at h4 ⊢
    linarith
  -- the Fubini interchange at the drift weight
  have hfub := band_fubini (μ := μ) hBmeas (w := g)
    (((comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hβadap hβcont hβbdd c
      hf'c).mul (isStronglyPredictable_of_bdd_adapted_cont hBmeas hβadap hβcont)).add
      (((comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hβadap hβcont hβbdd c
        hf''c).mul ((isStronglyPredictable_of_bdd_adapted_cont hBmeas hδadap hδcont).mul
          (isStronglyPredictable_of_bdd_adapted_cont hBmeas hδadap hδcont))).const_mul (1 / 2)))
    hg_bdd 0 T
  -- assemble
  have hmain : ∫ ω, f (X T ω) ∂μ - f c
      = ∫ s in Set.Ioc (0 : ℝ≥0) T, (∫ ω, g s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
    have h := integral_congr_ae hformula
    rw [integral_sub hint_f (integrable_const _), integral_add ((Lp.memLp _).integrable one_le_two)
      hDint, integral_itoIntegralCLM_T, zero_add] at h
    simpa using h.trans hfub
  rw [← sub_eq_iff_eq_add', hmain]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ ↦ ?_
  simp only [g]
  rw [integral_add (hAs s) ((hBs s).const_mul _), integral_const_mul]

end MathFin
