/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonOptional
public import MathFin.Models.StochVol.Heston.CommonHestonIto
public import MathFin.Models.StochVol.Heston.CommonAffineTest

/-!
# The stopped affine exponential has constant expectation

Let `(X, V)` be a Heston state on the common filtration and `σₙ` the rational exit time of
`|X| + V` from `[0, n)` (capped at `T`).  For `u` in the closed Laplace strip and `Re w ≤ 0`,
`E[exp(C(T - σₙ) + u X_{σₙ} + D(T - σₙ) V_{σₙ})] = exp(C(T) + u x₀ + D(T) v₀)`.

The proof applies the Itô formula at the random time `σₙ` to a compactly supported cut-off of
the real and imaginary parts of the affine exponential, uses the Riccati equations to kill the
drift on the plateau, and the optional-time theorem to kill the mean of the stochastic
integrals.  No completeness of the filtration and no Feller condition are used.

## Main definitions

* `locFun`

## Main results

* `stopped_affine_ell`
* `stopped_affine`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open MathFin.FilteredIto
namespace CommonAffineStopped

open MeasureTheory ProbabilityTheory Filter Topology Set
open MathFin.FilteredIto.CommonNoise MathFin.FilteredIto.CommonPredictable
      MathFin.FilteredIto.CommonIntegral
  MathFin.FilteredIto.CommonProcessGeneral MathFin.FilteredIto.CommonContinuous
        MathFin.FilteredIto.CommonStopping
  MathFin.FilteredIto.CommonCovariation MathFin.FilteredIto.CommonRiemann
        MathFin.FilteredIto.CommonIto MathFin.Heston.CommonYamada
  MathFin.FilteredIto.CommonOptional MathFin.Heston.CommonHestonIto MathFin.Heston.CommonAffine
open scoped NNReal ENNReal

local notation "leb" => MathFin.ItoIntegralL2.timeMeasure

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℝ≥0 mΩ} {B Z : ℝ≥0 → Ω → ℝ}

/-- The localizing functional `|X| + V`. -/
def locFun (X V : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω ↦ |X t ω| + V t ω

/-- **Stopped affine identity for a real-linear functional `ℓ`.** -/
theorem stopped_affine_ell (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} (p : Parameters) (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) {u w : ℂ}
    (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0) {x₀ v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    {X V : ℝ≥0 → Ω → ℝ} {Hv Hx : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)}
    (hpX : IsStronglyPredictable ℱ X) (hpV : IsStronglyPredictable ℱ V)
    (hcX : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc 0 T))
    (hcV : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ V t ω) (Set.Icc 0 T))
    (hVnn : ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ V t ω)
    (hHv : ⇑Hv =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ p.xi * Real.sqrt (V z.1 z.2))
    (hHx : ⇑Hx =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ Real.sqrt (V z.1 z.2))
    (heqV : ∀ᵐ ω ∂μ, ∀ t ≤ T, V t ω = v₀
      + (∫ s in Set.Ioc 0 t, p.kappa * (p.theta - V s ω) ∂leb)
      + itoContinuousMod T hP.left.measurable_eval Hv t ω)
    (heqX : ∀ᵐ ω ∂μ, ∀ t ≤ T, X t ω = x₀
      + (∫ s in Set.Ioc 0 t, (p.r - p.q) - (1 / 2 : ℝ) * V s ω ∂leb)
      + itoContinuousMod T (hP.correlated_brownian hρ).measurable_eval Hx t ω)
    (ℓ : ℂ →L[ℝ] ℝ) {n : ℕ} (hn : |x₀| + v₀ < n) :
    Integrable (fun ω ↦ ℓ (affST p u w T
      (fun l ↦ hestonY X V l (CommonOptional.exitTime T (locFun X V) n ω) ω))) μ ∧
      ∫ ω, ℓ (affST p u w T
        (fun l ↦ hestonY X V l (CommonOptional.exitTime T (locFun X V) n ω) ω)) ∂μ
        = ℓ (affST p u w T (hestonY0 x₀ v₀)) := by
  have hY := hestonItoProc hP hBc hZc p hρ hpX hpV hcX hcV hHv hHx heqV heqX
  obtain ⟨δ, hδ, hDC, hCC, -⟩ := contDiffOn_globalLaplace p u w hξ hρ hu hw
  have hT : (0 : ℝ) ≤ T := T.2
  have hdiff : ContDiff ℝ 2 (affTest p u w T δ hT hδ n ℓ) :=
    contDiff_affTest p u w T δ hT hδ n ℓ hDC hCC
  obtain ⟨C₁, C₂, hf⟩ := itoTest_affTest p u w T δ hT hδ n ℓ hDC hCC
  set σ := CommonOptional.exitTime T (locFun X V) n with hσdef
  have hσT : ∀ ω, σ ω ≤ T := fun ω => exitTime_le T _ _ ω
  have hXc := contProcess_of_predictable hpX hcX
  have hVc := contProcess_of_predictable hpV hcV
  have hgad : ∀ t, Measurable[ℱ t] (locFun X V t) := fun t =>
    (continuous_abs.measurable.comp (hXc.adapted t)).add (hVc.adapted t)
  have hσopt : IsOptional ℱ σ := isOptional_exitTime hgad T n
  have hWc : ∀ ω, Continuous fun t : ℝ≥0 ↦ correlatedNoise p.rho B Z t ω := fun ω =>
    ((hBc ω).const_mul p.rho).add ((hZc ω).const_mul (orthogonalWeight p.rho))
  -- initial values
  have hX0 : ∀ᵐ ω ∂μ, X 0 ω = x₀ := by
    filter_upwards [heqX, itoContinuousMod_zero_ae (hP.correlated_brownian hρ) T hWc Hx]
      with ω h1 h2
    rw [h1 0 (zero_le : (0 : ℝ≥0) ≤ T), h2, Set.Ioc_self, Measure.restrict_empty,
      integral_zero_measure]
    ring
  have hV0 : ∀ᵐ ω ∂μ, V 0 ω = v₀ := by
    filter_upwards [heqV, itoContinuousMod_zero_ae hP.left T hBc Hv] with ω h1 h2
    rw [h1 0 (zero_le : (0 : ℝ≥0) ≤ T), h2, Set.Ioc_self, Measure.restrict_empty,
      integral_zero_measure]
    ring
  -- pathwise bounds before the exit time
  have hbound : ∀ᵐ ω ∂μ, ∀ s : ℝ≥0, s ≤ σ ω → |X s ω| ≤ n ∧ 0 ≤ V s ω ∧ V s ω ≤ n := by
    filter_upwards [hcX, hcV, hVnn, hX0, hV0] with ω hxω hvω hnn hx0 hv0 s hs
    have hgc : ContinuousOn (fun t ↦ locFun X V t ω) (Set.Icc 0 T) :=
      (continuous_abs.comp_continuousOn hxω).add hvω
    have hg0 : locFun X V 0 ω < n := by
      simp only [locFun, hx0, hv0]; exact hn
    have hle := le_of_le_exitTime hgc hg0 hs
    have hVs := hnn s (hs.trans (hσT ω))
    simp only [locFun] at hle
    exact ⟨by linarith, hVs, by linarith [abs_nonneg (X s ω)]⟩
  have hplat : ∀ᵐ ω ∂μ, ∀ s : ℝ≥0, s ≤ σ ω →
      InPlateau T δ n (fun l ↦ hestonY X V l s ω) := by
    filter_upwards [hbound] with ω hω s hs
    obtain ⟨h1, h2, h3⟩ := hω s hs
    have hsT : (s : ℝ) ≤ T := NNReal.coe_le_coe.2 (hs.trans (hσT ω))
    have hs0 : (0 : ℝ) ≤ s := NNReal.coe_nonneg s
    refine ⟨?_, ?_, ?_⟩
    · show |(s : ℝ) - T / 2| < T / 2 + δ / 3
      rw [abs_lt]; constructor <;> linarith
    · show |X s ω| < n + 1
      linarith
    · show |V s ω| < n + 1
      rw [abs_of_nonneg h2]; linarith
  -- Itô's formula at the exit time, with vanishing drift
  have hIto := ito_formula_random_time hP hBc hZc hY hf hσT
  set MBf : Fin 3 → Ω → ℝ := fun i ω ↦ itoContinuousMod T hP.left.measurable_eval
    (mulKernel T (goodProcess_pd hY.proc hf i).pred (goodProcess_pd hY.proc hf i).bdd
      (hestonKerB p Hv Hx i)) (σ ω) ω with hMBf
  set MZf : Fin 3 → Ω → ℝ := fun i ω ↦ itoContinuousMod T hP.right.measurable_eval
    (mulKernel T (goodProcess_pd hY.proc hf i).pred (goodProcess_pd hY.proc hf i).bdd
      (hestonKerZ p Hx i)) (σ ω) ω with hMZf
  set c := affTest p u w T δ hT hδ n ℓ (hestonY0 x₀ v₀) with hc
  have key : ∀ (L R I M₁ M₂ : ℝ), L = R + I + M₁ + M₂ → I = 0 → L = R + (M₁ + M₂) := by
    intro L R I M₁ M₂ h1 h2; rw [h1, h2]; ring
  have hmain : ∀ᵐ ω ∂μ, affTest p u w T δ hT hδ n ℓ (fun l ↦ hestonY X V l (σ ω) ω)
      = c + (∑ i, MBf i ω + ∑ i, MZf i ω) := by
    filter_upwards [hIto, hplat, hbound] with ω h1 hpl hbd
    refine key _ _ _ _ _ h1 ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    have hsσ : s ≤ σ ω := hs.2
    have hsT : (s : ℝ) ≤ T := NNReal.coe_le_coe.2 (hsσ.trans (hσT ω))
    exact drift_affTest_eq_zero hξ hρ hu hw hdiff (sq_add_orthogonalWeight_sq hρ)
      (hpl s hsσ) hsT (hbd s hsσ).2.1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
  -- integrability and mean zero of the stochastic terms at the optional time
  have hMB : ∀ i, Integrable (MBf i) μ ∧ ∫ ω, MBf i ω ∂μ = 0 := fun i =>
    itoContinuousMod_optional hP.left hBc _ hσopt hσT
  have hMZ : ∀ i, Integrable (MZf i) μ ∧ ∫ ω, MZf i ω ∂μ = 0 := fun i =>
    itoContinuousMod_optional hP.right hZc _ hσopt hσT
  have hSB : Integrable (fun ω ↦ ∑ i, MBf i ω) μ :=
    integrable_finsetSum _ fun i _ => (hMB i).1
  have hSZ : Integrable (fun ω ↦ ∑ i, MZf i ω) μ :=
    integrable_finsetSum _ fun i _ => (hMZ i).1
  have hS : Integrable (fun ω ↦ ∑ i, MBf i ω + ∑ i, MZf i ω) μ := hSB.add hSZ
  have hRint : Integrable (fun ω ↦ c + (∑ i, MBf i ω + ∑ i, MZf i ω)) μ :=
    (integrable_const c).add hS
  -- on the plateau the test function is `ℓ` of the affine exponential
  have hy0 : InPlateau T δ n (hestonY0 x₀ v₀) := by
    have hx : |x₀| < n := by linarith
    refine ⟨?_, ?_, ?_⟩
    · show |(0 : ℝ) - T / 2| < T / 2 + δ / 3
      rw [zero_sub, abs_neg, abs_of_nonneg (by linarith)]; linarith
    · show |x₀| < n + 1
      linarith
    · show |v₀| < n + 1
      rw [abs_of_nonneg hv₀]; linarith [abs_nonneg x₀]
  have hL : ∀ᵐ ω ∂μ, ℓ (affST p u w T (fun l ↦ hestonY X V l (σ ω) ω))
      = c + (∑ i, MBf i ω + ∑ i, MZf i ω) := by
    filter_upwards [hmain, hplat] with ω h1 hpl
    rw [← h1, affTest_eq_of_plateau p u w T δ hT hδ n ℓ (hpl (σ ω) le_rfl)]
  refine ⟨hRint.congr (hL.mono fun ω h => h.symm), ?_⟩
  rw [integral_congr_ae hL, integral_add (integrable_const _) hS, integral_add hSB hSZ,
    integral_finsetSum _ fun i _ => (hMB i).1, integral_finsetSum _ fun i _ => (hMZ i).1,
    Finset.sum_eq_zero fun i _ => (hMB i).2, Finset.sum_eq_zero fun i _ => (hMZ i).2,
    integral_const, probReal_univ, one_smul, add_zero, add_zero, hc]
  exact affTest_eq_of_plateau p u w T δ hT hδ n ℓ hy0

/-- **Stopped affine identity (complex form).** -/
theorem stopped_affine (hP : IndependentPair ℱ B Z μ)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 ↦ B u ω) (hZc : ∀ ω, Continuous fun u : ℝ≥0 ↦ Z u ω)
    {T : ℝ≥0} (p : Parameters) (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1) {u w : ℂ}
    (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0) {x₀ v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    {X V : ℝ≥0 → Ω → ℝ} {Hv Hx : Lp ℝ 2 (trimMeasureT (μ := μ) T ℱ)}
    (hpX : IsStronglyPredictable ℱ X) (hpV : IsStronglyPredictable ℱ V)
    (hcX : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc 0 T))
    (hcV : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ V t ω) (Set.Icc 0 T))
    (hVnn : ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ V t ω)
    (hHv : ⇑Hv =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ p.xi * Real.sqrt (V z.1 z.2))
    (hHx : ⇑Hx =ᵐ[trimMeasureT (μ := μ) T ℱ] fun z ↦ Real.sqrt (V z.1 z.2))
    (heqV : ∀ᵐ ω ∂μ, ∀ t ≤ T, V t ω = v₀
      + (∫ s in Set.Ioc 0 t, p.kappa * (p.theta - V s ω) ∂leb)
      + itoContinuousMod T hP.left.measurable_eval Hv t ω)
    (heqX : ∀ᵐ ω ∂μ, ∀ t ≤ T, X t ω = x₀
      + (∫ s in Set.Ioc 0 t, (p.r - p.q) - (1 / 2 : ℝ) * V s ω ∂leb)
      + itoContinuousMod T (hP.correlated_brownian hρ).measurable_eval Hx t ω)
    {n : ℕ} (hn : |x₀| + v₀ < n) :
    Integrable (fun ω ↦ affST p u w T
      (fun l ↦ hestonY X V l (CommonOptional.exitTime T (locFun X V) n ω) ω)) μ ∧
      ∫ ω, affST p u w T (fun l ↦ hestonY X V l (CommonOptional.exitTime T (locFun X V) n ω) ω) ∂μ
        = affST p u w T (hestonY0 x₀ v₀) := by
  obtain ⟨hre, ere⟩ := stopped_affine_ell hP hBc hZc p hξ hρ hu hw hv₀ hpX hpV hcX hcV hVnn
    hHv hHx heqV heqX Complex.reCLM hn
  obtain ⟨him, eim⟩ := stopped_affine_ell hP hBc hZc p hξ hρ hu hw hv₀ hpX hpV hcX hcV hVnn
    hHv hHx heqV heqX Complex.imCLM hn
  simp only [Complex.reCLM_apply] at hre ere
  simp only [Complex.imCLM_apply] at him eim
  have hint : Integrable (fun ω ↦ affST p u w T
      (fun l ↦ hestonY X V l (CommonOptional.exitTime T (locFun X V) n ω) ω)) μ :=
    Integrable.re_im_iff.1 ⟨by simpa using hre, by simpa using him⟩
  refine ⟨hint, Complex.ext ?_ ?_⟩
  · have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [← h, ere]
  · have h := integral_im hint
    simp only [RCLike.im_to_complex] at h
    rw [← h, eim]

end CommonAffineStopped
end MathFin.Heston
