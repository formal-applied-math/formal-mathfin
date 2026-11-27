/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.Girsanov.NovikovCore
public import MathFin.Probability.Brownian.Girsanov.GirsanovPredictableTheta
public import MathFin.Probability.Brownian.Ito.ItoIntegralPredictableL2

/-!
# Novikov's criterion for the Itô integral: `E Z_T = 1`

For a predictable `θ` with `E exp(½∫₀ᵀθ² ds) < ∞`, the Doléans exponential
`Z_T = exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds)` has unit mean. The analytic half is `NovikovCore`
(`integral_exp_eq_one_of_novikov`), a statement about real random variables. This file supplies
its hypotheses from the Itô integral, by truncating `θ`:

* `θₙ = clip n θ` is bounded and predictable, so `c·θₙ` is too, for every real `c`, and the
  bounded Girsanov development gives `E Z_T(cθₙ) = 1` (`integral_ZTpred_eq_one`). Reading
  `Z_T(cθₙ)` as `exp(c·Mₙ − c²/2·Aₙ)` with `Mₙ = −∫θₙ dB`, `Aₙ = ∫₀ᵀθₙ² ds` is
  `lintegral_exp_scaled_eq_one`: the Itô integral is linear (`processToLpPredictable` is
  homogeneous on `c·ψ`) and the representative's slice integral is `∫₀ᵀ(cψ)² ds` almost surely.
* `Aₙ ≤ A' = ∫₀ᵀθ² ds` and `Aₙ → A'` almost surely, by monotone domination and dominated
  convergence on the almost surely integrable slices of the square-integrable `θ`.
* The classes of the clips converge to the class `φ` of `θ` in `L²(trimMeasure T)`
  (`tendsto_processToLpPredictable_clip`), so the Itô integrals converge in `L²(μ)`, hence in
  measure, hence almost surely along a subsequence.

The condition `E exp(½A') < ∞` also forces `E A' < ∞`, i.e. `θ ∈ L²((0,T] × Ω)`, which is the
domain of the `L²` Itô integral (`memLp_trim_of_novikov`).

## Main results

* `lintegral_exp_scaled_eq_one`: for a bounded predictable `ψ` and any real `c`,
  `E exp(−c·∫ψ dB − c²/2·∫₀ᵀψ² ds) = 1`.
* `integral_contDoleansExp_eq_one_of_novikov`: if `θ` is predictable, `φ ∈ L²(trimMeasure T)` is
  its class, and `E exp(½∫₀ᵀθ² ds) < ∞`, then `E exp(−∫θ dB − ½∫₀ᵀθ² ds) = 1`.
* `memLp_trim_of_novikov`: almost surely integrable slices `θ_·(ω)²` and `E exp(½∫₀ᵀθ² ds) < ∞`
  put `θ` in `L²(trimMeasure T)`.
* `exists_integral_contDoleansExp_eq_one_of_novikov`: Novikov's theorem for the Itô integral, with
  the class of `θ` produced rather than assumed.

## What is not here

Only `E Z_T = 1` is proved. That the process `t ↦ Z_t` is a martingale on `[0,T]`, and Girsanov's
theorem for such a `θ` (that `B + ∫θ ds` is a Brownian motion under `Z_T·P`), are not: the
bounded Girsanov development (`Btheta_isBrownianOn_predictable_of_bdd`) uses boundedness of `θ`
for the uniform moment bounds of the simple approximants, and Novikov's `θ` has no such bound.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  §3.5
* [D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*][RevuzYor], §VIII.1
* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 9.1.7

## Tags

Novikov condition, Doléans exponential, Girsanov theorem, Itô integral, truncation,
MSC 60H05, MSC 60G44
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology NNReal
open scoped NNReal ENNReal
open ItoIntegralL2 ItoIntegralProcess ItoIntegralCLM ItoIsometryAdapted ItoIntegralBrownian
  ItoIntegralRiemannBridge SimpleDoleansMoments ItoIntegralProcessContinuousModification
  ItoIntegralLocalised

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### Measurability and integrability of the slices -/

/-- A predictable process is jointly measurable on `ℝ≥0 × Ω`. -/
lemma stronglyMeasurable_uncurry_of_predictable (hBmeas : ∀ t, Measurable (B t))
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) :
    StronglyMeasurable (Function.uncurry θ) :=
  (hpred : StronglyMeasurable[(natFiltration hBmeas).predictable] (Function.uncurry θ)).mono
    (natFiltration hBmeas).predictable_le_prod

/-- `ω ↦ ∫₀ᵀ g(s,ω)² ds` is measurable for a jointly measurable `g`. -/
lemma measurable_integral_sq {g : ℝ≥0 → Ω → ℝ} (hg : StronglyMeasurable (Function.uncurry g))
    (T : ℝ≥0) :
    Measurable fun ω ↦ ∫ s in Set.Ioc (0 : ℝ≥0) T, g s ω ^ 2 ∂timeMeasure :=
  (StronglyMeasurable.integral_prod_left' (μ := timeMeasureHorizon T)
    (f := fun z : ℝ≥0 × Ω ↦ Function.uncurry g z ^ 2) (hg.pow 2)).measurable

/-- Clipping does not increase the absolute value. -/
lemma abs_clampM_le_abs {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |clampM M x| ≤ |x| := by
  rw [clampM, abs_le]
  have h : -|x| ≤ min M x := le_min (by linarith [abs_nonneg x]) (neg_abs_le x)
  exact ⟨le_max_of_le_right h,
    max_le (by linarith [abs_nonneg x]) ((min_le_right _ _).trans (le_abs_self x))⟩

/-- For a class `φ ∈ L²(trimMeasure T)` of `θ`, almost every slice `θ_·(ω)²` is integrable on
`(0,T]`: Fubini for `timeMeasureHorizon T ⊗ μ`. -/
lemma ae_integrable_sq_slice (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) {θ : ℝ≥0 → Ω → ℝ}
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hφ : φ =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry θ) :
    ∀ᵐ ω ∂μ, Integrable (fun s ↦ θ s ω ^ 2) (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) := by
  have hG : MemLp (Function.uncurry θ) 2 (trimMeasure (μ := μ) T hBmeas) :=
    (Lp.memLp φ).ae_eq hφ
  have h1 := (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).1 hG
  have h2 : Integrable (fun z ↦ Function.uncurry θ z ^ 2) ((timeMeasureHorizon T).prod μ) :=
    integrable_of_integrable_trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod h1
  exact h2.prod_left_ae

/-! ### The unit-mean hypothesis for the truncations -/

/-- The realization of `c·ψ` is `c` times the realization of `ψ`. -/
lemma processToLpPredictable_const_mul (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {ψ : ℝ≥0 → Ω → ℝ} (hψ : IsStronglyPredictable (natFiltration hBmeas) ψ) {C : ℝ}
    (hbdd : ∀ t ω, |ψ t ω| ≤ C) (c : ℝ)
    (hχ : IsStronglyPredictable (natFiltration hBmeas) fun t ω ↦ c * ψ t ω) {C' : ℝ}
    (hbdd' : ∀ t ω, |c * ψ t ω| ≤ C') :
    processToLpPredictable (μ := μ) T hBmeas hχ hbdd'
      = c • processToLpPredictable (μ := μ) T hBmeas hψ hbdd := by
  refine Lp.ext ?_
  filter_upwards [processToLpPredictable_coeFn (μ := μ) T hBmeas hχ hbdd',
    processToLpPredictable_coeFn (μ := μ) T hBmeas hψ hbdd,
    Lp.coeFn_smul c (processToLpPredictable (μ := μ) T hBmeas hψ hbdd)] with z h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul]
  rfl

/-- **Unit mean of the scaled exponentials of a bounded integrand.** For a bounded predictable `ψ`
and any real `c`, `E exp(c·(−∫ψ dB) − c²/2·∫₀ᵀψ² ds) = 1`: the bounded Girsanov density
`Z_T(cψ)` (`integral_ZTpred_eq_one`), whose Itô integral is `c` times that of `ψ` and whose
quadratic variation is `c²` times `∫₀ᵀψ² ds`, almost surely. -/
lemma lintegral_exp_scaled_eq_one (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (T : ℝ≥0) {ψ : ℝ≥0 → Ω → ℝ} (hψ : IsStronglyPredictable (natFiltration hBmeas) ψ) {C : ℝ}
    (hbdd : ∀ t ω, |ψ t ω| ≤ C) (c : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (c * -(itoIntegralCLM hB T hBmeas
        (processToLpPredictable (μ := μ) T hBmeas hψ hbdd) ω)
      - c ^ 2 / 2 * ∫ s in Set.Ioc (0 : ℝ≥0) T, ψ s ω ^ 2 ∂timeMeasure)) ∂μ = 1 := by
  have hχ : IsStronglyPredictable (natFiltration hBmeas) fun t ω ↦ c * ψ t ω :=
    (by fun_prop : Continuous fun x : ℝ ↦ c * x).comp_stronglyMeasurable hψ
  have hbdd' : ∀ t ω, |c * ψ t ω| ≤ |c| * C := fun t ω ↦ by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbdd t ω) (abs_nonneg c)
  obtain ⟨V, hV⟩ := exists_approxSeq (μ := μ) hBmeas T hχ hbdd'
  have hint := (memLp_ZTpred_one hB hBmeas T hχ hbdd' V hV).integrable le_rfl
  have hone := integral_ZTpred_eq_one hB hBmeas T hχ hbdd' V hV
  have hle : ∫⁻ ω, ENNReal.ofReal (ZTpred hB T hBmeas hχ hbdd' ω) ∂μ = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun ω ↦ (contDoleansExp_pos _ _ _ _).le), hone, ENNReal.ofReal_one]
  refine Eq.trans (lintegral_congr_ae ?_) hle
  have hsm := processToLpPredictable_const_mul (μ := μ) T hBmeas hψ hbdd c hχ hbdd'
  have hI : itoIntPred hB T hBmeas hχ hbdd' =ᵐ[μ] fun ω ↦
      c * itoIntegralCLM hB T hBmeas (processToLpPredictable (μ := μ) T hBmeas hψ hbdd) ω := by
    have h : itoIntegralCLM hB T hBmeas (processToLpPredictable (μ := μ) T hBmeas hχ hbdd')
        = c • itoIntegralCLM hB T hBmeas
            (processToLpPredictable (μ := μ) T hBmeas hψ hbdd) := by
      rw [hsm, map_smul]
    show ⇑(itoIntegralCLM hB T hBmeas (processToLpPredictable (μ := μ) T hBmeas hχ hbdd'))
      =ᵐ[μ] _
    rw [h]
    filter_upwards [Lp.coeFn_smul c (itoIntegralCLM hB T hBmeas
      (processToLpPredictable (μ := μ) T hBmeas hψ hbdd))] with ω hω
    rw [hω, Pi.smul_apply, smul_eq_mul]
  have hslice := processToLpPredictable_ae_slice (μ := μ) T hBmeas hχ hbdd'
  filter_upwards [hI, hslice] with ω h1 h2
  have h1' : itoIntPred hB T hBmeas hχ hbdd' ω = c * itoIntegralCLM hB T hBmeas
      (processToLpPredictable (μ := μ) T hBmeas hψ hbdd) ω := h1
  have h2' : ∀ᵐ s ∂(timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)),
      processToLpPredictable (μ := μ) T hBmeas hχ hbdd' (s, ω) = c * ψ s ω := h2
  have hA : ∫ s in Set.Ioc (0 : ℝ≥0) T,
        (processToLpPredictable (μ := μ) T hBmeas hχ hbdd' (s, ω)) ^ 2 ∂timeMeasure
      = c ^ 2 * ∫ s in Set.Ioc (0 : ℝ≥0) T, ψ s ω ^ 2 ∂timeMeasure := by
    have h3 : ∫ s in Set.Ioc (0 : ℝ≥0) T,
          (processToLpPredictable (μ := μ) T hBmeas hχ hbdd' (s, ω)) ^ 2 ∂timeMeasure
        = ∫ s in Set.Ioc (0 : ℝ≥0) T, (c * ψ s ω) ^ 2 ∂timeMeasure :=
      integral_congr_ae (h2'.mono fun s hs ↦ by simp only [hs])
    rw [h3]
    simp_rw [mul_pow]
    exact integral_const_mul _ _
  have hZ : ZTpred hB T hBmeas hχ hbdd' ω = Real.exp (-(itoIntPred hB T hBmeas hχ hbdd' ω)
      - 2⁻¹ * ∫ s in Set.Ioc (0 : ℝ≥0) T,
        (processToLpPredictable (μ := μ) T hBmeas hχ hbdd' (s, ω)) ^ 2 ∂timeMeasure) := rfl
  rw [hZ, h1', hA]
  exact congrArg (fun x ↦ ENNReal.ofReal (Real.exp x)) (by ring)

/-! ### Novikov's criterion for the Itô integral -/

/-- **Novikov's criterion for the Itô integral.** Let `θ` be predictable for the natural
filtration of a Brownian motion `B`, let `φ ∈ L²(trimMeasure T)` be its class (that is, `θ` is
square-integrable on `(0,T] × Ω`), and suppose `E exp(½∫₀ᵀθ² ds) < ∞`. Then the Doléans
exponential has unit mean:

  `E exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds) = 1`,

where `∫₀ᵀθ dB` is the `L²` Itô integral `itoIntegralCLM φ`. The proof truncates `θ` to
`[−n, n]`, applies the bounded Girsanov density to `c·θₙ` for every `c`
(`lintegral_exp_scaled_eq_one`), and passes to the limit with the analytic core
(`integral_exp_eq_one_of_novikov`) along a subsequence on which the Itô integrals converge almost
surely. The square-integrability is not an extra hypothesis in substance: it follows from the
Novikov condition when the slices are almost surely integrable
(`memLp_trim_of_novikov`, `exists_integral_contDoleansExp_eq_one_of_novikov`). -/
theorem integral_contDoleansExp_eq_one_of_novikov (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hφ : φ =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry θ)
    (hNov : ∫⁻ ω, ENNReal.ofReal (Real.exp (2⁻¹ *
      ∫ s in Set.Ioc (0 : ℝ≥0) T, θ s ω ^ 2 ∂timeMeasure)) ∂μ ≠ ⊤) :
    ∫ ω, contDoleansExp (⇑(itoIntegralCLM hB T hBmeas φ)) θ T ω ∂μ = 1 := by
  have hSM : ∀ N : ℕ, StronglyMeasurable (Function.uncurry (clip N θ)) := fun N ↦
    stronglyMeasurable_uncurry_of_predictable hBmeas (clip_isStronglyPredictable hBmeas hpred N)
  have hSMθ := stronglyMeasurable_uncurry_of_predictable hBmeas hpred
  set φn : ℕ → Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) := fun N ↦
    processToLpPredictable (μ := μ) T hBmeas (clip_isStronglyPredictable hBmeas hpred N)
      (abs_clip_le N θ) with hφn
  have hlim : Tendsto φn atTop (𝓝 φ) :=
    tendsto_processToLpPredictable_clip hBmeas hpred φ hφ
  -- the Itô integrals of the clips converge in measure, hence a.e. along a subsequence
  have hWlim : TendstoInMeasure μ (fun n ↦ ⇑(itoIntegralCLM hB T hBmeas (φn n))) atTop
      ⇑(itoIntegralCLM hB T hBmeas φ) :=
    tendstoInMeasure_of_tendsto_Lp (((itoIntegralCLM hB T hBmeas).continuous.tendsto φ).comp hlim)
  obtain ⟨ns, hns, hae⟩ := hWlim.exists_seq_tendsto_ae
  have hint := ae_integrable_sq_slice hBmeas T φ hφ
  have hclip_le : ∀ (n : ℕ) (s : ℝ≥0) (ω : Ω), clip n θ s ω ^ 2 ≤ θ s ω ^ 2 := fun n s ω ↦
    sq_le_sq.2 (abs_clampM_le_abs (Nat.cast_nonneg n) _)
  have hM : ∀ k, Measurable fun ω ↦ -(itoIntegralCLM hB T hBmeas (φn (ns k)) ω) := fun k ↦
    (Lp.stronglyMeasurable _).measurable.neg
  have hM' : Measurable fun ω ↦ -(itoIntegralCLM hB T hBmeas φ ω) :=
    (Lp.stronglyMeasurable _).measurable.neg
  have hA : ∀ k, Measurable fun ω ↦
      ∫ s in Set.Ioc (0 : ℝ≥0) T, clip (ns k) θ s ω ^ 2 ∂timeMeasure := fun k ↦
    measurable_integral_sq (hSM (ns k)) T
  have hA' := measurable_integral_sq hSMθ T
  have hA0 : ∀ k ω, 0 ≤ ∫ s in Set.Ioc (0 : ℝ≥0) T, clip (ns k) θ s ω ^ 2 ∂timeMeasure :=
    fun k ω ↦ integral_nonneg fun s ↦ sq_nonneg _
  have hAle : ∀ᵐ ω ∂μ, ∀ k, (∫ s in Set.Ioc (0 : ℝ≥0) T, clip (ns k) θ s ω ^ 2 ∂timeMeasure)
      ≤ ∫ s in Set.Ioc (0 : ℝ≥0) T, θ s ω ^ 2 ∂timeMeasure := by
    filter_upwards [hint] with ω hω k
    exact integral_mono_of_nonneg (ae_of_all _ fun s ↦ sq_nonneg _) hω
      (ae_of_all _ fun s ↦ hclip_le _ s ω)
  have hAlim : ∀ᵐ ω ∂μ, Tendsto
      (fun k ↦ ∫ s in Set.Ioc (0 : ℝ≥0) T, clip (ns k) θ s ω ^ 2 ∂timeMeasure) atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ≥0) T, θ s ω ^ 2 ∂timeMeasure)) := by
    filter_upwards [hint] with ω hω
    have hmeas : ∀ N : ℕ, AEStronglyMeasurable (fun s ↦ clip N θ s ω ^ 2)
        (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) := fun N ↦
      (((hSM N).measurable.comp
        (measurable_prodMk_right (y := ω))).pow_const 2).aestronglyMeasurable
    have hbound : ∀ N : ℕ, ∀ᵐ s ∂(timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)),
        ‖clip N θ s ω ^ 2‖ ≤ θ s ω ^ 2 := fun N ↦ ae_of_all _ fun s ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hclip_le N s ω
    have hpt : ∀ᵐ s ∂(timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)),
        Tendsto (fun N : ℕ ↦ clip N θ s ω ^ 2) atTop (𝓝 (θ s ω ^ 2)) := ae_of_all _ fun s ↦ by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|θ s ω|⌉₊] with N hN
      have hle : |θ s ω| ≤ N := (Nat.le_ceil _).trans (Nat.cast_le.2 hN)
      rw [clip_eq_self hle]
    exact (tendsto_integral_of_dominated_convergence (fun s ↦ θ s ω ^ 2) hmeas hω hbound hpt).comp
      hns.tendsto_atTop
  have hmart : ∀ k (c : ℝ), ∫⁻ ω, ENNReal.ofReal (Real.exp
      (c * -(itoIntegralCLM hB T hBmeas (φn (ns k)) ω)
        - c ^ 2 / 2 * ∫ s in Set.Ioc (0 : ℝ≥0) T, clip (ns k) θ s ω ^ 2 ∂timeMeasure)) ∂μ = 1 :=
    fun k c ↦ lintegral_exp_scaled_eq_one hB hBmeas T
      (clip_isStronglyPredictable hBmeas hpred (ns k)) (abs_clip_le (ns k) θ) c
  exact integral_exp_eq_one_of_novikov (P := μ)
    (M := fun k ω ↦ -(itoIntegralCLM hB T hBmeas (φn (ns k)) ω))
    (A := fun k ω ↦ ∫ s in Set.Ioc (0 : ℝ≥0) T, clip (ns k) θ s ω ^ 2 ∂timeMeasure)
    (M' := fun ω ↦ -(itoIntegralCLM hB T hBmeas φ ω))
    (A' := fun ω ↦ ∫ s in Set.Ioc (0 : ℝ≥0) T, θ s ω ^ 2 ∂timeMeasure)
    hM hA hM' hA' hA0 hAle hmart (hae.mono fun ω h ↦ h.neg) hAlim hNov

/-- **Novikov's condition puts `θ` in `L²((0,T] × Ω)`.** If the slices `θ_·(ω)²` are almost surely
integrable on `(0,T]` and `E exp(½∫₀ᵀθ² ds) < ∞`, then `θ` is square-integrable for
`trimMeasure T`: `x ≤ 2 exp(x/2)` gives `E ∫₀ᵀθ² ds ≤ 2 E exp(½∫₀ᵀθ² ds)`, and Tonelli reads the
left side as the integral of `θ²` over the product measure. -/
theorem memLp_trim_of_novikov (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ)
    (hslice : ∀ᵐ ω ∂μ,
      Integrable (fun s ↦ θ s ω ^ 2) (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)))
    (hNov : ∫⁻ ω, ENNReal.ofReal (Real.exp (2⁻¹ *
      ∫ s in Set.Ioc (0 : ℝ≥0) T, θ s ω ^ 2 ∂timeMeasure)) ∂μ ≠ ⊤) :
    MemLp (Function.uncurry θ) 2 (trimMeasure (μ := μ) T hBmeas) := by
  have hm := (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod
  have hg : StronglyMeasurable[(natFiltration hBmeas).predictable]
      fun z ↦ Function.uncurry θ z ^ 2 := StronglyMeasurable.pow hpred 2
  refine (memLp_two_iff_integrable_sq hpred.aestronglyMeasurable).2
    ⟨hg.aestronglyMeasurable, ?_⟩
  show ∫⁻ z, ‖Function.uncurry θ z ^ 2‖ₑ
      ∂(((timeMeasureHorizon T).prod μ).trim hm) < ⊤
  have hmeasP : Measurable[(natFiltration hBmeas).predictable]
      fun z ↦ ‖Function.uncurry θ z ^ 2‖ₑ := by
    letI := (natFiltration (mΩ := mΩ) hBmeas).predictable
    exact hg.measurable.enorm
  have hmeasF : Measurable fun z : ℝ≥0 × Ω ↦ ‖Function.uncurry θ z ^ 2‖ₑ :=
    ((stronglyMeasurable_uncurry_of_predictable hBmeas hpred).pow 2).measurable.enorm
  rw [lintegral_trim hm hmeasP, lintegral_prod_symm' _ hmeasF]
  have hle : ∫⁻ ω, ∫⁻ s, ‖Function.uncurry θ (s, ω) ^ 2‖ₑ ∂(timeMeasureHorizon T) ∂μ
      ≤ ∫⁻ ω, 2 * ENNReal.ofReal (Real.exp (2⁻¹ *
          ∫ s in Set.Ioc (0 : ℝ≥0) T, θ s ω ^ 2 ∂timeMeasure)) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hslice] with ω hω
    have hω' : Integrable (fun s ↦ θ s ω ^ 2) (timeMeasureHorizon T) := hω
    calc ∫⁻ s, ‖Function.uncurry θ (s, ω) ^ 2‖ₑ ∂(timeMeasureHorizon T)
        = ENNReal.ofReal (∫ s, ‖θ s ω ^ 2‖ ∂(timeMeasureHorizon T)) :=
          (ofReal_integral_norm_eq_lintegral_enorm hω').symm
      _ = ENNReal.ofReal (∫ s in Set.Ioc (0 : ℝ≥0) T, θ s ω ^ 2 ∂timeMeasure) :=
          congrArg ENNReal.ofReal (integral_congr_ae
            (ae_of_all _ fun s ↦ Real.norm_of_nonneg (sq_nonneg (θ s ω))))
      _ ≤ 2 * ENNReal.ofReal (Real.exp (2⁻¹ *
            ∫ s in Set.Ioc (0 : ℝ≥0) T, θ s ω ^ 2 ∂timeMeasure)) := by
          generalize (∫ s in Set.Ioc (0 : ℝ≥0) T, θ s ω ^ 2 ∂timeMeasure) = a
          have ha : a ≤ 2 * Real.exp (2⁻¹ * a) := by
            have := Real.add_one_le_exp (2⁻¹ * a)
            linarith
          calc ENNReal.ofReal a ≤ ENNReal.ofReal (2 * Real.exp (2⁻¹ * a)) :=
                ENNReal.ofReal_le_ofReal ha
            _ = 2 * ENNReal.ofReal (Real.exp (2⁻¹ * a)) := by
                rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  refine lt_of_le_of_lt hle ?_
  rw [lintegral_const_mul' 2 _ (by simp)]
  exact ENNReal.mul_lt_top (by simp) hNov.lt_top

/-- **Novikov's theorem for the Itô integral, `E Z_T = 1`.** Let `θ` be predictable for the natural
filtration of a Brownian motion, with almost surely integrable slices `θ_·(ω)²` on `(0,T]` and
`E exp(½∫₀ᵀθ² ds) < ∞`. Then `θ` has a class `φ ∈ L²(trimMeasure T)` and the Doléans exponential of
its `L²` Itô integral has unit mean, `E exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds) = 1`. This is the unit mean of
`Z_T`, not the martingale property of `t ↦ Z_t` nor Girsanov's theorem for `θ`. -/
theorem exists_integral_contDoleansExp_eq_one_of_novikov (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ)
    (hslice : ∀ᵐ ω ∂μ,
      Integrable (fun s ↦ θ s ω ^ 2) (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)))
    (hNov : ∫⁻ ω, ENNReal.ofReal (Real.exp (2⁻¹ *
      ∫ s in Set.Ioc (0 : ℝ≥0) T, θ s ω ^ 2 ∂timeMeasure)) ∂μ ≠ ⊤) :
    ∃ φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas),
      φ =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry θ ∧
        ∫ ω, contDoleansExp (⇑(itoIntegralCLM hB T hBmeas φ)) θ T ω ∂μ = 1 := by
  have hL := memLp_trim_of_novikov hBmeas T hpred hslice hNov
  exact ⟨hL.toLp _, hL.coeFn_toLp,
    integral_contDoleansExp_eq_one_of_novikov hB hBmeas T hpred _ hL.coeFn_toLp hNov⟩

end MathFin
