/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.Ito.ItoIntegralLocalisedPredictable

/-!
# The localised Itô integral is the `L²` Itô integral of a square-integrable integrand

`predItoIntegral` (`ItoIntegralLocalisedPredictable`) is the Itô integral of a predictable
integrand with almost surely continuous paths, possibly unbounded, built by clipping.
`itoProcessCLM` is the Itô process of an element of `Lp ℝ 2 (trimMeasure T)`. For a bounded
integrand the two agree (`itoProcessCLM_processToLpPredictable`, `itoContinuousMod_modification`);
this file extends the agreement to every integrand that is square-integrable on
`(0, T] × Ω`.

The proof clips `θ` to `[−N, N]` and lets `N → ∞`. The classes of the clips converge to the class
of `θ` in `L²(trimMeasure T)` by dominated convergence, so the `L²` Itô processes converge in
`L²(μ)`, hence in probability. On the other hand the clipped continuous integrals converge almost
surely to `predItoIntegral`, since on each path the clip is inactive from some `N` on. Limits in
probability are unique.

## Main results

* `memLp_uncurry_trimMeasure_of_integral_sq_le`: a predictable process whose second moments at
  the times of `(0, T]` are bounded by a constant is square-integrable for `trimMeasure T`.
* `tendsto_processToLpPredictable_clip`: the classes of the clips of a square-integrable
  integrand converge to its class in `Lp ℝ 2 (trimMeasure T)`.
* `ae_predItoIntegral_eq_itoProcessCLM`: for a predictable integrand with almost surely
  continuous paths on `[0, T]`, and a class `φ` of `Lp ℝ 2 (trimMeasure T)` that is almost
  everywhere the integrand, `predItoIntegral θ t` is almost surely `itoProcessCLM T t φ` for every
  `t ≤ T`. The existence of such a `φ` is the hypothesis that `θ` is square-integrable on
  `(0, T] × Ω`; it is not proved for any particular integrand here.

## References

* [Revuz and Yor, *Continuous Martingales and Brownian Motion*][RevuzYor], Proposition IV.2.13
* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  Section 3.2.D

## Tags

Itô integral, predictable integrand, square-integrable integrand, clipping, limit in probability,
MSC 60H05, MSC 60G44
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralLocalised

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralBrownian
  QuadraticVariationL2 ItoIntegralProcessContinuousModification ItoIntegralRiemannBridge
  LocalisationInMeasure ItoIntegralPredictable ItoLocalMartingale
  ItoIntegralProcessLocalMartingaleGeneral
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### Square-integrability for the predictable measure -/

/-- **A predictable process with bounded second moments is square-integrable for
`trimMeasure T`.** If `θ` is predictable and, at every time `s ∈ (0, T]`, `θ_s²` is integrable
with `𝔼[θ_s²] ≤ C`, then `θ` is in `L²(trimMeasure T)`: the integral of `θ²` over the trimmed
product measure is the one over `timeMeasureHorizon T ⊗ μ` (`lintegral_trim`), which Tonelli
bounds by `C · T`. -/
theorem memLp_uncurry_trimMeasure_of_integral_sq_le (hBmeas : ∀ t, Measurable (B t))
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) (T : ℝ≥0)
    (C : ℝ)
    (hC : ∀ s ∈ Ioc (0 : ℝ≥0) T,
      Integrable (fun ω ↦ θ s ω ^ 2) μ ∧ ∫ ω, θ s ω ^ 2 ∂μ ≤ C) :
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
  rw [lintegral_trim hm hmeasP,
    lintegral_prod _ (hmeasP.mono hm le_rfl).aemeasurable]
  have hle : ∫⁻ s, ∫⁻ ω, ‖Function.uncurry θ (s, ω) ^ 2‖ₑ ∂μ ∂(timeMeasureHorizon T)
      ≤ ∫⁻ _, ENNReal.ofReal C ∂(timeMeasureHorizon T) := by
    refine lintegral_mono_ae ?_
    have hs : ∀ᵐ s ∂(timeMeasureHorizon T), s ∈ Ioc (0 : ℝ≥0) T := by
      rw [timeMeasureHorizon]
      exact ae_restrict_mem measurableSet_Ioc
    filter_upwards [hs] with s hs
    obtain ⟨hint, hbound⟩ := hC s hs
    calc ∫⁻ ω, ‖Function.uncurry θ (s, ω) ^ 2‖ₑ ∂μ
        = ENNReal.ofReal (∫ ω, ‖θ s ω ^ 2‖ ∂μ) :=
          (ofReal_integral_norm_eq_lintegral_enorm hint).symm
      _ = ENNReal.ofReal (∫ ω, θ s ω ^ 2 ∂μ) := by
          simp only [norm_pow, Real.norm_eq_abs, sq_abs]
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hbound
  exact lt_of_le_of_lt (hle.trans_eq (lintegral_const _))
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))

/-! ### The clips converge in `L²` -/

/-- Clipping moves a real by at most its own size. -/
theorem abs_clampM_sub_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |clampM M x - x| ≤ |x| := by
  rw [clampM, abs_le]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
    have h0 : 0 ≤ max (-M) (min M x) := le_max_of_le_right (le_min hM h)
    have h1 : max (-M) (min M x) ≤ x := max_le (by linarith) (min_le_right _ _)
    constructor <;> linarith
  · rw [abs_of_nonpos h, min_eq_right (h.trans hM)]
    have h0 : x ≤ max (-M) x := le_max_right _ _
    have h1 : max (-M) x ≤ 0 := max_le (neg_nonpos.2 hM) h
    constructor <;> linarith

/-- **The classes of the clips converge to the class of the integrand.** If `φ` is a class of
`Lp ℝ 2 (trimMeasure T)` that is almost everywhere the predictable integrand `θ`, the classes
of `clip N θ` (bounded, hence in `L²`) converge to `φ` as `N → ∞`: dominated convergence for
`∫ (clip N θ − θ)²`, dominated by `θ²`. -/
theorem tendsto_processToLpPredictable_clip {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t))
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hφ : φ =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry θ) :
    Tendsto (fun N : ℕ ↦ processToLpPredictable (μ := μ) T hBmeas
        (clip_isStronglyPredictable hBmeas hpred N) (abs_clip_le N θ)) atTop (𝓝 φ) := by
  have hG : MemLp (Function.uncurry θ) 2 (trimMeasure (μ := μ) T hBmeas) :=
    (Lp.memLp φ).ae_eq hφ
  have hF (N : ℕ) : MemLp (Function.uncurry (clip N θ)) 2 (trimMeasure (μ := μ) T hBmeas) :=
    memLp_uncurry_of_bdd_predictable T hBmeas (clip_isStronglyPredictable hBmeas hpred N)
      (abs_clip_le N θ)
  have hφeq : φ = hG.toLp (Function.uncurry θ) := Lp.ext (hφ.trans hG.coeFn_toLp.symm)
  have hint : Tendsto (fun N : ℕ ↦ ∫ z, (Function.uncurry (clip N θ) z
      - Function.uncurry θ z) ^ 2 ∂(trimMeasure (μ := μ) T hBmeas)) atTop (𝓝 0) := by
    have hbound : ∀ N : ℕ, ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas),
        ‖(Function.uncurry (clip N θ) z - Function.uncurry θ z) ^ 2‖
          ≤ Function.uncurry θ z ^ 2 := by
      intro N
      refine ae_of_all _ fun z ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq.2 (abs_clampM_sub_le (Nat.cast_nonneg N) _)
    have hlim : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas),
        Tendsto (fun N : ℕ ↦ (Function.uncurry (clip N θ) z - Function.uncurry θ z) ^ 2)
          atTop (𝓝 ((fun _ ↦ (0 : ℝ)) z)) := by
      refine ae_of_all _ fun z ↦ ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|θ z.1 z.2|⌉₊] with N hN
      have hle : |θ z.1 z.2| ≤ N := (Nat.le_ceil _).trans (Nat.cast_le.2 hN)
      show (0 : ℝ) = (clip N θ z.1 z.2 - θ z.1 z.2) ^ 2
      rw [clip_eq_self hle]
      simp
    letI := (natFiltration (mΩ := mΩ) hBmeas).predictable
    have hmeas (N : ℕ) : AEStronglyMeasurable
        (fun z ↦ (Function.uncurry (clip N θ) z - Function.uncurry θ z) ^ 2)
        (trimMeasure (μ := μ) T hBmeas) :=
      ((hF N).aestronglyMeasurable.sub hG.aestronglyMeasurable).pow 2
    have h := tendsto_integral_of_dominated_convergence
      (m := (natFiltration (mΩ := mΩ) hBmeas).predictable)
      (μ := trimMeasure (μ := μ) T hBmeas)
      (F := fun (N : ℕ) z ↦ (Function.uncurry (clip N θ) z - Function.uncurry θ z) ^ 2)
      (f := fun _ ↦ (0 : ℝ)) (fun z ↦ Function.uncurry θ z ^ 2)
      hmeas
      ((memLp_two_iff_integrable_sq hG.aestronglyMeasurable).1 hG) hbound hlim
    simpa using h
  rw [hφeq]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (tendsto_norm_toLp_sub' hF hG hint)

/-! ### The agreement -/

/-- **The localised Itô integral is the `L²` Itô process, for a square-integrable integrand.**
Let `θ` be predictable for the natural filtration of `B`, with almost surely continuous paths on
`[0, T]`, and let `φ ∈ Lp ℝ 2 (trimMeasure T)` be almost everywhere equal to `θ` (that is, `θ` is
square-integrable on `(0, T] × Ω`). Then for every `t ≤ T`, almost surely

  `predItoIntegral θ t = (itoProcessCLM T t φ)`.

Both are `∫₀ᵗ θ dB`; the first is built by clipping and is continuous in `t`, the second is an
`L²` class and carries no pathwise information. This is the bridge between the two constructions
for an integrand that is not bounded. It does not say that every predictable integrand with
continuous paths is square-integrable: that is the hypothesis `hφ`. -/
theorem ae_predItoIntegral_eq_itoProcessCLM (hB : IsPreBrownianReal B μ)
    (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ)
    (hσc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ θ t ω) (Icc 0 T))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hφ : φ =ᵐ[trimMeasure (μ := μ) T hBmeas] Function.uncurry θ) {t : ℝ≥0} (ht : t ≤ T) :
    (fun ω ↦ predItoIntegral (μ := μ) T hBmeas hpred t ω)
      =ᵐ[μ] ⇑(itoProcessCLM hB T t hBmeas φ) := by
  set φN : ℕ → Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) := fun N ↦
    processToLpPredictable (μ := μ) T hBmeas (clip_isStronglyPredictable hBmeas hpred N)
      (abs_clip_le N θ) with hφN
  have hlim : Tendsto φN atTop (𝓝 φ) :=
    tendsto_processToLpPredictable_clip hBmeas hpred φ hφ
  -- the clipped continuous integrals are modifications of the `L²` Itô processes of the clips
  have h1 (N : ℕ) : (fun ω ↦ clipPredMod (μ := μ) T hBmeas hpred N t ω)
      =ᵐ[μ] ⇑(itoProcessCLM hB T t hBmeas (φN N)) :=
    itoContinuousMod_modification hB T hBmeas hBcont (φN N) ht
  -- the `L²` Itô processes of the clips converge to that of `φ`
  have h2 : TendstoInMeasure μ (fun N ↦ ⇑(itoProcessCLM hB T t hBmeas (φN N))) atTop
      ⇑(itoProcessCLM hB T t hBmeas φ) :=
    tendstoInMeasure_of_tendsto_Lp
      (((itoProcessCLM hB T t hBmeas).continuous.tendsto φ).comp hlim)
  have h3 : TendstoInMeasure μ
      (fun N ω ↦ clipPredMod (μ := μ) T hBmeas hpred N t ω) atTop
      ⇑(itoProcessCLM hB T t hBmeas φ) :=
    h2.congr_left fun N ↦ (h1 N).symm
  -- the clipped integrals converge almost surely to `predItoIntegral`
  have h4 : TendstoInMeasure μ
      (fun N ω ↦ clipPredMod (μ := μ) T hBmeas hpred N t ω) atTop
      (fun ω ↦ predItoIntegral (μ := μ) T hBmeas hpred t ω) := by
    refine tendstoInMeasure_of_tendsto_ae (fun N ↦ ?_) ?_
    · exact (Lp.aestronglyMeasurable (itoProcessCLM hB T t hBmeas (φN N))).congr (h1 N).symm
    · filter_upwards [ae_predItoIntegral_eq hB T hBmeas hBcont hpred hσc, hσc] with ω hω hc
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (denseLevel t fun s ↦ θ s ω)] with N hN
      exact hω N t ⟨zero_le, ht⟩ fun s hs ↦
        (abs_le_denseLevel (hc.mono (Icc_subset_Icc_right ht)) s hs).trans (Nat.cast_le.2 hN)
  exact tendstoInMeasure_ae_unique h4 h3

end ItoIntegralLocalised
end MathFin
