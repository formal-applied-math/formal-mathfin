/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaAdapted
public import MathFin.Foundations.ItoIntegralCrossHorizon

/-! # Riemann sums of a predictable integrand with almost surely continuous paths

The Riemann-sum characterisation of `∫ θ dB` (`tendstoInMeasure_riemannσ`) is proved for a bounded
adapted `θ` with every path continuous. Here `θ` is bounded and predictable, and its paths are
continuous on `[0, T]` only almost surely. A continuous function of an Itô process is such an
integrand: the continuous version of the Itô integral is predictable
(`itoContinuousMod_isStronglyPredictable`), but has continuous paths only almost surely.

* `itoProcessCLM_processToLpPredictable`: the `L²` Itô process at time `t` of a bounded predictable
  integrand, built at horizon `T ≥ t`, is its Itô integral at horizon `t`. The band truncation of
  `itoProcessCLM_consist`, whose only use of path continuity was predictability.
* `tendstoInMeasure_riemannStieltjes_itoContinuousMod`: for `M` a version of `∫ σ dB` (`σ` bounded,
  adapted, path-continuous) and `w` bounded predictable with almost surely continuous paths, the
  sums `∑ w(tₖ)(M_{tₖ₊₁} − M_{tₖ})` on the uniform partitions of `[0, t]` converge in probability
  to the continuous Itô integral of `w σ` at `t`, built at any horizon `T ≥ t`
  (`tendstoInMeasure_riemannStieltjes` at horizon `t`, then the horizon).
* `tendstoInMeasure_riemannσ_of_predictable`: the case `σ = 1`, `M = B − B₀`: the Riemann sums
  `∑ w(tₖ)(B_{tₖ₊₁} − B_{tₖ})` on `[0, t]` converge in probability to the continuous Itô integral
  of `w` at `t`.
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralPredictable

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralRiemannBridge
  ItoIntegralProcessContinuousModification QuadraticVariationL2 AdaptedRiemannStieltjes
  ItoFormulaAdapted
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)

/-! ### The horizon -/

/-- The band truncation `𝟙_{[0, t]} θ` of a bounded predictable integrand is `L²` at every
horizon. -/
theorem memLp_indicator_Iic_prod {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C)
    (t : ℝ≥0) :
    MemLp ((Iic t ×ˢ (univ : Set Ω)).indicator (Function.uncurry θ)) 2
      (trimMeasure_T (μ := μ) T hBmeas) := by
  refine MemLp.of_bound (hpred.indicator (measurableSet_predictable_Iic_prod
    (𝓕 := natFiltration (mΩ := mΩ) hBmeas) (i := t) MeasurableSet.univ)).aestronglyMeasurable C
    (ae_of_all _ fun z ↦ ?_)
  by_cases hz : z ∈ Iic t ×ˢ (univ : Set Ω)
  · rw [indicator_of_mem hz, Real.norm_eq_abs]
    exact hbdd z.1 z.2
  · rw [indicator_of_notMem hz, norm_zero]
    exact (abs_nonneg _).trans (hbdd 0 z.2)

include hB in
/-- **The Itô process of a bounded predictable integrand does not depend on the horizon**: built
at horizon `T ≥ t`, at time `t` it is the Itô integral built at horizon `t`. The value at `t` sees
only the band `(0, t]` of the integrand (`itoProcessCLM_eq_zero_of_vanishes_before`,
`itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after`), whose integral is the same at every
horizon (`itoIntegralCLM_cross_horizon`). -/
theorem itoProcessCLM_processToLpPredictable {t : ℝ≥0} (htT : t ≤ T) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) :
    itoProcessCLM hB T t hBmeas (processToLpPredictable T hBmeas hpred hbdd)
      = itoIntegralCLM_T hB t hBmeas (processToLpPredictable t hBmeas hpred hbdd) := by
  set g := (Iic t ×ˢ (univ : Set Ω)).indicator (Function.uncurry θ)
  have hg (S : ℝ≥0) : MemLp g 2 (trimMeasure_T (μ := μ) S hBmeas) :=
    memLp_indicator_Iic_prod S hBmeas hpred hbdd t
  have hgle {z : ℝ≥0 × Ω} (hz : z.1 ≤ t) : g z = Function.uncurry θ z :=
    indicator_of_mem (mem_prod.2 ⟨hz, mem_univ _⟩) _
  have hggt {z : ℝ≥0 × Ω} (hz : t < z.1) : g z = 0 :=
    indicator_of_notMem (fun h ↦ (not_le.2 hz) (mem_prod.1 h).1) _
  have hband (S : ℝ≥0) (hS : t ≤ S) :
      itoProcessCLM hB S t hBmeas (processToLpPredictable S hBmeas hpred hbdd)
        = itoIntegralCLM_T hB S hBmeas ((hg S).toLp g) := by
    have hzero : itoProcessCLM hB S t hBmeas
        (processToLpPredictable S hBmeas hpred hbdd - (hg S).toLp g) = 0 := by
      refine itoProcessCLM_eq_zero_of_vanishes_before hB S t hS hBmeas _ ?_
      filter_upwards [processToLpPredictable_coeFn (μ := μ) S hBmeas hpred hbdd,
        Lp.coeFn_sub (processToLpPredictable S hBmeas hpred hbdd) ((hg S).toLp g),
        (hg S).coeFn_toLp] with p hp1 hp2 hp3 hp4
      rw [hp2, Pi.sub_apply, hp1, hp3, hgle hp4, sub_self]
    rw [map_sub, sub_eq_zero] at hzero
    rw [hzero]
    refine (itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after hB S t hS hBmeas _ ?_).symm
    filter_upwards [(hg S).coeFn_toLp] with p hp hpt
    rw [hp, hggt hpt]
  have hLp : (hg t).toLp g = processToLpPredictable t hBmeas hpred hbdd := by
    refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
    filter_upwards [ae_fst_mem_Ioc_trimMeasure_T (μ := μ) t hBmeas] with z hz
    exact hgle hz.2
  rw [hband T htT, ← itoIntegralCLM_cross_horizon hB hBmeas htT (fun z hz ↦ hggt hz) (hg t) (hg T),
    hLp]

/-! ### Riemann–Stieltjes sums against an Itô integral -/

variable {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C)

include hB hBcont in
/-- **Riemann–Stieltjes sums of a predictable weight against an Itô integral converge to the Itô
integral of the product.** Let `M` be, at each time of `[0, t]`, a version of `∫ σ dB`, with `σ`
bounded, adapted and path-continuous, and `w` bounded predictable with paths almost surely
continuous on `[0, t]`. The sums `∑ w(tₖ)(M_{tₖ₊₁} − M_{tₖ})` on the uniform partitions of `[0, t]`
converge in probability to the continuous Itô integral at `t` of `θ = w σ`, built at any horizon
`T ≥ t`. -/
theorem tendstoInMeasure_riemannStieltjes_itoContinuousMod {t : ℝ≥0} (ht : t ≤ T)
    {M : ℝ≥0 → Ω → ℝ}
    (hM : ∀ s ≤ t, M s =ᵐ[μ] itoProcessCLM hB t s hBmeas (processToLp t hBmeas hadap hcont hbdd))
    {w : ℝ≥0 → Ω → ℝ} (hw_pred : IsStronglyPredictable (natFiltration hBmeas) w)
    (hw_cont : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Icc 0 t)) {Cw : ℝ}
    (hw_bdd : ∀ s ω, |w s ω| ≤ Cw) {θ : ℝ≥0 → Ω → ℝ}
    (hθ_pred : IsStronglyPredictable (natFiltration hBmeas) θ) {Cθ : ℝ}
    (hθ_bdd : ∀ s ω, |θ s ω| ≤ Cθ) (hθ : ∀ s ω, θ s ω = w s ω * σ s ω) :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ Finset.range n, w (unifPart t n k) ω
        * (M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω)) atTop
      (itoContinuousMod T hBmeas (processToLpPredictable (μ := μ) T hBmeas hθ_pred hθ_bdd) t) := by
  set φt := processToLp (μ := μ) t hBmeas hadap hcont hbdd
  have h := tendstoInMeasure_riemannStieltjes hB t hBmeas φt hM hw_pred hw_cont hw_bdd
  rw [itoIntegralAgainst_weightLp hB t hBmeas φt hw_pred hw_bdd
    (processToLpPredictable t hBmeas hθ_pred hθ_bdd) ?_] at h
  · refine h.congr_right ?_
    filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont
      (processToLpPredictable T hBmeas hθ_pred hθ_bdd) ht] with ω hω
    rw [hω, itoProcessCLM_processToLpPredictable hB T hBmeas ht hθ_pred hθ_bdd]
  · filter_upwards [processToLpPredictable_coeFn (μ := μ) t hBmeas hθ_pred hθ_bdd,
      processToLp_coeFn (μ := μ) t hBmeas hadap hcont hbdd] with z h1 h2
    rw [h1, h2]
    exact (hθ z.1 z.2).trans (mul_comm _ _)

omit mΩ [IsProbabilityMeasure μ] in
/-- The Riemann sums of the constant `1` telescope to the increment `B_t − B_0`. -/
theorem riemannσ_one {t : ℝ≥0} {n : ℕ} (hn : n ≠ 0) (ω : Ω) :
    riemannσ (B := B) (fun _ _ ↦ (1 : ℝ)) t n ω = B t ω - B 0 ω := by
  simp only [riemannσ, one_mul]
  rw [Finset.sum_range_sub (fun k ↦ B (unifPart t n k) ω)]
  simp [unifPart, hn]

include hB in
/-- **The Brownian increment is the Itô integral of `1`**, at each time: the Riemann sums of `1`
are `B_s − B_0` (`riemannσ_one`). -/
theorem ae_eq_itoProcessCLM_one {t s : ℝ≥0} (hs : s ≤ t) :
    (fun ω ↦ B s ω - B 0 ω) =ᵐ[μ] itoProcessCLM hB t s hBmeas
      (processToLp (μ := μ) t hBmeas (σ := fun _ _ ↦ (1 : ℝ)) (fun _ ↦ stronglyMeasurable_const)
        (fun _ ↦ continuous_const) (C := 1) fun _ _ ↦ by simp) := by
  rw [itoProcessCLM_consist hB hBmeas le_rfl hs, itoProcessCLM_terminal_eq]
  have h1 : TendstoInMeasure μ (fun n ↦ riemannσ (B := B) (fun _ _ ↦ (1 : ℝ)) s n) atTop
      fun ω ↦ B s ω - B 0 ω := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) (ae_of_all _ fun ω ↦ ?_)
    · exact (memLp_riemannσ hB hBmeas (fun _ ↦ stronglyMeasurable_const) (C := 1)
        (fun _ _ ↦ by simp) s n).aestronglyMeasurable
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      exact (riemannσ_one hn ω).symm
  exact tendstoInMeasure_ae_unique h1 (tendstoInMeasure_riemannσ hB hBmeas
    (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) (C := 1) (fun _ _ ↦ by simp) s)

include hB hBcont in
/-- **The Riemann sums of a bounded predictable integrand with almost surely continuous paths
converge to its Itô integral.** For `t ≤ T` the sums `∑ w(tₖ)(B_{tₖ₊₁} − B_{tₖ})` on the uniform
partitions of `[0, t]` converge in probability to the continuous Itô integral of `w` at `t`, built
at horizon `T`: `tendstoInMeasure_riemannStieltjes_itoContinuousMod` for `σ = 1`, `M = B − B_0`. -/
theorem tendstoInMeasure_riemannσ_of_predictable {w : ℝ≥0 → Ω → ℝ}
    (hw_pred : IsStronglyPredictable (natFiltration hBmeas) w)
    (hw_cont : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Icc 0 T)) {Cw : ℝ}
    (hw_bdd : ∀ s ω, |w s ω| ≤ Cw) {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ↦ riemannσ (B := B) w t n) atTop
      (itoContinuousMod T hBmeas (processToLpPredictable (μ := μ) T hBmeas hw_pred hw_bdd) t) := by
  refine (tendstoInMeasure_riemannStieltjes_itoContinuousMod hB T hBmeas hBcont
    (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const) (C := 1) (by simp) ht
    (M := fun s ω ↦ B s ω - B 0 ω) (fun s hs ↦ ae_eq_itoProcessCLM_one hB hBmeas hs)
    hw_pred (hw_cont.mono fun _ h ↦ h.mono (Icc_subset_Icc_right ht)) hw_bdd hw_pred hw_bdd
    fun _ _ ↦ (mul_one _).symm).congr_left fun n ↦ Eventually.of_forall fun ω ↦ ?_
  simp only [riemannσ, sub_sub_sub_cancel_right]

end ItoIntegralPredictable
end MathFin
