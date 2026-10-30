/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralLocalisedLocalMartingale
public import MathFin.Foundations.ItoIntegralPredictableRiemann

/-! # The Itô integral of a predictable integrand with almost surely continuous paths

`localItoIntegral` (`ItoIntegralLocalised`) is `∫ σ dB` for an adapted `σ` with every path
continuous. A continuous function of an Itô process, such as the integrand `f_x(s, X_s) σ_s` of
Itô's formula, is predictable but continuous only almost surely: the continuous version of the
Itô integral is continuous off a null set. This file builds `∫ σ dB` on `[0, T]` for `σ`
predictable for the natural filtration of `B`, with paths continuous on `[0, T]` almost surely,
and not necessarily bounded.

The construction is that of `localItoIntegral`. The integrand clipped to `[−N, N]` is bounded and
predictable, so it has a continuous Itô integral `M^N` (`clipPredMod`); its Riemann sums converge
to it (`tendstoInMeasure_riemannσ_of_predictable`), so `M^n` and `M^N` agree almost surely up to
each time where `σ` stays in `[−n, n]`. At time `t` the integral reads `M^N_t` at the least
integer `N` bounding the path of `σ` on a countable dense subset of `[0, t]` (`denseLevel`). On a
continuous path that is the bound on `[0, t]`; on every path it is `𝓕_t`-measurable, so the
integral is adapted.

* `tendstoInMeasure_riemannσ_predItoIntegral`: for `t ≤ T` the Riemann sums of `σ` on `[0, t]`
  converge in probability to `predItoIntegral t`.
* `stronglyAdapted_predItoIntegral`, `ae_continuousOn_predItoIntegral`: it is adapted to the
  natural filtration, and almost every path is continuous on `[0, T]`.
* `ae_predItoIntegral_congr`: integrands that are almost surely the same path on `[0, T]` have
  integrals that are almost surely the same path on `[0, T]`.
* `ae_predItoIntegral_eq_localItoIntegral`: for `σ` adapted with every path continuous it is
  `localItoIntegral`, up to indistinguishability on `[0, T]`.
* `tendstoInMeasure_riemannStieltjes_localItoIntegral`: for `M = localItoIntegral σ` and `w`
  predictable with almost surely continuous paths, the Riemann–Stieltjes sums of `w` against `M`
  on `[0, t]` converge in probability to `predItoIntegral (w σ) t`: `∫ w dM = ∫ w σ dB`.
* `exists_continuous_localMartingale_predItoIntegral`: it has a version with every path
  continuous that is a local martingale for the null-augmented Brownian filtration; the proof
  localises by the exit times of a version of `σ` with every path continuous.

Not here: integrands with paths not almost surely continuous, the local martingale for the
unaugmented natural filtration, and `T = ∞`.
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

/-! ### The level of a path on a countable dense set -/

/-- A countable dense subset of `[0, t]`. -/
noncomputable def denseIcc (t : ℝ≥0) : Set ℝ≥0 := (exists_countable_dense_Icc t).choose

theorem denseIcc_subset (t : ℝ≥0) : denseIcc t ⊆ Icc 0 t :=
  (exists_countable_dense_Icc t).choose_spec.1

theorem countable_denseIcc (t : ℝ≥0) : (denseIcc t).Countable :=
  (exists_countable_dense_Icc t).choose_spec.2.1

theorem Icc_subset_closure_denseIcc (t : ℝ≥0) : Icc 0 t ⊆ closure (denseIcc t) :=
  (exists_countable_dense_Icc t).choose_spec.2.2

/-- The least integer bounding the path `x` on the countable dense set `denseIcc t`; `0` when
there is none. On a path continuous on `[0, t]` it is the least integer bounding it on `[0, t]`. -/
noncomputable def denseLevel (t : ℝ≥0) (x : ℝ≥0 → ℝ) : ℕ :=
  sInf {N : ℕ | ∀ s ∈ denseIcc t, |x s| ≤ N}

/-- A path continuous on `[0, t]` is bounded there by its level. -/
theorem abs_le_denseLevel {t : ℝ≥0} {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 t)) :
    ∀ s ∈ Icc 0 t, |x s| ≤ denseLevel t x := by
  obtain ⟨N, hN⟩ := exists_nat_abs_le_Icc hx
  exact fun s hs ↦ abs_le_of_dense (denseIcc_subset t) (Icc_subset_closure_denseIcc t) hx
    (Nat.sInf_mem (s := {N : ℕ | ∀ s ∈ denseIcc t, |x s| ≤ N})
      ⟨N, fun s hs ↦ hN s (denseIcc_subset t hs)⟩) hs

theorem denseLevel_le {t : ℝ≥0} {x : ℝ≥0 → ℝ} {N : ℕ} (h : ∀ s ∈ Icc 0 t, |x s| ≤ N) :
    denseLevel t x ≤ N :=
  Nat.sInf_le fun s hs ↦ h s (denseIcc_subset t hs)

/-- The level of a process is measurable when the process is, on `[0, t]`: it reads the process
at countably many times. -/
theorem measurable_denseLevel {Ω : Type*} {mΩ : MeasurableSpace Ω} {t : ℝ≥0}
    {X : ℝ≥0 → Ω → ℝ} (hXm : ∀ s ∈ Icc 0 t, Measurable (X s)) :
    Measurable fun ω ↦ denseLevel t fun s ↦ X s ω := by
  have hE (M : ℕ) : MeasurableSet {ω | ∀ s ∈ denseIcc t, |X s ω| ≤ M} :=
    measurableSet_forall_abs_le_of_countable (countable_denseIcc t)
      (fun s hs ↦ hXm s (denseIcc_subset t hs)) M
  have key (ω : Ω) (N : ℕ) : (denseLevel t fun s ↦ X s ω) ≤ N
      ↔ ω ∈ {ω | ∀ s ∈ denseIcc t, |X s ω| ≤ N}
        ∨ ∀ M : ℕ, ω ∉ {ω | ∀ s ∈ denseIcc t, |X s ω| ≤ M} := by
    by_cases hS : ∃ M : ℕ, ∀ s ∈ denseIcc t, |X s ω| ≤ M
    · refine ⟨fun h ↦ Or.inl fun s hs ↦ (Nat.sInf_mem hS s hs).trans (Nat.cast_le.2 h), ?_⟩
      rintro (h | h)
      · exact Nat.sInf_le h
      · exact absurd hS fun ⟨M, hM⟩ ↦ h M hM
    · have h0 : (denseLevel t fun s ↦ X s ω) = 0 :=
        Nat.sInf_eq_zero.2 (Or.inr (eq_empty_of_forall_notMem fun M hM ↦ hS ⟨M, hM⟩))
      exact ⟨fun _ ↦ Or.inr fun M hM ↦ hS ⟨M, hM⟩, fun _ ↦ h0 ▸ Nat.zero_le N⟩
  refine measurable_of_Iic fun N ↦ ?_
  have hset : (fun ω ↦ denseLevel t fun s ↦ X s ω) ⁻¹' Iic N
      = {ω | ∀ s ∈ denseIcc t, |X s ω| ≤ N} ∪ ⋂ M : ℕ, {ω | ∀ s ∈ denseIcc t, |X s ω| ≤ M}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_union, mem_iInter, mem_compl_iff]
    exact key ω N
  rw [hset]
  exact (hE N).union (MeasurableSet.iInter fun M ↦ (hE M).compl)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) {σ : ℝ≥0 → Ω → ℝ}
  (hpred : IsStronglyPredictable (natFiltration hBmeas) σ)
  (hσc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ σ t ω) (Icc 0 T))

omit [IsProbabilityMeasure μ] in
include hpred in
theorem clip_isStronglyPredictable (N : ℕ) :
    IsStronglyPredictable (natFiltration hBmeas) (clip N σ) :=
  (continuous_clampM N).comp_stronglyMeasurable hpred

/-! ### The clipped integrals -/

/-- The continuous Itô integral of the predictable integrand clipped to `[−N, N]`. -/
noncomputable def clipPredMod (N : ℕ) : ℝ≥0 → Ω → ℝ :=
  itoContinuousMod T hBmeas (processToLpPredictable (μ := μ) T hBmeas
    (clip_isStronglyPredictable hBmeas hpred N) (abs_clip_le N σ))

include hB hBcont hσc in
/-- The Riemann sums of the clipped integrand on `[0, t]` converge to its continuous Itô
integral at `t`. -/
theorem tendstoInMeasure_riemannσ_clipPredMod (N : ℕ) {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ↦ riemannσ (B := B) (clip N σ) t n) atTop
      (clipPredMod (μ := μ) T hBmeas hpred N t) :=
  tendstoInMeasure_riemannσ_of_predictable hB T hBmeas hBcont
    (clip_isStronglyPredictable hBmeas hpred N)
    (hσc.mono fun _ h ↦ (continuous_clampM N).comp_continuousOn h) (abs_clip_le N σ) ht

include hB hBcont hσc in
/-- **The clipped integrals agree where the clipping is inactive.** For `n ≤ N`, almost surely,
`M^n_t = M^N_t` at every `t ≤ T` up to which `σ` stays in `[−n, n]`. -/
theorem ae_clipPredMod_eq {n N : ℕ} (hnN : n ≤ N) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, |σ s ω| ≤ n) →
      clipPredMod (μ := μ) T hBmeas hpred n t ω = clipPredMod (μ := μ) T hBmeas hpred N t ω := by
  refine ae_forall_eq_of_continuousOn_of_antitone
    (A := fun t ↦ {ω | ∀ s ∈ Icc 0 t, |σ s ω| ≤ n})
    (itoContinuousMod_continuousOn hB T hBmeas hBcont _)
    (itoContinuousMod_continuousOn hB T hBmeas hBcont _)
    (fun _ _ hst _ h s hs ↦ h s ⟨hs.1, hs.2.trans hst⟩) fun t ht ↦ ?_
  refine ae_eq_of_tendstoInMeasure_of_eqOn (A := {ω | ∀ s ∈ Icc 0 t, |σ s ω| ≤ n})
    (tendstoInMeasure_riemannσ_clipPredMod hB T hBmeas hBcont hpred hσc n ht.2)
    (tendstoInMeasure_riemannσ_clipPredMod hB T hBmeas hBcont hpred hσc N ht.2) fun m ω hω ↦ ?_
  refine riemannσ_congr (fun s hs ↦ ?_) m
  have hs' := hω s ⟨zero_le, hs.2⟩
  rw [clip_eq_self hs', clip_eq_self (hs'.trans (Nat.cast_le.2 hnN))]

/-! ### The integral -/

/-- **The Itô integral of a predictable integrand**, possibly unbounded, meant for paths
continuous on `[0, T]` almost surely: at time `t`, on each path, the continuous Itô integral of
`σ` clipped at the least integer bounding that path on a countable dense subset of `[0, t]`. It is
the integral on `[0, T]` only; past `T` its value carries no meaning. -/
noncomputable def predItoIntegral (t : ℝ≥0) (ω : Ω) : ℝ :=
  clipPredMod (μ := μ) T hBmeas hpred (denseLevel t fun s ↦ σ s ω) t ω

include hB hBcont hσc in
/-- Almost surely, at every `t ≤ T` up to which `σ` stays in `[−N, N]`, the integral is `M^N_t`. -/
theorem ae_predItoIntegral_eq :
    ∀ᵐ ω ∂μ, ∀ N : ℕ, ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, |σ s ω| ≤ N) →
      predItoIntegral (μ := μ) T hBmeas hpred t ω = clipPredMod (μ := μ) T hBmeas hpred N t ω := by
  filter_upwards [ae_all_iff.2 fun n ↦ ae_all_iff.2 fun k ↦
    ae_clipPredMod_eq hB T hBmeas hBcont hpred hσc (Nat.le_add_right n k), hσc]
    with ω hω hc N t ht hN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (denseLevel_le hN)
  exact hω _ k t ht (abs_le_denseLevel (hc.mono (Icc_subset_Icc_right ht.2)))

include hB hBcont in
/-- **The integral is adapted**: the level at `t` reads `σ` at countably many times of `[0, t]`
(`measurable_denseLevel`), and each clipped integral is predictable
(`itoContinuousMod_isStronglyPredictable`). -/
theorem stronglyAdapted_predItoIntegral :
    StronglyAdapted (natFiltration hBmeas) (predItoIntegral (μ := μ) T hBmeas hpred) :=
  fun t ↦ (measurable_apply_countable
    (f := fun N ↦ clipPredMod (μ := μ) T hBmeas hpred N t)
    (fun _ ↦ ((itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont _).stronglyAdapted
      t).measurable)
    (measurable_denseLevel fun s hs ↦ ((hpred.stronglyAdapted s).mono
      ((natFiltration hBmeas).mono hs.2)).measurable)).stronglyMeasurable

include hB hBcont hσc in
/-- **Almost every path of the integral is continuous on `[0, T]`.** -/
theorem ae_continuousOn_predItoIntegral :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ predItoIntegral (μ := μ) T hBmeas hpred t ω) (Icc 0 T) := by
  filter_upwards [ae_predItoIntegral_eq hB T hBmeas hBcont hpred hσc, hσc,
    ae_all_iff.2 fun N ↦ itoContinuousMod_continuousOn hB T hBmeas hBcont
      (processToLpPredictable (μ := μ) T hBmeas (clip_isStronglyPredictable hBmeas hpred N)
        (abs_clip_le N σ))] with ω hω hc hM
  exact (hM (denseLevel T fun s ↦ σ s ω)).congr fun t ht ↦
    hω _ t ht fun s hs ↦ abs_le_denseLevel hc s ⟨hs.1, hs.2.trans ht.2⟩

include hB hBcont hσc in
/-- **The integral is the limit in probability of its Riemann sums.** For `t ≤ T` the left-point
sums `∑ σ(tₖ)(B_{tₖ₊₁} − B_{tₖ})` on the uniform partitions of `[0, t]` converge in probability to
`predItoIntegral t`: on the event that `σ` stays in `[−N, N]` up to `t` they are the sums of the
clipped integrand, and the events exhaust `Ω` in probability (`tendsto_measure_compl_abs_le`). -/
theorem tendstoInMeasure_riemannσ_predItoIntegral {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ↦ riemannσ (B := B) σ t n) atTop
      (predItoIntegral (μ := μ) T hBmeas hpred t) := by
  refine tendstoInMeasure_of_eqOn (A := fun N : ℕ ↦ {ω | ∀ s ∈ Icc 0 t, |σ s ω| ≤ N})
    (tendsto_measure_compl_abs_le
      (fun s ↦ ((hpred.stronglyAdapted s).mono ((natFiltration hBmeas).le s)).measurable)
      (hσc.mono fun _ h ↦ h.mono (Icc_subset_Icc_right ht)))
    (fun N ↦ tendstoInMeasure_riemannσ_clipPredMod hB T hBmeas hBcont hpred hσc N ht)
    (fun N m ω hω ↦ riemannσ_congr (fun s hs ↦ (clip_eq_self (hω s ⟨zero_le, hs.2⟩)).symm) m)
    fun N ↦ ?_
  filter_upwards [ae_predItoIntegral_eq hB T hBmeas hBcont hpred hσc] with ω hω hN
    using hω N t ⟨zero_le, ht⟩ hN

include hB hBcont hσc in
/-- **Indistinguishable integrands have indistinguishable integrals.** If `σ` and `σ'` are almost
surely the same path on `[0, T]`, so are their integrals: at each time both are limits in
probability of Riemann sums that agree almost surely. -/
theorem ae_predItoIntegral_congr {σ' : ℝ≥0 → Ω → ℝ}
    (hpred' : IsStronglyPredictable (natFiltration hBmeas) σ')
    (hσc' : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ σ' t ω) (Icc 0 T))
    (h : ∀ᵐ ω ∂μ, ∀ s ∈ Icc 0 T, σ s ω = σ' s ω) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, predItoIntegral (μ := μ) T hBmeas hpred t ω
      = predItoIntegral (μ := μ) T hBmeas hpred' t ω :=
  ae_forall_eq_of_tendstoInMeasure (ae_continuousOn_predItoIntegral hB T hBmeas hBcont hpred hσc)
    (ae_continuousOn_predItoIntegral hB T hBmeas hBcont hpred' hσc')
    (fun _ ht ↦ tendstoInMeasure_riemannσ_predItoIntegral hB T hBmeas hBcont hpred hσc ht.2)
    fun t ht ↦ (tendstoInMeasure_riemannσ_predItoIntegral hB T hBmeas hBcont hpred' hσc'
      ht.2).congr_left fun n ↦ by
        filter_upwards [h] with ω hω
        exact riemannσ_congr (fun s hs ↦ (hω s ⟨hs.1, hs.2.trans ht.2⟩).symm) n

include hB hBcont in
/-- **For an adapted integrand with every path continuous it is `localItoIntegral`**, up to
indistinguishability on `[0, T]`: both are limits in probability of the same Riemann sums. -/
theorem ae_predItoIntegral_eq_localItoIntegral
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) :
    ∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, predItoIntegral (μ := μ) T hBmeas
        (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont) t ω
      = localItoIntegral (μ := μ) T hBmeas hadap hcont t ω :=
  ae_forall_eq_of_tendstoInMeasure
    (ae_continuousOn_predItoIntegral hB T hBmeas hBcont _
      (.of_forall fun ω ↦ (hcont ω).continuousOn))
    (ae_continuousOn_localItoIntegral hB T hBmeas hBcont hadap hcont)
    (fun _ ht ↦ tendstoInMeasure_riemannσ_predItoIntegral hB T hBmeas hBcont _
      (.of_forall fun ω ↦ (hcont ω).continuousOn) ht.2)
    fun _ ht ↦ tendstoInMeasure_riemannσ_localItoIntegral hB T hBmeas hBcont hadap hcont ht.2

/-! ### Integrals against the integral -/

include hB hBcont in
/-- **Riemann–Stieltjes sums against `∫ σ dB` converge to `∫ w σ dB`.** Let `σ` be adapted with
every path continuous, `M = localItoIntegral σ`, and `w` predictable with paths almost surely
continuous on `[0, T]`, neither bounded. For `t ≤ T` the sums `∑ w(tₖ)(M_{tₖ₊₁} − M_{tₖ})` on the
uniform partitions of `[0, t]` converge in probability to `predItoIntegral (w σ) t`. On the event
that `σ` and `w` stay in `[−N, N]` on `[0, T]` the sums are those of `clip N w` against the
integral of `clip N σ`, which converge to the `L²` integral of `clip N w · clip N σ`
(`tendstoInMeasure_riemannStieltjes_itoContinuousMod`), and there that integral and the integral
of `w σ` are limits of the same Riemann sums. The events exhaust `Ω` in probability. -/
theorem tendstoInMeasure_riemannStieltjes_localItoIntegral
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {w : ℝ≥0 → Ω → ℝ}
    (hw_pred : IsStronglyPredictable (natFiltration hBmeas) w)
    (hw_cont : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Icc 0 T)) {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ Finset.range n, w (unifPart t n k) ω
        * (localItoIntegral (μ := μ) T hBmeas hadap hcont (unifPart t n (k + 1)) ω
          - localItoIntegral (μ := μ) T hBmeas hadap hcont (unifPart t n k) ω)) atTop
      (predItoIntegral (μ := μ) T hBmeas
        (hw_pred.mul (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont)) t) := by
  have hσp := isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont
  have hθ : IsStronglyPredictable (natFiltration hBmeas) fun s ω ↦ w s ω * σ s ω := hw_pred.mul hσp
  have hθc : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω * σ s ω) (Icc 0 T) :=
    hw_cont.mono fun ω h ↦ h.mul (hcont ω).continuousOn
  have hθN (N : ℕ) : IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ clip N w s ω * clip N σ s ω :=
    (clip_isStronglyPredictable hBmeas hw_pred N).mul (clip_isStronglyPredictable hBmeas hσp N)
  have hθNb (N : ℕ) (s : ℝ≥0) (ω : Ω) : |clip N w s ω * clip N σ s ω| ≤ N * N := by
    rw [abs_mul]
    exact mul_le_mul (abs_clip_le N w s ω) (abs_clip_le N σ s ω) (abs_nonneg _) (Nat.cast_nonneg N)
  have hwNc (N : ℕ) : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ clip N w s ω) (Icc 0 T) :=
    hw_cont.mono fun _ h ↦ (continuous_clampM N).comp_continuousOn h
  have hAσ := tendsto_measure_compl_abs_le_of_stronglyAdapted (μ := μ) (T := T) hadap hcont
  have hAw := tendsto_measure_compl_abs_le (μ := μ)
    (fun s ↦ ((hw_pred.stronglyAdapted s).mono ((natFiltration hBmeas).le s)).measurable) hw_cont
  refine tendstoInMeasure_of_ae_eqOn
    (A := fun N : ℕ ↦ {ω | ∀ s ∈ Icc 0 T, |σ s ω| ≤ N} ∩ {ω | ∀ s ∈ Icc 0 T, |w s ω| ≤ N})
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hAσ.add hAw)
      (fun _ ↦ bot_le) fun N ↦ (measure_mono (compl_inter _ _).le).trans (measure_union_le _ _))
    (fun N ↦ tendstoInMeasure_riemannStieltjes_itoContinuousMod hB T hBmeas hBcont
      (clip_adapted hadap N) (clip_continuous hcont N) (abs_clip_le N σ) ht
      (M := clipItoMod (μ := μ) T hBmeas hadap hcont N)
      (fun s hs ↦ (itoContinuousMod_modification hB T hBmeas hBcont _ (hs.trans ht)).trans
        (by rw [itoProcessCLM_consist hB hBmeas hs ht]))
      (clip_isStronglyPredictable hBmeas hw_pred N)
      ((hwNc N).mono fun _ h ↦ h.mono (Icc_subset_Icc_right ht)) (abs_clip_le N w) (hθN N)
      (hθNb N) fun _ _ ↦ rfl) (fun N n ↦ ?_) fun N ↦ ?_
  · filter_upwards [ae_localItoIntegral_eq hB T hBmeas hBcont hadap hcont] with ω hM hω
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.1 hk
    have h1 : unifPart t n k ∈ Icc 0 T := ⟨zero_le, (unifPart_le_T hk'.le).trans ht⟩
    have h2 : unifPart t n (k + 1) ∈ Icc 0 T := ⟨zero_le, (unifPart_le_T hk').trans ht⟩
    rw [hM N _ h1 fun r hr ↦ hω.1 r ⟨hr.1, hr.2.trans h1.2⟩,
      hM N _ h2 fun r hr ↦ hω.1 r ⟨hr.1, hr.2.trans h2.2⟩, clip_eq_self (hω.2 _ h1)]
  · have hloc := ae_eq_of_tendstoInMeasure_of_eqOn
      (A := {ω | ∀ s ∈ Icc 0 T, |σ s ω| ≤ N} ∩ {ω | ∀ s ∈ Icc 0 T, |w s ω| ≤ N})
      (tendstoInMeasure_riemannσ_clipPredMod hB T hBmeas hBcont hθ hθc (N * N) ht)
      (tendstoInMeasure_riemannσ_of_predictable hB T hBmeas hBcont (hθN N)
        ((hwNc N).mono fun ω h ↦ h.mul (clip_continuous hcont N ω).continuousOn) (hθNb N) ht)
      fun m ω hω ↦ riemannσ_congr (fun s hs ↦ ?_) m
    · filter_upwards [ae_predItoIntegral_eq hB T hBmeas hBcont hθ hθc, hloc] with ω h1 h2 hω
      rw [h1 (N * N) t ⟨zero_le, ht⟩ fun s hs ↦ ?_, h2 hω]
      have hs' : s ∈ Icc 0 T := ⟨zero_le, hs.2.trans ht⟩
      rw [abs_mul, Nat.cast_mul]
      exact mul_le_mul (hω.2 s hs') (hω.1 s hs') (abs_nonneg _) (Nat.cast_nonneg N)
    · have hs' : s ∈ Icc 0 T := ⟨zero_le, hs.2.trans ht⟩
      have hb : |w s ω * σ s ω| ≤ ((N * N : ℕ) : ℝ) := by
        rw [abs_mul, Nat.cast_mul]
        exact mul_le_mul (hω.2 s hs') (hω.1 s hs') (abs_nonneg _) (Nat.cast_nonneg N)
      simp only [clip, clampM_eq_self hb, clampM_eq_self (hω.2 s hs'), clampM_eq_self (hω.1 s hs')]

/-! ### The local martingale -/

include hB hBcont hσc in
/-- **The Itô integral of a predictable integrand with almost surely continuous paths is a
continuous local martingale.** There is a process `X`, almost surely equal to `predItoIntegral` at
every `t ≤ T`, with every path continuous, that is a local martingale for the null-augmented
Brownian filtration. The proof zeroes off a co-null set `G` of the null σ-algebra, on which `σ`
and every clipped integral `M^N` are continuous on `[0, T]` and the integral is `M^N` up to each
time where `σ` stays in `[−N, N]`. The version `σ' = 𝟙_G σ(· ∧ T)` of `σ` has every path
continuous and is adapted to the augmentation, so its exit times `exitTime σ' N` localise; up to
them the integral, frozen at `T` and zeroed off `G`, is `M^N` frozen and zeroed the same way, a
martingale (`martingale_itoLocalMod`). -/
theorem exists_continuous_localMartingale_predItoIntegral :
    ∃ X : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂μ, ∀ t ∈ Icc 0 T, X t ω = predItoIntegral (μ := μ) T hBmeas hpred t ω) ∧
      (∀ ω, Continuous fun t ↦ X t ω) ∧
      IsLocalMartingale X (augFiltration (μ := μ) hBmeas) μ := by
  obtain ⟨G, hG, hGc, hGgood⟩ := exists_nullsAlg_of_ae (μ := μ)
    (p := fun ω ↦ ContinuousOn (fun t ↦ σ t ω) (Icc 0 T)
      ∧ (∀ N, ContinuousOn (fun t ↦ clipPredMod (μ := μ) T hBmeas hpred N t ω) (Icc 0 T))
      ∧ ContinuousOn (fun t ↦ predItoIntegral (μ := μ) T hBmeas hpred t ω) (Icc 0 T)
      ∧ ∀ N : ℕ, ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, |σ s ω| ≤ N) →
        predItoIntegral (μ := μ) T hBmeas hpred t ω
          = clipPredMod (μ := μ) T hBmeas hpred N t ω) <| by
    filter_upwards [hσc, ae_all_iff.2 fun N ↦ itoContinuousMod_continuousOn hB T hBmeas hBcont
        (processToLpPredictable (μ := μ) T hBmeas (clip_isStronglyPredictable hBmeas hpred N)
          (abs_clip_le N σ)),
      ae_continuousOn_predItoIntegral hB T hBmeas hBcont hpred hσc,
      ae_predItoIntegral_eq hB T hBmeas hBcont hpred hσc] with ω h0 h1 h2 h3
      using ⟨h0, h1, h2, h3⟩
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := by rw [ae_iff]; exact hGc
  have hGaug (i : ℝ≥0) : MeasurableSet[augFiltration (μ := μ) hBmeas i] G :=
    le_sup_right (b := nullsAlg mΩ μ) _ hG
  set X : ℝ≥0 → Ω → ℝ := fun t ↦ G.indicator (predItoIntegral (μ := μ) T hBmeas hpred (min t T))
  set σ' : ℝ≥0 → Ω → ℝ := fun t ↦ G.indicator (σ (min t T))
  have hXc : ∀ ω, Continuous fun t ↦ X t ω :=
    continuous_indicator_min fun ω hω ↦ (hGgood ω hω).2.2.1
  have hσ'c : ∀ ω, Continuous fun t ↦ σ' t ω := continuous_indicator_min fun ω hω ↦ (hGgood ω hω).1
  have hτ : IsLocalizingSequence (augFiltration (μ := μ) hBmeas) (fun N ↦ exitTime σ' N) μ :=
    isLocalizingSequence_exitTime_of_measurable (fun t ↦
      (((hpred.stronglyAdapted (min t T)).mono (((natFiltration hBmeas).mono
        (min_le_left t T)).trans le_sup_left)).measurable).indicator (hGaug t)) hσ'c
  have hmart (N : ℕ) : Martingale
      (stoppedProcess (fun i ↦ {ω | ⊥ < exitTime σ' N ω}.indicator (X i)) (exitTime σ' N))
      (augFiltration (μ := μ) hBmeas) μ := by
    refine martingale_stoppedProcess_of_ae_eq (hτ.isStoppingTime N) (fun i ↦
      ((stronglyAdapted_predItoIntegral hB T hBmeas hBcont hpred (min i T)).mono
        (((natFiltration hBmeas).mono (min_le_left i T)).trans le_sup_left)).indicator (hGaug i))
      (fun ω ↦ (hXc ω).isCadlag.right_continuous)
      (martingale_itoLocalMod hB T hBmeas hBcont hG hGc (processToLpPredictable (μ := μ) T hBmeas
        (clip_isStronglyPredictable hBmeas hpred N) (abs_clip_le N σ)))
      (fun ω ↦ (continuous_indicator_min (fun ω hω ↦ (hGgood ω hω).2.1 N) ω).isCadlag
        |>.right_continuous) ?_
    filter_upwards [hGae] with ω hω hpos u hu
    simp only [X, itoLocalMod, Set.indicator_of_mem hω]
    refine (hGgood ω hω).2.2.2 N _ ⟨zero_le, min_le_right u T⟩ fun s hs ↦ ?_
    have h := abs_le_of_le_exitTime hσ'c hpos
      ((WithTop.coe_le_coe.2 (hs.2.trans (min_le_left u T))).trans hu)
    simpa only [σ', Set.indicator_of_mem hω, min_eq_left (hs.2.trans (min_le_right u T))] using h
  refine ⟨X, ?_, hXc, ⟨_, hτ, fun N ↦ ⟨hmart N,
    isStable_isCadlag X (fun ω ↦ (hXc ω).isCadlag) _ (hτ.isStoppingTime N)⟩⟩⟩
  filter_upwards [hGae] with ω hω t ht
  simp only [X, Set.indicator_of_mem hω, min_eq_left ht.2]

end ItoIntegralLocalised
end MathFin
