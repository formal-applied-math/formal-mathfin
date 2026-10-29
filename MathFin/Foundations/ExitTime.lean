/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralBrownian
public import MathFin.Foundations.ItoIntegralProcessLocalMartingaleGeneral

/-! # Exit times of a continuous process — the localization toolkit

The first genuine **localizing sequence** for the repo's Itô tower: the exit time of the closed
exterior `{x : N ≤ |x|}`,

  `exitTime N ω = inf {t : N ≤ |B_t ω|}`  (`⊤` if `|B|` never reaches `N`),

as a stopping time for the **raw** Brownian filtration — no right-continuity needed, because the
hit set `{x : N ≤ |x|}` is *closed* (so by continuity of paths the `sInf` is attained), making
`{exitTime N ≤ i}` the event `{∃ s ∈ [0,i], N ≤ |B_s|}`, which is the measurable rational
`⋂ₘ ⋃_{q ≤ i} {N − 1/(m+1) ≤ |B_q|}` (continuity again, using only times `q ≤ i`). The closed set
is essential: the open-exterior `{N < |x|}` route only characterizes `{exitTime < i}`, which lands
in `𝓕_{i⁺}` — the right-continuous filtration the Brownian natural filtration does not provide.

For continuous paths the exit times escape to infinity (each path is bounded on every compact
`[0,T]`), so `exitTime N ↑ ⊤` as `N → ∞` — a genuine `IsLocalizingSequence`. This is the gating
piece for the unrestricted-`C³` Itô formula (Summit C): it localizes the bounded-derivative
process formula to general `C³` `f`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open ItoIntegralL2 ItoIntegralBrownian ItoIntegralProcessLocalMartingaleGeneral
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- The exit time of the closed exterior `{x : N ≤ |x|}`: the first time `|B|` reaches `N`,
`⊤` if it never does. -/
noncomputable def exitTime (B : ℝ≥0 → Ω → ℝ) (N : ℕ) : Ω → WithTop ℝ≥0 :=
  hittingAfter B {x : ℝ | (N : ℝ) ≤ |x|} 0

/-- A rational time `Real.toNNReal q ≤ i` within `δ` of any `s ≤ i` (approaching from below, so the
constraint `≤ i` is automatic). The boundary case `s = 0` is handled by `q = 0`. -/
private lemma exists_rat_time_below {i s : ℝ≥0} (hsi : s ≤ i) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ, Real.toNNReal q ≤ i ∧ dist (Real.toNNReal q) s < δ := by
  rcases eq_or_lt_of_le (zero_le: (0 : ℝ≥0) ≤ s) with hs0 | hs0
  · refine ⟨0, ?_, ?_⟩
    · simp
    · rw [← hs0]; simpa using hδ
  · -- `0 < s`: pick a real rational `q` with `(s - δ) < toNNReal q < s`
    have hlt : Real.toNNReal ((s : ℝ) - δ) < s := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal']
      have : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
      rw [max_lt_iff]; exact ⟨by linarith, this⟩
    obtain ⟨q, _, haq, hqs⟩ := (NNReal.lt_iff_exists_rat_btwn _ _).mp hlt
    refine ⟨q, (le_of_lt hqs).trans hsi, ?_⟩
    rw [NNReal.dist_eq]
    have h1 : (Real.toNNReal q : ℝ) < (s : ℝ) := by exact_mod_cast hqs
    have h2 : (s : ℝ) - δ < (Real.toNNReal q : ℝ) := by
      have hc : ((Real.toNNReal ((s : ℝ) - δ) : ℝ≥0) : ℝ) < (Real.toNNReal q : ℝ) :=
        by exact_mod_cast haq
      rw [Real.coe_toNNReal'] at hc
      exact lt_of_le_of_lt (le_max_left _ _) hc
    rw [abs_of_nonpos (by linarith)]; linarith

/-- **The closed-set `≤` characterization** (continuity ⇒ the `sInf` is attained):
`exitTime N ω ≤ i ↔ ∃ s ∈ [0,i], N ≤ |B_s ω|`. -/
lemma exitTime_le_iff (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (N : ℕ) (i : ℝ≥0) (ω : Ω) :
    exitTime B N ω ≤ (i : WithTop ℝ≥0) ↔ ∃ s ∈ Set.Icc (0 : ℝ≥0) i, (N : ℝ) ≤ |B s ω| := by
  set A : Set ℝ≥0 := (fun s : ℝ≥0 ↦ B s ω) ⁻¹' {x : ℝ | (N : ℝ) ≤ |x|}
  have hAcl : IsClosed A :=
    (isClosed_le continuous_const continuous_abs).preimage (hBcont ω)
  constructor
  · intro h
    have hne : exitTime B N ω ≠ ⊤ := by
      intro htop; rw [htop] at h; exact absurd (top_le_iff.mp h) (WithTop.coe_ne_top)
    have hexists : ∃ j : ℝ≥0, (0 : ℝ≥0) ≤ j ∧ B j ω ∈ {x : ℝ | (N : ℝ) ≤ |x|} := by
      by_contra hcon
      apply hne
      rw [exitTime, hittingAfter_eq_top_iff]
      intro j hj hmem; exact hcon ⟨j, hj, hmem⟩
    have hAne : A.Nonempty := by obtain ⟨j, _, hj⟩ := hexists; exact ⟨j, hj⟩
    have hval : exitTime B N ω = ((sInf A : ℝ≥0) : WithTop ℝ≥0) := by
      rw [exitTime]
      simp only [hittingAfter_def]
      rw [if_pos hexists]
      congr 1
      apply le_antisymm
      · exact csInf_le_csInf (OrderBot.bddBelow _) hAne (fun x hx ↦ ⟨zero_le, hx⟩)
      · refine csInf_le_csInf (OrderBot.bddBelow _) ?_ (fun x hx ↦ hx.2)
        obtain ⟨j, hj⟩ := hexists; exact ⟨j, hj⟩
    have hmem : sInf A ∈ A := hAcl.csInf_mem hAne (OrderBot.bddBelow A)
    have hle : sInf A ≤ i := by
      have hcast : ((sInf A : ℝ≥0) : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0) := hval ▸ h
      exact_mod_cast hcast
    exact ⟨sInf A, ⟨zero_le, hle⟩, hmem⟩
  · rintro ⟨s, ⟨_, hsi⟩, hs⟩
    exact (hittingAfter_le_of_mem (zero_le) (show B s ω ∈ {x : ℝ | (N : ℝ) ≤ |x|} from hs)).trans
      (by exact_mod_cast hsi)

/-- The exit event `{∃ s ∈ [0,i], N ≤ |B_s|}` as the measurable rational `⋂ₘ ⋃_{q ≤ i}`. -/
lemma exists_le_abs_eq_iInter_iUnion
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (N : ℕ) (i : ℝ≥0) (ω : Ω) :
    (∃ s ∈ Set.Icc (0 : ℝ≥0) i, (N : ℝ) ≤ |B s ω|)
      ↔ ∀ m : ℕ, ∃ q : ℚ, Real.toNNReal q ≤ i
          ∧ (N : ℝ) - 1 / (m + 1) ≤ |B (Real.toNNReal q) ω| := by
  have hg : Continuous fun s : ℝ≥0 ↦ |B s ω| := continuous_abs.comp (hBcont ω)
  constructor
  · rintro ⟨s, ⟨_, hsi⟩, hs⟩ m
    have hpos : (0 : ℝ) < 1 / (m + 1) := by positivity
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hg.continuousAt (1 / (m + 1)) hpos
    obtain ⟨q, hq_le, hq_close⟩ := exists_rat_time_below hsi hδ
    refine ⟨q, hq_le, ?_⟩
    have hgc := hδc hq_close
    rw [Real.dist_eq] at hgc
    have h2 : |B (Real.toNNReal q) ω| > |B s ω| - 1 / (m + 1) := by
      have := abs_lt.mp hgc; linarith [this.1]
    linarith [hs]
  · intro h
    obtain ⟨s, hs_mem, hs_max⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr (zero_le)) hg.continuousOn
    refine ⟨s, hs_mem, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
    obtain ⟨q, hq_le, hq⟩ := h m
    have h1 : |B (Real.toNNReal q) ω| ≤ |B s ω| :=
      hs_max (Set.mem_Icc.mpr ⟨zero_le, hq_le⟩)
    linarith

/-- **The exit time of a continuous adapted process is a stopping time**, for any filtration: no
right-continuity, the hit set being closed, so `{exitTime N ≤ i}` is the rational `⋂ₘ ⋃_{q ≤ i}`
event. -/
theorem isStoppingTime_exitTime_of_measurable {𝓕 : Filtration ℝ≥0 mΩ}
    (hBmeas : ∀ t, Measurable[𝓕 t] (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    (N : ℕ) : IsStoppingTime 𝓕 (exitTime B N) := by
  intro i
  have hset : {ω | exitTime B N ω ≤ (i : WithTop ℝ≥0)}
      = ⋂ m : ℕ, ⋃ q : {q : ℚ // Real.toNNReal q ≤ i},
          {ω | (N : ℝ) - 1 / (m + 1) ≤ |B (Real.toNNReal (q : ℚ)) ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Subtype.exists, exists_prop]
    rw [exitTime_le_iff hBcont, exists_le_abs_eq_iInter_iUnion hBcont]
  rw [hset]
  refine MeasurableSet.iInter fun m ↦ MeasurableSet.iUnion fun q ↦ ?_
  exact measurableSet_le measurable_const
    ((continuous_abs.measurable.comp (hBmeas _)).mono (𝓕.mono q.2) le_rfl)

/-- **The exit time is a stopping time for the raw Brownian filtration.** -/
theorem isStoppingTime_exitTime (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (N : ℕ) :
    IsStoppingTime (ItoIntegralL2.natFiltration hBmeas) (exitTime B N) :=
  isStoppingTime_exitTime_of_measurable (measurable_eval_natFiltration hBmeas) hBcont N

/-- **The exit times increase with `N`** (the closed exterior shrinks, so the hit comes later or
never): `N ≤ M → exitTime N ω ≤ exitTime M ω`, pointwise in `ω`. -/
lemma exitTime_mono (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) {N M : ℕ} (hNM : N ≤ M)
    (ω : Ω) : exitTime B N ω ≤ exitTime B M ω := by
  rcases eq_or_ne (exitTime B M ω) ⊤ with h | h
  · rw [h]; exact le_top
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h
    rw [← ht, exitTime_le_iff hBcont]
    obtain ⟨s, hs_mem, hs⟩ := (exitTime_le_iff hBcont M t ω).mp ht.ge
    exact ⟨s, hs_mem, le_trans (by exact_mod_cast hNM) hs⟩

/-- `N ↦ exitTime N ω` is monotone, pointwise in `ω`. -/
lemma exitTime_monotone (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (ω : Ω) :
    Monotone fun N : ℕ ↦ exitTime B N ω :=
  fun _ _ hNM ↦ exitTime_mono hBcont hNM ω

/-- **The exit times escape to infinity.** A continuous path is bounded on every compact `[0,c]`, so
once `N` exceeds that bound the exterior is never reached before `c`; hence `exitTime N ω ↑ ⊤`. -/
lemma exitTime_tendsto_top (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (ω : Ω) :
    Tendsto (fun N : ℕ ↦ exitTime B N ω) atTop (𝓝 ⊤) := by
  rw [WithTop.tendsto_nhds_top_iff]
  intro c
  obtain ⟨s, _, hs_max⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (zero_le : (0 : ℝ≥0) ≤ c))
    (continuous_abs.comp (hBcont ω)).continuousOn
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt |B s ω|
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
  rw [← not_le, exitTime_le_iff hBcont]
  rintro ⟨u, hu_mem, hu⟩
  have h1 : |B u ω| ≤ |B s ω| := hs_max hu_mem
  have h2 : |B s ω| < (N : ℝ) := lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
  linarith

/-- **The exit times of a continuous adapted process form a localizing sequence**: each is a
stopping time (closed-set route, no right-continuity), the sequence is monotone, and it escapes to
`⊤` (continuous paths are bounded on compacts). -/
theorem isLocalizingSequence_exitTime_of_measurable {𝓕 : Filtration ℝ≥0 mΩ}
    (hBmeas : ∀ t, Measurable[𝓕 t] (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) :
    IsLocalizingSequence 𝓕 (fun N ↦ exitTime B N) μ where
  isStoppingTime := isStoppingTime_exitTime_of_measurable hBmeas hBcont
  tendsto_top := Filter.Eventually.of_forall (exitTime_tendsto_top hBcont)
  mono := Filter.Eventually.of_forall (exitTime_monotone hBcont)

/-- **The Brownian exit times form a localizing sequence** for the null-augmented filtration:
each `exitTime N` is a stopping time (closed-set route, no right-continuity), the sequence is
a.s. monotone, and it escapes to `⊤` a.s. (continuous paths are bounded on compacts). This is the
repo's first genuine `IsLocalizingSequence` — the localization engine that lifts the
bounded-derivative Itô formula to unbounded coefficients. -/
theorem isLocalizingSequence_exitTime (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) :
    IsLocalizingSequence (augFiltration (μ := μ) hBmeas) (fun N ↦ exitTime B N) μ :=
  isLocalizingSequence_exitTime_of_measurable (fun t ↦
    (measurable_eval_natFiltration hBmeas t).mono le_sup_left le_rfl) hBcont

/-- **The path stays confined up to the exit time.** On `{s ≤ τ_N}` with `0 < s`, `|B_s| ≤ N`:
for `u < s ≤ τ_N` the exit has not happened (`|B_u| < N`), and left-continuity carries the bound
to the boundary value at `s`. -/
lemma abs_le_N_of_le_exitTime (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {N : ℕ} {s : ℝ≥0} {ω : Ω} (hs0 : 0 < s)
    (h : (s : WithTop ℝ≥0) ≤ exitTime B N ω) : |B s ω| ≤ (N : ℝ) := by
  have hbelow : ∀ u : ℝ≥0, u < s → |B u ω| < (N : ℝ) := by
    intro u hu
    by_contra hN
    rw [not_lt] at hN
    have hle : exitTime B N ω ≤ (u : WithTop ℝ≥0) :=
      (exitTime_le_iff hBcont N u ω).mpr ⟨u, ⟨zero_le, le_refl u⟩, hN⟩
    exact absurd hle (not_le.mpr (lt_of_lt_of_le (by exact_mod_cast hu) h))
  have htend : Tendsto (fun u : ℝ≥0 ↦ |B u ω|) (𝓝[<] s) (𝓝 (|B s ω|)) :=
    (continuous_abs.comp (hBcont ω)).continuousWithinAt
  haveI : (𝓝[<] s).NeBot := nhdsWithin_Iio_neBot' ⟨0, hs0⟩ le_rfl
  exact le_of_tendsto htend
    (eventually_nhdsWithin_of_forall fun u hu ↦ le_of_lt (hbelow u hu))

/-- **Up to a positive exit time the path stays in `[−N, N]`**, the time `0` included: there the
exit has not yet happened. -/
lemma abs_le_of_le_exitTime (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {N : ℕ} {s : ℝ≥0} {ω : Ω} (hpos : ⊥ < exitTime B N ω)
    (h : (s : WithTop ℝ≥0) ≤ exitTime B N ω) : |B s ω| ≤ (N : ℝ) := by
  rcases (zero_le : 0 ≤ s).eq_or_lt with rfl | hs0
  · by_contra hN
    exact hpos.not_ge <| (exitTime_le_iff hBcont N 0 ω).mpr ⟨0, ⟨le_rfl, le_rfl⟩, (not_le.mp hN).le⟩
  · exact abs_le_N_of_le_exitTime hBcont hs0 h

/-- **A process that is a martingale up to a stopping time, stopped there, is a martingale.** If
the adapted right-continuous `X` is almost surely the right-continuous martingale `M` on the
stochastic interval `[0, τ]` (when `τ > 0`), then `X` stopped at `τ` (and zeroed on `{τ = 0}`) is,
at each time, almost surely `M` stopped the same way, a martingale
(`Martingale.stoppedProcess_indicator`), and it is adapted
(`StronglyAdapted.stoppedProcess_indicator`). -/
theorem martingale_stoppedProcess_of_ae_eq [IsFiniteMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) (hB : StronglyAdapted 𝓕 B)
    (hBc : ∀ ω, IsRightContinuous fun t ↦ B t ω) {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 μ)
    (hMc : ∀ ω, IsRightContinuous fun t ↦ M t ω)
    (hBM : ∀ᵐ ω ∂μ, ⊥ < τ ω → ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ τ ω → B u ω = M u ω) :
    Martingale (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (B i)) τ) 𝓕 μ := by
  have hstop (i : ℝ≥0) :
      (fun ω ↦ stoppedProcess (fun j ↦ {ω | ⊥ < τ ω}.indicator (B j)) τ i ω)
        =ᵐ[μ] fun ω ↦ stoppedProcess (fun j ↦ {ω | ⊥ < τ ω}.indicator (M j)) τ i ω := by
    filter_upwards [hBM] with ω hω
    by_cases hpos : ⊥ < τ ω
    · have hmem : ω ∈ {ω | ⊥ < τ ω} := hpos
      rcases le_total (i : WithTop ℝ≥0) (τ ω) with hle | hge
      · rw [stoppedProcess_eq_of_le hle, stoppedProcess_eq_of_le hle,
          Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        exact hω hpos i hle
      · rw [stoppedProcess_eq_of_ge hge, stoppedProcess_eq_of_ge hge,
          Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hge)
        refine hω hpos (τ ω).untopA (le_of_eq ?_)
        rw [← hv]; rfl
    · have hnmem : ω ∉ {ω | ⊥ < τ ω} := hpos
      have hle : τ ω ≤ (i : WithTop ℝ≥0) := (not_lt.mp hpos).trans bot_le
      rw [stoppedProcess_eq_of_ge hle, stoppedProcess_eq_of_ge hle,
        Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hnmem]
  refine ⟨hB.stoppedProcess_indicator hBc hτ, fun i j hij ↦ ?_⟩
  exact (condExp_congr_ae (hstop j)).trans <|
    ((hM.stoppedProcess_indicator hMc hτ).2 i j hij).trans (hstop i).symm

end MathFin
