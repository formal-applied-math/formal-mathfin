/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-! # Localisation in the sample space

A statement about a process with continuous paths is often proved first on the event that the
path stays in `[−N, N]` up to `T`, where the process may be replaced by a bounded one, and then
on all of `Ω`. This file collects what that needs, without stopping times.

* **Convergence in measure is local** (`tendstoInMeasure_of_ae_eqOn`, `tendstoInMeasure_of_eqOn`):
  if, on each of a sequence of events whose complements have measure tending to `0`, the sequence
  agrees with one converging in measure, and the limit agrees with the other limit, the sequence
  converges in measure. The events need not be measurable.
* **Limits in measure are local** (`ae_eq_of_tendstoInMeasure_of_eqOn`): two sequences converging
  in measure that agree on an event have limits that agree almost everywhere on it. This is
  Mathlib's `tendstoInMeasure_ae_unique` on an event.
* **Continuous paths stay bounded** (`tendsto_measure_compl_abs_le`): the events "the path stays
  in `[−N, N]` up to `T`" exhaust `Ω` in probability.
* **Continuous paths that agree at each time agree as paths** (`ae_forall_eq_of_continuousOn`),
  on `[0, T]` and on an event: the analogue, for a closed interval, of Degenne's
  `indistinguishable_of_modification_on`, which is stated on an open set.
-/

@[expose] public section

namespace MathFin
namespace LocalisationInMeasure

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-! ### Limits in measure are local -/

/-- **Convergence in measure is local.** If on each of a sequence of events `A N`, whose
complements have measure tending to `0`, the sequence `g` agrees almost everywhere with a
sequence `G N` that converges in measure to `H N`, and `h` agrees with `H N` almost everywhere on
`A N`, then `g` converges in measure to `h`. The events need not be measurable. -/
theorem tendstoInMeasure_of_ae_eqOn {Ω E : Type*} [MeasurableSpace Ω] [EDist E] {μ : Measure Ω}
    {g : ℕ → Ω → E} {h : Ω → E} {A : ℕ → Set Ω} (hA : Tendsto (fun N ↦ μ (A N)ᶜ) atTop (𝓝 0))
    {G : ℕ → ℕ → Ω → E} {H : ℕ → Ω → E} (hGH : ∀ N, TendstoInMeasure μ (G N) atTop (H N))
    (hg : ∀ N n, ∀ᵐ ω ∂μ, ω ∈ A N → g n ω = G N n ω)
    (hh : ∀ N, ∀ᵐ ω ∂μ, ω ∈ A N → h ω = H N ω) :
    TendstoInMeasure μ g atTop h := by
  intro ε hε
  refine ENNReal.tendsto_atTop_zero.2 fun δ hδ ↦ ?_
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 hA (δ / 2) (ENNReal.half_pos hδ.ne')
  obtain ⟨n₀, hn₀⟩ := ENNReal.tendsto_atTop_zero.1 (hGH N ε hε) (δ / 2) (ENNReal.half_pos hδ.ne')
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have hgh : ∀ᵐ ω ∂μ, ω ∈ A N → g n ω = G N n ω ∧ h ω = H N ω :=
    ((hg N n).and (hh N)).mono fun ω hp hω ↦ ⟨hp.1 hω, hp.2 hω⟩
  calc μ {ω | ε ≤ edist (g n ω) (h ω)}
      ≤ μ ((A N)ᶜ ∪ {ω | ε ≤ edist (G N n ω) (H N ω)}
          ∪ {ω | ¬(ω ∈ A N → g n ω = G N n ω ∧ h ω = H N ω)}) := by
        refine measure_mono fun ω hω ↦ ?_
        by_cases hωA : ω ∈ A N
        · by_cases hωe : g n ω = G N n ω ∧ h ω = H N ω
          · exact Or.inl (Or.inr (by simpa only [mem_ofPred_eq, hωe.1, hωe.2] using hω))
          · exact Or.inr fun h' ↦ hωe (h' hωA)
        · exact Or.inl (Or.inl hωA)
    _ ≤ μ (A N)ᶜ + μ {ω | ε ≤ edist (G N n ω) (H N ω)} + 0 := by
        rw [← ae_iff.1 hgh]
        exact (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ δ / 2 + δ / 2 + 0 := by gcongr; exacts [hN N le_rfl, hn₀ n hn]
    _ = δ := by rw [add_zero, ENNReal.add_halves]

/-- **Convergence in measure is local**, for sequences that agree everywhere on the events:
`tendstoInMeasure_of_ae_eqOn`. -/
theorem tendstoInMeasure_of_eqOn {Ω E : Type*} [MeasurableSpace Ω] [EDist E] {μ : Measure Ω}
    {g : ℕ → Ω → E} {h : Ω → E} {A : ℕ → Set Ω} (hA : Tendsto (fun N ↦ μ (A N)ᶜ) atTop (𝓝 0))
    {G : ℕ → ℕ → Ω → E} {H : ℕ → Ω → E} (hGH : ∀ N, TendstoInMeasure μ (G N) atTop (H N))
    (hg : ∀ N n, EqOn (g n) (G N n) (A N)) (hh : ∀ N, ∀ᵐ ω ∂μ, ω ∈ A N → h ω = H N ω) :
    TendstoInMeasure μ g atTop h :=
  tendstoInMeasure_of_ae_eqOn hA hGH (fun N n ↦ Eventually.of_forall (hg N n)) hh

/-- **Limits in measure are local.** Two sequences that agree on an event and converge in measure
have limits that agree almost everywhere on the event: along a common subsequence both converge
almost surely. On `A = univ` this is `tendstoInMeasure_ae_unique`. -/
theorem ae_eq_of_tendstoInMeasure_of_eqOn {Ω E : Type*} [MeasurableSpace Ω] [EMetricSpace E]
    {μ : Measure Ω} {g g' : ℕ → Ω → E} {h h' : Ω → E} {A : Set Ω}
    (hg : TendstoInMeasure μ g atTop h) (hg' : TendstoInMeasure μ g' atTop h')
    (heq : ∀ n, EqOn (g n) (g' n) A) :
    ∀ᵐ ω ∂μ, ω ∈ A → h ω = h' ω := by
  obtain ⟨n₁, hn₁, h1⟩ := hg.exists_seq_tendsto_ae
  obtain ⟨n₂, hn₂, h2⟩ := (hg'.comp hn₁.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [h1, h2] with ω h1 h2 hω
  exact tendsto_nhds_unique (h1.comp hn₂.tendsto_atTop)
    (h2.congr fun i ↦ (heq _ hω).symm)

/-! ### Bounded paths -/

/-- `[0, T]` has a countable dense subset. -/
theorem exists_countable_dense_Icc (T : ℝ≥0) :
    ∃ D ⊆ Icc (0 : ℝ≥0) T, D.Countable ∧ Icc 0 T ⊆ closure D :=
  (TopologicalSpace.IsSeparable.of_separableSpace _).exists_countable_dense_subset

/-- A path continuous on `[0, T]` and bounded by `R` on a dense subset is bounded by `R` on
`[0, T]`. -/
theorem abs_le_of_dense {T : ℝ≥0} {D : Set ℝ≥0} (hDI : D ⊆ Icc 0 T) (hDd : Icc 0 T ⊆ closure D)
    {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T)) {R : ℝ} (h : ∀ t ∈ D, |x t| ≤ R) {t : ℝ≥0}
    (ht : t ∈ Icc 0 T) : |x t| ≤ R :=
  abs_le.2 ((hx.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Icc).closure_subset_iff.2
    (fun s hs ↦ ⟨hDI hs, abs_le.1 (h s hs)⟩) (hDd ht)).2

/-- A path continuous on `[0, T]` is bounded there by an integer. -/
theorem exists_nat_abs_le_Icc {T : ℝ≥0} {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T)) :
    ∃ N : ℕ, ∀ t ∈ Icc 0 T, |x t| ≤ N := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  obtain ⟨N, hN⟩ := exists_nat_ge R
  exact ⟨N, fun t ht ↦ (hR t ht).trans hN⟩

/-- **Two processes with continuous paths that agree at each time agree as paths.** If almost
every path of `Y` and of `Y'` is continuous on `[0, T]`, and at each `t ∈ [0, T]` they agree almost
everywhere on an event `A`, then almost everywhere on `A` they agree at every `t ∈ [0, T]`: on a
countable dense set of times, and so everywhere by continuity. -/
theorem ae_forall_eq_of_continuousOn {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : ℝ≥0} {Y Y' : ℝ≥0 → Ω → ℝ} (hY : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Y t ω) (Icc 0 T))
    (hY' : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Y' t ω) (Icc 0 T)) {A : Set Ω}
    (h : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂μ, ω ∈ A → Y t ω = Y' t ω) :
    ∀ᵐ ω ∂μ, ω ∈ A → ∀ t ∈ Icc 0 T, Y t ω = Y' t ω := by
  obtain ⟨D, hDI, hDc, hDd⟩ := exists_countable_dense_Icc T
  filter_upwards [hY, hY', (ae_ball_iff hDc).2 fun t ht ↦ h t (hDI ht)] with ω h1 h2 h3 hω
  exact EqOn.of_subset_closure (fun t ht ↦ h3 t ht hω) h1 h2 hDI hDd

/-- **A process with continuous paths stays in `[−N, N]` up to `T` with probability tending to
`1`.** The events are not assumed measurable. Their complements are covered by the
non-continuity null set and the complements of the measurable events "bounded by `N` on a
countable dense set", which decrease to a null set. -/
theorem tendsto_measure_compl_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {T : ℝ≥0} {X : ℝ≥0 → Ω → ℝ}
    (hXm : ∀ t, Measurable (X t)) (hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc 0 T)) :
    Tendsto (fun N : ℕ ↦ μ {ω | ∀ t ∈ Icc 0 T, |X t ω| ≤ N}ᶜ) atTop (𝓝 0) := by
  obtain ⟨D, hDI, hDc, hDd⟩ := exists_countable_dense_Icc T
  set G : ℕ → Set Ω := fun N ↦ {ω | ∀ t ∈ D, |X t ω| ≤ N}
  have hGm (N : ℕ) : MeasurableSet (G N) := by
    simp only [G, ofPred_forall]
    exact MeasurableSet.biInter hDc fun t _ ↦
      measurableSet_le (continuous_abs.measurable.comp (hXm t)) measurable_const
  have hGlim := tendsto_measure_iInter_atTop (μ := μ) (s := fun N ↦ (G N)ᶜ)
    (fun N ↦ (hGm N).compl.nullMeasurableSet)
    (fun N M hNM ↦ compl_subset_compl.2 fun ω hω t ht ↦ (hω t ht).trans (Nat.cast_le.2 hNM))
    ⟨0, measure_ne_top _ _⟩
  have hnull : μ {ω | ¬ContinuousOn (fun t ↦ X t ω) (Icc 0 T)} = 0 := ae_iff.1 hXc
  have hinter : μ (⋂ N, (G N)ᶜ) = 0 := by
    refine measure_mono_null ?_ hnull
    intro ω hω hc
    obtain ⟨N, hN⟩ := exists_nat_abs_le_Icc hc
    exact mem_iInter.1 hω N fun t ht ↦ hN t (hDI ht)
  rw [hinter] at hGlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGlim (fun _ ↦ bot_le)
    fun N ↦ ?_
  calc μ {ω | ∀ t ∈ Icc 0 T, |X t ω| ≤ N}ᶜ
      ≤ μ ({ω | ¬ContinuousOn (fun t ↦ X t ω) (Icc 0 T)} ∪ (G N)ᶜ) := by
        refine measure_mono fun ω hω ↦ ?_
        by_cases hc : ContinuousOn (fun t ↦ X t ω) (Icc 0 T)
        · exact Or.inr fun hG ↦ hω fun t ht ↦ abs_le_of_dense hDI hDd hc hG ht
        · exact Or.inl hc
    _ ≤ μ {ω | ¬ContinuousOn (fun t ↦ X t ω) (Icc 0 T)} + μ (G N)ᶜ := measure_union_le _ _
    _ = μ (G N)ᶜ := by rw [hnull, zero_add]

end LocalisationInMeasure
end MathFin
