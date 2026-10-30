/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralBrownian
public import MathFin.Foundations.AdaptedProcessToLp

/-! # Riemann ↔ CLM bridge for a bounded **adapted continuous** integrand `θ`

For an **arbitrary bounded adapted continuous** process `θ : ℝ≥0 → Ω → ℝ` — the integrand shape
the general adapted Girsanov theorem needs (the market price of risk is a genuine adapted process,
not a function of `B_s` alone) — the uniform-partition Riemann–Itô sums `riemannσ θ T n =
∑_{k<n} θ(tₖ)·(B_{t_{k+1}} − B_{tₖ})` (`ItoRiemannSum`) converge in `L²(μ)` to
`itoIntegralCLM_T (processToLp θ)` — the genuine continuous Itô integral of the σ-realization
`processToLp θ` (`AdaptedProcessToLp`). This is the one bridge: the integrand
`(s, B_s) ↦ φ(s, B_s)` of `ItoIntegralRiemannBridgeTD` is a special case of it, and `φ ∘ B` the
case of that which is constant in time.

The coefficient `θ(tₖ)` is `𝓕_{tₖ}`-measurable and bounded — exactly `stepSP`'s requirement — so the
left-endpoint step process is directly a `TBoundedSP`, and the `L²`-membership of the Riemann sum
is obtained by plain domination (`memLp_riemannσ`), so no `AdaptedAt`-vs-`natFiltration` bridge is
needed. The a.e. convergence uses the partition-cell collapse (`cell_collapse`) against `θ`'s own
path continuity.

## Main results

* `itoIntegralCLM_T_of_bdd_adapted_cont` — `∑ θ(tₖ)·ΔBₖ → itoIntegralCLM_T (processToLp θ)` in `L²`.
* `tendstoInMeasure_riemannσ` — the same, in measure.
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralRiemannBridge

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal
open scoped MeasureTheory NNReal ENNReal InnerProductSpace
open ItoIntegralL2 ItoIntegralCLM ItoIsometryAdapted ItoIntegralBrownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

omit hB in
/-- The simple-process coercion is additive over a finite sum (pointwise). -/
lemma coe_finsetSum_apply {ι' : Type*} (hBmeas : ∀ t, Measurable (B t)) (s : Finset ι')
    (W : ι' → SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (i : ℝ≥0) (ω : Ω) :
    ⇑(∑ k ∈ s, W k) i ω = ∑ k ∈ s, ⇑(W k) i ω := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, SimpleProcess.coe_add, Pi.add_apply, Pi.add_apply, ih,
      Finset.sum_insert ha]

omit hB in
/-- On `(0,T]`, the cell-indicator sum collapses to the unique containing cell's value,
whose left endpoint is within `T/n` of `s` (the `Nat.find` partition-cell argument). -/
lemma cell_collapse (T : ℝ≥0) (n : ℕ) (hn : 0 < n) (s : ℝ≥0) (hs : s ∈ Set.Ioc 0 T)
    (v : ℕ → ℝ) :
    ∃ k, k < n ∧ (∑ j ∈ Finset.range n,
        (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator (fun _ ↦ v j) s) = v k
      ∧ |(unifPart T n k : ℝ) - s| ≤ (T : ℝ) / n := by
  have hmono : Monotone (unifPart T n) := unifPart_mono T n
  have hlast : unifPart T n n = T := unifPart_self T hn.ne'
  have hgap : ∀ k, (unifPart T n (k + 1) : ℝ) - unifPart T n k = (T : ℝ) / n :=
    unifPart_succ_sub T n
  have hex : ∃ k, s ≤ unifPart T n (k + 1) :=
    ⟨n - 1, by rw [Nat.sub_add_cancel hn, hlast]; exact hs.2⟩
  set K := Nat.find hex
  have hKspec : s ≤ unifPart T n (K + 1) := Nat.find_spec hex
  have hKle : K ≤ n - 1 := Nat.find_le (by rw [Nat.sub_add_cancel hn, hlast]; exact hs.2)
  have hKlt : K < n := lt_of_le_of_lt hKle (Nat.sub_lt hn one_pos)
  have hlow : unifPart T n K < s := by
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · rw [hK0, unifPart_zero]; exact hs.1
    · have hmin := Nat.find_min hex (m := K - 1) (Nat.sub_lt hKpos one_pos)
      have hK1 : K - 1 + 1 = K := by omega
      rw [hK1] at hmin
      exact not_le.mp hmin
  refine ⟨K, hKlt, ?_, ?_⟩
  · rw [Finset.sum_eq_single K]
    · rw [Set.indicator_of_mem]; exact ⟨hlow, hKspec⟩
    · intro l _ hlK
      apply Set.indicator_of_notMem
      rintro ⟨hl1, hl2⟩
      rcases lt_or_gt_of_ne hlK with hlt | hgt
      · exact (Nat.find_min hex hlt) hl2
      · exact absurd hl1 (not_lt.mpr (le_trans hKspec (hmono (Nat.succ_le_of_lt hgt))))
    · intro hKnot; exact absurd (Finset.mem_range.mpr hKlt) hKnot
  · rw [abs_le]
    have hcoe_low : (unifPart T n K : ℝ) < s := by exact_mod_cast hlow
    have hcoe_hi : (s : ℝ) ≤ unifPart T n (K + 1) := by exact_mod_cast hKspec
    have hg := hgap K
    have hTn : (0 : ℝ) ≤ (T : ℝ) / n := div_nonneg (NNReal.coe_nonneg T) (Nat.cast_nonneg n)
    exact ⟨by nlinarith [hcoe_low, hcoe_hi, hg], by nlinarith [hcoe_low, hTn]⟩

omit hB in
/-- **The left-endpoint step functions converge where the function is continuous.** At a time
`s ∈ (0, T]` at which `g` is continuous within `[0, T]`, the cell-indicator sums
`∑ⱼ 𝟙_{(tⱼ, tⱼ₊₁]}(s)·g(tⱼ)` tend to `g s`: the cell containing `s` has its left endpoint in
`[0, T]`, within `T/n` of `s` (`cell_collapse`). -/
lemma tendsto_sum_indicator_unifPart (T : ℝ≥0) {s : ℝ≥0} (hs : s ∈ Set.Ioc 0 T) {g : ℝ≥0 → ℝ}
    (hg : ContinuousWithinAt g (Set.Icc 0 T) s) :
    Tendsto (fun n ↦ ∑ j ∈ Finset.range n,
      (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator (fun _ ↦ g (unifPart T n j)) s)
      atTop (𝓝 (g s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.mp hg ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hn1 : 0 < n := one_pos.trans_le ((le_max_right _ _).trans hn)
  obtain ⟨k, hk, hval, hclose⟩ := cell_collapse T n hn1 s hs (fun j ↦ g (unifPart T n j))
  rw [hval]
  refine hδc ⟨zero_le, unifPart_le_T hk.le⟩ ?_
  rw [NNReal.dist_eq]
  refine hclose.trans_lt ?_
  rw [div_lt_iff₀ (Nat.cast_pos.2 hn1), mul_comm]
  exact (div_lt_iff₀ hδ).mp (hN.trans_le (Nat.cast_le.2 ((le_max_left _ _).trans hn)))

omit hB in
/-- On `(0, T]` the left-endpoint step function is `0` or a value of `g`, so a bound on `g`
bounds it. -/
lemma abs_sum_indicator_unifPart_le (T : ℝ≥0) (n : ℕ) {s : ℝ≥0} (hs : s ∈ Set.Ioc 0 T)
    {g : ℝ≥0 → ℝ} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ t, |g t| ≤ C) :
    |∑ j ∈ Finset.range n,
      (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator (fun _ ↦ g (unifPart T n j)) s|
      ≤ C := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hC
  · obtain ⟨k, _, hval, _⟩ := cell_collapse T n hn s hs (fun j ↦ g (unifPart T n j))
    exact hval ▸ hg _

omit hB in
/-- If `∫ (Fₙ − G)² → 0` then `‖⟦Fₙ⟧ − ⟦G⟧‖ → 0`, any measure. The single-fixed-limit
variant of `ItoIntegralBrownian.tendsto_norm_toLp_sub` (which compares two *sequences*
`Fₙ, Gₙ`); kept as a separate lemma because the `G`-shape genuinely differs. The generic
`L²` facts `ItoIntegralL2.lp_two_norm_sq` / `ItoIntegralBrownian.lp_dist_sq` it rests on. -/
lemma tendsto_norm_toLp_sub' {α : Type*} {m : MeasurableSpace α} {ν : Measure α}
    {F : ℕ → α → ℝ} {G : α → ℝ} (hF : ∀ n, MemLp (F n) 2 ν) (hG : MemLp G 2 ν)
    (h : Tendsto (fun n ↦ ∫ z, (F n z - G z) ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ‖(hF n).toLp (F n) - hG.toLp G‖) atTop (𝓝 0) := by
  have heq : (fun n ↦ ‖(hF n).toLp (F n) - hG.toLp G‖)
      = fun n ↦ Real.sqrt (∫ z, (F n z - G z) ^ 2 ∂ν) := by
    funext n; rw [← lp_dist_sq (hF n) hG, Real.sqrt_sq (norm_nonneg _)]
  rw [heq]
  simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp h

omit hB in
/-- **The uncurried step process is a sum of cell indicators**:
`uncurry (stepσ n) (s,ω) = ∑_{k<n} 𝟙_{(tₖ,t_{k+1}]}(s)·θ(tₖ)ω`. -/
lemma uncurry_stepσ (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    Function.uncurry ⇑(stepσ hBmeas hadap hbdd T n).val (s, ω)
      = ∑ k ∈ Finset.range n, (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
          (fun _ ↦ θ (unifPart T n k) ω) s := by
  change ⇑(stepσ hBmeas hadap hbdd T n).val s ω = _
  rw [stepσ, AddSubmonoidClass.coe_finsetSum, coe_finsetSum_apply,
    ← Finset.sum_attach (Finset.range n) (fun k ↦
      (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
        (fun _ ↦ θ (unifPart T n k) ω) s)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [SimpleProcess.apply_eq]
  simp only [stepSP]
  rw [Finsupp.sum_single_index (by simp)]
  simp

omit hB in
/-- On `(0, T]` the step process is `0` or a value of `θ`, so it inherits the bound `C`. -/
lemma abs_uncurry_stepσ_le (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) {s : ℝ≥0} (hs : s ∈ Set.Ioc 0 T)
    (ω : Ω) : |Function.uncurry ⇑(stepσ hBmeas hadap hbdd T n).val (s, ω)| ≤ C :=
  uncurry_stepσ hBmeas hadap hbdd T n s ω ▸ abs_sum_indicator_unifPart_le T n hs
    ((abs_nonneg _).trans (hbdd 0 ω)) fun t ↦ hbdd t ω

omit hB in
/-- **The step processes converge where the path is continuous**: at a time `s ∈ (0, T]` at which
`s ↦ θ_s ω` is continuous within `[0, T]`, `stepσ n (s, ω) → θ_s ω`
(`tendsto_sum_indicator_unifPart` along the path). -/
lemma tendsto_uncurry_stepσ (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) {s : ℝ≥0} (hs : s ∈ Set.Ioc 0 T) {ω : Ω}
    (hcont : ContinuousWithinAt (fun s : ℝ≥0 ↦ θ s ω) (Set.Icc 0 T) s) :
    Tendsto (fun n ↦ Function.uncurry ⇑(stepσ hBmeas hadap hbdd T n).val (s, ω)) atTop
      (𝓝 (θ s ω)) := by
  simp only [uncurry_stepσ]
  exact tendsto_sum_indicator_unifPart T hs hcont

/-- **Riemann ↔ CLM bridge, adapted case.** For a bounded (`|θ| ≤ C`) adapted (`𝓕`-measurable in
each `t`) continuous (every path `s ↦ θ_s ω`) integrand, the uniform-partition Riemann–Itô sums
`∑ θ(tₖ)·ΔBₖ` converge in `L²(μ)` to `itoIntegralCLM_T (processToLp θ)`. -/
theorem itoIntegralCLM_T_of_bdd_adapted_cont (hBmeas : ∀ t, Measurable (B t))
    {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ θ s ω))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    Tendsto (fun n ↦ (memLp_riemannσ hB hBmeas hadap hbdd T n).toLp (riemannσ (B := B) θ T n))
      atTop (𝓝 (itoIntegralCLM_T hB T hBmeas
        (processToLp (μ := μ) T hBmeas hadap hcont hbdd))) := by
  set f : ℕ → ℝ≥0 × Ω → ℝ := fun n ↦ Function.uncurry ⇑(stepσ hBmeas hadap hbdd T n).val with hf
  set gθ_fn : ℝ≥0 × Ω → ℝ := Function.uncurry θ with hgθ
  have hf_memLp : ∀ n, MemLp (f n) 2 (trimMeasure_T (μ := μ) T hBmeas) :=
    fun n ↦ memLp_uncurry_trim_T T hBmeas _
  have hgθ_memLp : MemLp gθ_fn 2 (trimMeasure_T (μ := μ) T hBmeas) :=
    memLp_uncurry_of_bdd_adapted_cont T hBmeas hadap hcont hbdd
  -- `trimMeasure_T` is supported on `(0,T] × Ω`
  have hsupp := ae_fst_mem_Ioc_trimMeasure_T (μ := μ) T hBmeas
  -- the uncurried step functions converge a.e. to `θ` (cell collapse + path continuity)
  have hae_conv : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
      Tendsto (fun n ↦ f n z) atTop (𝓝 (gθ_fn z)) := by
    filter_upwards [hsupp] with z hz
    exact tendsto_uncurry_stepσ hBmeas hadap hbdd T hz (hcont z.2).continuousWithinAt
  -- uniform bound `|f n| ≤ C` a.e.
  have hf_bdd : ∀ n, ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), |f n z| ≤ C := fun n ↦ by
    filter_upwards [hsupp] with z hz
    exact abs_uncurry_stepσ_le hBmeas hadap hbdd T n hz z.2
  -- L² convergence of the integrals (dominated convergence, bound `(2C)²`)
  have hint : Tendsto (fun n ↦ ∫ z, (f n z - gθ_fn z) ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas))
      atTop (𝓝 0) := by
    have hlim : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
        Tendsto (fun n ↦ (f n z - gθ_fn z) ^ 2) atTop (𝓝 ((fun _ ↦ (0 : ℝ)) z)) := by
      filter_upwards [hae_conv] with z hz
      simpa using ((hz.sub_const (gθ_fn z)).pow 2)
    have hbnd : ∀ n, ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
        ‖(f n z - gθ_fn z) ^ 2‖ ≤ (2 * C) ^ 2 := by
      intro n
      filter_upwards [hf_bdd n, hsupp] with z hzb hz
      have hC0 : (0 : ℝ) ≤ C := (abs_nonneg _).trans (hbdd 0 z.2)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hgb : |gθ_fn z| ≤ C := by rw [hgθ]; exact hbdd _ _
      have : |f n z - gθ_fn z| ≤ 2 * C := (abs_sub _ _).trans (by linarith)
      nlinarith [this, abs_nonneg (f n z - gθ_fn z), sq_abs (f n z - gθ_fn z)]
    have := tendsto_integral_of_dominated_convergence (fun _ ↦ (2 * C) ^ 2)
      (fun n ↦ ((hf_memLp n).aestronglyMeasurable.sub hgθ_memLp.aestronglyMeasurable).pow 2)
      (integrable_const _) hbnd hlim
    simpa using this
  have hLp : Tendsto (fun n ↦ (hf_memLp n).toLp (f n)) atTop (𝓝 (hgθ_memLp.toLp gθ_fn)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (tendsto_norm_toLp_sub' hf_memLp hgθ_memLp hint)
  have key : ∀ n, itoIntegralCLM_T hB T hBmeas ((hf_memLp n).toLp (f n))
      = (memLp_riemannσ hB hBmeas hadap hbdd T n).toLp (riemannσ (B := B) θ T n) := fun n ↦
    itoIntegralCLM_T_stepσ hB hBmeas hadap hbdd T n
  have htarget : hgθ_memLp.toLp gθ_fn = processToLp (μ := μ) T hBmeas hadap hcont hbdd := rfl
  rw [← htarget]
  exact (Filter.tendsto_congr key).mp
    (((itoIntegralCLM_T hB T hBmeas).continuous.tendsto _).comp hLp)

/-- **The Riemann–Itô sums converge in measure to `∫₀ᵀ θ dB`.** From the `L²` convergence
`itoIntegralCLM_T_of_bdd_adapted_cont` via `tendstoInMeasure_of_tendsto_Lp`, transported from the
`Lp` classes to the `riemannσ` functions. -/
theorem tendstoInMeasure_riemannσ (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    TendstoInMeasure μ (fun n ↦ riemannσ (B := B) θ T n) atTop
      ⇑(itoIntegralCLM_T hB T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)) := by
  refine TendstoInMeasure.congr
    (fun n ↦ (memLp_riemannσ hB hBmeas hadap hbdd T n).coeFn_toLp) EventuallyEq.rfl ?_
  exact tendstoInMeasure_of_tendsto_Lp
    (itoIntegralCLM_T_of_bdd_adapted_cont hB hBmeas hadap hcont hbdd T)

end ItoIntegralRiemannBridge
end MathFin
