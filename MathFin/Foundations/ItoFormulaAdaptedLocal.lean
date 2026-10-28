/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaAdapted
public import MathFin.Foundations.ItoFormulaLocalized
public import MathFin.Foundations.ItoIntegralCrossHorizon

/-! # Itô's formula for adapted coefficients: every `C²` function, every time

`ito_formula_adapted` proves Itô's formula along `X = x₀ + ∫ b ds + M`, `M = ∫ σ dB`
(`adaptedItoProcess`), for `f ∈ C²` with `f'` and `f''` bounded, at the horizon `T`. This file
removes both restrictions.

For `f ∈ C²` with no growth condition the integral `∫ f'(X) dM` cannot be the `L²` Itô integral,
since `f'(X)` need not be square-integrable. It is the limit in probability of the left-point
Riemann–Stieltjes sums `∑ f'(X_{tₖ}) (M_{tₖ₊₁} − M_{tₖ})`, and Itô's formula says that this limit
exists and equals `f(X_T) − f(x₀) − ∫₀ᵀ (f'(X) b + ½ f''(X) σ²) ds` (`ito_formula_adapted_local`).
When `f'` is bounded the same sums on `[0, T]` converge in probability to the `L²` Itô integral of
`f'(X)·σ`, the integral of `ito_formula_adapted` (`tendstoInMeasure_riemannStieltjes_itoIntegral`):
where both readings of `∫ f'(X) dM` are defined, they are limits in probability of the same sums.

The proof is a localisation in space. A `C²` function agrees on `[−N, N]`, with its first two
derivatives, with a `C²` function whose derivatives are bounded (`exists_bddDeriv_eqOn_Icc`: `f`
composed with the cutoff `SmoothTrunc.cut`). On the event that the path of `X` stays in `[−N, N]`
up to `T`, the Riemann sums of the two functions coincide, and the bounded formula
`ito_formula_adapted_against` identifies the limit of the second. These events exhaust `Ω` up to
a null set, because almost every path is continuous and so bounded on `[0, T]`
(`tendsto_measure_compl_abs_le`), and a limit in measure that holds on each of them holds on `Ω`
(`tendstoInMeasure_of_eqOn`).

The formula at an intermediate time `t ≤ T` is the formula at horizon `t`. The process built at
horizon `t` and the one built at horizon `T` are almost surely the same path on `[0, t]`: their
`L²` integrals agree at each time (`itoProcessCLM_consist`) and both continuous modifications are
continuous on `[0, t]`, so Degenne's `indistinguishable_of_modification_on` applies. Hence
`ito_formula_adapted_local_le`, for the process at horizon `T` on the partitions of `[0, t]`.

`ItoFormulaAdaptedTD` extends both to a time-dependent `f(t, x)`, and `ItoFormulaAdaptedUnbounded`
to unbounded coefficients `σ`, `b`. Not here: the formula as an identity of processes (all `t` at
once, almost surely).
-/

@[expose] public section

namespace MathFin
namespace ItoFormulaAdapted

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralBrownian
  QuadraticVariationL2 ItoIntegralProcessContinuousModification AdaptedDrift AdaptedRiemannStieltjes
open scoped NNReal ENNReal

/-! ### Limits in measure are local -/

/-- **Convergence in measure is local.** If on each of a sequence of events `A N`, whose
complements have measure tending to `0`, the sequence `g` agrees almost everywhere with a
sequence `G N` that converges in measure to `H N`, and `h` agrees with `H N` almost everywhere on
`A N`, then `g` converges in measure to `h`. The events need not be measurable. -/
theorem tendstoInMeasure_of_ae_eqOn {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : ℕ → Ω → ℝ} {h : Ω → ℝ} {A : ℕ → Set Ω} (hA : Tendsto (fun N ↦ μ (A N)ᶜ) atTop (𝓝 0))
    {G : ℕ → ℕ → Ω → ℝ} {H : ℕ → Ω → ℝ} (hGH : ∀ N, TendstoInMeasure μ (G N) atTop (H N))
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
theorem tendstoInMeasure_of_eqOn {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : ℕ → Ω → ℝ} {h : Ω → ℝ} {A : ℕ → Set Ω} (hA : Tendsto (fun N ↦ μ (A N)ᶜ) atTop (𝓝 0))
    {G : ℕ → ℕ → Ω → ℝ} {H : ℕ → Ω → ℝ} (hGH : ∀ N, TendstoInMeasure μ (G N) atTop (H N))
    (hg : ∀ N n, EqOn (g n) (G N n) (A N)) (hh : ∀ N, ∀ᵐ ω ∂μ, ω ∈ A N → h ω = H N ω) :
    TendstoInMeasure μ g atTop h :=
  tendstoInMeasure_of_ae_eqOn hA hGH (fun N n ↦ Eventually.of_forall (hg N n)) hh

/-- **Limits in measure are local.** Two sequences that agree on an event and converge in measure
have limits that agree almost everywhere on the event: along a common subsequence both converge
almost surely. -/
theorem ae_eq_of_tendstoInMeasure_of_eqOn {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g g' : ℕ → Ω → ℝ} {h h' : Ω → ℝ} {A : Set Ω} (hg : TendstoInMeasure μ g atTop h)
    (hg' : TendstoInMeasure μ g' atTop h') (heq : ∀ n, EqOn (g n) (g' n) A) :
    ∀ᵐ ω ∂μ, ω ∈ A → h ω = h' ω := by
  obtain ⟨n₁, hn₁, h1⟩ := hg.exists_seq_tendsto_ae
  obtain ⟨n₂, hn₂, h2⟩ := exists_seq_tendsto_ae_comp hg' hn₁
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

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- **A process with continuous paths stays in `[−N, N]` up to `T` with probability tending to
`1`.** The events are not assumed measurable. Their complements are covered by the
non-continuity null set and the complements of the measurable events "bounded by `N` on a
countable dense set", which decrease to a null set. -/
theorem tendsto_measure_compl_abs_le [IsFiniteMeasure μ] {T : ℝ≥0} {X : ℝ≥0 → Ω → ℝ}
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
    (fun N M hNM ↦ compl_subset_compl.2 fun ω hω t ht ↦ (hω t ht).trans (by exact_mod_cast hNM))
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

/-! ### A `C²` function is locally one with bounded derivatives -/

omit mΩ in
/-- **A `C²` function agrees on `[−R, R]` with a `C²` function whose derivatives are bounded**,
and so do their first and second derivatives: compose with the cutoff `SmoothTrunc.cut N`, which
is the identity on `[−(N + 1), N + 1]` and has bounded range and bounded derivatives. -/
theorem exists_bddDeriv_eqOn_Icc {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hf'' : Continuous f'') (R : ℝ) :
    ∃ (g g' g'' : ℝ → ℝ) (C₁ C₂ : ℝ), (∀ x, HasDerivAt g (g' x) x) ∧
      (∀ x, HasDerivAt g' (g'' x) x) ∧ Continuous g'' ∧ (∀ x, |g' x| ≤ C₁) ∧
      (∀ x, |g'' x| ≤ C₂) ∧ ∀ x, |x| ≤ R → g x = f x ∧ g' x = f' x ∧ g'' x = f'' x := by
  obtain ⟨S⟩ := smoothTrunc_exists
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  set N := ⌈R⌉₊
  have hmem (x : ℝ) : S.cut N x ∈ Icc (-(S.M₀ * (N + 1))) (S.M₀ * (N + 1)) :=
    abs_le.1 (S.cut_bdd N x)
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hf'c.continuousOn
    (s := Icc (-(S.M₀ * (N + 1))) (S.M₀ * (N + 1)))
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hf''.continuousOn
    (s := Icc (-(S.M₀ * (N + 1))) (S.M₀ * (N + 1)))
  have habs {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B :=
    (abs_mul a b).trans_le (mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha))
  refine ⟨fun x ↦ f (S.cut N x), fun x ↦ f' (S.cut N x) * S.cutD1 N x,
    fun x ↦ f'' (S.cut N x) * S.cutD1 N x * S.cutD1 N x + f' (S.cut N x) * S.cutD2 N x,
    C₁ * S.M₁, C₂ * S.M₁ * S.M₁ + C₁ * S.M₂, fun x ↦ (hf _).comp x (S.cut_hasDerivAt N x),
    fun x ↦ ((hf' _).comp x (S.cut_hasDerivAt N x)).mul (S.cutD1_hasDerivAt N x),
    (((hf''.comp (S.continuous_cut N)).mul (S.continuous_cutD1 N)).mul
      (S.continuous_cutD1 N)).add ((hf'c.comp (S.continuous_cut N)).mul (S.continuous_cutD2 N)),
    fun x ↦ habs (hC₁ _ (hmem x)) (S.cutD1_bdd N x),
    fun x ↦ (abs_add_le _ _).trans (add_le_add
      (habs (habs (hC₂ _ (hmem x)) (S.cutD1_bdd N x)) (S.cutD1_bdd N x))
      (habs (hC₁ _ (hmem x)) (S.cutD2_bdd N x))), fun x hx ↦ ?_⟩
  have hxN : |x| ≤ N := hx.trans (Nat.le_ceil R)
  simp [S.cut_eq_id_of_abs_le (by linarith : |x| ≤ (N : ℝ) + 1),
    S.cutD1_eq_one_of_abs_lt (by linarith : |x| < (N : ℝ) + 1),
    S.cutD2_eq_zero_of_abs_lt (by linarith : |x| < (N : ℝ) + 1)]

/-! ### The formula -/

variable [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
  (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
  {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C)
  {b : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) {Cb : ℝ} (hb_bdd : ∀ s ω, |b s ω| ≤ Cb) (x₀ : ℝ)

include hB hBcont hb_adap hb_cont hb_bdd in
/-- **With `f'` bounded, the Riemann sums converge to the `L²` Itô integral.** For `f'`
continuous and bounded, the left-point Riemann–Stieltjes sums of `f'(X)` against `M = ∫ σ dB` on
the uniform partitions of `[0, T]` converge in probability to the Itô integral of the class of
`f'(X)·σ`, the stochastic integral of `ito_formula_adapted`. -/
theorem tendstoInMeasure_riemannStieltjes_itoIntegral {f' : ℝ → ℝ} (hf'c : Continuous f')
    {C₁ : ℝ} (hf1 : ∀ x, |f' x| ≤ C₁) :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ Finset.range n,
        f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b
          (unifPart T n k) ω)
        * (itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
            (unifPart T n (k + 1)) ω
          - itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
            (unifPart T n k) ω)) atTop
      (itoIntegralCLM_T hB T hBmeas (processToLpPredictable T hBmeas
        (comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont hadap hcont
          (processToLp (μ := μ) T hBmeas hadap hcont hbdd) hb_adap hb_cont hb_bdd x₀ hf'c)
        (abs_comp_mul_le hf1 hbdd _))) := by
  set φ := processToLp (μ := μ) T hBmeas hadap hcont hbdd
  have hpred := comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hb_adap hb_cont
    hb_bdd x₀ hf'c
  rw [← itoIntegralAgainst_weightLp hB T hBmeas φ hpred (fun s ω ↦ hf1 _) _ ?_]
  · exact tendstoInMeasure_riemannStieltjes hB T hBmeas φ
      (fun t ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φ ht) hpred
      ((ae_continuousOn_adaptedItoProcess hB T hBmeas hBcont φ hb_cont hb_bdd x₀).mono
        fun ω h ↦ hf'c.comp_continuousOn h) fun s ω ↦ hf1 _
  · filter_upwards [processToLpPredictable_coeFn (μ := μ) T hBmeas
        (comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont hadap hcont φ
          hb_adap hb_cont hb_bdd x₀ hf'c) (abs_comp_mul_le hf1 hbdd _),
      processToLp_coeFn (μ := μ) T hBmeas hadap hcont hbdd] with z h1 h2
    rw [h1, h2]
    exact mul_comm _ _

include hB hBcont in
/-- **The martingale part does not depend on the horizon.** For `t ≤ T` the continuous
modifications of `M = ∫ σ dB` built at horizons `t` and `T` are almost surely the same path on
`[0, t]`: they are modifications of each other there (`itoProcessCLM_consist`), hence
indistinguishable on `[0, t)` by continuity (`indistinguishable_of_modification_on`), and equal
almost surely at `t`. -/
theorem ae_itoContinuousMod_eq_of_le {t : ℝ≥0} (ht : t ≤ T) :
    ∀ᵐ ω ∂μ, ∀ s ∈ Icc 0 t,
      itoContinuousMod t hBmeas (processToLp (μ := μ) t hBmeas hadap hcont hbdd) s ω
        = itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd) s ω := by
  set φ := processToLp (μ := μ) T hBmeas hadap hcont hbdd
  set φt := processToLp (μ := μ) t hBmeas hadap hcont hbdd
  have hmod (s : ℝ≥0) (hs : s ≤ t) : (fun ω ↦ itoContinuousMod t hBmeas φt s ω)
      =ᵐ[μ] fun ω ↦ itoContinuousMod T hBmeas φ s ω := by
    have hLp := itoProcessCLM_consist hB hBmeas hs ht hadap hcont hbdd
    refine ((itoContinuousMod_modification hB t hBmeas hBcont φt hs).trans
      (Eventually.of_forall fun ω ↦ ?_)).trans
      (itoContinuousMod_modification hB T hBmeas hBcont φ (hs.trans ht)).symm
    rw [hLp]
  filter_upwards [indistinguishable_of_modification_on (P := μ) isOpen_Iio
      ((itoContinuousMod_continuousOn hB t hBmeas hBcont φt).mono fun ω h ↦
        h.mono fun s hs ↦ ⟨zero_le, le_of_lt hs⟩)
      ((itoContinuousMod_continuousOn hB T hBmeas hBcont φ).mono fun ω h ↦
        h.mono fun s hs ↦ ⟨zero_le, (le_of_lt hs).trans ht⟩)
      fun s hs ↦ hmod s (le_of_lt hs), hmod t le_rfl] with ω h1 h2 s hs
  rcases hs.2.lt_or_eq with hlt | rfl
  exacts [h1 s hlt, h2]

variable {T hBmeas x₀} in
/-- Two Itô processes with the same start and drift whose martingale parts agree on a set of
times agree there. -/
theorem adaptedItoProcess_eq_of_eqOn {T' : ℝ≥0} {φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)}
    {φ' : Lp ℝ 2 (trimMeasure_T (μ := μ) T' hBmeas)} {ω : Ω} {S : Set ℝ≥0}
    (h : ∀ s ∈ S, itoContinuousMod T' hBmeas φ' s ω = itoContinuousMod T hBmeas φ s ω)
    {s : ℝ≥0} (hs : s ∈ S) :
    adaptedItoProcess T' hBmeas φ' x₀ b s ω = adaptedItoProcess T hBmeas φ x₀ b s ω := by
  simp only [adaptedItoProcess, h s hs]

variable {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
  (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hf'' : Continuous f'')

include hB hBcont hb_adap hb_cont hb_bdd hf hf' hf'' in
/-- **Itô's formula for a `C²` function of an Itô process with adapted coefficients.** Let `B` be
a Brownian motion with every path continuous, `σ` and `b` bounded, adapted to the natural
filtration of `B` and with every path continuous, `X = x₀ + ∫ b ds + M` with `M = ∫ σ dB`
(`adaptedItoProcess`, `itoContinuousMod`), and `f` twice differentiable with `f''` continuous.
Then the left-point Riemann–Stieltjes sums of `f'(X)` against `M` on the uniform partitions of
`[0, T]` converge in probability, and their limit `∫₀ᵀ f'(X) dM` satisfies

`∫₀ᵀ f'(X_s) dM_s = f(X_T) − f(x₀) − ∫₀ᵀ (f'(X_s) b_s + ½ f''(X_s) σ_s²) ds`.

No bound on `f'` or `f''` is assumed. -/
theorem ito_formula_adapted_local :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ Finset.range n,
        f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b
          (unifPart T n k) ω)
        * (itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
            (unifPart T n (k + 1)) ω
          - itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
            (unifPart T n k) ω)) atTop
      fun ω ↦ f (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
          x₀ b T ω) - f x₀
        - ∫ s in Ioc 0 T, (f' (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω) * b s ω
            + 1 / 2 * (f'' (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)
              * σ s ω ^ 2)) ∂timeMeasure := by
  set φ := processToLp (μ := μ) T hBmeas hadap hcont hbdd
  set X := adaptedItoProcess T hBmeas φ x₀ b
  have hpred : IsStronglyPredictable (natFiltration hBmeas) X :=
    adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hb_adap hb_cont hb_bdd x₀
  have hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc 0 T) :=
    ae_continuousOn_adaptedItoProcess hB T hBmeas hBcont φ hb_cont hb_bdd x₀
  choose g g' g'' C₁ C₂ hg hg' hg'' hg1 hg2 hgf using fun N : ℕ ↦
    exists_bddDeriv_eqOn_Icc hf hf' hf'' N
  have hg'c (N : ℕ) : Continuous (g' N) :=
    Differentiable.continuous fun x ↦ (hg' N x).differentiableAt
  refine tendstoInMeasure_of_eqOn (A := fun N : ℕ ↦ {ω | ∀ t ∈ Icc 0 T, |X t ω| ≤ N})
    (tendsto_measure_compl_abs_le (fun t ↦ ((hpred.stronglyAdapted t).mono
      ((natFiltration hBmeas).le t)).measurable) hXc)
    (fun N ↦ tendstoInMeasure_riemannStieltjes hB T hBmeas φ
      (fun t ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φ ht)
      (comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hb_adap hb_cont hb_bdd
        x₀ (hg'c N)) (hXc.mono fun ω h ↦ (hg'c N).comp_continuousOn h)
      fun s ω ↦ hg1 N (X s ω))
    (fun N n ω hω ↦ Finset.sum_congr rfl fun k hk ↦ ?_) fun N ↦ ?_
  · rw [(hgf N _ (hω _ ⟨zero_le, unifPart_le_T (Finset.mem_range.1 hk).le⟩)).2.1]
  filter_upwards [ito_formula_adapted_against hB T hBmeas hBcont hadap hcont hbdd hb_adap hb_cont
      hb_bdd x₀ (hg N) (hg' N) (hg'' N) (hg1 N) (hg2 N),
    adaptedItoProcess_zero hB T hBmeas hBcont φ x₀ (b := b)] with ω hk h0 hω
  have hx₀ : X 0 ω = x₀ := h0
  have hT := hgf N _ (hω T ⟨zero_le, le_rfl⟩)
  have h0' := hgf N x₀ (hx₀ ▸ hω 0 ⟨le_rfl, zero_le⟩)
  have hint : ∫ s in Ioc 0 T, (g' N (X s ω) * b s ω + 1 / 2 * (g'' N (X s ω) * σ s ω ^ 2))
        ∂timeMeasure
      = ∫ s in Ioc 0 T, (f' (X s ω) * b s ω + 1 / 2 * (f'' (X s ω) * σ s ω ^ 2))
        ∂timeMeasure := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    have h := hgf N _ (hω s (Ioc_subset_Icc_self hs))
    simp only [h.2.1, h.2.2]
  rw [hT.1, h0'.1, hint] at hk
  linarith

include hB hBcont hb_adap hb_cont hb_bdd hf hf' hf'' in
/-- **Itô's formula for a `C²` function of an Itô process with adapted coefficients, at every
time `t ≤ T`.** For the process `X = x₀ + ∫ b ds + M` built at horizon `T`, and `t ≤ T`, the
left-point Riemann–Stieltjes sums of `f'(X)` against `M` on the uniform partitions of `[0, t]`
converge in probability to

`f(X_t) − f(x₀) − ∫₀ᵗ (f'(X_s) b_s + ½ f''(X_s) σ_s²) ds`.

The proof is the formula at horizon `t`: the process built at horizon `t` is almost surely the
same path on `[0, t]` (`ae_itoContinuousMod_eq_of_le`). -/
theorem ito_formula_adapted_local_le {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ Finset.range n,
        f' (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b
          (unifPart t n k) ω)
        * (itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
            (unifPart t n (k + 1)) ω
          - itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
            (unifPart t n k) ω)) atTop
      fun ω ↦ f (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
          x₀ b t ω) - f x₀
        - ∫ s in Ioc 0 t, (f' (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω) * b s ω
            + 1 / 2 * (f'' (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)
              * σ s ω ^ 2)) ∂timeMeasure := by
  have hM := ae_itoContinuousMod_eq_of_le hB T hBmeas hBcont hadap hcont hbdd ht
  refine (ito_formula_adapted_local hB t hBmeas hBcont hadap hcont hbdd hb_adap hb_cont hb_bdd
    x₀ hf hf' hf'').congr (fun n ↦ ?_) ?_
  · filter_upwards [hM] with ω hω
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.1 hk
    rw [adaptedItoProcess_eq_of_eqOn hω ⟨zero_le, unifPart_le_T hk'.le⟩,
      hω _ ⟨zero_le, unifPart_le_T hk'⟩, hω _ ⟨zero_le, unifPart_le_T hk'.le⟩]
  · filter_upwards [hM] with ω hω
    rw [adaptedItoProcess_eq_of_eqOn hω ⟨zero_le, le_rfl⟩]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    rw [adaptedItoProcess_eq_of_eqOn hω (Ioc_subset_Icc_self hs)]

end ItoFormulaAdapted
end MathFin
