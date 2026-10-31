/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.ConvexSeparation
public import MathFin.Foundations.MartingaleTransform
public import MathFin.Foundations.FTAP
public import MathFin.Foundations.FTAPOnePeriod
public import MathFin.Foundations.NoArbitrageCore
public import MathFin.Foundations.ContinuousMarket

/-!
# Discrete-time FTAP on a finite probability space (scalar, finite horizon)

The finite-Ω, finite-horizon, single-asset **Fundamental Theorem of Asset
Pricing** (Harrison–Pliska / the finite case of Dalang–Morton–Willinger): a
market has **no arbitrage** iff it admits an **equivalent martingale measure**.

The discounted price `S : ℕ → Ω → ℝ` is adapted to a filtration `𝓕` on a finite
probability space `(Ω, P)` with full support; a trading strategy `φ` is
predictable (`φ (n+1)` is `𝓕 n`-measurable) and its discounted gains are the
martingale transform `martingaleTransform φ S`.

The backward direction is the geometric heart of the theorem: the attainable
gains span a subspace of `Ω → ℝ` that, under no arbitrage, misses the standard
simplex, so the separating-dual kernel `exists_pos_dual_of_disjoint_stdSimplex`
(`Foundations/ConvexSeparation.lean`) produces a strictly-positive pricing
functional — the EMM. The forward direction is `MathFin.IsEMM.noArbitrage` (`Foundations/FTAP.lean`,
where `IsEMM` and `NoArbitrage` are defined for a general space and `F`-valued price), shared with
the one-period market.

## Scope

Finite Ω, one scalar discounted asset, finite horizon `T`. The general-Ω DMW
theorem (which needs L⁰-closedness under no arbitrage and measurable selection)
and the `d`-asset generalisation are out of scope here.

## Relation to the other EMM notions

* **One period.** At horizon `1` with trivial initial information `𝓕 0 = ⊥`, the time-`0`
  price and the time-`1` holding are constants, and this market is the one-period market of
  `Foundations/FTAPOnePeriod.lean` for the increment `Y = S 1 − S 0`: the EMMs coincide
  (`isEMM_one_iff_onePeriod`) and so do the no-arbitrage conditions
  (`noArbitrage_one_iff_onePeriod`).
* **Continuous time.** `ContinuousMarket.IsEMM` is a process-level notion over `ℝ≥0` on a
  general Ω, with a horizon `T : ℝ≥0` like this one, and stays separate. It restricts in one
  direction: sampled along any monotone schedule inside `[0, T]`, a continuous-time EMM is an
  EMM here for the sampled price and filtration (`ContinuousMarket.IsEMM.sampled`, in
  `ContinuousMarket.lean`, general Ω, though `ftap_discrete` itself needs finite Ω), and it is a
  one-period EMM for every increment
  `S t − S s` with `s, t ≤ T` (`ContinuousMarket.IsEMM.increment`). The converses are not claimed: neither restriction
  sees adaptedness of `S` at all times or the martingale property between arbitrary times.

## Main definitions / results (assembled across this file)

* `MathFin.NoArbitrage`, `MathFin.IsEMM` (`Foundations/FTAP.lean`)
* `MathFin.ftap_discrete` — the biconditional `NoArbitrage ↔ ∃ Q, IsEMM Q`
* `MathFin.isEMM_one_iff_onePeriod`, `MathFin.noArbitrage_one_iff_onePeriod`
* `MathFin.ContinuousMarket.IsEMM.increment`
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

-- Heterogeneous use of one rich `variable` context: the algebraic transform
-- lemmas need only `S`, and several theorems do not touch
-- `Nonempty`/`MeasurableSingletonClass`/`IsProbabilityMeasure`. Five scattered
-- `omit … in` clauses would be noisier than a single suppression, so we disable
-- the unused-section-variable linter file-wide (deliberate, localized).
set_option linter.unusedSectionVars false

/-- On a finite space every strategy is bounded on the horizon. -/
private lemma exists_bound_horizon {Ω : Type*} [Fintype Ω] (N : ℕ) (φ : ℕ → Ω → ℝ) :
    ∃ K : ℝ, ∀ n ≤ N, ∀ ω, ‖φ n ω‖ ≤ K :=
  ⟨∑ n ∈ Finset.range (N + 1), ∑ ω', |φ n ω'|, fun n hn ω ↦ by
    rw [Real.norm_eq_abs]
    exact (Finset.single_le_sum (f := fun ω' ↦ |φ n ω'|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ ω)).trans
      (Finset.single_le_sum (f := fun n ↦ ∑ ω', |φ n ω'|)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))⟩

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {mΩ : MeasurableSpace Ω}
  [MeasurableSingletonClass Ω] (𝓕 : Filtration ℕ mΩ)
  (P : Measure Ω) [IsProbabilityMeasure P] (S : ℕ → Ω → ℝ) (T : ℕ)

omit [Fintype Ω] in
/-- On a full-support measure a null set is empty — hence any two full-support
measures on `Ω` are mutually absolutely continuous. -/
private lemma eq_empty_of_pos_singleton {μ : Measure Ω} (hμ : ∀ ω, 0 < μ {ω})
    {s : Set Ω} (hs : μ s = 0) : s = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨ω, hω⟩
  exact absurd (hs ▸ measure_mono (Set.singleton_subset_iff.mpr hω) : μ {ω} ≤ 0)
    (not_le.mpr (hμ ω))

/-- `𝟙_A · (S_{t+1} − S_t)` — the discounted gain of holding one unit on the
event `A` over period `t+1`. -/
noncomputable def incrementIndicator (t : ℕ) (A : Set Ω) : Ω → ℝ :=
  fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω * (S (t + 1) ω - S t ω)

/-- The **attainable-gains subspace**: the span of the single-period
increment-indicators `𝟙_A · (S_{t+1} − S_t)` over `t < T` and `𝓕_t`-measurable
events `A`. Every element is the discounted gains of some predictable strategy
(see `mem_gains_imp_predictable`). -/
noncomputable def gainsSubspace : Submodule ℝ (Ω → ℝ) :=
  Submodule.span ℝ
    { g | ∃ t, t < T ∧ ∃ A : Set Ω, MeasurableSet[𝓕 t] A ∧ g = incrementIndicator S t A }

omit [Fintype Ω] in
/-- The martingale transform is additive in the strategy. -/
private lemma martingaleTransform_add (φ ψ : ℕ → Ω → ℝ) (n : ℕ) :
    martingaleTransform (φ + ψ) S n
      = martingaleTransform φ S n + martingaleTransform ψ S n := by
  funext ω
  simp only [martingaleTransform, Pi.add_apply, Real.inner_apply, add_mul, Finset.sum_add_distrib]

omit [Fintype Ω] in
/-- The martingale transform is homogeneous in the strategy. -/
private lemma martingaleTransform_smul (c : ℝ) (φ : ℕ → Ω → ℝ) (n : ℕ) :
    martingaleTransform (c • φ) S n = c • martingaleTransform φ S n := by
  funext ω
  simp only [martingaleTransform, Pi.smul_apply, smul_eq_mul, Real.inner_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

omit [MeasurableSingletonClass Ω] [Fintype Ω] in
/-- Every element of the attainable-gains subspace is the discounted gains of a
predictable strategy. (`span`-induction: the generators are the gains of the
single-period indicator strategies, and predictable gains are closed under the
vector-space operations.) -/
theorem mem_gains_imp_predictable {g : Ω → ℝ} (hg : g ∈ gainsSubspace 𝓕 S T) :
    ∃ φ : ℕ → Ω → ℝ,
      StronglyAdapted 𝓕 (fun n ↦ φ (n + 1)) ∧ martingaleTransform φ S T = g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, htT, A, hA, rfl⟩ := hx
    refine ⟨fun s ↦ if s = t + 1 then A.indicator (fun _ ↦ (1 : ℝ)) else 0, ?_, ?_⟩
    · intro n
      dsimp only
      split_ifs with h
      · have hnt : n = t := by omega
        subst hnt
        exact stronglyMeasurable_const.indicator hA
      · exact stronglyMeasurable_const
    · funext ω
      simp only [martingaleTransform, Real.inner_apply]
      rw [Finset.sum_eq_single t]
      · simp [incrementIndicator]
      · intro k _ hk
        rw [if_neg (by omega : ¬ k + 1 = t + 1)]
        simp
      · intro ht
        exact absurd (Finset.mem_range.mpr htT) ht
  | zero => exact ⟨0, fun _ ↦ stronglyMeasurable_const, by funext ω; simp [martingaleTransform]⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨φ, hφ, hφeq⟩ := ihx
    obtain ⟨ψ, hψ, hψeq⟩ := ihy
    exact ⟨φ + ψ, fun n ↦ (hφ n).add (hψ n),
      by rw [martingaleTransform_add, hφeq, hψeq]⟩
  | smul c x _ ih =>
    obtain ⟨φ, hφ, hφeq⟩ := ih
    exact ⟨c • φ, fun n ↦ (hφ n).const_smul c, by rw [martingaleTransform_smul, hφeq]⟩

omit [IsProbabilityMeasure P] in
/-- Under no arbitrage, the attainable-gains subspace is disjoint from the
standard simplex: a non-negative, non-zero gains vector would be an arbitrage. -/
theorem gains_disjoint_stdSimplex (hP : ∀ ω, 0 < P {ω}) (hNA : NoArbitrage 𝓕 P S T) :
    ∀ v ∈ gainsSubspace 𝓕 S T, v ∉ stdSimplex ℝ Ω := by
  intro v hv hsimplex
  obtain ⟨φ, hφ, hφeq⟩ := mem_gains_imp_predictable 𝓕 S T hv
  -- The gains are `≥ 0` (`v` is in the simplex), so no arbitrage forces them `= 0`.
  have hge : 0 ≤ᵐ[P] martingaleTransform φ S T := by
    rw [hφeq]; exact Filter.Eventually.of_forall fun ω ↦ hsimplex.1 ω
  have hzero : v =ᵐ[P] 0 := by
    rw [← hφeq]
    exact hNA φ (fun t _ ↦ hφ t) (exists_bound_horizon T φ) hge
  -- But `∑ v = 1`, so some `v ω₀ > 0`, contradicting `v = 0` a.e. on full support.
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀, 0 < v ω₀ := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hle : ∑ ω, v ω ≤ 0 := Finset.sum_nonpos fun ω _ ↦ hcon ω
    rw [hsimplex.2] at hle; linarith
  have hnull : P {ω | v ω ≠ 0} = 0 := by simpa using ae_iff.mp hzero
  have hmem : ω₀ ∈ {ω | v ω ≠ 0} := ne_of_gt hω₀
  rw [eq_empty_of_pos_singleton hP hnull] at hmem
  simp at hmem

omit [IsProbabilityMeasure P] [Fintype Ω] in
/-- **Backward direction**: no arbitrage ⟹ an equivalent martingale measure
exists. The separating-dual `q` of the gains subspace, normalised to a
probability `Q`, is the EMM: strict positivity gives `Q ~ P`, and the
annihilation of every increment-indicator gives the martingale property via the
conditional-expectation characterisation. -/
theorem exists_isEMM_of_noArbitrage [Finite Ω] (hS : StronglyAdapted 𝓕 S)
    (hP : ∀ ω, 0 < P {ω}) (hNA : NoArbitrage 𝓕 P S T) :
    ∃ Q, IsEMM 𝓕 P S T Q := by
  cases nonempty_fintype Ω
  classical
  obtain ⟨q, hq_pos, hq_dual⟩ :=
    exists_pos_dual_of_disjoint_stdSimplex (gainsSubspace 𝓕 S T)
      (gains_disjoint_stdSimplex 𝓕 P S T hP hNA)
  set Z : ℝ := ∑ ω, q ω with hZ
  have hZpos : 0 < Z := Finset.sum_pos (fun ω _ ↦ hq_pos ω) Finset.univ_nonempty
  have hmnn : ∀ ω, (0 : ℝ) ≤ q ω / Z := fun ω ↦ (div_pos (hq_pos ω) hZpos).le
  have hsum1 : ∑ ω, ENNReal.ofReal (q ω / Z) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ ↦ hmnn ω), ← Finset.sum_div, ← hZ,
      div_self hZpos.ne', ENNReal.ofReal_one]
  set Q : Measure Ω := (PMF.ofFintype (fun ω ↦ ENNReal.ofReal (q ω / Z)) hsum1).toMeasure
    with hQdef
  haveI hQprob : IsProbabilityMeasure Q := by rw [hQdef]; infer_instance
  have hQsingle : ∀ ω, Q {ω} = ENNReal.ofReal (q ω / Z) := fun ω ↦ by
    rw [hQdef, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton ω), PMF.ofFintype_apply]
  have hQpos : ∀ ω, 0 < Q {ω} := fun ω ↦ by
    rw [hQsingle ω]; exact ENNReal.ofReal_pos.mpr (div_pos (hq_pos ω) hZpos)
  have hQint : ∀ h : Ω → ℝ, ∫ ω, h ω ∂Q = ∑ ω, (q ω / Z) * h ω := by
    intro h
    rw [hQdef, PMF.integral_eq_sum]
    exact Finset.sum_congr rfl fun ω _ ↦ by
      rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hmnn ω), smul_eq_mul]
  -- Full support ⇒ `P` and `Q` are mutually absolutely continuous.
  have hQP : Q ≪ P := by
    intro s hs; rw [eq_empty_of_pos_singleton hP hs]; exact measure_empty
  have hPQ : P ≪ Q := by
    intro s hs; rw [eq_empty_of_pos_singleton hQpos hs]; exact measure_empty
  refine ⟨Q, .of_condExp_succ ⟨hQprob, hQP, hPQ⟩ (fun t _ ↦ hS t) (fun t _ ↦ Integrable.of_finite)
    fun t htT ↦ ?_⟩
  -- Martingale property via the conditional-expectation characterisation.
  refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le t) Integrable.of_finite
    (fun s _ _ ↦ Integrable.of_finite.integrableOn) (fun s hs _ ↦ ?_)
    (hS t).aestronglyMeasurable
  -- Key: `∫_s (S_{t+1} − S_t) dQ = 0` because the increment-indicator is annihilated.
  have hsm : MeasurableSet s := 𝓕.le t s hs
  have hinc_eq : s.indicator (fun ω ↦ S (t + 1) ω - S t ω) = incrementIndicator S t s := by
    funext ω; simp only [incrementIndicator, Set.indicator_apply]; split_ifs <;> ring
  have hkey : ∫ ω, s.indicator (fun ω ↦ S (t + 1) ω - S t ω) ω ∂Q = 0 := by
    rw [hinc_eq, hQint]
    have hdual := hq_dual (incrementIndicator S t s)
      (Submodule.subset_span ⟨t, htT, s, hs, rfl⟩)
    calc ∑ ω, (q ω / Z) * incrementIndicator S t s ω
        = (∑ ω, q ω * incrementIndicator S t s ω) / Z := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl fun ω _ ↦ by ring
      _ = 0 := by rw [hdual, zero_div]
  rw [integral_indicator hsm,
    integral_sub Integrable.of_finite.integrableOn Integrable.of_finite.integrableOn] at hkey
  linarith [hkey]

omit [IsProbabilityMeasure P] [Fintype Ω] in
/-- **Finite-Ω Fundamental Theorem of Asset Pricing** (Harrison–Pliska; the
finite case of Dalang–Morton–Willinger): a finite-horizon, single-asset market
on a finite full-support probability space has no arbitrage **iff** it admits an
equivalent martingale measure. -/
theorem ftap_discrete [Finite Ω] (hS : StronglyAdapted 𝓕 S) (hP : ∀ ω, 0 < P {ω}) :
    NoArbitrage 𝓕 P S T ↔ ∃ Q, IsEMM 𝓕 P S T Q :=
  ⟨fun hNA ↦ exists_isEMM_of_noArbitrage 𝓕 P S T hS hP hNA,
   fun ⟨_, hQ⟩ ↦ hQ.noArbitrage⟩

/-! ### Horizon one: the one-period market

With trivial initial information `𝓕 0 = ⊥`, a `⊥`-measurable function is constant
(`stronglyMeasurable_bot_iff`): the time-`0` price is a number, the time-`1` holding is a
constant position, and `Q[· | ⊥]` is the plain expectation (`condExp_bot`). The one-step
market is then the one-period market of `Foundations/FTAPOnePeriod.lean` for the increment
`S 1 − S 0`. -/

omit [Nonempty Ω] [IsProbabilityMeasure P] [Fintype Ω] in
/-- **At horizon `1` the discrete-time EMM is the one-period EMM.** With `𝓕 0 = ⊥` and `S`
adapted, `Q` is an equivalent martingale measure for the one-step market iff it is one for
the one-period excess return `S 1 − S 0`: the one-step martingale condition
`S 0 = E_Q[S 1]` (the price `S 0` being a constant) is `E_Q[S 1 − S 0] = 0`. -/
theorem isEMM_one_iff_onePeriod [Finite Ω] (hS : StronglyAdapted 𝓕 S) (h0 : 𝓕 0 = ⊥)
    {Q : Measure Ω} :
    IsEMM 𝓕 P S 1 Q ↔ OnePeriod.IsEMM P (S 1 - S 0) Q := by
  have hS0 : StronglyMeasurable[𝓕 0] (S 0) := hS 0
  rw [h0] at hS0
  obtain ⟨c, hc⟩ := stronglyMeasurable_bot_iff.mp hS0
  -- under a probability measure, the constant price `S 0 = c` has mean `c`
  have hmean (μ : Measure Ω) [IsProbabilityMeasure μ] : ∫ ω, S 0 ω ∂μ = c := by simp [hc]
  constructor
  · intro hQ
    haveI := hQ.isProb
    have hm := (hQ.condExp_eq (Nat.zero_le 1) le_rfl).symm
    rw [h0, condExp_bot, hc] at hm
    obtain ⟨_, hcQ⟩ := hm.exists
    refine ⟨hQ.toIsEquivProbMeasure, Integrable.of_finite, ?_⟩
    change ∫ ω, (S 1 ω - S 0 ω) ∂Q = 0
    rw [integral_sub Integrable.of_finite Integrable.of_finite, hmean Q]
    exact sub_eq_zero.mpr hcQ.symm
  · intro hQ
    haveI := hQ.isProb
    refine .of_condExp_succ hQ.toIsEquivProbMeasure (fun t _ ↦ hS t)
      (fun t _ ↦ Integrable.of_finite) fun t ht ↦ ?_
    obtain rfl : t = 0 := by omega
    rw [h0, condExp_bot, hc]
    have hfair : ∫ ω, (S 1 ω - S 0 ω) ∂Q = 0 := hQ.fair
    rw [integral_sub Integrable.of_finite Integrable.of_finite, hmean Q] at hfair
    exact Filter.Eventually.of_forall fun _ ↦ (sub_eq_zero.mp hfair).symm

omit [Fintype Ω] [Nonempty Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure P] in
/-- **At horizon `1` discrete-time no arbitrage is one-period no arbitrage.** With
`𝓕 0 = ⊥`, a predictable strategy holds a constant `θ` over the single period, and its
discounted gain `martingaleTransform φ S 1` is `θ · (S 1 − S 0)`. -/
theorem noArbitrage_one_iff_onePeriod (h0 : 𝓕 0 = ⊥) :
    NoArbitrage 𝓕 P S 1 ↔ OnePeriod.NoArbitrage P (S 1 - S 0) := by
  have hgain (φ : ℕ → Ω → ℝ) :
      martingaleTransform φ S 1 = fun ω ↦ φ 1 ω * (S 1 - S 0) ω := by
    funext ω; simp [martingaleTransform, mul_comm]
  constructor
  · intro hNA θ hθ
    have h := hNA (fun _ _ ↦ θ) (fun _ _ ↦ stronglyMeasurable_const) ⟨|θ|, fun _ _ _ ↦ by simp⟩
      (by rw [hgain]; exact hθ)
    rwa [hgain] at h
  · intro hNA φ hφ _ hpos
    have hφ1 : StronglyMeasurable[𝓕 0] (φ 1) := hφ 0 one_pos
    rw [h0] at hφ1
    obtain ⟨θ, hθ⟩ := stronglyMeasurable_bot_iff.mp hφ1
    simp only [hgain φ, hθ] at hpos ⊢
    exact hNA θ hpos

end MathFin

/-! ### The continuous-time EMM, sampled

A continuous-time EMM `ContinuousMarket.IsEMM` (`Foundations/ContinuousMarket.lean`) is a
process-level object on a general Ω. It restricts to the discrete-time notion
(`ContinuousMarket.IsEMM.sampled`, there) and to the one-period notion (below); these
restrictions are one-directional. -/

namespace MathFin.ContinuousMarket

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **A continuous-time EMM is a one-period EMM for every increment before the horizon.** If `Q`
is an equivalent martingale measure up to `T` for the discounted price `S`, then for any two
dates `s`, `t ≤ T` it is an equivalent martingale measure, in the sense of
`Foundations/FTAPOnePeriodVector.lean`, for the one-period excess return `S t − S s` with a
constant holding: a martingale has constant expectation. -/
theorem IsEMM.increment {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {S : ℝ≥0 → Ω → F} {T : ℝ≥0} {Q : Measure Ω}
    (h : IsEMM 𝓕 P S T Q) {s t : ℝ≥0} (hs : s ≤ T) (ht : t ≤ T) :
    OnePeriodVector.IsEMM P (S t - S s) Q := by
  haveI := h.isProb
  have hmean {u : ℝ≥0} (hu : u ≤ T) : ∫ ω, S u ω ∂Q = ∫ ω, S 0 ω ∂Q := by
    rw [← integral_condExp (𝓕.le 0)]
    exact integral_congr_ae (h.condExp_eq zero_le hu)
  refine ⟨h.toIsEquivProbMeasure, (h.integrable ht).sub (h.integrable hs), ?_⟩
  change ∫ ω, (S t ω - S s ω) ∂Q = 0
  rw [integral_sub (h.integrable ht) (h.integrable hs), hmean ht, hmean hs, sub_self]

end MathFin.ContinuousMarket
