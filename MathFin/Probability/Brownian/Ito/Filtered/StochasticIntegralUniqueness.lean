/-
Copyright (c) 2026 Raphael Coelho, Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonPredictable
public import MathFin.Probability.Brownian.Ito.StochasticIntegralCharacterisation

/-!
# Stochastic Integral Uniqueness

Adapted from MathFin.StochasticIntegralCharacterisation, copyright (c) 2026 Raphael Coelho.
Released under Apache 2.0 license.

## Main results

* `isStochasticIntegral_of_predictable_versions`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto.StochasticIntegralUniqueness
open ProbabilityTheory MeasureTheory Filter Topology
open scoped NNReal ENNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {Y : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}
    {I I' : (ℝ≥0 → Ω → ℝ) → Ω → ℝ} {S S' : Set (ℝ≥0 → Ω → ℝ)}

private def Agree (μ : Measure Ω) (I : (ℝ≥0 → Ω → ℝ) → Ω → ℝ) (S : Set (ℝ≥0 → Ω → ℝ))
    (I' : (ℝ≥0 → Ω → ℝ) → Ω → ℝ) (S' : Set (ℝ≥0 → Ω → ℝ)) (Z : ℝ≥0 → Ω → ℝ) : Prop :=
  Z ∈ S ∧ Z ∈ S' ∧ I Z =ᵐ[μ] I' Z

private theorem Agree.add (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' :
      IsRiemannStieltjesExtension μ Y ℱ I' S') {Z₁ Z₂ : ℝ≥0 → Ω → ℝ}
    (h₁ : Agree μ I S I' S' Z₁) (h₂ : Agree μ I S I' S' Z₂) :
    Agree μ I S I' S' (Z₁ + Z₂) := by
  obtain ⟨hS, hI⟩ := hI.integral_add Z₁ Z₂
    h₁.1 h₂.1
  obtain ⟨hS', hI''⟩ := hI'.integral_add Z₁ Z₂ h₁.2.1 h₂.2.1
  exact ⟨hS, hS', hI.trans ((h₁.2.2.add h₂.2.2).trans hI''.symm)⟩

private theorem Agree.const_smul (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' :
      IsRiemannStieltjesExtension μ Y ℱ I' S')
    {Z : ℝ≥0 → Ω → ℝ} (h : Agree μ I S I' S' Z) (c : ℝ) :
    Agree μ I S I' S' (c • Z) := by
  obtain ⟨hS, hI⟩ := hI.integral_smul Z c h.1
  obtain ⟨hS', hI''⟩ := hI'.integral_smul Z c h.2.1
  exact ⟨hS, hS', hI.trans ((h.2.2.const_smul c).trans hI''.symm)⟩

private theorem Agree.sub (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' :
      IsRiemannStieltjesExtension μ Y ℱ I' S') {Z₁ Z₂ : ℝ≥0 → Ω → ℝ}
    (h₁ : Agree μ I S I' S' Z₁) (h₂ : Agree μ I S I' S' Z₂) :
    Agree μ I S I' S' (Z₁ - Z₂) := by
  simpa [sub_eq_add_neg] using h₁.add hI hI' (h₂.const_smul hI hI' (-1))

/-- **`Agree` is closed under dominated limits**: both integrals pass to the limit in measure,
and limits in measure are almost surely unique. -/
private theorem Agree.of_tendsto (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' :
      IsRiemannStieltjesExtension μ Y ℱ I' S')
    {Z : ℕ → ℝ≥0 → Ω → ℝ} {Zd Zl : ℝ≥0 → Ω → ℝ} (hZ : ∀ n, Agree μ I S I' S' (Z n))
    (hZd : Zd ∈ S ∧ Zd ∈ S') (hdom : ∀ n t ω, |Z n t ω| ≤ |Zd t ω|)
    (hlim : ∀ t ω, Tendsto (Z · t ω) atTop (𝓝 (Zl t ω))) : Agree μ I S I' S' Zl := by
  obtain ⟨hS, hconv⟩ := hI.integral_dct Z Zd Zl
    (fun n ↦ (hZ n).1) hZd.1 hdom hlim
  obtain ⟨hS', hconv'⟩ := hI'.integral_dct Z Zd Zl (fun n ↦ (hZ n).2.1) hZd.2 hdom hlim
  exact ⟨hS, hS', tendstoInMeasure_ae_unique hconv
    (hconv'.congr_left fun n ↦ ((hZ n).2.2).symm)⟩

private theorem agree_band (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' :
      IsRiemannStieltjesExtension μ Y ℱ I' S') {i j : ℝ≥0} (hij : i ≤ j)
    (X : @SimpleFunc Ω (ℱ i) ℝ) :
    Agree μ I S I' S' (fun k ω ↦ if k ∈ Set.Ioc i j then X ω else 0) := by
  obtain ⟨hS, hI⟩ := hI.elementary_ioc i j hij X
  obtain ⟨hS', hI''⟩ := hI'.elementary_ioc i j hij X
  exact ⟨hS, hS', hI.trans hI''.symm⟩

private theorem agree_bottomBand (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' :
      IsRiemannStieltjesExtension μ Y ℱ I' S') (i : ℝ≥0)
    (X : @SimpleFunc Ω (ℱ ⊥) ℝ) :
    Agree μ I S I' S' (fun k ω ↦ if k ∈ Set.Iic i then X ω else 0) := by
  obtain ⟨hS, hI⟩ := hI.elementary_iic i X
  obtain ⟨hS', hI''⟩ := hI'.elementary_iic i X
  exact ⟨hS, hS', hI.trans hI''.symm⟩

open MathFin.StochasticIntegralCharacterisation (cut cut_add)

private theorem agree_cut_univ (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' :
      IsRiemannStieltjesExtension μ Y ℱ I' S') (K : ℝ≥0) :
    Agree μ I S I' S' (cut 1 K) := by
  convert agree_bottomBand hI hI' K (@SimpleFunc.const Ω ℝ (ℱ ⊥) 1) using 1
  funext t ω
  by_cases h : t ≤ K <;> simp [cut, h]

private theorem agree_zero (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' :
      IsRiemannStieltjesExtension μ Y ℱ I' S') :
    Agree μ I S I' S' 0 := by
  simpa using (agree_cut_univ hI hI' 0).const_smul hI hI' 0

/-- **Predictable indicators**: for every predictable `A`, the integrals agree on `𝟙_A` cut at `K`.
A Dynkin argument over the predictable rectangles, on which agreement is the elementary
identity. -/
private theorem agree_cut_indicator (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' :
      IsRiemannStieltjesExtension μ Y ℱ I' S') (K : ℝ≥0) :
    ∀ A, MeasurableSet[(ℱ).predictable] A →
      Agree μ I S I' S' (cut (A.indicator 1) K) := by
  classical
  refine MeasurableSpace.induction_on_inter (m := (ℱ).predictable)
    (C := fun A _ ↦ Agree μ I S I' S' (cut (A.indicator 1) K))
    (MathFin.FilteredIto.CommonPredictable.generateFrom_predictableRect ℱ).symm
          (MathFin.FilteredIto.CommonPredictable.isPiSystem_predictableRect ℱ) ?_ ?_ ?_ ?_
  · convert agree_zero hI hI' using 1
    funext t ω
    simp [cut]
  · intro A hA
    rcases hA with ⟨F₀, hF₀, rfl⟩ | ⟨a, b, hab, F, hF, rfl⟩
    · -- the bottom rectangle `{0} × F₀` is the initial band at time `0`
      convert agree_bottomBand hI hI' ⊥ (@SimpleFunc.piecewise Ω ℝ (ℱ ⊥) F₀ hF₀
        (@SimpleFunc.const Ω ℝ (ℱ ⊥) 1)
        (@SimpleFunc.const Ω ℝ (ℱ ⊥) 0)) using 1
      funext t ω
      by_cases ht : t = 0 <;> by_cases hω : ω ∈ F₀ <;>
        simp [cut, Set.indicator_apply, ht, hω]
    · -- a rectangle `(a, b] × F`, cut at `K`, is a band, or nothing if it starts after `K`
      by_cases haK : a ≤ K
      · convert agree_band hI hI' (le_min hab.le haK)
          (@SimpleFunc.piecewise Ω ℝ (ℱ a) F hF
            (@SimpleFunc.const Ω ℝ (ℱ a) 1)
            (@SimpleFunc.const Ω ℝ (ℱ a) 0)) using 1
        funext t ω
        by_cases h1 : t ≤ K <;> by_cases h2 : a < t <;> by_cases h3 : t ≤ b <;>
          by_cases hω : ω ∈ F <;> simp [cut, h1, h2, h3, hω]
      · convert agree_zero hI hI' using 1
        funext t ω
        simp only [cut, Pi.zero_apply]
        rw [Set.indicator_apply]
        split_ifs with h1
        · exact Set.indicator_of_notMem
            (show (t, ω) ∉ Set.Ioc a b ×ˢ F from fun h ↦ haK (h.1.1.le.trans h1.1)) _
        · rfl
  · intro A _ hA
    convert (agree_cut_univ hI hI' K).sub hI hI' hA using 1
    funext t ω
    by_cases h : (t, ω) ∈ A <;> simp [cut, Set.indicator_apply, h]
  · intro f hdisj _ hf
    -- the partial unions agree, by additivity
    have hpart (N : ℕ) :
        Agree μ I S I' S' (cut ((⋃ n ∈ Finset.range N, f n).indicator 1) K) := by
      induction N with
      | zero =>
        convert agree_zero hI hI' using 1
        funext t ω
        simp [cut]
      | succ N ih =>
        have hdj : Disjoint (⋃ n ∈ Finset.range N, f n) (f N) :=
          Set.disjoint_iUnion₂_left.2 fun n hn ↦ hdisj (Finset.mem_range.1 hn).ne
        rw [Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm,
          Set.indicator_union_of_disjoint hdj]
        have hsum := ih.add hI hI' (hf N)
        rwa [← cut_add] at hsum
    refine Agree.of_tendsto hI hI' hpart ⟨(agree_cut_univ hI hI' K).1, (agree_cut_univ hI hI'
          K).2.1⟩
      (fun N t ω ↦ ?_) (fun t ω ↦ ?_)
    · simp only [cut, Set.indicator_apply, Pi.one_apply]
      split_ifs <;> simp
    · by_cases hz : (t, ω) ∈ ⋃ n, f n
      · obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hz
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop m] with N hN
        have hmem : (t, ω) ∈ ⋃ n ∈ Finset.range N, f n :=
          Set.mem_biUnion (Finset.mem_range.2 hN) hm
        simp only [cut, Set.indicator_apply, hz, hmem, ite_true, Pi.one_apply]
      · refine tendsto_const_nhds.congr' (Eventually.of_forall fun N ↦ ?_)
        have hmem : (t, ω) ∉ ⋃ n ∈ Finset.range N, f n := fun h ↦
          hz (Set.mem_iUnion.2 (by obtain ⟨n, -, hn⟩ := Set.mem_iUnion₂.1 h; exact ⟨n, hn⟩))
        simp only [cut, Set.indicator_apply, hz, hmem, ite_false]

/-- **Simple predictable functions**, cut at `K`, by linearity. -/
private theorem agree_cut_simpleFunc (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' :
      IsRiemannStieltjesExtension μ Y ℱ I' S') (K : ℝ≥0)
    (f : @SimpleFunc (ℝ≥0 × Ω) (ℱ).predictable ℝ) :
    Agree μ I S I' S' (cut f K) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := (ℱ).predictable
  induction f using SimpleFunc.induction with
  | @const c A hA =>
    convert (agree_cut_indicator hI hI' K A hA).const_smul hI hI' c using 1
    funext t ω
    by_cases h : (t, ω) ∈ A <;> simp [cut, Set.indicator_apply, h]
  | @add f g _ hf hg =>
    rw [SimpleFunc.coe_add, cut_add]
    exact hf.add hI hI' hg

/-- **Bounded predictable processes**, cut at `K`: a bounded approximation by simple functions,
dominated by the constant. -/
private theorem agree_cut_bounded (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' :
      IsRiemannStieltjesExtension μ Y ℱ I' S') (K : ℝ≥0)
    {Z : ℝ≥0 × Ω → ℝ} (hZ : Measurable[(ℱ).predictable] Z)
    {C : ℝ} (hC : 0 ≤ C) (hZC : ∀ z, ‖Z z‖ ≤ C) : Agree μ I S I' S' (cut Z K) := by
  have hsm := hZ.stronglyMeasurable
  have hdom := (agree_cut_univ hI hI' K).const_smul hI hI' C
  refine Agree.of_tendsto hI hI' (Z := fun n ↦ cut (hsm.approxBounded C n) K) (Zd := C • cut 1 K)
    (fun n ↦ agree_cut_simpleFunc hI hI' K _) ⟨hdom.1, hdom.2.1⟩ (fun n t ω ↦ ?_) (fun t ω ↦ ?_)
  · simp only [cut, Pi.smul_apply, smul_eq_mul, Set.indicator_apply, Pi.one_apply]
    split_ifs
    · rw [mul_one, abs_of_nonneg hC, ← Real.norm_eq_abs]
      exact StronglyMeasurable.norm_approxBounded_le hsm hC n _
    · simp
  · simp only [cut, Set.indicator_apply]
    split_ifs
    · exact StronglyMeasurable.tendsto_approxBounded_of_norm_le hsm (hZC _)
    · exact tendsto_const_nhds

/-- **Uniqueness, in full.** Every Riemann–Stieltjes extension agrees with the integral against
`M` on their common domain. Truncating a predictable version at height and time `n` gives bounded
processes on which they agree; the version itself dominates the truncations, so both integrals
pass to the limit. -/
private theorem ae_eq_of_predictable_version
    (hI : IsRiemannStieltjesExtension μ Y ℱ I S) (hI' : IsRiemannStieltjesExtension μ Y ℱ I' S')
          {X : ℝ≥0 → Ω → ℝ}
    (hX : X ∈ S) (hX' : X ∈ S')
    (hv : ∃ V, IsStronglyPredictable ℱ V ∧ X ≡ᵐ[μ] V) : I X =ᵐ[μ] I' X := by
  obtain ⟨V, hp, hXV⟩ := hv
  obtain ⟨hVS, hIV⟩ := hI.integral_indistinguishable X V hX hXV
  obtain ⟨hVS', hI'V⟩ := hI'.integral_indistinguishable X V hX' hXV
  -- truncate the version at height and time `n`
  set W : ℕ → ℝ≥0 → Ω → ℝ := fun n ↦
    cut ({z | |Function.uncurry V z| ≤ n}.indicator (Function.uncurry V)) n
  have hWagree (n : ℕ) : Agree μ I S I' S' (W n) := by
    have hm : Measurable[(ℱ).predictable]
        ({z | |Function.uncurry V z| ≤ n}.indicator (Function.uncurry V)) := by
      let : MeasurableSpace (ℝ≥0 × Ω) := (ℱ).predictable
      exact hp.measurable.indicator (measurableSet_le hp.measurable.abs measurable_const)
    refine agree_cut_bounded hI hI' n hm (Nat.cast_nonneg n) fun z ↦ ?_
    by_cases h : |Function.uncurry V z| ≤ n
    · simpa [Set.indicator_of_mem
        (show z ∈ {z | |Function.uncurry V z| ≤ n} from h)] using h
    · simp [Set.indicator_of_notMem
        (show z ∉ {z | |Function.uncurry V z| ≤ n} from h)]
  have hVagree : Agree μ I S I' S' V := by
    refine Agree.of_tendsto hI hI' hWagree ⟨hVS, hVS'⟩
      (fun n t ω ↦ by
        simp only [W, cut, ← Real.norm_eq_abs]
        exact (norm_indicator_le_norm_self _ _).trans (norm_indicator_le_norm_self _ _))
      (fun t ω ↦ tendsto_const_nhds.congr' ?_)
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ≥0)).eventually_ge_atTop t,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop |V t ω|] with n htn hVn
    simp only [W, cut, Set.indicator_of_mem
      (show (t, ω) ∈ Set.Iic (n : ℝ≥0) ×ˢ (Set.univ : Set Ω) from ⟨htn, Set.mem_univ _⟩)]
    rw [Set.indicator_of_mem
        (show (t, ω) ∈ {z | |Function.uncurry V z| ≤ (n : ℝ)} from hVn)]
    rfl
  exact hIV.trans (hVagree.2.2.trans hI'V.symm)

/-- A Riemann–Stieltjes extension supported on processes having predictable versions
already satisfies BrownianMotion's uniqueness condition. -/
theorem isStochasticIntegral_of_predictable_versions (hI : IsRiemannStieltjesExtension μ Y ℱ I S)
    (hv : ∀ X ∈ S, ∃ V, IsStronglyPredictable ℱ V ∧ X ≡ᵐ[μ] V) :
    IsStochasticIntegral μ Y ℱ I S where
  toIsRiemannStieltjesExtension := hI
  consistent I' S' h X hX := ae_eq_of_predictable_version hI h hX.1 hX.2 (hv X hX.1)

end MathFin.FilteredIto.StochasticIntegralUniqueness
