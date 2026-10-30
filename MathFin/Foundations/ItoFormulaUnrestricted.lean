/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaLocalized
public import MathFin.Foundations.ItoFormulaProcess
public import MathFin.Foundations.ExitTime

/-! # The double cutoff of Summit C, and the capped exit-time localizer

The Itô formulas with bounded derivatives (`ito_formula_td_process`) are extended to a general
`C^{1,2}` function by cutting `f` off, in time and in space, onto a compact square where its
continuous partials are bounded. This file holds that cutoff and the localizer that makes it inert.

* `SummitC.fTrunc N (t, x) = f(φₙ t, φₙ x)`, with `SummitC.fTruncT`, `fTruncX`, `fTruncXX` its
  partials in closed form by the chain rule (`fTrunc_hasDerivAt_t`, `_x`, `_xx`), each globally
  bounded (`fTruncT_bdd`, …), jointly continuous, and equal to the partials of `f` where
  `|t|, |x| ≤ N` (`fTrunc_eq_of`, …). The adapted Itô formula
  `ito_formula_adapted_td_local` (`ItoFormulaAdaptedTD`) localises in space with it.
* `sigmaSeq B N = min(τ_N, N)`, the exit time of `B` from `[−N, N]` capped at the level, and
  `isLocalizingSequence_sigma`: a localizing sequence for the null-augmented Brownian filtration.
  On `{t ≤ σ_N}` both the space cut and the time cut are inert.
* `continuous_timeMeasure_primitive`: the primitive `t ↦ ∫_{(0,t]} h` of a continuous `h` is
  continuous.

The unrestricted-`C²` Itô formula itself, the residual `f(t, B_t) − f(0, B_0) − ∫₀ᵗ (f_t + ½ f_xx)
ds` being a local martingale localised by `sigmaSeq`, is `ito_formula_unrestricted`
(`ItoFormulaUnrestrictedLocMart`). It is derived from the process formula for an Itô process with
unbounded coefficients (`exists_localMartingale_ito_formula`) at `σ = 1`, `b = 0`, not from this
cutoff.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology
open ItoIntegralL2 ItoIntegralBrownian ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral
open ItoIntegralProcessL2Infinite ItoIntegralProcessLocalMartingaleGeneral

/-- **The drift primitive is continuous.** `t ↦ ∫_{(0,t]} h dτ` for continuous `h` and
`τ = timeMeasure` (finite on compacts): dominated convergence, the integrand `t ↦ 𝟙_{(0,t]}(s)·h(s)`
having its only discontinuity in `t` at the τ-null point `t = s`. -/
lemma continuous_timeMeasure_primitive {h : ℝ≥0 → ℝ} (hh : Continuous h) :
    Continuous fun t : ℝ≥0 ↦ ∫ s in Set.Ioc 0 t, h s ∂ItoIntegralL2.timeMeasure := by
  have hrw : (fun t : ℝ≥0 ↦ ∫ s in Set.Ioc 0 t, h s ∂ItoIntegralL2.timeMeasure)
      = fun t ↦ ∫ s, (Set.Ioc 0 t).indicator h s ∂ItoIntegralL2.timeMeasure := by
    funext t; rw [integral_indicator measurableSet_Ioc]
  rw [hrw]
  refine continuous_iff_continuousAt.mpr fun t₀ ↦ ?_
  refine continuousAt_of_dominated
    (bound := fun s ↦ (Set.Icc 0 (t₀ + 1)).indicator (fun u ↦ |h u|) s)
    (Filter.Eventually.of_forall fun t ↦
      (hh.stronglyMeasurable.indicator measurableSet_Ioc).aestronglyMeasurable)
    (Filter.eventually_of_mem (Iio_mem_nhds (lt_add_one t₀)) fun t ht ↦
      Filter.Eventually.of_forall fun s ↦ ?_)
    ?_ ?_
  · -- pointwise domination by `𝟙_{[0,t₀+1]}·|h|`
    by_cases hmem : s ∈ Set.Ioc 0 t
    · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs,
        Set.indicator_of_mem (show s ∈ Set.Icc 0 (t₀ + 1) from
          ⟨zero_le, le_of_lt (lt_of_le_of_lt hmem.2 ht)⟩)]
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      exact Set.indicator_nonneg (fun s _ ↦ abs_nonneg _) s
  · -- the dominator is integrable (continuous on a compact, finite measure there)
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (hh.abs.continuousOn.integrableOn_compact isCompact_Icc)
  · -- a.e.-`s` continuity in `t` (off the null point `t₀`)
    have hne : ∀ᵐ s ∂ItoIntegralL2.timeMeasure, s ≠ t₀ := by
      rw [ae_iff]; simp only [not_not, Set.ofPred_eq_eq_singleton]
      exact ItoIntegralL2.timeMeasure_singleton t₀
    filter_upwards [hne] with s hs
    by_cases hs0 : 0 < s
    · rcases lt_or_gt_of_ne hs with hlt | hgt
      · refine (continuousAt_congr ?_).mpr (continuousAt_const (y := h s))
        filter_upwards [Ioi_mem_nhds hlt] with t ht
        exact Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hs0, le_of_lt ht⟩) h
      · refine (continuousAt_congr ?_).mpr (continuousAt_const (y := (0 : ℝ)))
        filter_upwards [Iio_mem_nhds hgt] with t ht
        exact Set.indicator_of_notMem (fun hmem ↦ absurd (Set.mem_Ioc.mp hmem).2 (not_le.mpr ht)) h
    · refine (continuousAt_congr ?_).mpr (continuousAt_const (y := (0 : ℝ)))
      have hs00 : s = 0 := le_antisymm (not_lt.mp hs0) (zero_le)
      filter_upwards with t
      exact Set.indicator_of_notMem
          (by rw [hs00]; exact fun hmem ↦ lt_irrefl 0 (Set.mem_Ioc.mp hmem).1) h

namespace SummitC

variable {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}

/-- The double cutoff `fTrunc N (t,x) = f(φₙ t, φₙ x)` — `f` confined to the compact square. -/
noncomputable def fTrunc (f : ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x : ℝ) : ℝ :=
  f (S.cut N t) (S.cut N x)
/-- `∂_t fTrunc = f_t(φₙ t, φₙ x)·φₙ'(t)`. -/
noncomputable def fTruncT (f_t : ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x : ℝ) : ℝ :=
  f_t (S.cut N t) (S.cut N x) * S.cutD1 N t
/-- `∂_x fTrunc = f_x(φₙ t, φₙ x)·φₙ'(x)`. -/
noncomputable def fTruncX (f_x : ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x : ℝ) : ℝ :=
  f_x (S.cut N t) (S.cut N x) * S.cutD1 N x
/-- `∂_xx fTrunc = f_xx·(φₙ' x)² + f_x·φₙ''(x)`. -/
noncomputable def fTruncXX (f_x f_xx : ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x : ℝ) : ℝ :=
  f_xx (S.cut N t) (S.cut N x) * (S.cutD1 N x * S.cutD1 N x) +
      f_x (S.cut N t) (S.cut N x) * S.cutD2 N x
/-- `∂_t fTrunc` exists with value `fTruncT` (chain rule through the time cut). -/
lemma fTrunc_hasDerivAt_t (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (S : SmoothTrunc) (N : ℕ) (t x : ℝ) :
    HasDerivAt (fun s ↦ fTrunc f S N s x) (fTruncT f_t S N t x) t :=
  (hf_t (S.cut N t) (S.cut N x)).comp t (S.cut_hasDerivAt N t)

/-- `∂_x fTrunc` exists with value `fTruncX` (chain rule through the space cut). -/
lemma fTrunc_hasDerivAt_x (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (S : SmoothTrunc) (N : ℕ) (t x : ℝ) :
    HasDerivAt (fun u ↦ fTrunc f S N t u) (fTruncX f_x S N t x) x :=
  (hf_x (S.cut N t) (S.cut N x)).comp x (S.cut_hasDerivAt N x)

/-- `∂_x fTruncX = fTruncXX` (product rule, `x`-derivative). -/
lemma fTrunc_hasDerivAt_xx (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (S : SmoothTrunc) (N : ℕ) (t x : ℝ) :
    HasDerivAt (fun u ↦ fTruncX f_x S N t u) (fTruncXX f_x f_xx S N t x) x := by
  have hu : HasDerivAt (fun u ↦ f_x (S.cut N t) (S.cut N u))
      (f_xx (S.cut N t) (S.cut N x) * S.cutD1 N x) x :=
    (hf_xx (S.cut N t) (S.cut N x)).comp x (S.cut_hasDerivAt N x)
  have hv : HasDerivAt (fun u ↦ S.cutD1 N u) (S.cutD2 N x) x := S.cutD1_hasDerivAt N x
  rw [show fTruncXX f_x f_xx S N t x
      = f_xx (S.cut N t) (S.cut N x) * S.cutD1 N x * S.cutD1 N x
        + f_x (S.cut N t) (S.cut N x) * S.cutD2 N x from by unfold fTruncXX; ring]
  exact hu.mul hv

/-! ### Constant bounds on the truncated partials -/

/-- `|a·b| ≤ A·B` from `|a| ≤ A` and `|b| ≤ B`. -/
private lemma abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)

/-- A jointly-continuous `g` is bounded after both arguments pass through the cutoff `φₙ` (which
maps into the compact square `[−M₀(N+1), M₀(N+1)]²`). -/
lemma exists_bound_cut (S : SmoothTrunc) (N : ℕ) {g : ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ ↦ g p.1 p.2) :
    ∃ C : ℝ, ∀ t x, |g (S.cut N t) (S.cut N x)| ≤ C := by
  set r : ℝ := S.M₀ * ((N : ℝ) + 1)
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := -r) (b := r)).prod
    (isCompact_Icc (a := -r) (b := r))).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun t x ↦ ?_⟩
  have hmem : ((S.cut N t, S.cut N x) : ℝ × ℝ) ∈ Set.Icc (-r) r ×ˢ Set.Icc (-r) r :=
    ⟨by rw [Set.mem_Icc, ← abs_le]; exact S.cut_bdd N t,
     by rw [Set.mem_Icc, ← abs_le]; exact S.cut_bdd N x⟩
  have := hC _ hmem
  rwa [Real.norm_eq_abs] at this

lemma fTruncT_bdd (S : SmoothTrunc) (N : ℕ)
    (hcont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2) :
    ∃ C : ℝ, ∀ t x, |fTruncT f_t S N t x| ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_cut S N hcont
  exact ⟨B * S.M₁, fun t x ↦ abs_mul_le_of (hB t x) (S.cutD1_bdd N t)⟩

lemma fTruncX_bdd (S : SmoothTrunc) (N : ℕ)
    (hcont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2) :
    ∃ C : ℝ, ∀ t x, |fTruncX f_x S N t x| ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_cut S N hcont
  exact ⟨B * S.M₁, fun t x ↦ abs_mul_le_of (hB t x) (S.cutD1_bdd N x)⟩

lemma fTruncXX_bdd (S : SmoothTrunc) (N : ℕ)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2) :
    ∃ C : ℝ, ∀ t x, |fTruncXX f_x f_xx S N t x| ≤ C := by
  obtain ⟨Bx, hBx⟩ := exists_bound_cut S N hf_x_cont
  obtain ⟨Bxx, hBxx⟩ := exists_bound_cut S N hf_xx_cont
  refine ⟨Bxx * (S.M₁ * S.M₁) + Bx * S.M₂, fun t x ↦ ?_⟩
  unfold fTruncXX
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_mul_le_of (hBxx t x) (abs_mul_le_of (S.cutD1_bdd N x) (S.cutD1_bdd N x))
  · exact abs_mul_le_of (hBx t x) (S.cutD2_bdd N x)

/-! ### Joint continuity of the partials -/

/-- `p ↦ (φₙ p.1, φₙ p.2)` is continuous. -/
private lemma continuous_cut_pair (S : SmoothTrunc) (N : ℕ) :
    Continuous fun p : ℝ × ℝ ↦ ((S.cut N p.1, S.cut N p.2) : ℝ × ℝ) :=
  ((S.continuous_cut N).comp continuous_fst).prodMk ((S.continuous_cut N).comp continuous_snd)

lemma fTruncT_continuous (S : SmoothTrunc) (N : ℕ)
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2) :
    Continuous fun p : ℝ × ℝ ↦ fTruncT f_t S N p.1 p.2 := by
  simp only [fTruncT]
  exact (hf_t_cont.comp (continuous_cut_pair S N)).mul ((S.continuous_cutD1 N).comp continuous_fst)

lemma fTruncX_continuous (S : SmoothTrunc) (N : ℕ)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2) :
    Continuous fun p : ℝ × ℝ ↦ fTruncX f_x S N p.1 p.2 := by
  simp only [fTruncX]
  exact (hf_x_cont.comp (continuous_cut_pair S N)).mul ((S.continuous_cutD1 N).comp continuous_snd)

lemma fTruncXX_continuous (S : SmoothTrunc) (N : ℕ)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2) :
    Continuous fun p : ℝ × ℝ ↦ fTruncXX f_x f_xx S N p.1 p.2 := by
  simp only [fTruncXX]
  refine ((hf_xx_cont.comp (continuous_cut_pair S N)).mul
    (((S.continuous_cutD1 N).comp continuous_snd).mul
      ((S.continuous_cutD1 N).comp continuous_snd))).add ?_
  exact (hf_x_cont.comp (continuous_cut_pair S N)).mul ((S.continuous_cutD2 N).comp continuous_snd)

/-! ### Cut inactivity — where `|z| ≤ N` the truncation is the identity -/

/-- Where `|z| ≤ N` the cutoff is inert: `φₙ z = z`, `φₙ' z = 1`, `φₙ'' z = 0` (the plateau
`[−(N+1), N+1] ⊋ [−N, N]`). -/
lemma cut_inactive (S : SmoothTrunc) {N : ℕ} {z : ℝ} (hz : |z| ≤ (N : ℝ)) :
    S.cut N z = z ∧ S.cutD1 N z = 1 ∧ S.cutD2 N z = 0 :=
  ⟨S.cut_eq_id_of_abs_le (le_trans hz (by linarith)),
   S.cutD1_eq_one_of_abs_lt (lt_of_le_of_lt hz (by linarith)),
   S.cutD2_eq_zero_of_abs_lt (lt_of_le_of_lt hz (by linarith))⟩

/-- On the inert region `fTrunc N = f`. -/
lemma fTrunc_eq_of (S : SmoothTrunc) {N : ℕ} {s y : ℝ} (hs : |s| ≤ (N : ℝ)) (hy : |y| ≤ (N : ℝ)) :
    fTrunc f S N s y = f s y := by
  unfold fTrunc; rw [(cut_inactive S hs).1, (cut_inactive S hy).1]

/-- On the inert region `fTruncT N = f_t`. -/
lemma fTruncT_eq_of (S : SmoothTrunc) {N : ℕ} {s y : ℝ} (hs : |s| ≤ (N : ℝ))
    (hy : |y| ≤ (N : ℝ)) : fTruncT f_t S N s y = f_t s y := by
  rw [fTruncT, (cut_inactive S hs).1, (cut_inactive S hy).1, (cut_inactive S hs).2.1, mul_one]

/-- On the inert region `fTruncX N = f_x`. -/
lemma fTruncX_eq_of (S : SmoothTrunc) {N : ℕ} {s y : ℝ} (hs : |s| ≤ (N : ℝ))
    (hy : |y| ≤ (N : ℝ)) : fTruncX f_x S N s y = f_x s y := by
  rw [fTruncX, (cut_inactive S hs).1, (cut_inactive S hy).1, (cut_inactive S hy).2.1, mul_one]

/-- On the inert region `fTruncXX N = f_xx`. -/
lemma fTruncXX_eq_of (S : SmoothTrunc) {N : ℕ} {s y : ℝ} (hs : |s| ≤ (N : ℝ))
    (hy : |y| ≤ (N : ℝ)) : fTruncXX f_x f_xx S N s y = f_xx s y := by
  rw [fTruncXX, (cut_inactive S hs).1, (cut_inactive S hy).1, (cut_inactive S hy).2.1,
    (cut_inactive S hy).2.2]
  ring

end SummitC

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The exit time capped at the level: `σ_N = min(τ_N, N)`. Capping the **time** keeps `t ≤ N` on
`{t ≤ σ_N}`, where the truncation's time cut is inert; still a genuine localizing sequence (the
exit times localize, and `min` with `N ↑ ⊤` preserves all three properties). -/
noncomputable def sigmaSeq (B : ℝ≥0 → Ω → ℝ) (N : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  min (exitTime B N ω) ((N : ℝ≥0) : WithTop ℝ≥0)

lemma isLocalizingSequence_sigma (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) :
    IsLocalizingSequence (augFiltration (μ := μ) hBmeas) (fun N ↦ sigmaSeq B N) μ where
  isStoppingTime := fun N ↦
    ((isLocalizingSequence_exitTime hBmeas hBcont).isStoppingTime N).min
      (isStoppingTime_const' _ _)
  tendsto_top := Filter.Eventually.of_forall fun ω ↦ by
    have htop := exitTime_tendsto_top hBcont ω
    rw [WithTop.tendsto_nhds_top_iff] at htop ⊢
    intro c
    have h2 : ∀ᶠ N : ℕ in atTop, (c : WithTop ℝ≥0) < ((N : ℝ≥0) : WithTop ℝ≥0) := by
      filter_upwards [eventually_gt_atTop ⌈c⌉₊] with N hN
      have hcN : (c : ℝ≥0) < (N : ℝ≥0) := lt_of_le_of_lt (Nat.le_ceil c) (by exact_mod_cast hN)
      exact_mod_cast hcN
    filter_upwards [htop c, h2] with N hN1 hN2
    exact lt_min hN1 hN2
  mono := Filter.Eventually.of_forall fun ω _ _ hNM ↦
    min_le_min (exitTime_monotone hBcont ω hNM) (by exact_mod_cast hNM)

end MathFin
