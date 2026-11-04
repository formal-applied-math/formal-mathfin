/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoDriftWeightedIsometry
public import MathFin.Foundations.AdaptedDrift

/-! # The drift block of the adapted Itô–drift identity (the discrete route, stage 5d)

`driftSum_expect_tendsto` and `driftBlock_tendsto`: the drift block of the discrete Itô
formula converges to `∫₀ᵀ 𝔼[f'(X_s)·β_s] ds`, by pathwise Riemann–Stieltjes sums
(`AdaptedDrift.tendsto_sum_mul_driftPath_sub`), dominated convergence and the Fubini
interchange `expectation_pathIntegral_eq`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 AdaptedDrift

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The drift block at the expectation level (DCT)**: the expectations of the per-cell
drift sums — `𝔼[∑ₖ g (X tₖ) · (AdaptedDrift.driftPath β tₖ₊₁ − AdaptedDrift.driftPath β tₖ)]`
— converge to the
expectation of the pathwise limit. Route: per-path Riemann–Stieltjes convergence
(`AdaptedDrift.tendsto_sum_mul_driftPath_sub` with weight `s ↦ g (X s ω)`, bounded by `C₁`)
under the global domination `|S_n| ≤ C₁·|D_β|·T` (the drift primitive is `D_β`-Lipschitz
per cell (`AdaptedDrift.abs_driftPath_sub_le`); the cells telescope to `T`;
`|g| ≤ C₁`). -/
theorem driftSum_expect_tendsto (hBmeas : ∀ t, Measurable (B t))
    {β : ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    (hXcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 ↦ X s ω)
    {g : ℝ → ℝ} {C1 : ℝ} (hgcont : Continuous g) (hg1 : ∀ x, |g x| ≤ C1) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ∑ k ∈ Finset.range n, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
      atTop (𝓝 (∫ ω, (∫ s in Set.Ioc (0:ℝ≥0) T, g (X s ω) * β s ω
        ∂ItoIntegralL2.timeMeasure) ∂μ)) := by
  have hC1 : (0:ℝ) ≤ C1 := le_trans (abs_nonneg _) (hg1 0)
  -- measurability of the summands
  have hXm : ∀ t : ℝ≥0, Measurable (X t) :=
    fun t ↦ (hXadap t).measurable.mono ((natFiltration hBmeas).le t) le_rfl
  have hgx : ∀ t : ℝ≥0, Measurable (fun ω ↦ g (X t ω)) :=
    fun t ↦ hgcont.measurable.comp (hXm t)
  have hdp : ∀ t : ℝ≥0, Measurable (driftPath β t) :=
    fun t ↦ (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd t).measurable.mono
      ((natFiltration hBmeas).le t) le_rfl
  have hmeasS : ∀ n : ℕ, Measurable (fun ω ↦ ∑ k ∈ Finset.range n,
      g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)) :=
    fun n ↦ Finset.measurable_sum _ fun k _ ↦
      (hgx _).mul ((hdp _).sub (hdp _))
  -- the uniform bound `|S_n| ≤ C₁·|D_β|·T`
  have hbound : ∀ n : ℕ, ∀ ω : Ω,
      |∑ k ∈ Finset.range n, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)|
      ≤ C1 * |Db| * (T : ℝ) := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
      exact mul_nonneg (mul_nonneg hC1 (abs_nonneg Db)) (NNReal.coe_nonneg T)
    · have hnT : unifPart T n n = T := unifPart_self T hn.ne'
      have h0 : unifPart T n 0 = 0 := unifPart_zero T n
      calc |∑ k ∈ Finset.range n, g (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)|
          ≤ ∑ k ∈ Finset.range n, |g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.range n, |g (X (unifPart T n k) ω)|
              * |driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω| :=
            Finset.sum_congr rfl fun k _ ↦ abs_mul _ _
        _ ≤ ∑ k ∈ Finset.range n, C1 * |driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω| :=
            Finset.sum_le_sum fun k _ ↦
              mul_le_mul_of_nonneg_right (hg1 (X (unifPart T n k) ω)) (abs_nonneg _)
        _ ≤ ∑ k ∈ Finset.range n, C1 * (|Db| * ((unifPart T n (k + 1) : ℝ)
              - unifPart T n k)) :=
            Finset.sum_le_sum fun k hk ↦ by
              refine mul_le_mul_of_nonneg_left ?_ hC1
              have hsub : (0:ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
                sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
              exact (abs_driftPath_sub_le hβcont hβbdd
                (unifPart_mono T n (Nat.le_succ k)) ω).trans
                (mul_le_mul_of_nonneg_right (le_abs_self Db) hsub)
        _ = C1 * |Db| * (T : ℝ) := by
            have hcomm : ∀ k ∈ Finset.range n, C1 * (|Db| * ((unifPart T n (k + 1) : ℝ)
                  - unifPart T n k))
                = (C1 * |Db|) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
              fun k _ ↦ by ring
            rw [Finset.sum_congr rfl hcomm, ← Finset.mul_sum,
              Finset.sum_range_sub (fun k : ℕ ↦ ((unifPart T n k : ℝ))), hnT, h0,
              NNReal.coe_zero, sub_zero]
  refine tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ C1 * |Db| * (T : ℝ))
    (fun n ↦ (hmeasS n).aestronglyMeasurable) (integrable_const _)
    (fun n ↦ Eventually.of_forall fun ω ↦ by
      simpa [Real.norm_eq_abs] using hbound n ω)
    (hXcont.mono fun ω hω ↦ tendsto_sum_mul_driftPath_sub hβcont hβbdd T ω
      (g := fun s ↦ g (X s ω)) (hgcont.comp hω).continuousOn fun s ↦ hg1 (X s ω))

/-- **The drift block** (`driftBlock_tendsto`): for `X` adapted and path-continuous, `g`
continuous with `|g| ≤ C₁`, and `β` bounded adapted path-continuous, the per-cell drift
sums of the adapted assembly converge to the time integral of the means `𝔼[g (X_s) β_s]`,

  `∑ₖ 𝔼[g (X tₖ) · (AdaptedDrift.driftPath β tₖ₊₁ − AdaptedDrift.driftPath β tₖ)]
  → ∫₀ᵀ 𝔼[g (X_s) β_s] ds`.

Route: the DCT convergence `driftSum_expect_tendsto` (per-path Riemann–Stieltjes sums +
global domination) for the expectation-of-sum form, the finite-sum/expectation interchange,
and the stage-1 Fubini lemma `expectation_pathIntegral_eq` crossing the expectation of the
limit integrand. -/
theorem driftBlock_tendsto (hBmeas : ∀ t, Measurable (B t)) {β : ℝ≥0 → Ω → ℝ}
    {X : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    (hXcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 ↦ X s ω)
    {g : ℝ → ℝ} {C1 : ℝ} (hgcont : Continuous g) (hg1 : ∀ x, |g x| ≤ C1) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
      atTop (𝓝 (∫ s in Set.Ioc (0:ℝ≥0) T,
          (∫ ω, g (X s ω) * β s ω ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
  have hC1 : (0:ℝ) ≤ C1 := le_trans (abs_nonneg _) (hg1 0)
  -- the DCT limit in expectation-of-sum form, bridged to sum-of-expectations form
  have hA : Tendsto (fun n : ℕ ↦ ∫ ω, ∑ k ∈ Finset.range n, g (X (unifPart T n k) ω)
      * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
    atTop (𝓝 (∫ ω, (∫ s in Set.Ioc (0:ℝ≥0) T, g (X s ω) * β s ω
      ∂ItoIntegralL2.timeMeasure) ∂μ)) :=
    driftSum_expect_tendsto hBmeas T hβadap hβcont hβbdd hXadap hXcont hgcont hg1
  have hswap : ∀ n : ℕ, (∑ k ∈ Finset.range n, ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
      = ∫ ω, ∑ k ∈ Finset.range n, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ := by
    intro n
    have hint : ∀ k ∈ Finset.range n, Integrable (fun ω ↦ g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)) μ := by
      intro k hk
      have hXk : Measurable (X (unifPart T n k)) :=
        (hXadap (unifPart T n k)).measurable.mono
          ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
      have hdp1 : Measurable (driftPath β (unifPart T n (k + 1))) :=
        (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd
          (unifPart T n (k + 1))).measurable.mono
          ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
      have hdp0 : Measurable (driftPath β (unifPart T n k)) :=
        (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd (unifPart T n k)).measurable.mono
          ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
      have hm : Measurable (fun ω ↦ g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)) :=
        (hgcont.measurable.comp hXk).mul (hdp1.sub hdp0)
      refine Integrable.of_bound hm.aestronglyMeasurable (C1 * |Db| * (T : ℝ) + 1) ?_
      filter_upwards with ω
      change ‖g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)‖
        ≤ C1 * |Db| * (T : ℝ) + 1
      rw [Real.norm_eq_abs, abs_mul]
      have hD : |driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω|
          ≤ |Db| * (T : ℝ) := by
        have hsub : (0:ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
          sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
        have hcellle : (unifPart T n (k + 1) : ℝ) - unifPart T n k ≤ (T : ℝ) := by
          have h1 : ((unifPart T n (k + 1) : ℝ)) ≤ (T : ℝ) :=
            NNReal.coe_le_coe.mpr (unifPart_le_T (Nat.succ_le_of_lt
              (Finset.mem_range.mp hk)))
          have h2 := NNReal.coe_nonneg (unifPart T n k)
          linarith
        exact (abs_driftPath_sub_le hβcont hβbdd
          (unifPart_mono T n (Nat.le_succ k)) ω).trans
          (mul_le_mul (le_abs_self Db) hcellle hsub (abs_nonneg Db))
      refine le_trans
        (mul_le_mul (hg1 (X (unifPart T n k) ω)) hD (abs_nonneg _) hC1) ?_
      linarith
    exact (integral_finsetSum _ hint).symm
  have hB : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ∂μ)
    atTop (𝓝 (∫ ω, (∫ s in Set.Ioc (0:ℝ≥0) T, g (X s ω) * β s ω
      ∂ItoIntegralL2.timeMeasure) ∂μ)) :=
    Tendsto.congr' (Eventually.of_forall fun n ↦ (hswap n).symm) hA
  -- the Fubini interchange on the limit integrand
  have hβm : ∀ t : ℝ≥0, Measurable (β t) :=
    fun t ↦ (hβadap t).measurable.mono ((natFiltration hBmeas).le t) le_rfl
  have hEq := expectation_pathIntegral_eq (μ := μ)
    (w := fun s ω ↦ g (X s ω) * β s ω)
    (fun s ↦ (hgcont.measurable.comp ((hXadap s).measurable.mono
      ((natFiltration hBmeas).le s) le_rfl)).mul (hβm s))
    (hXcont.mono fun ω h ↦ (hgcont.comp h).mul (hβcont ω))
    (mul_nonneg hC1 (abs_nonneg Db))
    (fun s ω ↦ by
      rw [abs_mul]
      exact mul_le_mul (hg1 (X s ω)) (le_trans (hβbdd s ω) (le_abs_self Db))
        (abs_nonneg _) hC1)
    T
  rw [← hEq]
  exact hB

end MathFin.ItoDriftConditional
