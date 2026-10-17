/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Foundations.ItoFormulaItoProcess
public import MathFin.Foundations.ItoIntegralProcessGeneral

/-! # The integrated Itô–drift identity (expectation form of Itô's formula)

The pathwise Itô formula `ito_formula_itoProcess` decomposes `f(X_T) − f(X₀)` into a centered
stochastic integral plus a `ds`-drift integral. This module proves a Fubini interchange and,
with it, the expectation form of that decomposition for the **constant-coefficient** Itô
process `X_t = X₀ + b·t + σ·B_t`:

* `expectation_pathIntegral_eq` — the Fubini interchange `𝔼[∫₀ᵀ g(s,ω) ds] = ∫₀ᵀ 𝔼[g(s,·)] ds`
  for a family with measurable sections, every path continuous, and `|g| ≤ C` everywhere,
  proved by pathwise Riemann sums
  (`tendsto_riemann_continuous`) + dominated convergence on both sides — no product-measure
  machinery, no Tonelli: boundedness makes both DCTs one-liners;
* `ito_drift_expectation_identity` — the integrated Itô–drift identity

  `𝔼[f(X_T)] = 𝔼[f(X₀ + b·0 + σ·B₀)] + ∫₀ᵀ 𝔼[f'(X_s)·b + ½·f''(X_s)·σ²] ds`,

  the expectation form of Itô's formula: integrating the pathwise formula kills the stochastic
  term by centering (`integral_itoIntegralCLM_T`) and interchanges the drift integral with the
  expectation by `expectation_pathIntegral_eq`. For `f` three times differentiable with
  `f'`, `f''`, `f'''` bounded, the exponential-growth hypotheses of `ito_formula_itoProcess`
  hold at `λ = 0`.

An adapted-coefficient analogue, `itoDrift_expectation_identity_adapted`
(`ItoFormulaAdaptedDrift`), assumes rather than constructs a `natFiltration`-adapted version
`M` of the Itô integral of `δ` with every path continuous; it is not used to derive the
constant-coefficient case here. For the process the library constructs, the pathwise formula
for adapted coefficients is `ItoFormulaAdapted.ito_formula_adapted`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral QuadraticVariationL2
  ItoIntegralBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Fubini for the path integral of a bounded path-continuous family** (the interchange the
integrated Itô–drift identity needs):

  `𝔼[∫₀ᵀ g(s, ω) ds] = ∫₀ᵀ 𝔼[g(s, ·)] ds`

for `g` with measurable sections, every `ω`-path continuous, and `|g s ω| ≤ C` for all `s`
and `ω`. Proof shape: pathwise Riemann
sums (`tendsto_riemann_continuous` — deterministic, applied per `ω` and to the deterministic
mean function `s ↦ 𝔼[g s]`) + dominated convergence (dominator `C·T`) for the expectation of
the limit. No product measure, no Tonelli — boundedness makes both DCTs one-liners. -/
theorem expectation_pathIntegral_eq {w : ℝ≥0 → Ω → ℝ}
    (hw_meas : ∀ s, Measurable (w s))
    (hw_cont : ∀ ω, Continuous fun s : ℝ≥0 ↦ w s ω)
    {C : ℝ} (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T : ℝ≥0) :
    ∫ ω, (∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ∂μ
      = ∫ s in Set.Ioc 0 T, (∫ ω, w s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
  -- bounded functions are integrable under the probability measure
  have hint_w : ∀ s, Integrable (w s) μ := fun s ↦
    Integrable.of_bound (hw_meas s).aestronglyMeasurable C
      (Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hw_bdd s ω)
  -- the mean function `s ↦ 𝔼[w s]` is bounded by `C` and continuous in `s`
  have hu_bdd : ∀ s, |∫ ω, w s ω ∂μ| ≤ C := by
    intro s
    calc |∫ ω, w s ω ∂μ| ≤ ∫ ω, |w s ω| ∂μ :=
        MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ ω, C ∂μ := integral_mono_of_nonneg
          (Eventually.of_forall fun ω ↦ abs_nonneg _) (integrable_const C)
          (Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hw_bdd s ω)
      _ = C := by rw [integral_const]; simp
  have hu_cont : Continuous fun s : ℝ≥0 ↦ ∫ ω, w s ω ∂μ :=
    continuous_iff_continuousAt.2 fun s₀ ↦
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (bound := fun _ : Ω ↦ C)
        (Eventually.of_forall fun s ↦ (hw_meas s).aestronglyMeasurable)
        (Eventually.of_forall fun s ↦ Eventually.of_forall fun ω ↦ by
          simpa [Real.norm_eq_abs] using hw_bdd s ω)
        (integrable_const C)
        (Eventually.of_forall fun ω ↦ (hw_cont ω).continuousAt)
  -- pathwise Riemann convergence per `ω` (the tower's deterministic lemma,
  -- applied to each `ω`-path) and for the deterministic mean function
  have hpath : ∀ ω : Ω, Tendsto
      (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
          w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      atTop (𝓝 (∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure)) :=
    fun ω ↦ tendsto_riemann_continuous (h := fun s : ℝ≥0 ↦ w s ω) (hw_cont ω) T
      (fun s _ ↦ hw_bdd s ω)
  have hdet : Tendsto
      (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω ∂μ) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      atTop (𝓝 (∫ s in Set.Ioc 0 T, (∫ ω, w s ω ∂μ) ∂ItoIntegralL2.timeMeasure)) :=
    tendsto_riemann_continuous (h := fun s : ℝ≥0 ↦ ∫ ω, w s ω ∂μ) hu_cont T
      (fun s _ ↦ hu_bdd s)
  -- measurability / integrability of the Riemann sums
  have hmeas_R : ∀ n : ℕ, Measurable (fun ω ↦ ∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) := fun n ↦
    Finset.measurable_sum _ fun k _ ↦ (hw_meas _).mul_const _
  have hint_R : ∀ n : ℕ, Integrable (fun ω ↦ ∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) μ := fun n ↦
    integrable_finsetSum _ fun k _ ↦ (hint_w _).mul_const _
  -- domination of the Riemann sums: `|R_n(ω)| ≤ C·T`
  have hR_bound : ∀ n : ℕ, ∀ ω : Ω,
      |∑ k ∈ Finset.range n,
          w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
        ≤ C * (T : ℝ) := by
    intro n ω
    have hCT : (0 : ℝ) ≤ C * (T : ℝ) := mul_nonneg hC0 (NNReal.coe_nonneg T)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
      exact hCT
    · have hΔ : ∀ k : ℕ, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ≥ 0 :=
        fun k ↦ sub_nonneg.mpr (by exact_mod_cast unifPart_mono T n (Nat.le_succ k))
      have hnn : unifPart T n n = T := by
        have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
        simp only [unifPart, div_self hne, one_mul]
      calc |∑ k ∈ Finset.range n,
            w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
          ≤ ∑ k ∈ Finset.range n,
            |w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.range n,
            |w (unifPart T n k) ω| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
            Finset.sum_congr rfl fun k _ ↦ by rw [abs_mul, abs_of_nonneg (hΔ k)]
        _ ≤ ∑ k ∈ Finset.range n, C * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
            Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right (hw_bdd _ ω) (hΔ k)
        _ = C * ∑ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
            (Finset.mul_sum (Finset.range n)
              (fun k ↦ ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) C).symm
        _ = C * ((unifPart T n n : ℝ) - unifPart T n 0) := by
            rw [Finset.sum_range_sub (fun k ↦ ((unifPart T n k : ℝ)))]
        _ = C * (T : ℝ) := by
            rw [hnn]
            simp only [unifPart, Nat.cast_zero, zero_div, zero_mul, NNReal.coe_zero,
              sub_zero]
  -- dominated convergence: `𝔼[R_n] → 𝔼[∫ w]`
  have hdct : Tendsto (fun n : ℕ ↦ ∫ ω, (∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ∂μ)
      atTop (𝓝 (∫ ω, (∫ s in Set.Ioc 0 T, w s ω ∂ItoIntegralL2.timeMeasure) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ C * (T : ℝ))
      (fun n ↦ (hmeas_R n).aestronglyMeasurable) (integrable_const _)
      (fun n ↦ Eventually.of_forall fun (ω : Ω) ↦ by
        simpa [Real.norm_eq_abs] using hR_bound n ω)
      (Eventually.of_forall fun ω ↦ hpath ω)
  -- the deterministic Riemann sums have the same values as `𝔼[R_n]` (finite sums),
  -- so the deterministic limit must be `𝔼[∫ w]`
  have hsum_eq : ∀ n : ℕ,
      ∫ ω, (∑ k ∈ Finset.range n,
          w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ∂μ
        = ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω ∂μ) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    intro n
    rw [integral_finsetSum _ fun k _ ↦ (hint_w _).mul_const _]
    exact Finset.sum_congr rfl fun k _ ↦ integral_mul_const _ _
  have hdet' : Tendsto (fun n : ℕ ↦ ∫ ω, (∑ k ∈ Finset.range n,
      w (unifPart T n k) ω * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ∂μ)
      atTop (𝓝 (∫ s in Set.Ioc 0 T, (∫ ω, w s ω ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
    refine hdet.congr' ?_
    exact Eventually.of_forall fun n ↦ (hsum_eq n).symm
  exact (tendsto_nhds_unique hdet' hdct).symm

/-- **The integrated Itô–drift identity, constant-coefficient case.** For the
constant-coefficient Itô process `X_t = X₀ + b·t + σ·B_t` and `f` three times differentiable
with `f'`, `f''`, `f'''` bounded,

  `𝔼[f(X_T)] = 𝔼[f(X₀ + b·0 + σ·B₀)] + ∫₀ᵀ 𝔼[f'(X_s)·b + ½·f''(X_s)·σ²] ds`.

Route: `ito_formula_itoProcess` (the pathwise a.e. Itô formula) gives
`f(X_T) − f(X₀) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ g(s,·) ds` with the stochastic term the genuine
Itô integral of `σ·f'(X_·)`; integrating kills the stochastic term by centering
(`integral_itoIntegralCLM_T`) and interchanges the drift integral with the expectation by
`expectation_pathIntegral_eq`. The derivative bounds instantiate the exponential-growth
hypotheses of `ito_formula_itoProcess` at `λ = 0`. -/
theorem ito_drift_expectation_identity
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    (T : ℝ≥0) (X₀ b σ : ℝ) {f f' f'' f''' : ℝ → ℝ}
    (hf' : ∀ x, HasDerivAt f (f' x) x) (hf'' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 C2 C3 : ℝ} (hg' : ∀ x, |f' x| ≤ C1) (hg'' : ∀ x, |f'' x| ≤ C2)
    (hg''' : ∀ x, |f''' x| ≤ C3) :
    ∫ ω, f (X₀ + b * (T : ℝ) + σ * B T ω) ∂μ
      = ∫ ω, f (X₀ + b * (0 : ℝ) + σ * B 0 ω) ∂μ
        + ∫ s in Set.Ioc 0 T,
            (∫ ω, f' (X₀ + b * (s : ℝ) + σ * B s ω) * b
                + (1 / 2) * (f'' (X₀ + b * (s : ℝ) + σ * B s ω) * σ ^ 2) ∂μ)
          ∂ItoIntegralL2.timeMeasure := by
  have hC1 : (0 : ℝ) ≤ C1 := le_trans (abs_nonneg _) (hg' 0)
  -- continuity of `f`, `f'`, `f''` (one higher derivative each)
  have hfcont : Continuous f := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf'' x).differentiableAt
  have hf''c : Continuous f'' := Differentiable.continuous fun x ↦ (hf''' x).differentiableAt
  -- the drift weight process `g`, in the exact shape of the formula's drift term
  set g : ℝ≥0 → Ω → ℝ := fun s ω ↦ f' (X₀ + b * (s : ℝ) + σ * B s ω) * b
      + (1 / 2) * (f'' (X₀ + b * (s : ℝ) + σ * B s ω) * σ ^ 2) with hg_def
  -- measurability of the inner argument and of the weight sections
  have harg_meas : ∀ s : ℝ≥0, Measurable (fun ω ↦ X₀ + b * (s : ℝ) + σ * B s ω) :=
    fun s ↦ ((hBmeas s).const_mul σ).const_add (X₀ + b * (s : ℝ))
  have hg_meas : ∀ s, Measurable (g s) := fun s ↦
    ((hf'c.measurable.comp (harg_meas s)).mul_const b).add
      (((hf''c.measurable.comp (harg_meas s)).mul_const (σ ^ 2)).const_mul (1 / 2))
  -- path continuity of the weight
  have harg_cont : ∀ ω : Ω, Continuous fun s : ℝ≥0 ↦ X₀ + b * (s : ℝ) + σ * B s ω :=
    fun ω ↦ (continuous_const.add (continuous_const.mul NNReal.continuous_coe)).add
      (continuous_const.mul (hBcont ω))
  have hg_cont : ∀ ω : Ω, Continuous fun s : ℝ≥0 ↦ g s ω := fun ω ↦
    ((hf'c.comp (harg_cont ω)).mul continuous_const).add
      (((hf''c.comp (harg_cont ω)).mul continuous_const).const_mul (1 / 2))
  -- boundedness: `|g| ≤ |b|·C₁ + ½·σ²·C₂`
  have hC2 : (0 : ℝ) ≤ C2 := le_trans (abs_nonneg _) (hg'' 0)
  have hG0 : (0 : ℝ) ≤ |b| * C1 + (1 / 2) * (σ ^ 2 * C2) :=
    add_nonneg (mul_nonneg (abs_nonneg b) hC1)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (mul_nonneg (sq_nonneg σ) hC2))
  have hg_bdd : ∀ s ω, |g s ω| ≤ |b| * C1 + (1 / 2) * (σ ^ 2 * C2) := by
    intro s ω
    have h1 : |f' (X₀ + b * (s : ℝ) + σ * B s ω) * b| ≤ |b| * C1 := by
      rw [abs_mul]
      calc |f' (X₀ + b * (s : ℝ) + σ * B s ω)| * |b|
          ≤ C1 * |b| := mul_le_mul_of_nonneg_right (hg' _) (abs_nonneg b)
        _ = |b| * C1 := mul_comm _ _
    have h2 : |(1 / 2) * (f'' (X₀ + b * (s : ℝ) + σ * B s ω) * σ ^ 2)|
        ≤ (1 / 2) * (σ ^ 2 * C2) := by
      have habs : |(1 / 2) * (f'' (X₀ + b * (s : ℝ) + σ * B s ω) * σ ^ 2)|
          = (1 / 2) * (|f'' (X₀ + b * (s : ℝ) + σ * B s ω)| * |σ ^ 2|) := by
        rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
      have hσ : |σ ^ 2| = σ ^ 2 := abs_of_nonneg (sq_nonneg σ)
      rw [habs, hσ]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hg'' _) (sq_nonneg σ)
    calc |g s ω| ≤ |f' (X₀ + b * (s : ℝ) + σ * B s ω) * b|
          + |(1 / 2) * (f'' (X₀ + b * (s : ℝ) + σ * B s ω) * σ ^ 2)| :=
        by simpa only [Real.norm_eq_abs] using abs_add_le _ _
      _ ≤ |b| * C1 + (1 / 2) * (σ ^ 2 * C2) := add_le_add h1 h2
  -- `f` has linear growth from the `|f'| ≤ C₁` bound; hence `f(X_t)` is integrable
  have hf_lin : ∀ x, |f x| ≤ |f 0| + C1 * |x| := by
    intro x
    have hmv : |f x - f 0| ≤ C1 * |x| := by
      have h := abs_sub_le_of_hasDerivAt (g := f) (g' := f') hf' hg' 0 x
      simpa using h
    calc |f x| = |f 0 + (f x - f 0)| := by congr 1; ring
      _ ≤ |f 0| + |f x - f 0| := abs_add_le _ _
      _ ≤ |f 0| + C1 * |x| := by linarith
  have hB_int : ∀ t : ℝ≥0, Integrable (B t) μ :=
    fun t ↦ (memLp_eval hB t).integrable one_le_two
  have hfX_int : ∀ t : ℝ≥0, Integrable (fun ω ↦ f (X₀ + b * (t : ℝ) + σ * B t ω)) μ := by
    intro t
    have hmeas : AEStronglyMeasurable (fun ω ↦ f (X₀ + b * (t : ℝ) + σ * B t ω)) μ :=
      (hfcont.measurable.comp (harg_meas t)).aestronglyMeasurable
    have habsB : Integrable (fun ω ↦ |B t ω|) μ := by
      have h := (memLp_eval hB t).norm.integrable one_le_two
      simpa [Real.norm_eq_abs] using h
    have hdom : Integrable (fun ω ↦ (|f 0| + C1 * (|X₀| + |b| * (t : ℝ)))
        + C1 * |σ| * |B t ω|) μ :=
      (integrable_const _).add (habsB.const_mul (C1 * |σ|))
    refine Integrable.mono' hdom hmeas (Eventually.of_forall fun ω ↦ ?_)
    have harg : |X₀ + b * (t : ℝ) + σ * B t ω| ≤ |X₀| + |b| * (t : ℝ) + |σ| * |B t ω| := by
      calc |X₀ + b * (t : ℝ) + σ * B t ω| ≤ |X₀ + b * (t : ℝ)| + |σ * B t ω| :=
            abs_add_le _ _
        _ ≤ (|X₀| + |b * (t : ℝ)|) + |σ * B t ω| := by
            have := abs_add_le X₀ (b * (t : ℝ)); linarith
        _ = |X₀| + |b| * (t : ℝ) + |σ| * |B t ω| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (NNReal.coe_nonneg t)]
    calc |f (X₀ + b * (t : ℝ) + σ * B t ω)|
        ≤ |f 0| + C1 * |X₀ + b * (t : ℝ) + σ * B t ω| := hf_lin _
      _ ≤ |f 0| + C1 * (|X₀| + |b| * (t : ℝ) + |σ| * |B t ω|) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left harg hC1)
      _ = (|f 0| + C1 * (|X₀| + |b| * (t : ℝ))) + C1 * |σ| * |B t ω| := by ring
  -- the Itô formula at the bounded (λ = 0) exponential-growth class
  have hgrowth : ∀ h : ℝ → ℝ, (∀ x, |h x| ≤ max C1 (max C2 C3)) →
      ∀ x, |h x| ≤ max C1 (max C2 C3) * Real.exp (0 * |x|) := by
    intro h hh x
    have hz : (0 : ℝ) * |x| = 0 := zero_mul _
    rw [hz, Real.exp_zero, mul_one]
    exact hh x
  have hb1 : ∀ x, |f' x| ≤ max C1 (max C2 C3) * Real.exp (0 * |x|) :=
    hgrowth f' fun x ↦ le_trans (hg' x) (le_max_left C1 (max C2 C3))
  have hb2 : ∀ x, |f'' x| ≤ max C1 (max C2 C3) * Real.exp (0 * |x|) :=
    hgrowth f'' fun x ↦ le_trans (hg'' x) (le_max_of_le_right (le_max_left C2 C3))
  have hb3 : ∀ x, |f''' x| ≤ max C1 (max C2 C3) * Real.exp (0 * |x|) :=
    hgrowth f''' fun x ↦ le_trans (hg''' x)
      (le_max_of_le_right (le_max_of_le_right le_rfl))
  obtain ⟨gfx, _, hId⟩ := ito_formula_itoProcess hB hBmeas hBcont T X₀ b σ hf' hf'' hf'''
    (lam := 0) (C := max C1 (max C2 C3)) (by norm_num : (0 : ℝ) ≤ 0) hb1 hb2 hb3
  -- the stochastic term is integrable (an L² element under a probability measure)
  have hsto_int : Integrable (fun ω ↦ (itoIntegralCLM_T hB T hBmeas gfx) ω) μ :=
    (Lp.memLp (itoIntegralCLM_T hB T hBmeas gfx)).integrable one_le_two
  -- the drift term is integrable (bounded path integral)
  have hdrift_int : Integrable (fun ω ↦ ∫ s in Set.Ioc 0 T, g s ω
      ∂ItoIntegralL2.timeMeasure) μ :=
    (memLp_pathIntegral_process hg_meas hg_cont hG0 hg_bdd T).integrable one_le_two
  -- integrate the a.e. identity; centering kills the stochastic term, Fubini
  -- interchanges the drift integral with the expectation
  have hfX0 : Integrable (fun ω ↦ f (X₀ + b * (0 : ℝ) + σ * B 0 ω)) μ := hfX_int 0
  have hmain : ∫ ω, f (X₀ + b * (T : ℝ) + σ * B T ω) ∂μ
      - ∫ ω, f (X₀ + b * (0 : ℝ) + σ * B 0 ω) ∂μ
      = ∫ s in Set.Ioc 0 T, (∫ ω, g s ω ∂μ) ∂ItoIntegralL2.timeMeasure := by
    calc ∫ ω, f (X₀ + b * (T : ℝ) + σ * B T ω) ∂μ
          - ∫ ω, f (X₀ + b * (0 : ℝ) + σ * B 0 ω) ∂μ
        = ∫ ω, (f (X₀ + b * (T : ℝ) + σ * B T ω)
            - f (X₀ + b * (0 : ℝ) + σ * B 0 ω)) ∂μ := by
          rw [integral_sub (hfX_int T) hfX0]
      _ = ∫ ω, (itoIntegralCLM_T hB T hBmeas gfx) ω
            + ∫ s in Set.Ioc 0 T, g s ω ∂ItoIntegralL2.timeMeasure ∂μ :=
          MeasureTheory.integral_congr_ae hId
      _ = ∫ ω, (itoIntegralCLM_T hB T hBmeas gfx) ω ∂μ
            + ∫ ω, (∫ s in Set.Ioc 0 T, g s ω ∂ItoIntegralL2.timeMeasure) ∂μ :=
          integral_add hsto_int hdrift_int
      _ = ∫ ω, (∫ s in Set.Ioc 0 T, g s ω ∂ItoIntegralL2.timeMeasure) ∂μ := by
          rw [integral_itoIntegralCLM_T hB T hBmeas gfx, zero_add]
      _ = ∫ s in Set.Ioc 0 T, (∫ ω, g s ω ∂μ) ∂ItoIntegralL2.timeMeasure :=
          expectation_pathIntegral_eq hg_meas hg_cont hG0 hg_bdd T
  linarith [hmain]

end MathFin
