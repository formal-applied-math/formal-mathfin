/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.AdaptedQuadraticVariation
public import MathFin.Foundations.AdaptedRiemannStieltjes
public import MathFin.Foundations.AdaptedDrift
public import MathFin.Foundations.ItoFormulaRemainder

/-! # The Itô process with adapted coefficients, and the convergences behind its Itô formula

Let `B` be a Brownian motion every path of which is continuous, and let `σ` and `b` be bounded
processes, adapted to the natural filtration of `B`, every path of which is continuous. Fix a
horizon `T` and a deterministic starting point `x₀`, and let

`X_t = x₀ + ∫₀ᵗ b_s ds + ∫₀ᵗ σ_s dB_s`

(`adaptedItoProcess`: the pathwise drift integral plus the continuous modification of the
stochastic integral). This module builds the process and proves the three convergences in
measure that Itô's formula for it is assembled from; the formula itself is in
`ItoFormulaAdaptedTD` (`ito_formula_adapted`, `ito_formula_adapted_td_against`), where the
one-variable `f(x)` is the case `f_t = 0` of `f(t, x)`.

`X` is a functional of the path of `B`, not a function of `(t, B_t)`, so the formula does not
reduce to the one for functions of Brownian motion. The classical proof splits `f(X_T) − f(X_0)`
on the uniform partition of `[0, T]` by the discrete formula into sums that converge:

* `∑ f'(X_{tₖ}) ΔAₖ → ∫ f'(X) b ds` on every path where `X` is continuous
  (`tendsto_sum_mul_driftPath_sub`);
* `∑ f'(X_{tₖ}) ΔMₖ → ∫ f'(X) dM` in measure (`tendstoInMeasure_riemannStieltjes`, from the
  mean-square convergence `tendsto_itoIntegralAgainst_stepσ`);
* `∑ f''(X_{tₖ}) (ΔXₖ)² → ∫ f''(X) σ² ds` in measure (`tendstoInMeasure_weighted_qv_adapted`,
  from the `L¹` convergence `tendsto_weighted_qv_adapted`);
* the Taylor remainders, which are controlled by the modulus of continuity of the second
  derivative on the range of the path (`abs_discreteTaylorRemainder_le_of_abs_sub_le`) and the
  uniform smallness of the increments of a continuous path
  (`eventually_abs_sub_unifPart_lt`).

The limits in measure hold almost surely along a common subsequence of partitions.
-/

@[expose] public section

namespace MathFin
namespace ItoFormulaAdapted

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralRiemannBridge
  ItoIntegralBrownian QuadraticVariationL2 ItoIntegralProcessContinuousModification
  AdaptedDrift AdaptedQuadraticVariation AdaptedRiemannStieltjes
  PredictableDensityGeneral StochasticIntegralCharacterisation LpMulIsometry
  AdaptedStochasticIntegralFreezing ItoIntegralAgainstMartingale
open scoped NNReal ENNReal

/-! ### Along one path -/

/-- **The increments of a continuous path over the uniform partition are uniformly small**, for
a fine enough partition: uniform continuity on the compact `[0, T]`. -/
theorem eventually_abs_sub_unifPart_lt (T : ℝ≥0) {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k < n, |x (unifPart T n (k + 1)) - x (unifPart T n k)| < ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hx) ε hε
  filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).eventually_lt_const hδ]
    with n hn k hk
  rw [← Real.dist_eq]
  refine h _ ⟨zero_le, unifPart_le_T hk⟩ _ ⟨zero_le, unifPart_le_T hk.le⟩ ?_
  rwa [NNReal.dist_eq, unifPart_succ_sub, abs_of_nonneg (by positivity)]

/-- **The second-order Taylor remainder under an oscillation bound on `f''`**: if `f''` stays
within `η` of `f''(x)` between `x` and `y`, the remainder is at most `η (y − x)²`. Two
applications of the mean value inequality. -/
theorem abs_discreteTaylorRemainder_le_of_abs_sub_le {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x) {x y η : ℝ}
    (hη : ∀ t ∈ uIcc x y, |f'' t - f'' x| ≤ η) :
    |discreteTaylorRemainder f f' f'' x y| ≤ η * (y - x) ^ 2 := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη x left_mem_uIcc)
  have hd1 (u : ℝ) : HasDerivAt (fun s ↦ f' s - f' x - f'' x * (s - x)) (f'' u - f'' x) u := by
    have h := ((hf' u).sub_const (f' x)).sub
      (((hasDerivAt_id u).sub_const x).const_mul (f'' x))
    simp only [id_eq] at h
    convert h using 1 <;> first | rfl | ring
  have hL1 (t : ℝ) (ht : t ∈ uIcc x y) : |f' t - f' x - f'' x * (t - x)| ≤ η * |y - x| := by
    have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ ↦ (hd1 u).hasDerivWithinAt) (fun u hu ↦ (Real.norm_eq_abs _).trans_le (hη u hu))
      left_mem_uIcc ht
    simp only [Real.norm_eq_abs, sub_self, mul_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc ht) hη0)
  have hd0 (u : ℝ) : HasDerivAt (fun s ↦ f s - f x - f' x * (s - x) - 1 / 2 * f'' x * (s - x) ^ 2)
      (f' u - f' x - f'' x * (u - x)) u := by
    have h := (((hf u).sub_const (f x)).sub
        (((hasDerivAt_id u).sub_const x).const_mul (f' x))).sub
        ((((hasDerivAt_id u).sub_const x).pow 2).const_mul (1 / 2 * f'' x))
    simp only [id_eq] at h
    convert h using 1 <;> first | rfl | ring
  have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ ↦ (hd0 u).hasDerivWithinAt) (fun u hu ↦ (Real.norm_eq_abs _).trans_le (hL1 u hu))
    left_mem_uIcc right_mem_uIcc
  simp only [Real.norm_eq_abs] at h
  rw [show f y - f x - f' x * (y - x) - 1 / 2 * f'' x * (y - x) ^ 2
        - (f x - f x - f' x * (x - x) - 1 / 2 * f'' x * (x - x) ^ 2)
      = discreteTaylorRemainder f f' f'' x y from by unfold discreteTaylorRemainder; ring] at h
  exact h.trans_eq (by rw [mul_assoc, ← sq, sq_abs])

/-! ### Convergence in measure -/

/-- A sequence converging in measure has, inside any subsequence, a further subsequence
converging almost everywhere. -/
theorem exists_seq_tendsto_ae_comp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : ℕ → Ω → ℝ} {g' : Ω → ℝ} (h : TendstoInMeasure μ g atTop g') {ns : ℕ → ℕ}
    (hns : StrictMono ns) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      ∀ᵐ ω ∂μ, Tendsto (fun i ↦ g (ns (ms i)) ω) atTop (𝓝 (g' ω)) :=
  TendstoInMeasure.exists_seq_tendsto_ae fun ε hε ↦ (h ε hε).comp hns.tendsto_atTop

/-- Convergence in `L¹`, stated on integrals of absolute differences, gives convergence in
measure. -/
theorem tendstoInMeasure_of_tendsto_integral_abs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : ℕ → Ω → ℝ} {g' : Ω → ℝ} (hint : ∀ n, Integrable (fun ω ↦ g n ω - g' ω) μ)
    (hg' : AEStronglyMeasurable g' μ)
    (h : Tendsto (fun n ↦ ∫ ω, |g n ω - g' ω| ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ g atTop g' := by
  refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun n ↦ ((hint n).aestronglyMeasurable.add hg').congr
      (ae_of_all _ fun ω ↦ sub_add_cancel (g n ω) (g' ω))) hg' ?_
  have h' := ENNReal.tendsto_ofReal h
  rw [ENNReal.ofReal_zero] at h'
  refine h'.congr fun n ↦ ?_
  rw [eLpNorm_one_eq_lintegral_enorm]
  exact ofReal_integral_norm_eq_lintegral_enorm (hint n)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
  {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C)

/-- **Riemann–Stieltjes sums against `M = φ●B` converge in measure** to the integral against
`M`, for any process `M` that agrees with the Itô integral process almost surely at each time
of `[0, T]`: the mean-square convergence `tendsto_itoIntegralAgainst_stepσ`, read on the
sums. -/
theorem tendstoInMeasure_riemannStieltjes (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    {M : ℝ≥0 → Ω → ℝ} (hM : ∀ t ≤ T, M t =ᵐ[μ] itoProcessCLM hB T t hBmeas φ)
    {w : ℝ≥0 → Ω → ℝ} (hw_pred : IsStronglyPredictable (natFiltration hBmeas) w)
    (hw_cont : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Icc 0 T)) {Cw : ℝ}
    (hw_bdd : ∀ s ω, |w s ω| ≤ Cw) :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ Finset.range n, w (unifPart T n k) ω
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) atTop
      (itoIntegralAgainstCLM hB T hBmeas φ (weightLp T hBmeas φ hw_pred hw_bdd)) := by
  refine (tendstoInMeasure_of_tendsto_Lp
    (tendsto_itoIntegralAgainst_stepσ hB T hBmeas φ hw_pred hw_cont hw_bdd)).congr
    (fun n ↦ (itoIntegralAgainst_stepσ hB T hBmeas φ hw_pred hw_bdd n).trans ?_)
    (EventuallyEq.refl _ _)
  have hMn : ∀ᵐ ω ∂μ, ∀ j : ℕ, j ≤ n →
      M (unifPart T n j) ω = itoProcessCLM hB T (unifPart T n j) hBmeas φ ω := by
    refine ae_all_iff.2 fun j ↦ ?_
    by_cases hj : j ≤ n
    · filter_upwards [hM _ (unifPart_le_T hj)] with ω hω _ using hω
    · exact ae_of_all _ fun ω h ↦ absurd h hj
  filter_upwards [hMn] with ω hω
  exact Finset.sum_congr rfl fun k hk ↦ by
    rw [hω (k + 1) (Finset.mem_range.mp hk), hω k (Finset.mem_range.mp hk).le]

/-- **The weighted quadratic variation of an Itô process converges in measure.** The `L¹`
convergence `tendsto_weighted_qv_adapted`, for a process whose time sections are measurable. -/
theorem tendstoInMeasure_weighted_qv_adapted {X A : ℝ≥0 → Ω → ℝ} {X₀ : Ω → ℝ} {Ca : ℝ}
    (hA : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → ∀ ω, |A t ω - A s ω| ≤ Ca * ((t : ℝ) - s))
    (hX : ∀ t ≤ T, X t =ᵐ[μ] fun ω ↦ X₀ ω + A t ω
      + itoProcessCLM hB T t hBmeas (processToLp T hBmeas hadap hcont hbdd) ω)
    (hX_meas : ∀ t, AEStronglyMeasurable (X t) μ) {w : ℝ≥0 → Ω → ℝ}
    (hw_adap : ∀ s, StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)] (w s))
    (hw_cont : ∀ᵐ ω ∂μ, ContinuousOn (fun s ↦ w s ω) (Icc 0 T)) {Cw : ℝ}
    (hw_bdd : ∀ s ω, |w s ω| ≤ Cw) :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ Finset.range n, w (unifPart T n k) ω
        * (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω) ^ 2) atTop
      fun ω ↦ ∫ s in Ioc 0 T, w s ω * σ s ω ^ 2 ∂timeMeasure := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hw_meas (s : ℝ≥0) : Measurable (w s) :=
    ((hw_adap s).mono ((natFiltration hBmeas).le s)).measurable
  have hσ_meas (s : ℝ≥0) : Measurable (σ s) :=
    ((hadap s).mono ((natFiltration hBmeas).le s)).measurable
  have hW : Integrable (fun ω ↦ ∫ s in Ioc 0 T, w s ω * σ s ω ^ 2 ∂timeMeasure) μ :=
    (memLp_pathIntegral_process_of_ae_continuous (w := fun s ω ↦ w s ω * σ s ω ^ 2)
      (fun s ↦ (hw_meas s).mul ((hσ_meas s).pow_const 2))
      ((abs_nonneg _).trans (abs_mul_sq_le hbdd hw_bdd 0 ω₀)) (abs_mul_sq_le hbdd hw_bdd) T
      (hw_cont.mono fun ω h ↦ h.mul ((hcont ω).pow 2).continuousOn)).integrable one_le_two
  -- each increment of `X` is in `L²`: a bounded drift increment plus an `L²` class
  have hΔ {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) : MemLp (fun ω ↦ X t ω - X s ω) 2 μ := by
    set φ := processToLp (μ := μ) T hBmeas hadap hcont hbdd
    have hI := (Lp.memLp (itoProcessCLM hB T t hBmeas φ)).sub
      (Lp.memLp (itoProcessCLM hB T s hBmeas φ))
    have hAm : MemLp (fun ω ↦ A t ω - A s ω) 2 μ :=
      MemLp.of_bound ((((hX_meas t).sub (hX_meas s)).sub hI.1).congr (by
        filter_upwards [hX t ht, hX s (hst.trans ht)] with ω h1 h2
        simp only [Pi.sub_apply, h1, h2]
        ring)) (Ca * ((t : ℝ) - s)) (ae_of_all _ fun ω ↦ hA hst ω)
    refine (hAm.add hI).ae_eq ?_
    filter_upwards [hX t ht, hX s (hst.trans ht)] with ω h1 h2
    simp only [Pi.add_apply, Pi.sub_apply, h1, h2]
    ring
  refine tendstoInMeasure_of_tendsto_integral_abs (fun n ↦ Integrable.sub
    (integrable_finsetSum _ fun k hk ↦ ?_) hW) hW.1
    (tendsto_weighted_qv_adapted hB T hBmeas hadap hcont hbdd hA hX hw_adap hw_cont hw_bdd)
  have hk' := Finset.mem_range.mp hk
  have hd := hΔ (unifPart_mono T n (Nat.le_succ k)) (unifPart_le_T hk')
  refine (hd.integrable_sq.const_mul Cw).mono'
    ((hw_meas _).aestronglyMeasurable.mul (hd.1.pow 2)) (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]
  exact mul_le_mul_of_nonneg_right (hw_bdd _ ω) (sq_nonneg _)

/-! ### The process -/

variable (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {b : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) {Cb : ℝ} (hb_bdd : ∀ s ω, |b s ω| ≤ Cb) (x₀ : ℝ)

/-- **The Itô process** `X_t = x₀ + ∫₀ᵗ b ds + ∫₀ᵗ φ dB` with drift rate `b` and integrand
class `φ`: the pathwise drift integral plus the continuous modification, at horizon `T`, of the
stochastic integral. It is meant for `t ≤ T`. For a Brownian motion with continuous paths and a
bounded rate with continuous paths, almost every path is continuous on `[0, T]`
(`ae_continuousOn_adaptedItoProcess`). -/
noncomputable def adaptedItoProcess (b : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x₀ + driftPath b t ω + itoContinuousMod T hBmeas φ t ω

include hBcont in
/-- At each time up to `T` the process is `x₀` plus the drift plus the Itô integral, almost
surely. -/
theorem adaptedItoProcess_ae_eq {t : ℝ≥0} (ht : t ≤ T) :
    adaptedItoProcess T hBmeas φ x₀ b t =ᵐ[μ] fun ω ↦ x₀ + driftPath b t ω
      + itoProcessCLM hB T t hBmeas φ ω :=
  (itoContinuousMod_modification hB T hBmeas hBcont φ ht).mono fun ω h ↦
    congrArg (x₀ + driftPath b t ω + ·) h

include hB hBcont in
/-- The process starts at `x₀`, almost surely. -/
theorem adaptedItoProcess_zero : adaptedItoProcess T hBmeas φ x₀ b 0 =ᵐ[μ] fun _ ↦ x₀ := by
  filter_upwards [adaptedItoProcess_ae_eq hB T hBmeas hBcont φ x₀ (b := b) zero_le,
    Lp.coeFn_zero ℝ 2 μ] with ω h h0
  rw [h, itoProcessCLM_zero_time, h0]
  simp [driftPath]

include hB hBcont hb_cont hb_bdd in
/-- Almost every path of the process is continuous on `[0, T]`. -/
theorem ae_continuousOn_adaptedItoProcess :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ adaptedItoProcess T hBmeas φ x₀ b t ω) (Icc 0 T) :=
  (itoContinuousMod_continuousOn hB T hBmeas hBcont φ).mono fun ω h ↦
    (continuous_const.add (continuous_driftPath hb_cont hb_bdd ω)).continuousOn.add h

include hB hBcont hb_adap hb_cont hb_bdd in
/-- The process is predictable for the natural filtration of `B`. -/
theorem adaptedItoProcess_isStronglyPredictable :
    IsStronglyPredictable (natFiltration hBmeas) (adaptedItoProcess T hBmeas φ x₀ b) :=
  StronglyMeasurable.add (stronglyMeasurable_const.add
      (driftPath_isStronglyPredictable hBmeas hb_adap hb_cont hb_bdd))
    (itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ)

include hB hBcont hb_adap hb_cont hb_bdd in
/-- A continuous function of the process is predictable. -/
theorem comp_adaptedItoProcess_isStronglyPredictable {g : ℝ → ℝ} (hg : Continuous g) :
    IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ g (adaptedItoProcess T hBmeas φ x₀ b s ω) :=
  hg.comp_stronglyMeasurable
    (adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hb_adap hb_cont hb_bdd x₀)

include hB hBcont hadap hcont hb_adap hb_cont hb_bdd in
/-- A continuous function of the process, times an adapted process with continuous paths, is
predictable. -/
theorem comp_adaptedItoProcess_mul_isStronglyPredictable {g : ℝ → ℝ} (hg : Continuous g) :
    IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ g (adaptedItoProcess T hBmeas φ x₀ b s ω) * σ s ω :=
  StronglyMeasurable.mul (comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ
      hb_adap hb_cont hb_bdd x₀ hg)
    (StronglyAdapted.isStronglyPredictable_of_leftContinuous hadap
      fun ω _ ↦ (hcont ω).continuousWithinAt)

omit mΩ in
/-- A product of functions bounded by `C₁` and `C` is bounded by `C₁ C`. -/
theorem abs_comp_mul_le {g : ℝ → ℝ} {C₁ C : ℝ} (hg : ∀ x, |g x| ≤ C₁) {σ : ℝ≥0 → Ω → ℝ}
    (hbdd : ∀ t ω, |σ t ω| ≤ C) (X : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) :
    |g (X s ω) * σ s ω| ≤ C₁ * C :=
  (abs_mul _ _).trans_le
    (mul_le_mul (hg _) (hbdd s ω) (abs_nonneg _) ((abs_nonneg _).trans (hg 0)))

end ItoFormulaAdapted
end MathFin
