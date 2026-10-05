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

/-! # Itô's formula for an Itô process with adapted coefficients

Let `B` be a Brownian motion every path of which is continuous, and let `σ` and `b` be bounded
processes, adapted to the natural filtration of `B`, every path of which is continuous. Fix a
horizon `T` and a deterministic starting point `x₀`, and let

`X_t = x₀ + ∫₀ᵗ b_s ds + ∫₀ᵗ σ_s dB_s`

(`adaptedItoProcess`: the pathwise drift integral plus the continuous modification of the
stochastic integral). For `f` twice continuously differentiable with `f'` and `f''` bounded,

`f(X_T) − f(x₀) = ∫₀ᵀ f'(X_s) σ_s dB_s + ∫₀ᵀ (f'(X_s) b_s + ½ f''(X_s) σ_s²) ds`

almost surely (`ito_formula_adapted`).

`X` is a functional of the path of `B`, not a function of `(t, B_t)`, so the formula does not
reduce to the one for functions of Brownian motion. The proof is the classical one. On the
uniform partition of `[0, T]` the discrete formula `discrete_ito_formula` splits
`f(X_T) − f(X_0)` into four sums:

* `∑ f'(X_{tₖ}) ΔAₖ → ∫ f'(X) b ds` on every path where `X` is continuous
  (`tendsto_sum_mul_driftPath_sub`);
* `∑ f'(X_{tₖ}) ΔMₖ → ∫ f'(X) dM` in measure (`tendstoInMeasure_riemannStieltjes`, from the
  mean-square convergence `tendsto_itoIntegralAgainst_stepσ`);
* `∑ f''(X_{tₖ}) (ΔXₖ)² → ∫ f''(X) σ² ds` in measure (`tendstoInMeasure_weighted_qv_adapted`,
  from the `L¹` convergence `tendsto_weighted_qv_adapted`);
* the Taylor remainders, at most `ρ(maxₖ|ΔXₖ|) · ∑ (ΔXₖ)²` for `ρ` the modulus of continuity
  of `f''` on the range of the path, tend to `0` on every continuous path along which
  `∑ (ΔXₖ)²` stays bounded (`tendsto_sum_discreteTaylorRemainder`).

The limits in measure hold almost surely along a common subsequence of partitions. Along it all
four sums converge at almost every `ω`, and the path-level statement `ito_formula_of_tendsto`
finishes.

The statement is at the terminal time `T`, for bounded coefficients and bounded derivatives.
Localisation to unbounded `f'`, `f''` or coefficients is not here.
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

/-- **The Taylor remainders vanish along a continuous path with bounded squared-increment
sums.** The path stays in a compact interval, on which `f''` is uniformly continuous, so once
the increments are small each remainder is at most `η (Δx)²`
(`abs_discreteTaylorRemainder_le_of_abs_sub_le`), and the sum at most `η Q`. -/
theorem tendsto_sum_discreteTaylorRemainder (T : ℝ≥0) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T)) {ν : ℕ → ℕ}
    (hν : Tendsto ν atTop atTop) {Q : ℝ}
    (hQ : ∀ᶠ i in atTop, ∑ k ∈ Finset.range (ν i),
      (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2 ≤ Q) :
    Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), discreteTaylorRemainder f f' f''
      (x (unifPart T (ν i) k)) (x (unifPart T (ν i) (k + 1)))) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hη : 0 < ε / (|Q| + 1) := by positivity
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf''.continuousOn (s := Icc (-R) R)) _ hη
  filter_upwards [hν.eventually (eventually_abs_sub_unifPart_lt T hx hδ), hQ] with i hosc hQi
  have hmem {k : ℕ} (hk : k ≤ ν i) : x (unifPart T (ν i) k) ∈ Icc (-R) R :=
    abs_le.1 (hR _ ⟨zero_le, unifPart_le_T hk⟩)
  rw [Real.dist_eq, sub_zero]
  calc |∑ k ∈ Finset.range (ν i), discreteTaylorRemainder f f' f''
          (x (unifPart T (ν i) k)) (x (unifPart T (ν i) (k + 1)))|
      ≤ ∑ k ∈ Finset.range (ν i), ε / (|Q| + 1)
          * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2 :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk ↦ by
          have hk' := Finset.mem_range.mp hk
          refine abs_discreteTaylorRemainder_le_of_abs_sub_le hf hf' fun t ht ↦ ?_
          rw [← Real.dist_eq]
          refine (hfδ _ (uIcc_subset_Icc (hmem hk'.le) (hmem hk') ht) _ (hmem hk'.le) ?_).le
          rw [Real.dist_eq]
          exact (abs_sub_left_of_mem_uIcc ht).trans_lt (hosc k hk'))
    _ = ε / (|Q| + 1) * ∑ k ∈ Finset.range (ν i),
          (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ ε / (|Q| + 1) * |Q| := by gcongr; exact hQi.trans (le_abs_self Q)
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg Q]

/-- **Itô's formula along one path.** Let `x = c + a + m` be a path continuous on `[0, T]`,
and `f ∈ C²`. If, along a sequence of uniform partitions, the Riemann–Stieltjes sums of `f'(x)`
against `a` and against `m` converge to `D` and `I`, the weighted squared-increment sums with
weight `f''(x)` converge to `W`, and the squared-increment sums stay bounded, then
`f(x_T) − f(x_0) = D + I + ½ W`. The discrete formula holds on each partition, and its Taylor
remainders vanish in the limit. -/
theorem ito_formula_of_tendsto (T : ℝ≥0) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') {x a m : ℝ≥0 → ℝ} {c : ℝ} (hxam : ∀ t, x t = c + a t + m t)
    (hx : ContinuousOn x (Icc 0 T)) {ν : ℕ → ℕ} (hν : Tendsto ν atTop atTop) {D I W Q : ℝ}
    (hD : Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), f' (x (unifPart T (ν i) k))
      * (a (unifPart T (ν i) (k + 1)) - a (unifPart T (ν i) k))) atTop (𝓝 D))
    (hI : Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), f' (x (unifPart T (ν i) k))
      * (m (unifPart T (ν i) (k + 1)) - m (unifPart T (ν i) k))) atTop (𝓝 I))
    (hW : Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), f'' (x (unifPart T (ν i) k))
      * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2) atTop (𝓝 W))
    (hQ : ∀ᶠ i in atTop, ∑ k ∈ Finset.range (ν i),
      (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2 ≤ Q) :
    f (x T) - f (x 0) = D + I + 1 / 2 * W := by
  have hlim := ((hD.add hI).add (hW.const_mul (1 / 2))).add
    (tendsto_sum_discreteTaylorRemainder T hf hf' hf'' hx hν hQ)
  rw [add_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [hν.eventually (eventually_ne_atTop 0)] with i hi
  have h := discrete_ito_formula (ν i) (fun k ↦ x (unifPart T (ν i) k)) f f' f''
  have hT : unifPart T (ν i) (ν i) = T := by simp [unifPart, hi]
  have h0 : unifPart T (ν i) 0 = 0 := by simp [unifPart]
  simp only [hT, h0] at h
  rw [h, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hxam, hxam]
  ring

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

/-! ### The formula -/

variable {f f' f'' : ℝ → ℝ}
  (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
  (hf'' : Continuous f'') {C₁ C₂ : ℝ} (hf1 : ∀ x, |f' x| ≤ C₁) (hf2 : ∀ x, |f'' x| ≤ C₂)

include hf hf'' hf2 in
/-- **Itô's formula, with the stochastic integral taken against `M = σ●B`.** For
`X = x₀ + ∫ b ds + ∫ σ dB` with `σ`, `b` bounded, adapted and path-continuous, and `f ∈ C²`
with `f'`, `f''` bounded, almost surely

`f(X_T) − f(x₀) = ∫₀ᵀ f'(X) dM + ∫₀ᵀ (f'(X_s) b_s + ½ f''(X_s) σ_s²) ds`,

where `∫ f'(X) dM` is the integral against `M` of the class of the weight `f'(X)` (`weightLp`).

Along a subsequence of the uniform partitions the Riemann–Stieltjes sums against `M`, the
weighted quadratic variation and the quadratic variation converge almost surely. On such a path,
where `X` is also continuous, `ito_formula_of_tendsto` applies. -/
theorem ito_formula_adapted_against :
    (fun ω ↦ f (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
        x₀ b T ω) - f x₀) =ᵐ[μ] fun ω ↦
      itoIntegralAgainstCLM hB T hBmeas (processToLp T hBmeas hadap hcont hbdd)
          (weightLp T hBmeas (processToLp T hBmeas hadap hcont hbdd)
            (comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont _ hb_adap hb_cont
              hb_bdd x₀ (Differentiable.continuous fun x ↦ (hf' x).differentiableAt))
            fun s ω ↦ hf1 (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)) ω
        + ∫ s in Ioc 0 T, (f' (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω) * b s ω
            + 1 / 2 * (f'' (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)
              * σ s ω ^ 2)) ∂timeMeasure := by
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  set φ := processToLp (μ := μ) T hBmeas hadap hcont hbdd
  set X := adaptedItoProcess T hBmeas φ x₀ b
  have hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc 0 T) :=
    ae_continuousOn_adaptedItoProcess hB T hBmeas hBcont φ hb_cont hb_bdd x₀
  have hpred : IsStronglyPredictable (natFiltration hBmeas) X :=
    adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hb_adap hb_cont hb_bdd x₀
  have hX (t : ℝ≥0) (ht : t ≤ T) :=
    adaptedItoProcess_ae_eq hB T hBmeas hBcont φ x₀ (b := b) ht
  have hXm (t : ℝ≥0) : AEStronglyMeasurable (X t) μ :=
    ((hpred.stronglyAdapted t).mono ((natFiltration hBmeas).le t)).aestronglyMeasurable
  -- the three limits in measure
  have hM := tendstoInMeasure_riemannStieltjes hB T hBmeas φ
    (fun t ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φ ht)
    (comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hb_adap hb_cont hb_bdd
      x₀ hf'c) (hXc.mono fun ω h ↦ hf'c.comp_continuousOn h) fun s ω ↦ hf1 (X s ω)
  have hW := tendstoInMeasure_weighted_qv_adapted hB T hBmeas hadap hcont hbdd
    (abs_driftPath_sub_le hb_cont hb_bdd) (X₀ := fun _ ↦ x₀) hX hXm
    (fun s ↦ hf''.comp_stronglyMeasurable (hpred.stronglyAdapted s))
    (hXc.mono fun ω h ↦ hf''.comp_continuousOn h) fun s ω ↦ hf2 (X s ω)
  have hQ := tendstoInMeasure_weighted_qv_adapted hB T hBmeas hadap hcont hbdd
    (abs_driftPath_sub_le hb_cont hb_bdd) (X₀ := fun _ ↦ x₀) hX hXm (w := fun _ _ ↦ (1 : ℝ))
    (fun _ ↦ stronglyMeasurable_const) (Eventually.of_forall fun _ ↦ continuousOn_const)
    (Cw := 1) fun _ _ ↦ abs_one.le
  -- a common subsequence along which all three converge almost surely
  obtain ⟨n₁, hn₁, h1⟩ := hM.exists_seq_tendsto_ae
  obtain ⟨n₂, hn₂, h2⟩ := exists_seq_tendsto_ae_comp hW hn₁
  obtain ⟨n₃, hn₃, h3⟩ := exists_seq_tendsto_ae_comp hQ (hn₁.comp hn₂)
  have hν : Tendsto (fun i ↦ n₁ (n₂ (n₃ i))) atTop atTop :=
    hn₁.tendsto_atTop.comp (hn₂.tendsto_atTop.comp hn₃.tendsto_atTop)
  filter_upwards [h1, h2, h3, hXc, adaptedItoProcess_zero hB T hBmeas hBcont φ x₀ (b := b)]
    with ω h1 h2 h3 hc h0
  have key := ito_formula_of_tendsto T hf hf' hf'' (x := fun t ↦ X t ω)
    (a := fun t ↦ driftPath b t ω) (m := fun t ↦ itoContinuousMod T hBmeas φ t ω)
    (fun _ ↦ rfl) hc hν
    ((tendsto_sum_mul_driftPath_sub hb_cont hb_bdd T ω (g := fun s ↦ f' (X s ω))
      (hf'c.comp_continuousOn hc) fun s ↦ hf1 (X s ω)).comp hν)
    (h1.comp (hn₂.tendsto_atTop.comp hn₃.tendsto_atTop)) (h2.comp hn₃.tendsto_atTop)
    ((Tendsto.eventually_lt_const (lt_add_one _) h3).mono fun i hi ↦ by
      simpa only [one_mul, Function.comp_apply] using hi.le)
  rw [show X 0 ω = x₀ from h0] at key
  have hi1 : IntegrableOn (fun s ↦ f' (X s ω) * b s ω) (Ioc 0 T) timeMeasure :=
    (((hf'c.comp_continuousOn hc).mul (hb_cont ω).continuousOn).integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hi2 : IntegrableOn (fun s ↦ f'' (X s ω) * σ s ω ^ 2) (Ioc 0 T) timeMeasure :=
    (((hf''.comp_continuousOn hc).mul ((hcont ω).pow 2).continuousOn).integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [integral_add hi1 (hi2.const_mul _), integral_const_mul]
  linarith

include hf hf'' hf2 in
/-- **Itô's formula for an Itô process with adapted coefficients.** Let `B` be a Brownian
motion with every path continuous, `σ` and `b` bounded, adapted to the natural filtration of `B`
and with every path continuous, and `X = x₀ + ∫ b ds + ∫ σ dB` (`adaptedItoProcess`). For
`f ∈ C²` with `f'` and `f''` bounded, almost surely

`f(X_T) − f(x₀) = ∫₀ᵀ f'(X_s) σ_s dB_s + ∫₀ᵀ (f'(X_s) b_s + ½ f''(X_s) σ_s²) ds`.

The stochastic integral is the Itô integral at horizon `T` of the class of the bounded
predictable process `f'(X)·σ`. -/
theorem ito_formula_adapted :
    (fun ω ↦ f (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
        x₀ b T ω) - f x₀) =ᵐ[μ] fun ω ↦
      itoIntegralCLM_T hB T hBmeas (processToLpPredictable T hBmeas
          (comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont hadap hcont
            (processToLp (μ := μ) T hBmeas hadap hcont hbdd) hb_adap hb_cont hb_bdd x₀
            (Differentiable.continuous fun x ↦ (hf' x).differentiableAt))
          (abs_comp_mul_le hf1 hbdd _)) ω
        + ∫ s in Ioc 0 T, (f' (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω) * b s ω
            + 1 / 2 * (f'' (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)
              * σ s ω ^ 2)) ∂timeMeasure := by
  rw [← itoIntegralAgainst_weightLp hB T hBmeas _
    (comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont _ hb_adap hb_cont hb_bdd
      x₀ (Differentiable.continuous fun x ↦ (hf' x).differentiableAt))
    (fun s ω ↦ hf1 _) _ ?_]
  · exact ito_formula_adapted_against hB T hBmeas hBcont hadap hcont hbdd hb_adap hb_cont hb_bdd
      x₀ hf hf' hf'' hf1 hf2
  · filter_upwards [processToLpPredictable_coeFn (μ := μ) T hBmeas
        (comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont hadap hcont
          (processToLp (μ := μ) T hBmeas hadap hcont hbdd) hb_adap hb_cont hb_bdd x₀
          (Differentiable.continuous fun x ↦ (hf' x).differentiableAt))
        (abs_comp_mul_le hf1 hbdd _),
      processToLp_coeFn (μ := μ) T hBmeas hadap hcont hbdd] with z h1 h2
    rw [h1, h2]
    exact mul_comm _ _

end ItoFormulaAdapted
end MathFin
