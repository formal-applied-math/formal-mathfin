/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaAdapted
public import MathFin.Foundations.ItoFormulaUnrestricted
public import MathFin.Foundations.ItoIntegralCrossHorizon
public import MathFin.Foundations.LocalisationInMeasure

/-! # Itô's formula for `f(t, X_t)` along an Itô process with adapted coefficients

Let `X = x₀ + ∫ b ds + M`, `M = ∫ σ dB` (`adaptedItoProcess`), with `σ`, `b` bounded, adapted and
path-continuous, and let `f(t, x)` have partial derivatives `f_t`, `f_x`, `f_xx`, each jointly
continuous. For `t ≤ T` the left-point Riemann–Stieltjes sums
`∑ f_x(tₖ, X_{tₖ}) (M_{tₖ₊₁} − M_{tₖ})` on the uniform partitions of `[0, t]` converge in
probability to

`f(t, X_t) − f(0, x₀) − ∫₀ᵗ (f_t + f_x b + ½ f_xx σ²)(s, X_s) ds`

(`ito_formula_adapted_td_local_le`). No bound on `f` or its derivatives is assumed, so
`∫ f_x(·, X) dM` cannot be the `L²` Itô integral: it is the limit in probability of the sums, and
the theorem says that the limit exists. A `C²` function `f(x)` is the case `f_t = 0`
(`ito_formula_adapted_local_le`). When `f'` is continuous and bounded the same sums on `[0, T]`
converge in probability to the `L²` Itô integral of `f'(X)·σ`, the integral of `ito_formula_adapted`
(`tendstoInMeasure_riemannStieltjes_itoIntegral`): where both readings of `∫ f'(X) dM` are
defined, they are limits in probability of the same sums.

* **Along one path** (`ito_formula_td_of_tendsto`). The discrete formula
  `discrete_ito_formula_2d` adds the sum `∑ f_t Δt` to those of the time-independent case. Its
  remainder is at most `η Δt + η (ΔX)²` once `f_t` and `f_xx` oscillate by less than `η` on a cell
  (`abs_discreteTaylorRemainder2D_le_of_osc`), so the remainders vanish along a continuous path
  with bounded quadratic variation: uniform continuity on the compact `[0, T] × [−R, R]`
  (`tendsto_sum_discreteTaylorRemainder2D`). No third derivative is needed.
* **Bounded partials** (`ito_formula_adapted_td_against`). The sums converge as in
  `ito_formula_adapted_against`, the weights `f_x(s, X_s)` and `f_xx(s, X_s)` being predictable as
  continuous functions of the time and of the process
  (`comp_time_adaptedItoProcess_isStronglyPredictable`), and `∑ f_t Δt` converges pathwise as a
  Riemann–Stieltjes sum against the drift path of the rate `1`.
* **Localisation in space** (`ito_formula_adapted_td_local`). The double cutoff `SummitC.fTrunc`,
  which `ItoFormulaUnrestricted` built for functions of Brownian motion, is `f` on
  `[0, T] × [−N, N]` once its level exceeds `T` and `N`, and has bounded partials. On the event
  that the path of `X` stays in `[−N, N]` up to `T` the Riemann sums of `f` and of the cutoff
  coincide; the events exhaust `Ω` in probability (`tendsto_measure_compl_abs_le`), and
  convergence in measure is local (`tendstoInMeasure_of_eqOn`).
* **Each `t ≤ T`** (`ito_formula_adapted_td_local_le`), from the formula at horizon `t`. The
  martingale parts built at horizons `t` and `T` are almost surely the same path on `[0, t]`
  (`ae_itoContinuousMod_eq_of_le`): their `L²` integrals agree at each time
  (`itoProcessCLM_consist`) and both continuous modifications are continuous on `[0, t]`.

`ItoFormulaAdaptedUnbounded` removes the bounds on `σ` and `b`, and `ItoFormulaAdaptedProcess`
states the formula as an identity of processes (all `t` at once, almost surely).
-/

@[expose] public section

namespace MathFin
namespace ItoFormulaAdapted

open MeasureTheory ProbabilityTheory Filter Topology Set
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral ItoIntegralBrownian
  QuadraticVariationL2 ItoIntegralProcessContinuousModification AdaptedDrift AdaptedRiemannStieltjes
  AdaptedQuadraticVariation ItoIntegralAgainstMartingale SummitC LocalisationInMeasure
open scoped NNReal ENNReal

/-! ### Along one path -/

/-- **The time-dependent Taylor remainder under oscillation bounds.** If `f_t` stays within `η`
of `f_t(t₀, x)` on `[t₀, t₁] × {y}`, and `f_xx(t₀, ·)` stays within `η` of `f_xx(t₀, x)` between
`x` and `y`, the remainder of `discrete_ito_formula_2d` is at most `η |t₁ − t₀| + η (y − x)²`:
the time increment at frozen space `y` by the mean value inequality, and the space remainder of
the `t₀`-section by `abs_discreteTaylorRemainder_le_of_abs_sub_le`. -/
theorem abs_discreteTaylorRemainder2D_le_of_osc {f f_t f_x f_xx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x) {t₀ t₁ x y η : ℝ}
    (hηt : ∀ s ∈ uIcc t₀ t₁, |f_t s y - f_t t₀ x| ≤ η)
    (hηx : ∀ u ∈ uIcc x y, |f_xx t₀ u - f_xx t₀ x| ≤ η) :
    |discreteTaylorRemainder2D f f_t f_x f_xx t₀ t₁ x y|
      ≤ η * |t₁ - t₀| + η * (y - x) ^ 2 := by
  have hsplit : discreteTaylorRemainder2D f f_t f_x f_xx t₀ t₁ x y
      = (f t₁ y - f_t t₀ x * t₁ - (f t₀ y - f_t t₀ x * t₀))
        + discreteTaylorRemainder (fun u ↦ f t₀ u) (fun u ↦ f_x t₀ u) (fun u ↦ f_xx t₀ u) x y := by
    unfold discreteTaylorRemainder2D discreteTaylorRemainder
    ring
  have hd (s : ℝ) : HasDerivAt (fun r ↦ f r y - f_t t₀ x * r) (f_t s y - f_t t₀ x) s :=
    ((hf_t s y).sub ((hasDerivAt_id s).const_mul (f_t t₀ x))).congr_deriv (by simp)
  have h1 := (convex_uIcc t₀ t₁).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ ↦ (hd s).hasDerivWithinAt) (fun s hs ↦ (Real.norm_eq_abs _).trans_le (hηt s hs))
    left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h1
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add h1
    (abs_discreteTaylorRemainder_le_of_abs_sub_le (fun u ↦ hf_x t₀ u) (fun u ↦ hf_xx t₀ u) hηx))

/-- **The time-dependent Taylor remainders vanish along a continuous path with bounded
squared-increment sums**, for `f_t` and `f_xx` jointly continuous. On the compact
`[0, T] × [−R, R]` holding the path they are uniformly continuous, so once the mesh and the
increments are small every remainder is at most `η Δt + η (Δx)²`
(`abs_discreteTaylorRemainder2D_le_of_osc`), and the sum at most `η (T + Q)`. -/
theorem tendsto_sum_discreteTaylorRemainder2D (T : ℝ≥0) {f f_t f_x f_xx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)
    {x : ℝ≥0 → ℝ} (hx : ContinuousOn x (Icc 0 T)) {ν : ℕ → ℕ}
    (hν : Tendsto ν atTop atTop) {Q : ℝ}
    (hQ : ∀ᶠ i in atTop, ∑ k ∈ Finset.range (ν i),
      (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2 ≤ Q) :
    Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), discreteTaylorRemainder2D f f_t f_x f_xx
      (unifPart T (ν i) k) (unifPart T (ν i) (k + 1))
      (x (unifPart T (ν i) k)) (x (unifPart T (ν i) (k + 1)))) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  set K : Set (ℝ × ℝ) := Icc 0 (T : ℝ) ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hη : 0 < ε / ((T : ℝ) + |Q| + 1) := by positivity
  obtain ⟨δt, hδt, hft⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hf_t_cont.continuousOn) _ hη
  obtain ⟨δx, hδx, hfx⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hf_xx_cont.continuousOn) _ hη
  have hδ : 0 < min δt δx := lt_min hδt hδx
  filter_upwards [hν.eventually (eventually_abs_sub_unifPart_lt T hx hδ),
    hν.eventually ((tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)).eventually_lt_const hδ), hQ]
    with i hosc hmesh hQi
  set η := ε / ((T : ℝ) + |Q| + 1) with hηdef
  have hmem {k : ℕ} (hk : k ≤ ν i) :
      ((unifPart T (ν i) k : ℝ), x (unifPart T (ν i) k)) ∈ K :=
    ⟨⟨(unifPart T (ν i) k).2, NNReal.coe_le_coe.2 (unifPart_le_T hk)⟩,
      abs_le.1 (hR _ ⟨zero_le, unifPart_le_T hk⟩)⟩
  have hstep {k : ℕ} (hk : k < ν i) :
      |discreteTaylorRemainder2D f f_t f_x f_xx (unifPart T (ν i) k) (unifPart T (ν i) (k + 1))
        (x (unifPart T (ν i) k)) (x (unifPart T (ν i) (k + 1)))|
        ≤ η * ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k)
          + η * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2 := by
    have hle : (unifPart T (ν i) k : ℝ) ≤ unifPart T (ν i) (k + 1) :=
      NNReal.coe_le_coe.2 (unifPart_mono T (ν i) (Nat.le_succ k))
    have hdt : ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k) = (T : ℝ) / (ν i) := by
      rw [unifPart_succ_sub]
    refine (abs_discreteTaylorRemainder2D_le_of_osc hf_t hf_x hf_xx (fun s hs ↦ ?_)
      (fun u hu ↦ ?_)).trans_eq (by rw [abs_of_nonneg (sub_nonneg.2 hle)])
    · rw [uIcc_of_le hle] at hs
      have h := hft (s, x (unifPart T (ν i) (k + 1)))
        ⟨⟨(unifPart T (ν i) k).2.trans hs.1,
          hs.2.trans (NNReal.coe_le_coe.2 (unifPart_le_T hk))⟩, (hmem (Nat.succ_le_of_lt hk)).2⟩
        _ (hmem hk.le) (by
          rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq,
            abs_of_nonneg (sub_nonneg.2 hs.1)]
          exact ⟨by linarith [hs.2, hmesh, min_le_left δt δx],
            (hosc k hk).trans_le (min_le_left _ _)⟩)
      simpa only [Real.dist_eq] using h.le
    · have h := hfx ((unifPart T (ν i) k : ℝ), u)
        ⟨(hmem hk.le).1, uIcc_subset_Icc (hmem hk.le).2 (hmem (Nat.succ_le_of_lt hk)).2 hu⟩ _
        (hmem hk.le) (by
          rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, sub_self, abs_zero]
          exact ⟨hδx, ((abs_sub_left_of_mem_uIcc hu).trans_lt (hosc k hk)).trans_le
            (min_le_right _ _)⟩)
      simpa only [Real.dist_eq] using h.le
  have hsum_t : ∑ k ∈ Finset.range (ν i),
      ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k) ≤ T := by
    rw [Finset.sum_range_sub (fun k ↦ (unifPart T (ν i) k : ℝ))]
    have h0 : unifPart T (ν i) 0 = 0 := unifPart_zero T (ν i)
    rw [h0, NNReal.coe_zero, sub_zero]
    exact NNReal.coe_le_coe.2 (unifPart_le_T le_rfl)
  rw [Real.dist_eq, sub_zero]
  calc _ ≤ ∑ k ∈ Finset.range (ν i), (η * ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k)
          + η * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2) :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun k hk ↦ hstep (Finset.mem_range.1 hk))
    _ = η * ∑ k ∈ Finset.range (ν i), ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k)
          + η * ∑ k ∈ Finset.range (ν i),
            (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ η * T + η * |Q| := add_le_add (mul_le_mul_of_nonneg_left hsum_t hη.le)
        (mul_le_mul_of_nonneg_left (hQi.trans (le_abs_self Q)) hη.le)
    _ < ε := by
        have h : η * ((T : ℝ) + |Q| + 1) = ε := by
          rw [hηdef]
          exact div_mul_cancel₀ ε (by positivity)
        linarith

/-- **Itô's formula along one path, for `f(t, x)`.** Let `x = c + a + m` be a path continuous on
`[0, T]`, and `f` with partials `f_t`, `f_x`, `f_xx`, `f_t` and `f_xx` jointly continuous. If
along a sequence of uniform partitions the Riemann sums of `f_t(t, x_t)` against `dt` and of
`f_x(t, x_t)` against `a` and against `m` converge to `E`, `D` and `I`, the weighted
squared-increment sums with weight `f_xx(t, x_t)` converge to `W`, and the squared-increment sums
stay bounded, then `f(T, x_T) − f(0, x_0) = E + D + I + ½ W`. -/
theorem ito_formula_td_of_tendsto (T : ℝ≥0) {f f_t f_x f_xx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)
    {x a m : ℝ≥0 → ℝ} {c : ℝ} (hxam : ∀ t, x t = c + a t + m t)
    (hx : ContinuousOn x (Icc 0 T)) {ν : ℕ → ℕ} (hν : Tendsto ν atTop atTop) {E D I W Q : ℝ}
    (hE : Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), f_t (unifPart T (ν i) k)
      (x (unifPart T (ν i) k)) * ((unifPart T (ν i) (k + 1) : ℝ) - unifPart T (ν i) k))
      atTop (𝓝 E))
    (hD : Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), f_x (unifPart T (ν i) k)
      (x (unifPart T (ν i) k)) * (a (unifPart T (ν i) (k + 1)) - a (unifPart T (ν i) k)))
      atTop (𝓝 D))
    (hI : Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), f_x (unifPart T (ν i) k)
      (x (unifPart T (ν i) k)) * (m (unifPart T (ν i) (k + 1)) - m (unifPart T (ν i) k)))
      atTop (𝓝 I))
    (hW : Tendsto (fun i ↦ ∑ k ∈ Finset.range (ν i), f_xx (unifPart T (ν i) k)
      (x (unifPart T (ν i) k)) * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2)
      atTop (𝓝 W))
    (hQ : ∀ᶠ i in atTop, ∑ k ∈ Finset.range (ν i),
      (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k)) ^ 2 ≤ Q) :
    f T (x T) - f 0 (x 0) = E + D + I + 1 / 2 * W := by
  have hlim := (((hE.add hD).add hI).add (hW.const_mul (1 / 2))).add
    (tendsto_sum_discreteTaylorRemainder2D T hf_t hf_x hf_xx hf_t_cont hf_xx_cont hx hν hQ)
  rw [add_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [hν.eventually (eventually_ne_atTop 0)] with i hi
  have h := discrete_ito_formula_2d (ν i) (fun k ↦ (unifPart T (ν i) k : ℝ))
    (fun k ↦ x (unifPart T (ν i) k)) f f_t f_x f_xx
  have hT : unifPart T (ν i) (ν i) = T := unifPart_self T hi
  have h0 : unifPart T (ν i) 0 = 0 := unifPart_zero T (ν i)
  simp only [hT, h0, NNReal.coe_zero] at h
  have hsplit : ∑ k ∈ Finset.range (ν i), f_x (unifPart T (ν i) k) (x (unifPart T (ν i) k))
        * (x (unifPart T (ν i) (k + 1)) - x (unifPart T (ν i) k))
      = ∑ k ∈ Finset.range (ν i), f_x (unifPart T (ν i) k) (x (unifPart T (ν i) k))
          * (a (unifPart T (ν i) (k + 1)) - a (unifPart T (ν i) k))
        + ∑ k ∈ Finset.range (ν i), f_x (unifPart T (ν i) k) (x (unifPart T (ν i) k))
          * (m (unifPart T (ν i) (k + 1)) - m (unifPart T (ν i) k)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← mul_add]
    congr 1
    rw [hxam (unifPart T (ν i) (k + 1)), hxam (unifPart T (ν i) k)]
    ring
  rw [h, hsplit]
  ring

/-! ### The process -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
  {σ : ℝ≥0 → Ω → ℝ}
  (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
  (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C)
  (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {b : ℝ≥0 → Ω → ℝ}
  (hb_adap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (b t))
  (hb_cont : ∀ ω, Continuous fun s ↦ b s ω) {Cb : ℝ} (hb_bdd : ∀ s ω, |b s ω| ≤ Cb) (x₀ : ℝ)

include hB hBcont hb_adap hb_cont hb_bdd in
/-- A jointly continuous function of the time and the process is predictable. -/
theorem comp_time_adaptedItoProcess_isStronglyPredictable {g : ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ ↦ g p.1 p.2) :
    IsStronglyPredictable (natFiltration hBmeas)
      fun s ω ↦ g s (adaptedItoProcess T hBmeas φ x₀ b s ω) := by
  have ht : IsStronglyPredictable (natFiltration hBmeas) fun (s : ℝ≥0) (_ : Ω) ↦ (s : ℝ) :=
    StronglyAdapted.isStronglyPredictable_of_leftContinuous (fun _ ↦ stronglyMeasurable_const)
      fun _ _ ↦ NNReal.continuous_coe.continuousWithinAt
  exact hg.comp_stronglyMeasurable (StronglyMeasurable.prodMk ht
    (adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hb_adap hb_cont hb_bdd x₀))

/-! ### The horizon -/

include hB hBcont in
/-- **The martingale part does not depend on the horizon.** For `t ≤ T` the continuous
modifications of `M = ∫ σ dB` built at horizons `t` and `T` are almost surely the same path on
`[0, t]`: they are modifications of each other there (`itoProcessCLM_consist`), and both paths are
continuous on `[0, t]` (`ae_forall_eq_of_continuousOn`). -/
theorem ae_itoContinuousMod_eq_of_le {t : ℝ≥0} (ht : t ≤ T) :
    ∀ᵐ ω ∂μ, ∀ s ∈ Icc 0 t,
      itoContinuousMod t hBmeas (processToLp (μ := μ) t hBmeas hadap hcont hbdd) s ω
        = itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd) s ω := by
  set φT := processToLp (μ := μ) T hBmeas hadap hcont hbdd
  set φt := processToLp (μ := μ) t hBmeas hadap hcont hbdd
  have hmod (s : ℝ≥0) (hs : s ≤ t) : (fun ω ↦ itoContinuousMod t hBmeas φt s ω)
      =ᵐ[μ] fun ω ↦ itoContinuousMod T hBmeas φT s ω := by
    have hLp := itoProcessCLM_consist hB hBmeas hs ht hadap hcont hbdd
    refine ((itoContinuousMod_modification hB t hBmeas hBcont φt hs).trans
      (Eventually.of_forall fun ω ↦ ?_)).trans
      (itoContinuousMod_modification hB T hBmeas hBcont φT (hs.trans ht)).symm
    rw [hLp]
  exact ae_forall_eq_of_continuousOn (itoContinuousMod_continuousOn hB t hBmeas hBcont φt)
    ((itoContinuousMod_continuousOn hB T hBmeas hBcont φT).mono fun ω h ↦
      h.mono (Icc_subset_Icc_right ht))
    fun s hs ↦ hmod s hs.2

variable {T hBmeas x₀} in
/-- Two Itô processes with the same start and drift whose martingale parts agree on a set of
times agree there. -/
theorem adaptedItoProcess_eq_of_eqOn {T' : ℝ≥0} {φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)}
    {φ' : Lp ℝ 2 (trimMeasure_T (μ := μ) T' hBmeas)} {ω : Ω} {S : Set ℝ≥0}
    (h : ∀ s ∈ S, itoContinuousMod T' hBmeas φ' s ω = itoContinuousMod T hBmeas φ s ω)
    {s : ℝ≥0} (hs : s ∈ S) :
    adaptedItoProcess T' hBmeas φ' x₀ b s ω = adaptedItoProcess T hBmeas φ x₀ b s ω := by
  simp only [adaptedItoProcess, h s hs]

/-! ### The formula with bounded partials -/

variable {f f_t f_x f_xx : ℝ → ℝ → ℝ}
  (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
  (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
  (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
  (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
  (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
  (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)

include hB hBcont hb_adap hb_cont hb_bdd hf_t hf_x hf_xx hf_t_cont hf_xx_cont in
/-- **Itô's formula for `f(t, X_t)` with bounded partials, the stochastic integral taken against
`M = σ●B`.** For `f` with jointly continuous partials `f_t`, `f_x`, `f_xx`, all bounded, almost
surely

`f(T, X_T) − f(0, x₀) = ∫₀ᵀ f_x(s, X_s) dM_s + ∫₀ᵀ (f_t + f_x b + ½ f_xx σ²)(s, X_s) ds`,

where `∫ f_x(·, X) dM` is the integral against `M` of the class of the weight `f_x(s, X_s)`
(`weightLp`). -/
theorem ito_formula_adapted_td_against {Ct C₁ C₂ : ℝ} (hbt : ∀ t x, |f_t t x| ≤ Ct)
    (hbx : ∀ t x, |f_x t x| ≤ C₁) (hbxx : ∀ t x, |f_xx t x| ≤ C₂) :
    (fun ω ↦ f T (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
        x₀ b T ω) - f 0 x₀) =ᵐ[μ] fun ω ↦
      itoIntegralAgainstCLM hB T hBmeas (processToLp T hBmeas hadap hcont hbdd)
          (weightLp T hBmeas (processToLp T hBmeas hadap hcont hbdd)
            (comp_time_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) hb_adap hb_cont hb_bdd x₀
              hf_x_cont)
            fun s ω ↦ hbx s (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)) ω
        + ∫ s in Ioc 0 T, (f_t s (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)
            + f_x s (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω) * b s ω
            + 1 / 2 * (f_xx s (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)
              * σ s ω ^ 2)) ∂timeMeasure := by
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
  -- a jointly continuous function of time and of a path continuous on `[0, T]`
  have hcomp {g : ℝ → ℝ → ℝ} (hg : Continuous fun p : ℝ × ℝ ↦ g p.1 p.2) {ω : Ω}
      (hω : ContinuousOn (fun t ↦ X t ω) (Icc 0 T)) :
      ContinuousOn (fun s : ℝ≥0 ↦ g s (X s ω)) (Icc 0 T) :=
    hg.comp_continuousOn (NNReal.continuous_coe.continuousOn.prodMk hω)
  have hadapt {g : ℝ → ℝ → ℝ} (hg : Continuous fun p : ℝ × ℝ ↦ g p.1 p.2) (s : ℝ≥0) :
      StronglyMeasurable[(natFiltration hBmeas s : MeasurableSpace Ω)]
        fun ω ↦ g s (X s ω) :=
    (hg.comp (by fun_prop : Continuous fun x : ℝ ↦ ((s : ℝ), x))).comp_stronglyMeasurable
      (hpred.stronglyAdapted s)
  -- the three limits in measure
  have hM := tendstoInMeasure_riemannStieltjes hB T hBmeas φ
    (fun t ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φ ht)
    (comp_time_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hb_adap hb_cont
      hb_bdd x₀ hf_x_cont) (hXc.mono fun ω h ↦ hcomp hf_x_cont h) fun s ω ↦ hbx s (X s ω)
  have hW := tendstoInMeasure_weighted_qv_adapted hB T hBmeas hadap hcont hbdd
    (abs_driftPath_sub_le hb_cont hb_bdd) (X₀ := fun _ ↦ x₀) hX hXm
    (w := fun s ω ↦ f_xx s (X s ω)) (hadapt hf_xx_cont)
    (hXc.mono fun ω h ↦ hcomp hf_xx_cont h) fun s ω ↦ hbxx s (X s ω)
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
  -- the `dt` sums, as sums against the drift path of the rate `1`
  have hE := (tendsto_sum_mul_driftPath_sub (b := fun (_ : ℝ≥0) (_ : Ω) ↦ (1 : ℝ))
    (fun _ ↦ continuous_const) (fun _ _ ↦ abs_one.le) T ω (hcomp hf_t_cont hc)
    fun s ↦ hbt s (X s ω)).comp hν
  simp only [driftPath_one, mul_one] at hE
  have key := ito_formula_td_of_tendsto T hf_t hf_x hf_xx hf_t_cont hf_xx_cont
    (x := fun t ↦ X t ω) (a := fun t ↦ driftPath b t ω)
    (m := fun t ↦ itoContinuousMod T hBmeas φ t ω) (fun _ ↦ rfl) hc hν hE
    ((tendsto_sum_mul_driftPath_sub hb_cont hb_bdd T ω (g := fun s ↦ f_x s (X s ω))
      (hcomp hf_x_cont hc) fun s ↦ hbx s (X s ω)).comp hν)
    (h1.comp (hn₂.tendsto_atTop.comp hn₃.tendsto_atTop)) (h2.comp hn₃.tendsto_atTop)
    ((Tendsto.eventually_lt_const (lt_add_one _) h3).mono fun i hi ↦ by
      simpa only [one_mul, Function.comp_apply] using hi.le)
  rw [show X 0 ω = x₀ from h0] at key
  have hint {g : ℝ≥0 → ℝ} (hg : ContinuousOn g (Icc 0 T)) : IntegrableOn g (Ioc 0 T) timeMeasure :=
    (hg.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hi0 : IntegrableOn (fun s : ℝ≥0 ↦ f_t s (X s ω)) (Ioc 0 T) timeMeasure :=
    hint (hcomp hf_t_cont hc)
  have hi1 : IntegrableOn (fun s : ℝ≥0 ↦ f_x s (X s ω) * b s ω) (Ioc 0 T) timeMeasure :=
    hint ((hcomp hf_x_cont hc).mul (hb_cont ω).continuousOn)
  have hi2 : IntegrableOn (fun s : ℝ≥0 ↦ f_xx s (X s ω) * σ s ω ^ 2) (Ioc 0 T) timeMeasure :=
    hint ((hcomp hf_xx_cont hc).mul ((hcont ω).pow 2).continuousOn)
  have hi01 : IntegrableOn (fun s : ℝ≥0 ↦ f_t s (X s ω) + f_x s (X s ω) * b s ω) (Ioc 0 T)
      timeMeasure := hi0.add hi1
  rw [integral_add hi01 (hi2.const_mul _), integral_add hi0 hi1, integral_const_mul]
  linarith

/-! ### Localisation -/

include hB hBcont hb_adap hb_cont hb_bdd hf_t hf_x hf_xx hf_t_cont hf_x_cont hf_xx_cont in
/-- **Itô's formula for `f(t, X_t)` along an Itô process with adapted coefficients.** Let `B` be
a Brownian motion with every path continuous, `σ` and `b` bounded, adapted to the natural
filtration of `B` and with every path continuous, `X = x₀ + ∫ b ds + M` with `M = ∫ σ dB`, and
`f(t, x)` with jointly continuous partials `f_t`, `f_x`, `f_xx`. Then the left-point
Riemann–Stieltjes sums of `f_x(t, X_t)` against `M` on the uniform partitions of `[0, T]`
converge in probability to

`f(T, X_T) − f(0, x₀) − ∫₀ᵀ (f_t + f_x b + ½ f_xx σ²)(s, X_s) ds`.

No bound on `f` or its partials is assumed. -/
theorem ito_formula_adapted_td_local :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ Finset.range n,
        f_x (unifPart T n k) (adaptedItoProcess T hBmeas
          (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b (unifPart T n k) ω)
        * (itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
            (unifPart T n (k + 1)) ω
          - itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
            (unifPart T n k) ω)) atTop
      fun ω ↦ f T (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
          x₀ b T ω) - f 0 x₀
        - ∫ s in Ioc 0 T, (f_t s (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)
            + f_x s (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω) * b s ω
            + 1 / 2 * (f_xx s (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)
              * σ s ω ^ 2)) ∂timeMeasure := by
  set φ := processToLp (μ := μ) T hBmeas hadap hcont hbdd
  set X := adaptedItoProcess T hBmeas φ x₀ b
  have hpred : IsStronglyPredictable (natFiltration hBmeas) X :=
    adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hb_adap hb_cont hb_bdd x₀
  have hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc 0 T) :=
    ae_continuousOn_adaptedItoProcess hB T hBmeas hBcont φ hb_cont hb_bdd x₀
  obtain ⟨S⟩ := smoothTrunc_exists
  -- the cutoff level `L N ≥ N, T`, so that on `[0, T] × [−N, N]` the cutoff is inert
  set L : ℕ → ℕ := fun N ↦ N + ⌈(T : ℝ)⌉₊
  have hLN (N : ℕ) : (N : ℝ) ≤ L N := by simp [L]
  have hLT (N : ℕ) {s : ℝ≥0} (hs : s ≤ T) : |(s : ℝ)| ≤ L N := by
    rw [abs_of_nonneg s.coe_nonneg]
    calc (s : ℝ) ≤ T := hs
      _ ≤ ⌈(T : ℝ)⌉₊ := Nat.le_ceil _
      _ ≤ L N := by simp [L]
  choose Ct hCt using fun N ↦ fTruncT_bdd (f_t := f_t) S (L N) hf_t_cont
  choose C₁ hC₁ using fun N ↦ fTruncX_bdd (f_x := f_x) S (L N) hf_x_cont
  choose C₂ hC₂ using fun N ↦ fTruncXX_bdd (f_x := f_x) (f_xx := f_xx) S (L N) hf_x_cont
    hf_xx_cont
  have hxc (N : ℕ) := fTruncX_continuous S (L N) hf_x_cont
  refine tendstoInMeasure_of_eqOn (A := fun N : ℕ ↦ {ω | ∀ t ∈ Icc 0 T, |X t ω| ≤ N})
    (tendsto_measure_compl_abs_le (fun t ↦ ((hpred.stronglyAdapted t).mono
      ((natFiltration hBmeas).le t)).measurable) hXc)
    (fun N ↦ tendstoInMeasure_riemannStieltjes hB T hBmeas φ
      (fun t ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φ ht)
      (comp_time_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φ hb_adap hb_cont
        hb_bdd x₀ (hxc N))
      (hXc.mono fun ω h ↦ (hxc N).comp_continuousOn
        (NNReal.continuous_coe.continuousOn.prodMk h))
      fun s ω ↦ hC₁ N s (X s ω))
    (fun N n ω hω ↦ Finset.sum_congr rfl fun k hk ↦ ?_) fun N ↦ ?_
  · have hk' : unifPart T n k ≤ T := unifPart_le_T (Finset.mem_range.1 hk).le
    rw [fTruncX_eq_of S (hLT N hk') ((hω _ ⟨zero_le, hk'⟩).trans (hLN N))]
  filter_upwards [ito_formula_adapted_td_against hB T hBmeas hBcont hadap hcont hbdd hb_adap
      hb_cont hb_bdd x₀ (fTrunc_hasDerivAt_t hf_t S (L N)) (fTrunc_hasDerivAt_x hf_x S (L N))
      (fTrunc_hasDerivAt_xx hf_xx S (L N)) (fTruncT_continuous S (L N) hf_t_cont) (hxc N)
      (fTruncXX_continuous S (L N) hf_x_cont hf_xx_cont) (hCt N) (hC₁ N) (hC₂ N),
    adaptedItoProcess_zero hB T hBmeas hBcont φ x₀ (b := b)] with ω hk h0 hω
  have hx₀ : |x₀| ≤ L N := by
    rw [← show X 0 ω = x₀ from h0]
    exact (hω 0 ⟨le_rfl, zero_le⟩).trans (hLN N)
  have hXT : |X T ω| ≤ L N := (hω T ⟨zero_le, le_rfl⟩).trans (hLN N)
  have hint : ∫ s in Ioc 0 T, (fTruncT f_t S (L N) s (X s ω)
          + fTruncX f_x S (L N) s (X s ω) * b s ω
          + 1 / 2 * (fTruncXX f_x f_xx S (L N) s (X s ω) * σ s ω ^ 2)) ∂timeMeasure
      = ∫ s in Ioc 0 T, (f_t s (X s ω) + f_x s (X s ω) * b s ω
          + 1 / 2 * (f_xx s (X s ω) * σ s ω ^ 2)) ∂timeMeasure := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    have hsT := hLT N hs.2
    have hXs := (hω s (Ioc_subset_Icc_self hs)).trans (hLN N)
    simp only [fTruncT_eq_of S hsT hXs, fTruncX_eq_of S hsT hXs, fTruncXX_eq_of S hsT hXs]
  rw [fTrunc_eq_of S (hLT N le_rfl) hXT, fTrunc_eq_of S (by simp) hx₀, hint] at hk
  linarith

include hB hBcont hb_adap hb_cont hb_bdd hf_t hf_x hf_xx hf_t_cont hf_x_cont hf_xx_cont in
/-- **Itô's formula for `f(t, X_t)` at every time `t ≤ T`.** For the process `X = x₀ + ∫ b ds + M`
built at horizon `T`, `t ≤ T`, and `f(t, x)` with jointly continuous partials `f_t`, `f_x`,
`f_xx`, the left-point Riemann–Stieltjes sums of `f_x(s, X_s)` against `M` on the uniform
partitions of `[0, t]` converge in probability to

`f(t, X_t) − f(0, x₀) − ∫₀ᵗ (f_t + f_x b + ½ f_xx σ²)(s, X_s) ds`. -/
theorem ito_formula_adapted_td_local_le {t : ℝ≥0} (ht : t ≤ T) :
    TendstoInMeasure μ (fun n ω ↦ ∑ k ∈ Finset.range n,
        f_x (unifPart t n k) (adaptedItoProcess T hBmeas
          (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b (unifPart t n k) ω)
        * (itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
            (unifPart t n (k + 1)) ω
          - itoContinuousMod T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
            (unifPart t n k) ω)) atTop
      fun ω ↦ f t (adaptedItoProcess T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd)
          x₀ b t ω) - f 0 x₀
        - ∫ s in Ioc 0 t, (f_t s (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)
            + f_x s (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω) * b s ω
            + 1 / 2 * (f_xx s (adaptedItoProcess T hBmeas
              (processToLp (μ := μ) T hBmeas hadap hcont hbdd) x₀ b s ω)
              * σ s ω ^ 2)) ∂timeMeasure := by
  have hM := ae_itoContinuousMod_eq_of_le hB T hBmeas hBcont hadap hcont hbdd ht
  refine (ito_formula_adapted_td_local hB t hBmeas hBcont hadap hcont hbdd hb_adap hb_cont
    hb_bdd x₀ hf_t hf_x hf_xx hf_t_cont hf_x_cont hf_xx_cont).congr (fun n ↦ ?_) ?_
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

/-! ### `C²` functions of the process -/

include hB hBcont hb_adap hb_cont hb_bdd in
/-- **Itô's formula for a `C²` function of an Itô process with adapted coefficients.** Let `B` be
a Brownian motion with every path continuous, `σ` and `b` bounded, adapted to the natural
filtration of `B` and with every path continuous, `X = x₀ + ∫ b ds + M` with `M = ∫ σ dB` built at
horizon `T` (`adaptedItoProcess`, `itoContinuousMod`), and `f` twice differentiable with `f''`
continuous. For `t ≤ T` the left-point Riemann–Stieltjes sums of `f'(X)` against `M` on the
uniform partitions of `[0, t]` converge in probability to

`f(X_t) − f(x₀) − ∫₀ᵗ (f'(X_s) b_s + ½ f''(X_s) σ_s²) ds`.

No bound on `f'` or `f''` is assumed. The case `f_t = 0` of `ito_formula_adapted_td_local_le`. -/
theorem ito_formula_adapted_local_le {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hf'' : Continuous f'') {t : ℝ≥0} (ht : t ≤ T) :
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
  have hf'c : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  refine (ito_formula_adapted_td_local_le hB T hBmeas hBcont hadap hcont hbdd hb_adap hb_cont
    hb_bdd x₀ (f := fun _ x ↦ f x) (f_t := fun _ _ ↦ 0) (fun t x ↦ hasDerivAt_const t (f x))
    (fun _ x ↦ hf x) (fun _ x ↦ hf' x) continuous_const (hf'c.comp continuous_snd)
    (hf''.comp continuous_snd) ht).congr_right (Eventually.of_forall fun ω ↦ ?_)
  simp only [zero_add]

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
  set φT := processToLp (μ := μ) T hBmeas hadap hcont hbdd
  have hpred := comp_adaptedItoProcess_isStronglyPredictable hB T hBmeas hBcont φT hb_adap
    hb_cont hb_bdd x₀ hf'c
  rw [← itoIntegralAgainst_weightLp hB T hBmeas φT hpred (fun s ω ↦ hf1 _) _ ?_]
  · exact tendstoInMeasure_riemannStieltjes hB T hBmeas φT
      (fun t ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φT ht) hpred
      ((ae_continuousOn_adaptedItoProcess hB T hBmeas hBcont φT hb_cont hb_bdd x₀).mono
        fun ω h ↦ hf'c.comp_continuousOn h) fun s ω ↦ hf1 _
  · filter_upwards [processToLpPredictable_coeFn (μ := μ) T hBmeas
        (comp_adaptedItoProcess_mul_isStronglyPredictable hB T hBmeas hBcont hadap hcont φT
          hb_adap hb_cont hb_bdd x₀ hf'c) (abs_comp_mul_le hf1 hbdd _),
      processToLp_coeFn (μ := μ) T hBmeas hadap hcont hbdd] with z h1 h2
    rw [h1, h2]
    exact mul_comm _ _

end ItoFormulaAdapted
end MathFin
