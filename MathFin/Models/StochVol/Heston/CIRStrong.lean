/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.SDEStability

/-!
# Strong existence for the CIR equation on every finite horizon

The regularized equations `dV = κ(θ - V) dt + ξ g_ε(V) dB`, `g_ε(x) = √(x⁺ + ε) - √ε`, have
Lipschitz coefficients and hence global strong solutions (`exists_lipschitz_sde_solution`).  Along
the schedule `ε_n = e^{-2(n+1)}`:

* the Yamada estimate gives `E|V^n_t - V^k_t| ≤ (1 + 10ξ²T)/(N+1)` for `n, k ≥ N`;
* hence the diffusion integrands `H_n = ξ g_{ε_n}(V^n)` are Cauchy in `L²`;
* the `L²` stability estimate (Gronwall) makes the processes `V^n` Cauchy in `L²`;
* the limits `V^∞, H^∞` satisfy `H^∞ = ξ √(V^∞⁺)` (a.e. subsequence), and the Itô process with
  drift `κ(θ - V^∞)` and diffusion `H^∞` is `V^∞` itself.

The limit solves the CIR equation, is nonnegative, and is pathwise unique.

## Main definitions

* `cirEps`
* `cirKH`
* `cirKL`

## Main results

* `exists_cir_strong_solution`
* `cir_strong_solution_unique`
* `ae_bounded_of_continuousOn`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace MathFin.Heston
open MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open MathFin MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM MathFin.ItoIntegralProcessGeneral
open MathFin.ItoIntegralProcessContinuousModification MathFin.ItoFormulaAdapted
open MathFin.AdaptedDrift MathFin.ItoIntegralAgainstMartingale

/-! ## The regularization schedule -/

/-- `ε_n = e^{-2(n+1)}`. -/
def cirEps (n : ℕ) : ℝ := Real.exp (-(2 * ((n : ℝ) + 1)))

theorem cirEps_pos (n : ℕ) : 0 < cirEps n := Real.exp_pos _

theorem exp_neg_le_one_div {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hx (by linarith [Real.add_one_le_exp x])

theorem cirEps_mul_exp_le {N n : ℕ} (hn : N ≤ n) :
    cirEps n * Real.exp ((N : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  unfold cirEps
  rw [← Real.exp_add]
  calc Real.exp (-(2 * ((n : ℝ) + 1)) + ((N : ℝ) + 1)) ≤ Real.exp (-((N : ℝ) + 1)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / ((N : ℝ) + 1) := exp_neg_le_one_div (by positivity)

theorem cirEps_le {N n : ℕ} (hn : N ≤ n) : cirEps n ≤ 1 / ((N : ℝ) + 1) := by
  have h1 : 1 ≤ Real.exp ((N : ℝ) + 1) := Real.one_le_exp (by positivity)
  have h2 := cirEps_mul_exp_le hn
  have h3 := cirEps_pos n
  nlinarith

theorem tendsto_cirEps : Tendsto cirEps atTop (𝓝 0) :=
  squeeze_zero (fun n => (cirEps_pos n).le) (fun n => cirEps_le (le_refl n))
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem continuous_cirRegularizedDiffusion (p : Parameters) (ε : ℝ) :
    Continuous (cirRegularizedDiffusion p ε) := by
  unfold cirRegularizedDiffusion cirApproxDiff
  exact continuous_const.mul ((Real.continuous_sqrt.comp
    ((continuous_id.max continuous_const).add continuous_const)).sub continuous_const)

theorem continuous_cirSqrtDiffusion (p : Parameters) : Continuous (cirSqrtDiffusion p) := by
  unfold cirSqrtDiffusion
  exact continuous_const.mul (Real.continuous_sqrt.comp (continuous_id.max continuous_const))

/-- `ξ g_{ε_i}(x_i) → ξ √(x⁺)` when `ε_i → 0`, `x_i → x`. -/
theorem tendsto_cirRegularizedDiffusion (p : Parameters) {ε x : ℕ → ℝ} {x₀ : ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun i => cirRegularizedDiffusion p (ε i) (x i)) atTop
      (𝓝 (cirSqrtDiffusion p x₀)) := by
  have hc : Continuous fun q : ℝ × ℝ => p.xi * (Real.sqrt (max q.2 0 + q.1) - Real.sqrt q.1) :=
    continuous_const.mul ((Real.continuous_sqrt.comp
      ((continuous_snd.max continuous_const).add continuous_fst)).sub
      (Real.continuous_sqrt.comp continuous_fst))
  have h := (hc.tendsto (0, x₀)).comp (hε.prodMk_nhds hx)
  simpa [Function.comp_def, cirRegularizedDiffusion, cirApproxDiff, cirSqrtDiffusion] using h

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

section Regularized
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

include hB hBcont in
/-- The regularized CIR equation has a global `L²` solution, in `l2ItoProcess` form. -/
theorem exists_cir_regularized_l2 (p : Parameters) {ε : ℝ} (hε : 0 < ε) (v₀ : ℝ) :
    ∃ G H : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas),
      (⇑G =ᵐ[trimMeasure (μ := μ) T hBmeas]
        fun z => cirDrift p (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) ∧
      (⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas]
        fun z => cirRegularizedDiffusion p ε (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) := by
  obtain ⟨X, G, H, hX, -, -, -, hG, hH, -⟩ := exists_lipschitz_sde_solution hB T hBmeas hBcont
    (lipschitzWith_cirDrift p) (lipschitzWith_cirRegularizedDiffusion p hε) v₀
  have hXeq : X = l2ItoProcess T hBmeas v₀ G H := by
    funext t ω
    exact hX t ω
  subst hXeq
  exact ⟨G, H, hG, hH⟩

include hB hBcont in
/-- Integrability of `|X_t - Y_t|` for two `L²` Itô processes. -/
theorem integrable_abs_l2ItoProcess_sub (x₀ : ℝ)
    (β γ β' γ' : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {t : ℝ≥0} (htT : t ≤ T) :
    Integrable (fun ω => |l2ItoProcess T hBmeas x₀ β γ t ω
      - l2ItoProcess T hBmeas x₀ β' γ' t ω|) μ := by
  have h1 := integrable_comp_at hB T hBmeas hBcont x₀ β γ
    (f := id) (f' := fun _ => 1) (fun x => hasDerivAt_id x) (C₁ := 1) (fun _ => by norm_num) htT
  have h2 := integrable_comp_at hB T hBmeas hBcont x₀ β' γ'
    (f := id) (f' := fun _ => 1) (fun x => hasDerivAt_id x) (C₁ := 1) (fun _ => by norm_num) htT
  refine (h1.sub h2).abs.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.sub_apply, id]
  congr 1
  ring

variable (p : Parameters) (hκ : 0 ≤ p.kappa) {v₀ : ℝ}
  (G H : ℕ → Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
  (hG : ∀ n, ⇑(G n) =ᵐ[trimMeasure (μ := μ) T hBmeas]
    fun z => cirDrift p (l2ItoProcess T hBmeas v₀ (G n) (H n) z.1 z.2))
  (hH : ∀ n, ⇑(H n) =ᵐ[trimMeasure (μ := μ) T hBmeas]
    fun z => cirRegularizedDiffusion p (cirEps n) (l2ItoProcess T hBmeas v₀ (G n) (H n) z.1 z.2))

include hB hBcont hκ hG hH in
/-- Uniform `L¹` Cauchy bound along the schedule. -/
theorem cir_regularized_l1_bound {N n k : ℕ} (hn : N ≤ n) (hk : N ≤ k) {t : ℝ≥0} (htT : t ≤ T) :
    ∫ ω, |l2ItoProcess T hBmeas v₀ (G n) (H n) t ω - l2ItoProcess T hBmeas v₀ (G k) (H k) t ω| ∂μ
      ≤ (1 + 10 * p.xi ^ 2 * T) * (1 / ((N : ℝ) + 1)) := by
  have hm : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  have h := cir_regularized_cauchy hB T hBmeas hBcont p hκ (cirEps_pos n).le (cirEps_pos k).le
    (yamadaParamsOf (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1) hb hm) (G n) (H n) (G k) (H k)
    (hG n) (hG k) (hH n) (hH k) htT
  rw [yamada_m_yamadaParamsOf] at h
  have hma : ((N : ℝ) + 1) * (yamadaParamsOf (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1) hb hm).a
      = 1 / Real.exp ((N : ℝ) + 1) := by
    show ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1) / Real.exp ((N : ℝ) + 1)) = 1 / Real.exp ((N : ℝ) + 1)
    field_simp
  rw [hma, yamadaParamsOf_b] at h
  have hdiv : 4 * p.xi ^ 2 * (cirEps n + cirEps k) / (1 / Real.exp ((N : ℝ) + 1))
      = 4 * p.xi ^ 2 * (cirEps n * Real.exp ((N : ℝ) + 1) + cirEps k * Real.exp ((N : ℝ) + 1)) := by
    rw [one_div, div_inv_eq_mul]
    ring
  rw [hdiv] at h
  have hεn := cirEps_mul_exp_le hn
  have hεk := cirEps_mul_exp_le hk
  have hξ : 0 ≤ p.xi ^ 2 := sq_nonneg _
  have htT' : (t : ℝ) ≤ T := by exact_mod_cast htT
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hsum : cirEps n * Real.exp ((N : ℝ) + 1) + cirEps k * Real.exp ((N : ℝ) + 1)
      ≤ 2 * (1 / ((N : ℝ) + 1)) := by linarith
  have hcoef : 2 * p.xi ^ 2 / ((N : ℝ) + 1)
        + 4 * p.xi ^ 2 * (cirEps n * Real.exp ((N : ℝ) + 1) + cirEps k * Real.exp ((N : ℝ) + 1))
      ≤ 10 * p.xi ^ 2 * (1 / ((N : ℝ) + 1)) := by
    have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 4 * p.xi ^ 2)
    have e : 2 * p.xi ^ 2 / ((N : ℝ) + 1) = 2 * p.xi ^ 2 * (1 / ((N : ℝ) + 1)) := by ring
    rw [e]
    linarith
  have hpos10 : (0 : ℝ) ≤ 10 * p.xi ^ 2 * (1 / ((N : ℝ) + 1)) := by positivity
  calc _ ≤ _ := h
    _ ≤ 1 / ((N : ℝ) + 1) + 10 * p.xi ^ 2 * (1 / ((N : ℝ) + 1)) * T := by
        have h1 := mul_le_mul_of_nonneg_right hcoef ht0
        have h2 := mul_le_mul_of_nonneg_left htT' hpos10
        linarith
    _ = (1 + 10 * p.xi ^ 2 * T) * (1 / ((N : ℝ) + 1)) := by ring

include hB hBcont hκ hG hH in
/-- The diffusion integrands are Cauchy in `L²`. -/
theorem cir_regularized_diffusion_cauchy {N n k : ℕ} (hn : N ≤ n) (hk : N ≤ k) :
    ‖H n - H k‖ ^ 2 ≤ T * (2 * p.xi ^ 2 * (1 + 10 * p.xi ^ 2 * T) + 8 * p.xi ^ 2)
      * (1 / ((N : ℝ) + 1)) := by
  set X : ℕ → ℝ≥0 → Ω → ℝ := fun j => l2ItoProcess T hBmeas v₀ (G j) (H j) with hXdef
  have hXpred : ∀ j, IsStronglyPredictable (natFiltration hBmeas) (X j) := fun j =>
    l2ItoProcess_isStronglyPredictable hB T hBmeas hBcont v₀ (G j) (H j)
  set f : ℝ≥0 × Ω → ℝ := fun z => cirRegularizedDiffusion p (cirEps n) (X n z.1 z.2)
    - cirRegularizedDiffusion p (cirEps k) (X k z.1 z.2) with hfdef
  have hf : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable] f :=
    ((continuous_cirRegularizedDiffusion p _).comp_stronglyMeasurable (hXpred n)).sub
      ((continuous_cirRegularizedDiffusion p _).comp_stronglyMeasurable (hXpred k))
  have hHf : ⇑(H n - H k) =ᵐ[trimMeasure (μ := μ) T hBmeas] f := by
    filter_upwards [Lp.coeFn_sub (H n) (H k), hH n, hH k] with z h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hN : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hξ : 0 ≤ p.xi ^ 2 := sq_nonneg _
  have hK : (0 : ℝ) ≤ (2 * p.xi ^ 2 * (1 + 10 * p.xi ^ 2 * T) + 8 * p.xi ^ 2)
      * (1 / ((N : ℝ) + 1)) := by positivity
  rw [← bandEnergy_self, bandEnergy_eq_slices T hBmeas hf hHf le_rfl,
    show (T : ℝ) * (2 * p.xi ^ 2 * (1 + 10 * p.xi ^ 2 * T) + 8 * p.xi ^ 2) * (1 / ((N : ℝ) + 1))
      = (2 * p.xi ^ 2 * (1 + 10 * p.xi ^ 2 * T) + 8 * p.xi ^ 2) * (1 / ((N : ℝ) + 1)) * T by ring]
  refine setIntegral_le_of_ae_le_const hK ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsT : s ≤ T := hs.2
  have hY := cir_regularized_l1_bound hB T hBmeas hBcont p hκ G H hG hH hn hk hsT
  have hint : Integrable (fun ω => |X n s ω - X k s ω|) μ :=
    integrable_abs_l2ItoProcess_sub hB T hBmeas hBcont v₀ (G n) (H n) (G k) (H k) hsT
  have hε : cirEps n + cirEps k ≤ 2 * (1 / ((N : ℝ) + 1)) := by
    linarith [cirEps_le hn, cirEps_le hk]
  calc ∫ ω, f (s, ω) ^ 2 ∂μ
      ≤ ∫ ω, (2 * p.xi ^ 2 * |X n s ω - X k s ω| + 4 * p.xi ^ 2 * (cirEps n + cirEps k)) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
          ((hint.const_mul _).add (integrable_const _))
          (ae_of_all _ fun ω => cirRegularizedDiffusion_cross_sq_le p (cirEps_pos n).le
            (cirEps_pos k).le _ _)
    _ = 2 * p.xi ^ 2 * ∫ ω, |X n s ω - X k s ω| ∂μ + 4 * p.xi ^ 2 * (cirEps n + cirEps k) := by
        rw [integral_add (hint.const_mul _) (integrable_const _), integral_const_mul]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ (2 * p.xi ^ 2 * (1 + 10 * p.xi ^ 2 * T) + 8 * p.xi ^ 2) * (1 / ((N : ℝ) + 1)) := by
        have e1 := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 2 * p.xi ^ 2)
        have e2 := mul_le_mul_of_nonneg_left hε (by positivity : (0 : ℝ) ≤ 4 * p.xi ^ 2)
        nlinarith

include hB hBcont hG in
/-- The drift integrand is affine in the process class. -/
theorem cir_regularized_drift_eq (n : ℕ) :
    G n = Lp.const 2 (trimMeasure (μ := μ) T hBmeas) (p.kappa * p.theta)
      - p.kappa • l2ItoProcessLp hB T hBmeas hBcont v₀ (G n) (H n) := by
  refine Lp.ext ?_
  filter_upwards [hG n, Lp.coeFn_sub (Lp.const 2 (trimMeasure (μ := μ) T hBmeas)
      (p.kappa * p.theta)) (p.kappa • l2ItoProcessLp hB T hBmeas hBcont v₀ (G n) (H n)),
    Lp.coeFn_const (p := 2) (μ := trimMeasure (μ := μ) T hBmeas) (p.kappa * p.theta),
    Lp.coeFn_smul p.kappa (l2ItoProcessLp hB T hBmeas hBcont v₀ (G n) (H n)),
    coeFn_l2ItoProcessLp hB T hBmeas hBcont v₀ (G n) (H n)] with z h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, h3, h4, Pi.smul_apply, h5]
  simp only [cirDrift, Function.const_apply, Function.uncurry_def, smul_eq_mul]
  ring

include hB hBcont hκ hG hH in
/-- The regularized processes are Cauchy in `L²`. -/
theorem cir_regularized_process_cauchy {N n k : ℕ} (hn : N ≤ n) (hk : N ≤ k) :
    ‖l2ItoProcessLp hB T hBmeas hBcont v₀ (G n) (H n)
        - l2ItoProcessLp hB T hBmeas hBcont v₀ (G k) (H k)‖ ^ 2
      ≤ 2 * T * Real.exp (2 * T * p.kappa ^ 2 * T)
        * (T * (2 * p.xi ^ 2 * (1 + 10 * p.xi ^ 2 * T) + 8 * p.xi ^ 2)) * (1 / ((N : ℝ) + 1)) := by
  have hβ : G n - G k = (-p.kappa) • (l2ItoProcessLp hB T hBmeas hBcont v₀ (G n) (H n)
      - l2ItoProcessLp hB T hBmeas hBcont v₀ (G k) (H k)) := by
    have e1 := cir_regularized_drift_eq hB T hBmeas hBcont p G H hG n
    have e2 := cir_regularized_drift_eq hB T hBmeas hBcont p G H hG k
    set Ln := l2ItoProcessLp hB T hBmeas hBcont v₀ (G n) (H n) with hLn
    set Lk := l2ItoProcessLp hB T hBmeas hBcont v₀ (G k) (H k) with hLk
    calc G n - G k
        = (Lp.const 2 (trimMeasure (μ := μ) T hBmeas) (p.kappa * p.theta) - p.kappa • Ln)
          - (Lp.const 2 (trimMeasure (μ := μ) T hBmeas) (p.kappa * p.theta) - p.kappa • Lk) :=
          congrArg₂ (· - ·) e1 e2
      _ = (-p.kappa) • (Ln - Lk) := by
          rw [smul_sub, neg_smul, neg_smul]
          abel
  have hs := norm_sq_l2ItoProcessLp_sub_le hB T hBmeas hBcont v₀ (G n) (H n) (G k) (H k)
    (-p.kappa) hβ
  have hd := cir_regularized_diffusion_cauchy hB T hBmeas hBcont p hκ G H hG hH hn hk
  rw [neg_sq] at hs
  have he : 0 ≤ 2 * (T : ℝ) * Real.exp (2 * T * p.kappa ^ 2 * T) := by positivity
  calc _ ≤ 2 * T * ‖H n - H k‖ ^ 2 * Real.exp (2 * T * p.kappa ^ 2 * T) := hs
    _ = 2 * T * Real.exp (2 * T * p.kappa ^ 2 * T) * ‖H n - H k‖ ^ 2 := by ring
    _ ≤ 2 * T * Real.exp (2 * T * p.kappa ^ 2 * T)
        * (T * (2 * p.xi ^ 2 * (1 + 10 * p.xi ^ 2 * T) + 8 * p.xi ^ 2) * (1 / ((N : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hd he
    _ = _ := by ring

end Regularized

/-! ## Passage to the limit -/

/-- The constant in the `L²` Cauchy bound of the diffusion integrands. -/
def cirKH (p : Parameters) (T : ℝ≥0) : ℝ :=
  T * (2 * p.xi ^ 2 * (1 + 10 * p.xi ^ 2 * T) + 8 * p.xi ^ 2)

/-- The constant in the `L²` Cauchy bound of the processes. -/
def cirKL (p : Parameters) (T : ℝ≥0) : ℝ :=
  2 * T * Real.exp (2 * T * p.kappa ^ 2 * T) * cirKH p T

theorem cirKH_nonneg (p : Parameters) (T : ℝ≥0) : 0 ≤ cirKH p T := by
  unfold cirKH; positivity

theorem cirKL_nonneg (p : Parameters) (T : ℝ≥0) : 0 ≤ cirKL p T := by
  unfold cirKL; have := cirKH_nonneg p T; positivity

theorem cauchySeq_of_norm_sq_le {E : Type*} [NormedAddCommGroup E] {u : ℕ → E} {K : ℝ}
    (h : ∀ n k N : ℕ, N ≤ n → N ≤ k → ‖u n - u k‖ ^ 2 ≤ K * (1 / ((N : ℝ) + 1))) :
    CauchySeq u := by
  refine cauchySeq_of_le_tendsto_0 (fun N => Real.sqrt (K * (1 / ((N : ℝ) + 1))))
    (fun n k N hn hk => ?_) ?_
  · rw [dist_eq_norm]
    exact (le_abs_self _).trans (Real.abs_le_sqrt (h n k N hn hk))
  · have := ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul K).sqrt
    simpa using this

theorem continuous_cirDiffusion (p : Parameters) : Continuous (cirDiffusion p) := by
  unfold cirDiffusion
  exact continuous_const.mul Real.continuous_sqrt

section Limit
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

include hB hBcont in
/-- **Strong existence for the CIR equation** (with diffusion `ξ √(x⁺)`), as an `L²` Itô
process. -/
theorem exists_cir_l2_solution (p : Parameters) (hκ : 0 ≤ p.kappa) (v₀ : ℝ) :
    ∃ G H : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas),
      (⇑G =ᵐ[trimMeasure (μ := μ) T hBmeas]
        fun z => cirDrift p (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) ∧
      (⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas]
        fun z => cirSqrtDiffusion p (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) := by
  have hex : ∀ n : ℕ, ∃ G H : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas),
      (⇑G =ᵐ[trimMeasure (μ := μ) T hBmeas]
        fun z => cirDrift p (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) ∧
      (⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas]
        fun z => cirRegularizedDiffusion p (cirEps n) (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) :=
    fun n => exists_cir_regularized_l2 hB T hBmeas hBcont p (cirEps_pos n) v₀
  choose G H hGH using hex
  have hG : ∀ n, ⇑(G n) =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirDrift p (l2ItoProcess T hBmeas v₀ (G n) (H n) z.1 z.2) := fun n => (hGH n).1
  have hH : ∀ n, ⇑(H n) =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirRegularizedDiffusion p (cirEps n) (l2ItoProcess T hBmeas v₀ (G n) (H n) z.1
            z.2) :=
    fun n => (hGH n).2
  -- Cauchy sequences in `L²`
  have hHc : CauchySeq H := by
    refine cauchySeq_of_norm_sq_le (K := cirKH p T) (fun n k N hn hk => ?_)
    have := cir_regularized_diffusion_cauchy hB T hBmeas hBcont p hκ G H hG hH hn hk
    unfold cirKH
    exact this
  have hLc : CauchySeq fun n => l2ItoProcessLp hB T hBmeas hBcont v₀ (G n) (H n) := by
    refine cauchySeq_of_norm_sq_le (K := cirKL p T) (fun n k N hn hk => ?_)
    have := cir_regularized_process_cauchy hB T hBmeas hBcont p hκ G H hG hH hn hk
    unfold cirKL cirKH
    exact this
  obtain ⟨Linf, hLinf⟩ := cauchySeq_tendsto_of_complete hLc
  obtain ⟨Hinf, hHinf⟩ := cauchySeq_tendsto_of_complete hHc
  -- the limit drift
  set Ginf : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas) :=
    Lp.const 2 (trimMeasure (μ := μ) T hBmeas) (p.kappa * p.theta) - p.kappa • Linf with hGinf
  have hGlim : Tendsto G atTop (𝓝 Ginf) := by
    have h := (tendsto_const_nhds (x := Lp.const 2 (trimMeasure (μ := μ) T hBmeas)
      (p.kappa * p.theta))).sub (hLinf.const_smul p.kappa)
    exact h.congr (fun n => (cir_regularized_drift_eq hB T hBmeas hBcont p G H hG n).symm)
  -- the limit Itô process is the limit of the processes
  have hlimL : Tendsto (fun n => l2ItoProcessLp hB T hBmeas hBcont v₀ (G n) (H n)) atTop
      (𝓝 (l2ItoProcessLp hB T hBmeas hBcont v₀ Ginf Hinf)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun n => norm_l2ItoProcessLp_sub_le hB T hBmeas hBcont v₀ (G n) (H n) Ginf Hinf) ?_
    have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp hGlim).const_mul (T : ℝ)
    have h2 := (tendsto_iff_norm_sub_tendsto_zero.mp hHinf).const_mul (Real.sqrt T)
    simpa using h1.add h2
  have hLeq : l2ItoProcessLp hB T hBmeas hBcont v₀ Ginf Hinf = Linf :=
    tendsto_nhds_unique hlimL hLinf
  have hVL : Function.uncurry (l2ItoProcess T hBmeas v₀ Ginf Hinf)
      =ᵐ[trimMeasure (μ := μ) T hBmeas] ⇑Linf := by
    have h := coeFn_l2ItoProcessLp hB T hBmeas hBcont v₀ Ginf Hinf
    rw [hLeq] at h
    exact h.symm
  -- identification of the limit diffusion along an a.e.-convergent subsequence
  have hHid : ⇑Hinf =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirSqrtDiffusion p (Linf z) := by
    obtain ⟨ns, hns, haeL⟩ := (tendstoInMeasure_of_tendsto_Lp hLinf).exists_seq_tendsto_ae
    obtain ⟨ms, hms, haeH⟩ :=
      (tendstoInMeasure_of_tendsto_Lp (hHinf.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
    have hall : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), ∀ j, H j z
        = cirRegularizedDiffusion p (cirEps j) (l2ItoProcessLp hB T hBmeas hBcont v₀ (G j) (H j)
              z) := by
      rw [ae_all_iff]
      intro j
      filter_upwards [hH j, coeFn_l2ItoProcessLp hB T hBmeas hBcont v₀ (G j) (H j)] with z h1 h2
      rw [h1, h2]
      rfl
    filter_upwards [haeL, haeH, hall] with z hz1 hz2 hz3
    have hsub : Tendsto (fun i => l2ItoProcessLp hB T hBmeas hBcont v₀ (G (ns (ms i)))
        (H (ns (ms i))) z) atTop (𝓝 (Linf z)) := hz1.comp hms.tendsto_atTop
    have hεsub : Tendsto (fun i => cirEps (ns (ms i))) atTop (𝓝 0) :=
      tendsto_cirEps.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)
    have hlim2 := tendsto_cirRegularizedDiffusion p hεsub hsub
    have hlim3 : Tendsto (fun i => H (ns (ms i)) z) atTop (𝓝 (cirSqrtDiffusion p (Linf z))) :=
      hlim2.congr (fun i => (hz3 _).symm)
    exact tendsto_nhds_unique hz2 hlim3
  refine ⟨Ginf, Hinf, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub (Lp.const 2 (trimMeasure (μ := μ) T hBmeas) (p.kappa * p.theta))
        (p.kappa • Linf),
      Lp.coeFn_const (p := 2) (μ := trimMeasure (μ := μ) T hBmeas) (p.kappa * p.theta),
      Lp.coeFn_smul p.kappa Linf, hVL] with z h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, ← h4]
    simp only [cirDrift, Function.const_apply, Function.uncurry_def, smul_eq_mul]
    ring
  · filter_upwards [hHid, hVL] with z h1 h2
    rw [h1, ← h2]
    rfl

include hB hBcont in
/-- **Strong existence for the CIR SDE on `[0,T]`.**  For `κ, θ ≥ 0` and `v₀ ≥ 0` there is a
predictable process `V`, with a.s. continuous paths on `[0,T]` and square-integrable on
`(0,T] × Ω`, which is nonnegative and satisfies, a.s. for all `t ≤ T`,
`V_t = v₀ + ∫₀ᵗ κ(θ - V_s) ds + ∫₀ᵗ ξ √V_s dB_s`. -/
theorem exists_cir_strong_solution (p : Parameters) (hκ : 0 ≤ p.kappa) (hθ : 0 ≤ p.theta)
    {v₀ : ℝ} (hv₀ : 0 ≤ v₀) :
    ∃ (V : ℝ≥0 → Ω → ℝ) (G H : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)),
      (∀ t ω, V t ω = v₀ + driftContinuousMod T hBmeas G t ω + itoContinuousMod T hBmeas H t ω) ∧
      IsStronglyPredictable (natFiltration hBmeas) V ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Set.Icc 0 T)) ∧
      MemLp (Function.uncurry V) 2 (trimMeasure (μ := μ) T hBmeas) ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ V t ω) ∧
      (⇑G =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => cirDrift p (V z.1 z.2)) ∧
      (⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => cirDiffusion p (V z.1 z.2)) ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, V t ω = v₀ + (∫ s in Set.Ioc 0 t, cirDrift p (V s ω) ∂timeMeasure)
        + itoContinuousMod T hBmeas H t ω) := by
  obtain ⟨G, H, hG, hH⟩ := exists_cir_l2_solution hB T hBmeas hBcont p hκ v₀
  set V := l2ItoProcess T hBmeas v₀ G H with hV
  have hpred : IsStronglyPredictable (natFiltration hBmeas) V :=
    l2ItoProcess_isStronglyPredictable hB T hBmeas hBcont v₀ G H
  have hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Set.Icc 0 T) :=
    ae_continuousOn_l2ItoProcess hB T hBmeas hBcont v₀ G H
  have hmem : MemLp (Function.uncurry V) 2 (trimMeasure (μ := μ) T hBmeas) :=
    (Lp.memLp (l2ItoProcessLp hB T hBmeas hBcont v₀ G H)).ae_eq
      (coeFn_l2ItoProcessLp hB T hBmeas hBcont v₀ G H)
  have hnn : ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ V t ω := cir_sqrt_nonneg hB T hBmeas hBcont p hκ hθ hv₀ G H hG hH
  have hH' : ⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => cirDiffusion p (V z.1 z.2) := by
    have hf : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
        (fun z : ℝ≥0 × Ω => cirSqrtDiffusion p (V z.1 z.2)) :=
      (continuous_cirSqrtDiffusion p).comp_stronglyMeasurable hpred
    have hg : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
        (fun z : ℝ≥0 × Ω => cirDiffusion p (V z.1 z.2)) :=
      (continuous_cirDiffusion p).comp_stronglyMeasurable hpred
    have heq := ae_eq_trim_of_pathwise T hBmeas hf hg (by
      filter_upwards [hnn] with ω hω t ht
      simp only [cirSqrtDiffusion, cirDiffusion, max_eq_left (hω t ht)])
    exact hH.trans heq
  have hpath : ∀ᵐ ω ∂μ, ∀ t ≤ T, V t ω = v₀ + (∫ s in Set.Ioc 0 t, cirDrift p (V s ω)
      ∂timeMeasure) + itoContinuousMod T hBmeas H t ω := by
    filter_upwards [driftContinuousMod_eq_setIntegral_all T hBmeas G,
      ae_ae_of_ae_trim T hBmeas hG] with ω h1 h2 t ht
    have hint : ∫ s in Set.Ioc 0 t, G (s, ω) ∂timeMeasure
        = ∫ s in Set.Ioc 0 t, cirDrift p (V s ω) ∂timeMeasure := by
      refine integral_congr_ae ?_
      rw [← timeMeasure_T_restrict_Ioc T ht]
      exact ae_restrict_of_ae h2
    show v₀ + driftContinuousMod T hBmeas G t ω + itoContinuousMod T hBmeas H t ω = _
    rw [h1 t ht, hint]
  exact ⟨V, G, H, fun t ω => rfl, hpred, hcont, hmem, hnn, hG, hH', hpath⟩

include hB hBcont in
/-- **Pathwise uniqueness of nonnegative CIR solutions** on `[0,T]`. -/
theorem cir_strong_solution_unique (p : Parameters) (hκ : 0 ≤ p.kappa) {v₀ : ℝ}
    (V₁ V₂ : ℝ≥0 → Ω → ℝ) (G₁ H₁ G₂ H₂ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hV₁ : ∀ t ω, V₁ t ω = v₀ + driftContinuousMod T hBmeas G₁ t ω
      + itoContinuousMod T hBmeas H₁ t ω)
    (hV₂ : ∀ t ω, V₂ t ω = v₀ + driftContinuousMod T hBmeas G₂ t ω
      + itoContinuousMod T hBmeas H₂ t ω)
    (hnn₁ : ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ V₁ t ω) (hnn₂ : ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ V₂ t ω)
    (hG₁ : ⇑G₁ =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => cirDrift p (V₁ z.1 z.2))
    (hG₂ : ⇑G₂ =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => cirDrift p (V₂ z.1 z.2))
    (hH₁ : ⇑H₁ =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => cirDiffusion p (V₁ z.1 z.2))
    (hH₂ : ⇑H₂ =ᵐ[trimMeasure (μ := μ) T hBmeas] fun z => cirDiffusion p (V₂ z.1 z.2)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, V₁ t ω = V₂ t ω := by
  have e₁ : V₁ = l2ItoProcess T hBmeas v₀ G₁ H₁ := by funext t ω; exact hV₁ t ω
  have e₂ : V₂ = l2ItoProcess T hBmeas v₀ G₂ H₂ := by funext t ω; exact hV₂ t ω
  subst e₁ e₂
  have hsq : ∀ (G H : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)),
      (∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ l2ItoProcess T hBmeas v₀ G H t ω) →
      (⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas]
        fun z => cirDiffusion p (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) →
      ⇑H =ᵐ[trimMeasure (μ := μ) T hBmeas]
        fun z => cirSqrtDiffusion p (l2ItoProcess T hBmeas v₀ G H z.1 z.2) := by
    intro G H hnn hH
    have hpred := l2ItoProcess_isStronglyPredictable hB T hBmeas hBcont v₀ G H
    have hf : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
        (fun z : ℝ≥0 × Ω => cirDiffusion p (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) :=
      (continuous_cirDiffusion p).comp_stronglyMeasurable hpred
    have hg : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
        (fun z : ℝ≥0 × Ω => cirSqrtDiffusion p (l2ItoProcess T hBmeas v₀ G H z.1 z.2)) :=
      (continuous_cirSqrtDiffusion p).comp_stronglyMeasurable hpred
    have heq := ae_eq_trim_of_pathwise T hBmeas hf hg (by
      filter_upwards [hnn] with ω hω t ht
      simp only [cirSqrtDiffusion, cirDiffusion, max_eq_left (hω t ht)])
    exact hH.trans heq
  exact cir_pathwise_unique hB T hBmeas hBcont p hκ G₁ H₁ G₂ H₂ hG₁ hG₂
    (hsq G₁ H₁ hnn₁ hH₁) (hsq G₂ H₂ hnn₂ hH₂)

/-- **Non-explosion**: a process with a.s. continuous paths on `[0,T]` is a.s. bounded there. -/
theorem ae_bounded_of_continuousOn {V : ℝ≥0 → Ω → ℝ}
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => V t ω) (Set.Icc 0 T)) :
    ∀ᵐ ω ∂μ, ∃ C : ℝ, ∀ t ≤ T, |V t ω| ≤ C := by
  filter_upwards [hcont] with ω hω
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0)
        T)).exists_bound_of_continuousOn hω
  exact ⟨C, fun t ht => by simpa [Real.norm_eq_abs] using hC t ⟨zero_le, ht⟩⟩

end Limit

end MathFin.Heston
