/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoDriftIncrementEnergy
public import MathFin.Foundations.ItoDriftWeightedIsometry
public import MathFin.Foundations.FiniteMeasureCauchySchwarz

/-! # The third-moment bound for the true increment (the discrete route, stage 5b)

The fourth moment of the true increment over a uniform cell (`trueIncr_pow4_le`,
`trueIncr_pow4_integrable`) from the step-sum recursion `stepSum_pow4_le`, passed to the true
increment through the step approximants' `L²` convergence and Fatou, and the cube bound
`trueIncr_pow3_le` by Cauchy–Schwarz interpolation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
  ItoIntegralProcessGeneral ItoIntegralProcess QuadraticVariationL2 ItoIntegralBrownian

/-- Young's pointwise inequality `|a|³|b| ≤ 3a⁴/4 + b⁴/4`: from
`(a − b)²(2a² + (a+b)²) = 3a⁴ + b⁴ − 4a³b ≥ 0`, evaluated at `(|a|, |b|)`. -/
private theorem young34 (a b : ℝ) : |a| ^ 3 * |b| ≤ 3 * a ^ 4 / 4 + b ^ 4 / 4 := by
  have h1 : (0:ℝ) ≤ (abs a - abs b) ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ 2 * abs a ^ 2 + (abs a + abs b) ^ 2 := by positivity
  have h3 : (abs a - abs b) ^ 2 * (2 * abs a ^ 2 + (abs a + abs b) ^ 2)
      = 3 * abs a ^ 4 + abs b ^ 4 - 4 * abs a ^ 3 * abs b := by ring
  have h4 : |a| ^ 4 = a ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have h5 : |b| ^ 4 = b ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have key : (0:ℝ) ≤ 3 * a ^ 4 + b ^ 4 - 4 * |a| ^ 3 * |b| := by
    have hpro := mul_nonneg h1 h2
    rw [h3, h4, h5] at hpro
    linarith
  linarith

/-- Young's pointwise inequality, the symmetric instance `|a|·|b|³ ≤ a⁴/4 + 3b⁴/4`. -/
private theorem young134 (a b : ℝ) : |a| * |b| ^ 3 ≤ a ^ 4 / 4 + 3 * b ^ 4 / 4 := by
  linarith [young34 b a, mul_comm (abs b ^ 3) (abs a)]


/-! #### Stage 5b — the third-moment bound

The fourth moment of the true increment over a uniform cell, obtained from the step-sum
recursion `stepSum_pow4_le` (the potential `3S² + 6D²SC + 3D⁴Q`: each refined-band Riemann
sum of the bounded adapted integrand has fourth moment at most `3·(D²·band length)²`),
passed to the true increment through the step approximants' `L²` convergence
(`clm_band_energy` + `deltaStepLp_tendsto`), convergence in measure, an a.e. subsequence,
and Fatou (`lintegral_liminf_le`). The cube bound then drops out by Cauchy–Schwarz
interpolation (`∫|X|³ ≤ ‖X‖₂·‖X‖₄²·...`). -/

section StageFiveB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  (hδadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (δ t))
  (hδcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ δ s ω)
  (hδbdd : ∀ t ω, |δ t ω| ≤ Dd)
  {M : ℝ≥0 → Ω → ℝ}
  (hMadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (M t))
  (hMeq : ∀ t, M t =ᵐ[μ] (itoProcessCLM hB T t hBmeas
    (processToLp T hBmeas hδadap hδcont hδbdd) : Ω → ℝ))

include hB hBmeas hδadap hδcont hδbdd hMadap hMeq

omit [IsProbabilityMeasure μ] hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- Third moment of a Brownian increment: `E[(B_{t₁} − B_{t₀})³] = 0` for `t₀ ≤ t₁`
(the law-transfer of the vanishing odd Gaussian moment). -/
private theorem integral_increment_pow3
    {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) :
    ∫ ω, (B t₁ ω - B t₀ ω) ^ 3 ∂μ = 0 := by
  have hv : nndist (t₁ : ℝ) (t₀ : ℝ) = t₁ - t₀ := by
    apply NNReal.coe_injective
    rw [coe_nndist, Real.dist_eq, NNReal.coe_sub ht,
      abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht))]
  have hlaw : HasLaw (fun ω ↦ B t₁ ω - B t₀ ω) (gaussianReal 0 (t₁ - t₀)) μ := by
    rw [← hv]; exact hB.hasLaw_sub t₁ t₀
  have hcomp := hlaw.integral_comp (f := fun x : ℝ ↦ x ^ 3)
    (measurable_id.pow_const 3).aestronglyMeasurable
  simp only [Function.comp_def] at hcomp
  rw [hcomp, integral_pow3_gaussianReal]

omit [IsProbabilityMeasure μ] hδadap hδcont hδbdd hMadap hMeq in
/-- Fourth-power isometry kernel: for `χ` measurable in the natural filtration at `t₀`,
`E[χ·(B t₁ − B t₀)⁴] = E[χ]·3·(t₁ − t₀)²`. -/
private theorem integral_natMeasurable_mul_increment_pow4
    {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {χ : Ω → ℝ} (hχ : Measurable[natFiltration hBmeas t₀] χ) :
    ∫ ω, χ ω * (B t₁ ω - B t₀ ω) ^ 4 ∂μ
      = (∫ ω, χ ω ∂μ) * (3 * ((t₁ : ℝ) - t₀) ^ 2) := by
  have hχm : Measurable χ := hχ.mono ((natFiltration hBmeas).le t₀) le_rfl
  have hΔm : Measurable (fun ω ↦ B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  rw [(adapted_indepFun_increment (hB.isFilteredPreBrownian hBmeas) ht hχ).integral_mul_comp
      (g := fun x : ℝ ↦ x ^ 4) (by fun_prop) hχm.aestronglyMeasurable hΔm.aemeasurable,
    integral_increment_pow4 hB ht]

omit [IsProbabilityMeasure μ] hδadap hδcont hδbdd hMadap hMeq in
/-- Third-power isometry kernel: for `χ` measurable in the natural filtration at `t₀`,
`E[χ·(B t₁ − B t₀)³] = 0` (the odd Gaussian moment vanishes). -/
private theorem integral_natMeasurable_mul_increment_pow3
    {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {χ : Ω → ℝ} (hχ : Measurable[natFiltration hBmeas t₀] χ) :
    ∫ ω, χ ω * (B t₁ ω - B t₀ ω) ^ 3 ∂μ = 0 := by
  have hχm : Measurable χ := hχ.mono ((natFiltration hBmeas).le t₀) le_rfl
  have hΔm : Measurable (fun ω ↦ B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  rw [(adapted_indepFun_increment (hB.isFilteredPreBrownian hBmeas) ht hχ).integral_mul_comp
      (g := fun x : ℝ ↦ x ^ 3) (by fun_prop) hχm.aestronglyMeasurable hΔm.aemeasurable,
    integral_increment_pow3 hB ht, mul_zero]

set_option maxHeartbeats 1600000 in
-- a long estimate: elaborating the whole proof exceeds the default budget
omit [IsProbabilityMeasure μ] hδadap hδcont hδbdd hMadap hMeq in
/-- **The step-sum fourth-moment recursion**: for a bounded integrand sampled along a
monotone time grid (`φ j` measurable in `𝓕_{s j}`, `|φ| ≤ D`), the fourth moment of the
Itô sum is at most `3·(D²·total gap)²`. -/
private theorem stepSum_pow4_le {s : ℕ → ℝ≥0} (hsmono : Monotone s) {φ : ℕ → Ω → ℝ}
    (hφm : ∀ j, Measurable[natFiltration hBmeas (s j)] (φ j))
    {D : ℝ} (hφbdd : ∀ j ω, |φ j ω| ≤ D) (N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal
        ((∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4) ∂μ
      ≤ ENNReal.ofReal
        (3 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)) ^ 2) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  induction N with
  | zero => simp
  | succ N ihN =>
    have hexpan : ∀ ω : Ω,
        (∑ k ∈ Finset.range (N + 1), φ k ω * (B (s (k + 1)) ω - B (s k) ω))
          = (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            + φ N ω * (B (s (N + 1)) ω - B (s N) ω) := fun ω ↦ by
      rw [Finset.sum_range_succ]
    have hgapexpan : (∑ k ∈ Finset.range (N + 1), ((s (k + 1) : ℝ) - s k))
        = (∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k))
          + ((s (N + 1) : ℝ) - s N) := by
      rw [Finset.sum_range_succ]
    have hexpan4 : ∀ ω : Ω,
        (∑ k ∈ Finset.range (N + 1), φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
          = ((∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            + φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 := fun ω ↦ by
      rw [hexpan ω]
    -- measurability at the later grid point
    have hφmN : ∀ k : ℕ, k ≤ N → Measurable[natFiltration hBmeas (s N)] (φ k) := fun k hk ↦
      (hφm k).mono ((natFiltration hBmeas).mono (hsmono hk)) le_rfl
    have hBle : ∀ {u : ℝ≥0}, u ≤ s N →
        Measurable[natFiltration hBmeas (s N)] (B u) := by
      intro u hu
      have hle : MeasurableSpace.comap (B u) (inferInstance : MeasurableSpace ℝ)
          ≤ natFiltration hBmeas (s N) := le_iSup₂_of_le u hu le_rfl
      exact (measurable_iff_comap_le.mpr le_rfl).mono hle le_rfl
    have hYm : ∀ k : ℕ, k < N → Measurable[natFiltration hBmeas (s N)]
        (fun ω ↦ φ k ω * (B (s (k + 1)) ω - B (s k) ω)) := by
      intro k hk
      exact (hφmN k (Nat.le_of_lt hk)).mul
        ((hBle (hsmono (Nat.succ_le_of_lt hk))).sub (hBle (hsmono (Nat.le_of_lt hk))))
    have hZm : Measurable[natFiltration hBmeas (s N)]
        (fun ω ↦ ∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) :=
      Finset.measurable_sum _ fun k hk ↦ hYm k (Finset.mem_range.mp hk)
    have hyadapt : Measurable[natFiltration hBmeas (s N)] (φ N) := hφmN N (Nat.le_refl N)
    -- the exact second moment via the discrete Itô isometry
    have hφL2 : ∀ k : ℕ, MemLp (φ k) 2 μ := fun k ↦
      MemLp.of_bound (((hφm k).mono ((natFiltration hBmeas).le _) le_rfl)).aestronglyMeasurable
        D (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hφbdd k ω)
    have hZ2 : ∫ ω, (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 ∂μ
        = ∑ k ∈ Finset.range N, (∫ ω, (φ k ω) ^ 2 ∂μ) * ((s (k + 1) : ℝ) - s k) :=
      ito_isometry_discrete (hB.isFilteredPreBrownian hBmeas) hsmono hφm hφL2
    -- the fourth moment of the last rectangle and its bound
    have hy4 : ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ
        = (∫ ω, (φ N ω) ^ 4 ∂μ) * (3 * ((s (N + 1) : ℝ) - s N) ^ 2) := by
      have h := integral_natMeasurable_mul_increment_pow4 hB hBmeas
        (hsmono (Nat.le_succ N))
        (χ := fun ω ↦ (φ N ω) ^ 4) ((hφmN N (Nat.le_refl N)).pow_const 4)
      rw [integral_congr_ae (Eventually.of_forall fun ω ↦ by rw [mul_pow])]
      exact h
    have hy4le : ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ
        ≤ 3 * (D ^ 2 * ((s (N + 1) : ℝ) - s N)) ^ 2 := by
      rw [hy4]
      have hφ4 : ∫ ω, (φ N ω) ^ 4 ∂μ ≤ D ^ 4 := by
        refine le_trans (integral_mono_of_nonneg (μ := μ)
          (Eventually.of_forall fun ω ↦ show (0:ℝ) ≤ φ N ω ^ 4 from by positivity)
          (integrable_const (D ^ 4)) (ae_of_all μ fun ω ↦ ?_)) ?_
        · exact (Even.pow_abs (n := 4) ⟨2, rfl⟩ _).symm.trans_le
            (pow_le_pow_left₀ (abs_nonneg _) (hφbdd N ω) 4)
        · rw [integral_const]
          simp
      calc (∫ ω, (φ N ω) ^ 4 ∂μ) * (3 * ((s (N + 1) : ℝ) - s N) ^ 2)
          ≤ D ^ 4 * (3 * ((s (N + 1) : ℝ) - s N) ^ 2) :=
            mul_le_mul_of_nonneg_right hφ4 (mul_nonneg zero_le_three (sq_nonneg _))
        _ = 3 * (D ^ 2 * ((s (N + 1) : ℝ) - s N)) ^ 2 := by ring
    -- integrability of the rectangle products
    have hY4mem : ∀ k : ℕ, MemLp (fun ω ↦ φ k ω * (B (s (k + 1)) ω - B (s k) ω)) 4 μ := by
      intro k
      have hφ4 : Integrable (fun ω ↦ (φ k ω) ^ 4) μ :=
        Integrable.mono' (integrable_const (D ^ 4))
          (((hφm k).mono ((natFiltration hBmeas).le _) le_rfl).pow_const
            4 |>.aestronglyMeasurable)
          (ae_of_all μ fun ω ↦ by
            change ‖(φ k ω) ^ 4‖ ≤ D ^ 4
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (φ k ω) ^ 4)]
            exact (Even.pow_abs (n := 4) ⟨2, rfl⟩ _).symm.trans_le
              (pow_le_pow_left₀ (abs_nonneg _) (hφbdd k ω) 4))
      have hΔ4 : Integrable (fun ω ↦ (B (s (k + 1)) ω - B (s k) ω) ^ 4) μ := by
        have h := (memLp_increment_four hB (s k) (s (k + 1))).integrable_norm_pow
          (by norm_num)
        refine h.congr (Eventually.of_forall fun ω ↦ ?_)
        change ‖B (s (k + 1)) ω - B (s k) ω‖ ^ 4 = (B (s (k + 1)) ω - B (s k) ω) ^ 4
        rw [Real.norm_eq_abs, pow_abs]
        exact abs_of_nonneg (by positivity : (0:ℝ) ≤
          (B (s (k + 1)) ω - B (s k) ω) ^ 4)
      have hindep4 := (adapted_indepFun_increment (hB.isFilteredPreBrownian hBmeas)
        (hsmono (Nat.le_succ k)) (hφm k)).comp
        (φ := fun x : ℝ ↦ x ^ 4) (ψ := fun x : ℝ ↦ x ^ 4) (by fun_prop) (by fun_prop)
      have hint4 : Integrable (fun ω ↦ (φ k ω) ^ 4
          * (B (s (k + 1)) ω - B (s k) ω) ^ 4) μ := hindep4.integrable_mul hφ4 hΔ4
      have hpt : ∀ ω : Ω, ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ 4
          = (φ k ω) ^ 4 * (B (s (k + 1)) ω - B (s k) ω) ^ 4 := by
        intro ω
        show ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ 4 = _
        rw [Real.norm_eq_abs, abs_mul, mul_pow,
          ← abs_pow (φ k ω) 4, ← abs_pow (B (s (k + 1)) ω - B (s k) ω) 4,
          abs_of_nonneg (show (0:ℝ) ≤ φ k ω ^ 4 from by positivity),
          abs_of_nonneg (show (0:ℝ) ≤ (B (s (k + 1)) ω - B (s k) ω) ^ 4
            from by positivity)]
      have hint4' : Integrable (fun ω ↦
          ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ 4) μ :=
        hint4.congr (Eventually.of_forall fun ω ↦ (hpt ω).symm)
      have hsm : AEStronglyMeasurable
          (fun ω ↦ φ k ω * (B (s (k + 1)) ω - B (s k) ω)) μ :=
        (((hφm k).mono ((natFiltration hBmeas).le _) le_rfl).mul
          ((hBmeas (s (k + 1))).sub (hBmeas (s k)))).aestronglyMeasurable
      have hint4'' : Integrable (fun ω ↦
          ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖
            ^ ((4 : ℕ) : ℝ≥0∞).toReal) μ := by
        have h4r : ((4 : ℕ) : ℝ≥0∞).toReal = (4 : ℝ) := by norm_num
        rw [h4r]
        have hint4' : Integrable (fun ω ↦
            ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ 4) μ :=
          hint4.congr (Eventually.of_forall fun ω ↦ (hpt ω).symm)
        have hcongr : (fun ω ↦ ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ (4 : ℝ))
            = (fun ω ↦ ‖φ k ω * (B (s (k + 1)) ω - B (s k) ω)‖ ^ 4) := by
          funext ω
          exact Real.rpow_natCast _ 4
        rw [hcongr]
        exact hint4'
      exact (integrable_norm_rpow_iff hsm (by norm_num) (by simp)).mp hint4''
    have hZ4mem : MemLp (fun ω ↦ ∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) 4 μ :=
      memLp_finsetSum _ fun k _ ↦ hY4mem k
    have hZaesm := hZ4mem.aestronglyMeasurable
    have hintZ4 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4) μ := by
      have h := hZ4mem.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
      refine h.congr (Eventually.of_forall fun ω ↦ ?_)
      change ‖(∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω))‖ ^ 4
        = (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
      rw [Real.norm_eq_abs,
        ← abs_pow (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) 4,
        abs_of_nonneg (by positivity : (0:ℝ) ≤
          (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4)]
    have hZmeas : Measurable (fun ω ↦ ∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) :=
      hZm.mono ((natFiltration hBmeas).le (s N)) le_rfl
    have hintZ2 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2) μ :=
      Integrable.mono' (integrable_norm_pow_of_le (p := 2) (q := 4) hZaesm (by norm_num)
        (hZ4mem.integrable_norm_pow (by norm_num)))
        (hZmeas.pow_const 2).aestronglyMeasurable
        (ae_of_all μ fun ω ↦ by rw [norm_pow])
    have hintYN4 : Integrable (fun ω ↦ (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4) μ :=
      (hY4mem N).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
      |>.congr (Eventually.of_forall fun ω ↦ by
        change ‖φ N ω * (B (s (N + 1)) ω - B (s N) ω)‖ ^ 4
          = (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4
        rw [Real.norm_eq_abs,
          ← abs_pow (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) 4,
          abs_of_nonneg (by positivity : (0:ℝ) ≤
            (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4)])
    have hφmeasN : Measurable (φ N) :=
      (hφmN N (Nat.le_refl N)).mono ((natFiltration hBmeas).le (s N)) le_rfl
    have hΔmeasN : Measurable (fun ω ↦ B (s (N + 1)) ω - B (s N) ω) :=
      (hBmeas (s (N + 1))).sub (hBmeas (s N))
    -- the odd-term integrabilities (Young domination by fourth powers)
    have hintZY0 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω))) μ :=
      Integrable.mono' ((hintZ4.const_mul (3 / 4)).add (hintYN4.const_mul (1 / 4)))
        ((hZmeas.pow_const 3).mul (hφmeasN.mul hΔmeasN)).aestronglyMeasurable
        (ae_of_all μ fun ω ↦ by
          change ‖(∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
              * (φ N ω * (B (s (N + 1)) ω - B (s N) ω))‖
            ≤ 3 / 4 * (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 1 / 4 * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
          have hy := young34 (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            (φ N ω * (B (s (N + 1)) ω - B (s N) ω))
          linarith)
    have hintSY3 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω))
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3) μ :=
      Integrable.mono' ((hintZ4.const_mul (1 / 4)).add (hintYN4.const_mul (3 / 4)))
        (hZmeas.mul ((hφmeasN.mul hΔmeasN).pow_const 3)).aestronglyMeasurable
        (ae_of_all μ fun ω ↦ by
          change ‖(∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω))
              * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3‖
            ≤ 1 / 4 * (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 3 / 4 * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
          have hy := young134 (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            (φ N ω * (B (s (N + 1)) ω - B (s N) ω))
          linarith)
    have hintZY2 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2) μ :=
      Integrable.mono' ((hintZ4.const_mul (1 / 2)).add (hintYN4.const_mul (1 / 2)))
        (Measurable.aestronglyMeasurable (Measurable.mul
          (Measurable.pow_const hZmeas 2)
          (Measurable.pow_const
            (Measurable.mul hφmeasN hΔmeasN) 2)))
        (ae_of_all μ fun ω ↦ by
          change ‖(∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
              * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2‖
            ≤ 1 / 2 * (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 1 / 2 * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4
          have habs : ‖(∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
              * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2‖
              = (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 :=
            abs_of_nonneg (by positivity)
          rw [habs]
          have hgen : ∀ a b : ℝ, (2:ℝ) * (a ^ 2 * b ^ 2) ≤ a ^ 4 + b ^ 4 := by
            intro a b
            have hx : (a ^ 2 - b ^ 2) ^ 2 = a ^ 4 + b ^ 4 - 2 * (a ^ 2 * b ^ 2) := by ring
            have h : (0:ℝ) ≤ (a ^ 2 - b ^ 2) ^ 2 := sq_nonneg _
            rw [hx] at h
            linarith
          have hsq := hgen (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            (φ N ω * (B (s (N + 1)) ω - B (s N) ω))
          linarith)
    -- the martingale-difference zeros (odd kernels) and the weighted even term
    have hZ3adapt : Measurable[natFiltration hBmeas (s N)] (fun ω ↦
        (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3 * φ N ω) :=
      (hZm.pow_const 3).mul hyadapt
    have hZY0 : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ∂μ = 0 := by
      rw [show (fun ω ↦ (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
        = (fun ω ↦ ((∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3 * φ N ω)
          * (B (s (N + 1)) ω - B (s N) ω)) from by funext ω; ring]
      exact integral_adapted_mul_increment (hB.isFilteredPreBrownian hBmeas)
        (hsmono (Nat.le_succ N)) hZ3adapt
    have hcoef3 : Measurable[natFiltration hBmeas (s N)] (fun ω ↦
        (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) * (φ N ω) ^ 3) :=
      hZm.mul (hyadapt.pow_const 3)
    have hY30 : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω))
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3 ∂μ = 0 := by
      rw [show (fun ω ↦ (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3)
        = (fun ω ↦ ((∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) * (φ N ω) ^ 3)
          * (B (s (N + 1)) ω - B (s N) ω) ^ 3) from by funext ω; ring]
      exact integral_natMeasurable_mul_increment_pow3 hB hBmeas (hsmono (Nat.le_succ N)) hcoef3
    -- the even mixed term: isometry kernel at `χ = Z²φN²`
    have hZ2adapt : Measurable[natFiltration hBmeas (s N)] (fun ω ↦
        (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
          * (φ N ω) ^ 2) :=
      (hZm.pow_const 2).mul (hyadapt.pow_const 2)
    have hZ2le : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 ∂μ
        ≤ D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k) := by
      rw [hZ2]
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ ↦
        mul_le_mul_of_nonneg_right
          (by
            have hmono : ∫ (a : Ω), φ k a ^ 2 ∂μ ≤ ∫ (a : Ω), D ^ 2 ∂μ :=
              integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
                (integrable_const (D ^ 2)) (ae_of_all _ fun ω ↦
                  sq_le_sq.mpr ((hφbdd k ω).trans (le_abs_self D)))
            rw [integral_const] at hmono
            simpa using hmono)
          (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hsmono (Nat.le_succ k))))
    have hZ2phi2 : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * (φ N ω) ^ 2 ∂μ
        ≤ D ^ 2 * ∫ ω, (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 ∂μ := by
      refine le_trans (integral_mono_of_nonneg (μ := μ)
        (Eventually.of_forall fun ω ↦ show (0:ℝ) ≤
          (∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
            * (φ N ω) ^ 2 from by positivity)
        (hintZ2.const_mul (D ^ 2)) (ae_of_all μ fun ω ↦ ?_)) ?_
      · calc (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * (φ N ω) ^ 2
            ≤ (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * D ^ 2 :=
              mul_le_mul_of_nonneg_left (sq_le_sq.mpr ((hφbdd N ω).trans (le_abs_self D)))
                (pow_two_nonneg (∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω)))
        _ = D ^ 2 * (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 := mul_comm _ _
      · rw [integral_const_mul]
    have hZY2 : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 ∂μ
        = (∫ ω, (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * (φ N ω) ^ 2 ∂μ)
          * ((s (N + 1) : ℝ) - s N) := by
      rw [show (fun ω ↦ (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)
        = (fun ω ↦ ((∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * (φ N ω) ^ 2)
          * (B (s (N + 1)) ω - B (s N) ω) ^ 2) from by funext ω; ring]
      exact integral_adapted_mul_increment_sq (hB.isFilteredPreBrownian hBmeas)
        (hsmono (Nat.le_succ N)) hZ2adapt
    have hZY2le : ∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
        * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 ∂μ
        ≤ (D ^ 2 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)))
          * ((s (N + 1) : ℝ) - s N) := by
      rw [hZY2]
      calc (∫ ω, (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 * (φ N ω) ^ 2 ∂μ)
            * ((s (N + 1) : ℝ) - s N)
          ≤ (D ^ 2 * ∫ ω, (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2 ∂μ)
            * ((s (N + 1) : ℝ) - s N) :=
            mul_le_mul_of_nonneg_right hZ2phi2 (sub_nonneg.mpr
              (NNReal.coe_le_coe.mpr (hsmono (Nat.le_succ N))))
        _ ≤ (D ^ 2 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)))
            * ((s (N + 1) : ℝ) - s N) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hZ2le (sq_nonneg D)) (sub_nonneg.mpr
                (NNReal.coe_le_coe.mpr (hsmono (Nat.le_succ N))))
    -- the full expansion, odd kernels zeroed
    have hintBIG2 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
      + 4 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))) μ :=
      hintZ4.add (hintZY0.const_mul 4)
    have hintBIG3 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
      + 4 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
      + 6 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)) μ :=
      hintBIG2.add (hintZY2.const_mul 6)
    have hintBIG4 : Integrable (fun ω ↦ (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
      + 4 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
      + 6 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)
      + 4 * ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
          * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3)) μ :=
      hintBIG3.add (hintSY3.const_mul 4)
    have hexp : ∫ ω, ((∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω))
          + φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ
        = ∫ ω, (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
          + 6 * ∫ ω, (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
            * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 ∂μ
          + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ := by
      calc ∫ ω, ((∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            + φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ
          = ∫ ω, ((∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
              + 6 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω))
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3)
              + (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4) ∂μ :=
            integral_congr_ae (Eventually.of_forall fun ω ↦ by ring)
        _ = ∫ ω, ((∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
              + 6 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω))
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3)) ∂μ
            + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ :=
            integral_add hintBIG4 hintYN4
        _ = (∫ ω, ((∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))
              + 6 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2)) ∂μ
            + ∫ ω, 4 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω))
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3) ∂μ)
            + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ :=
            by rw [integral_add hintBIG3 (hintSY3.const_mul 4)]
        _ = ((∫ ω, ((∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4
              + 4 * ((∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)))) ∂μ
            + ∫ ω, 6 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2) ∂μ)
            + ∫ ω, 4 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω))
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3) ∂μ)
            + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ :=
            by rw [integral_add hintBIG2 (hintZY2.const_mul 6)]
        _ = (((∫ ω, (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
            + ∫ ω, 4 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 3
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω))) ∂μ)
            + ∫ ω, 6 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2) ∂μ)
            + ∫ ω, 4 * ((∑ k ∈ Finset.range N,
                  φ k ω * (B (s (k + 1)) ω - B (s k) ω))
                * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 3) ∂μ)
            + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ :=
            by rw [integral_add hintZ4 (hintZY0.const_mul 4)]
        _ = ∫ ω, (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
              + 6 * ∫ ω, (∑ k ∈ Finset.range N,
                    φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
                  * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 ∂μ
              + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul]
            rw [hZY0, hY30]
            ring
    -- the real-form IH (the ∫⁻ ihN converted through the internal integrability)
    have ihNreal : ∫ ω, (∑ k ∈ Finset.range N,
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
        ≤ 3 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)) ^ 2 := by
      have h1 : ENNReal.ofReal (∫ ω, (∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ)
          = ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range N,
          φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hintZ4
          (Eventually.of_forall fun ω ↦ show (0:ℝ) ≤ (∑ k ∈ Finset.range N,
            φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 from by positivity)
      have h2 := ihN
      rw [← h1] at h2
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    -- assemble (real form)
    have hreal : ∫ ω, (∑ k ∈ Finset.range (N + 1),
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
      ≤ 3 * (D ^ 2 * ∑ k ∈ Finset.range (N + 1), ((s (k + 1) : ℝ) - s k)) ^ 2 := by
      rw [hgapexpan, integral_congr_ae (Eventually.of_forall hexpan4)]
      calc ∫ ω, ((∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω))
            + φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ
          = ∫ ω, (∑ k ∈ Finset.range N,
              φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 ∂μ
            + 6 * ∫ ω, (∑ k ∈ Finset.range N,
                φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 2
              * (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 2 ∂μ
            + ∫ ω, (φ N ω * (B (s (N + 1)) ω - B (s N) ω)) ^ 4 ∂μ := hexp
        _ ≤ 3 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)) ^ 2
            + 6 * ((D ^ 2 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)))
              * ((s (N + 1) : ℝ) - s N))
            + 3 * (D ^ 2 * ((s (N + 1) : ℝ) - s N)) ^ 2 :=
            add_le_add (add_le_add ihNreal
              (mul_le_mul_of_nonneg_left hZY2le (by norm_num))) hy4le
        _ = 3 * (D ^ 2 * ((∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k))
              + ((s (N + 1) : ℝ) - s N))) ^ 2 := by
            ring
    -- integrability of the step sum's fourth power, and the ∫⁻ conversion
    have hintS : Integrable (fun ω ↦ (∑ k ∈ Finset.range (N + 1),
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4) μ := by
      refine (hintBIG4.add hintYN4).congr (Eventually.of_forall fun ω ↦ ?_)
      simp only [Pi.add_apply]
      rw [hexpan4 ω]
      ring
    rw [← ofReal_integral_eq_lintegral_ofReal hintS
      (Eventually.of_forall fun ω ↦ show (0:ℝ) ≤ (∑ k ∈ Finset.range (N + 1),
        φ k ω * (B (s (k + 1)) ω - B (s k) ω)) ^ 4 from by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
omit hB hδcont hMadap hMeq in
/-- The step-approximant process value at a grid point of its own partition, as the
running Itô sum (the range form of `itoSimpleProcess_stepσ_incr`). -/
private theorem stepValue_eq_sum {m J : ℕ} (hJm : J ≤ m) (ω : Ω) :
    itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T m).val (unifPart T m J) ω
      = ∑ j ∈ Finset.range J, δ (unifPart T m j) ω
          * (B (unifPart T m (j + 1)) ω - B (unifPart T m j) ω) := by
  induction J with
  | zero =>
    rw [unifPart_zero]
    simp
  | succ J ihJ =>
    have hJm' : J < m := Nat.lt_of_succ_le hJm
    have hincr := itoSimpleProcess_stepσ_incr hBmeas hδadap hδbdd T (n := m) (k := J) hJm' ω
    rw [Finset.sum_range_succ, ← ihJ (Nat.le_of_succ_le hJm)]
    rw [show itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T m).val
          (unifPart T m (J + 1)) ω
        = itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T m).val (unifPart T m J) ω
          + δ (unifPart T m J) ω
            * (B (unifPart T m (J + 1)) ω - B (unifPart T m J) ω) from by rw [← hincr]; ring]

omit hMadap hMeq in
/-- **The `∫⁻` fourth-moment bound** for the CLM increment over a uniform cell (the Fatou
passage from the step approximants):
`∫⁻ ω, ENNReal.ofReal ((CLM_v − CLM_u) ω ^ 4) ∂μ ≤ ENNReal.ofReal (3·(D_δ²·cell)²)`.
Route: refine each cell into `2^p` sub-cells (the grid `m = n·2^p` contains the cell
endpoints), so the step-approximant band increment is exactly an Itô sum over consecutive
refined grid points (`stepSum_pow4_le` bounds its fourth moment uniformly in `p`); the `L²`
contraction (`itoProcessCLM_norm_le`) plus `deltaStepLp_tendsto` converge the increments in
measure, an a.e. subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`) and Fatou
(`lintegral_liminf_le'`) pass the bound to the true increment. The `∫⁻` form is the honest
one: it feeds both the `Integrable` extraction and the real-integral bound. -/
private theorem trueIncr_pow4_lintegral_le {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    ∫⁻ ω, ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd)
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) ∂μ
      ≤ ENNReal.ofReal (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
  -- grid arithmetic: the refined partition `m = n·2^p` contains the cell endpoints
  have hgrid : ∀ (p j : ℕ), unifPart T (n * 2 ^ p) (2 ^ p * j) = unifPart T n j := by
    intro p j
    have hn0 : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    have h2r : (2 : ℝ) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
    refine NNReal.coe_injective ?_
    push_cast [unifPart]
    field_simp [hn0, h2r]
  have hJ1le : ∀ p : ℕ, 2 ^ p * k ≤ n * 2 ^ p := fun p ↦
    (Nat.mul_le_mul (le_refl (2 ^ p)) hk.le).trans_eq (Nat.mul_comm (2 ^ p) n)
  have hJ2le : ∀ p : ℕ, 2 ^ p * (k + 1) ≤ n * 2 ^ p := fun p ↦
    (Nat.mul_le_mul (le_refl (2 ^ p)) hk).trans_eq (Nat.mul_comm (2 ^ p) n)
  -- the a.e. identification of the CLM process of a step embedding
  have hcoe : ∀ (p : ℕ) (t : ℝ≥0),
      (itoProcessCLM hB T t hBmeas (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)) : Ω → ℝ)
        =ᵐ[μ] itoSimpleProcess hBmeas (stepσ hBmeas hδadap hδbdd T (n * 2 ^ p)).val t := by
    intro p t
    rw [show (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p))
          = simpleAssembly_T (μ := μ) T hBmeas
            (stepσ hBmeas hδadap hδbdd T (n * 2 ^ p)) from rfl,
      itoProcessCLM_simpleAssembly_T hB T t hBmeas
        (stepσ hBmeas hδadap hδbdd T (n * 2 ^ p))]
    exact (memLp_itoSimpleProcess hB hBmeas
      (stepσ hBmeas hδadap hδbdd T (n * 2 ^ p)).val t).coeFn_toLp
  -- the refined step-sum identification (a.e.)
  have hsumae : ∀ (p : ℕ),
      (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)) : Ω → ℝ) ω)
        =ᵐ[μ] (fun ω ↦ ∑ j ∈ Finset.range (2 ^ p),
            δ (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω
              * (B (unifPart T (n * 2 ^ p) (2 ^ p * k + j + 1)) ω
                - B (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω)) := by
    intro p
    filter_upwards [hcoe p (unifPart T n (k + 1)), hcoe p (unifPart T n k)] with ω h1 h2
    rw [← hgrid p (k + 1)] at h1
    rw [← hgrid p k] at h2
    have hv1 := stepValue_eq_sum (T := T) hBmeas hδadap hδbdd (hJ2le p) ω
    have hv0 := stepValue_eq_sum (T := T) hBmeas hδadap hδbdd (hJ1le p) ω
    rw [← hgrid p (k + 1), ← hgrid p k, h1, h2, hv1, hv0,
      show ((2:ℕ) ^ p * (k + 1)) = 2 ^ p * k + 2 ^ p from by ring, Finset.sum_range_add,
      add_sub_cancel_left]
  -- the refined-band gap telescopes to the cell length
  have hgapsum : ∀ p : ℕ, ∑ j ∈ Finset.range (2 ^ p),
      ((unifPart T (n * 2 ^ p) (2 ^ p * k + (j + 1)) : ℝ)
        - unifPart T (n * 2 ^ p) (2 ^ p * k + j))
      = ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    intro p
    rw [Finset.sum_range_sub (fun j : ℕ ↦ ((unifPart T (n * 2 ^ p) (2 ^ p * k + j) : ℝ)))]
    simp only [Nat.add_zero]
    rw [show ((2 : ℕ) ^ p * k + 2 ^ p) = 2 ^ p * (k + 1) from by ring, hgrid p (k + 1),
      hgrid p k]
  -- the per-refinement fourth-moment bound (uniform in `p`, `∫⁻` form)
  have hperp : ∀ p : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((∑ j ∈ Finset.range (2 ^ p),
          δ (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω
            * (B (unifPart T (n * 2 ^ p) (2 ^ p * k + (j + 1))) ω
              - B (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω)) ^ 4) ∂μ
        ≤ ENNReal.ofReal
          (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
    intro p
    refine le_trans (stepSum_pow4_le hB hBmeas
      (Monotone.comp (unifPart_mono T (n * 2 ^ p))
        fun i j hij ↦ Nat.add_le_add_left hij (2 ^ p * k))
      (fun j ↦ (hδadap (unifPart T (n * 2 ^ p) (2 ^ p * k + j))).measurable)
      (fun j ω ↦ hδbdd (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω) (2 ^ p)) ?_
    change ENNReal.ofReal (3 * (Dd ^ 2 * ∑ j ∈ Finset.range (2 ^ p),
        ((unifPart T (n * 2 ^ p) (2 ^ p * k + (j + 1)) : ℝ)
          - unifPart T (n * 2 ^ p) (2 ^ p * k + j))) ^ 2)
      ≤ ENNReal.ofReal
        (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2)
    rw [hgapsum p]
  -- the `L²` contraction convergence of the band increments
  have hconv : Tendsto (fun p : ℕ ↦
      ‖((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p))
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)))
        - (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)) : Lp ℝ 2 μ)‖) atTop (𝓝 0) := by
    have hemb : Tendsto (fun p : ℕ ↦ n * 2 ^ p) atTop atTop := by
      refine Filter.tendsto_atTop_atTop.mpr fun j ↦ ⟨j, fun p hp ↦ ?_⟩
      calc j ≤ p := hp
        _ ≤ 2 ^ p := Nat.lt_two_pow_self.le
        _ ≤ n * 2 ^ p :=
          (Nat.le_mul_of_pos_right (2 ^ p) hn).trans_eq (Nat.mul_comm (2 ^ p) n)
    have hsub := deltaStepLp_tendsto (T := T) hB hBmeas hδadap hδcont hδbdd
    have hFp : Tendsto (fun p : ℕ ↦
        ‖(deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
          - processToLp T hBmeas hδadap hδcont hδbdd :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero.mp hsub).comp hemb
    refine squeeze_zero' (Eventually.of_forall fun _p ↦ norm_nonneg _)
      (Eventually.of_forall fun p ↦ ?_)
      (by simpa using hFp.mul (tendsto_const_nhds (x := (2 : ℝ))))
    have hdec : ∀ p : ℕ,
        ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p))
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)))
        - (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)) : Lp ℝ 2 μ)
        = (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)) := by
      intro p
      simp only [map_sub]
      abel
    rw [hdec p]
    calc ‖(itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ)‖
        ≤ ‖itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)‖
          + ‖itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)‖ := norm_sub_le _ _
      _ ≤ ‖(deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ * 2 := by
          have h1 := itoProcessCLM_norm_le hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)
          have h2 := itoProcessCLM_norm_le hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
              - processToLp T hBmeas hδadap hδcont hδbdd)
          have h3 : ‖(deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
                - processToLp T hBmeas hδadap hδcont hδbdd :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ * 2
              = ‖(deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
                  - processToLp T hBmeas hδadap hδcont hδbdd :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖
              + ‖(deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)
                  - processToLp T hBmeas hδadap hδcont hδbdd :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ := by ring
          rw [h3]
          exact add_le_add h1 h2
      _ = _ := rfl
  -- convergence in measure, a.e. subsequence, Fatou
  have h2inst : Fact (1 ≤ 2) := ⟨by norm_num⟩
  have hLp : Tendsto (fun p : ℕ ↦
      (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p))
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)) : Lp ℝ 2 μ)) atTop
      (𝓝 (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd)
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hconv
  have htmi : TendstoInMeasure μ (fun p : ℕ ↦
      ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p))
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ p)) : Lp ℝ 2 μ) : Ω → ℝ)) atTop
      ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd)
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp (p := 2) hLp
  obtain ⟨ns, _hnsmono, hae⟩ := htmi.exists_seq_tendsto_ae
  -- the Fatou functions and their a.e. limit (coe-of-difference forms throughout)
  have hXmeas : ∀ i : ℕ, AEMeasurable
      (fun ω : Ω ↦ ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)) μ :=
    fun i ↦ (ENNReal.continuous_ofReal.measurable).comp_aemeasurable
      (AEMeasurable.pow_const
        (Lp.aestronglyMeasurable
          (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)) :
            Lp ℝ 2 μ)).aemeasurable 4)
  have hbound : ∀ i : ℕ,
      ∫⁻ ω, ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) ∂μ
      ≤ ENNReal.ofReal (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
    intro i
    have hc : ∀ᵐ ω : Ω ∂μ, ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)
        = ENNReal.ofReal ((∑ j ∈ Finset.range (2 ^ ns i),
          δ (unifPart T (n * 2 ^ ns i) (2 ^ ns i * k + j)) ω
            * (B (unifPart T (n * 2 ^ ns i) (2 ^ ns i * k + j + 1)) ω
              - B (unifPart T (n * 2 ^ ns i) (2 ^ ns i * k + j)) ω)) ^ 4) := by
      filter_upwards [Lp.coeFn_sub
          (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)))
          (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))),
        hsumae (ns i)] with ω h1 h2
      rw [h1, Pi.sub_apply, h2]
    rw [lintegral_congr_ae hc]
    exact hperp (ns i)
  have hGmeas : AEMeasurable
      (fun ω : Ω ↦ ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd)
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)) μ :=
    (ENNReal.continuous_ofReal.measurable).comp_aemeasurable
      (AEMeasurable.pow_const
        (Lp.aestronglyMeasurable
          (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd)
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd) :
            Lp ℝ 2 μ)).aemeasurable 4)
  have hlimfun : ∀ᵐ ω : Ω ∂μ,
      ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd)
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)
        = atTop.liminf (fun i : ℕ ↦ ENNReal.ofReal
          ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
                (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i))
              - itoProcessCLM hB T (unifPart T n k) hBmeas
                (deltaStepLp hBmeas hδadap hδbdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)) := by
    filter_upwards [hae] with ω hw
    have hcont : Continuous fun x : ℝ ↦ ENNReal.ofReal (x ^ 4) :=
      (ENNReal.continuous_ofReal).comp (continuous_pow (4 : ℕ))
    exact ((hcont.tendsto _).comp hw).liminf_eq.symm
  have hlimint : ∫⁻ ω, ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd)
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) ∂μ
      ≤ ENNReal.ofReal (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
    rw [lintegral_congr_ae hlimfun]
    refine le_trans (lintegral_liminf_le' fun i ↦ hXmeas i) ?_
    exact Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hbound)
  -- the ∫⁻-bound is the conclusion of the lemma
  exact hlimint

omit hMadap hMeq in
/-- The CLM increment is in `L⁴` (coe-difference form): `AEStronglyMeasurable` from the
`Lp` structure, finiteness from the ∫⁻-bound of `trueIncr_pow4_lintegral_le`
(`hasFiniteIntegral_iff_ofReal` — note the elaboration-order trap of
`ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top …`: the `≠ ⊤` arguments force
`a := ENNReal.ofReal _`, so a lintegral LHS never unifies; stay in the `ofReal` world). -/
private theorem clmIncr_pow4_integrable {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    Integrable (fun ω ↦ (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) μ :=
  ⟨(Lp.aestronglyMeasurable
      (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd)
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd) :
        Lp ℝ 2 μ)).pow 4,
    by
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω ↦ by positivity)]
      exact lt_of_le_of_lt
        (trueIncr_pow4_lintegral_le hB hBmeas hδadap hδcont hδbdd hn k hk)
        ENNReal.ofReal_lt_top⟩

omit hMadap in
/-- The fourth power of the true increment is a.e. the fourth power of the CLM coe-difference
(the a.e. transfer along `hMeq`, shared by `trueIncr_pow4_integrable` and `trueIncr_pow4_le`). -/
private theorem abs_pow4_trueIncr_ae (n k : ℕ) :
    (fun ω ↦ |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4)
    =ᵐ[μ] (fun ω ↦ (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd)
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) := by
  filter_upwards [hMeq (unifPart T n (k + 1)), hMeq (unifPart T n k),
    Lp.coeFn_sub
      (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd))
      (itoProcessCLM hB T (unifPart T n k) hBmeas
        (processToLp T hBmeas hδadap hδcont hδbdd))] with ω h1 h0 hsub
  show |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4 = _
  rw [h1, h0, ← Pi.sub_apply, ← hsub, ← abs_pow]
  exact abs_of_nonneg (by positivity)

omit hMadap in
/-- The true increment is in `L⁴` (modifying-process form): the a.e. transfer of
`clmIncr_pow4_integrable` along the `hMeq` congruence. -/
theorem trueIncr_pow4_integrable {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    Integrable (fun ω ↦ |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4) μ := by
  have hG4 := abs_pow4_trueIncr_ae hB hBmeas hδadap hδcont hδbdd hMeq n k
  exact (clmIncr_pow4_integrable hB hBmeas hδadap hδcont hδbdd hn k hk).congr hG4.symm

omit hMadap in
/-- **The fourth moment of the true increment** over a uniform cell:
`𝔼[(M_{tₖ₊₁} − M_{tₖ})⁴] ≤ 3·(D_δ²·cell)²` — the a.e. transfer of the CLM ∫⁻-bound to the
modifying process `M`, with the real integral recovered from the ∫⁻-bound by
`ofReal`-injectivity (`ofReal_integral_eq_lintegral_ofReal` +
`ENNReal.ofReal_le_ofReal_iff`). -/
theorem trueIncr_pow4_le {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    ∫ ω, |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4 ∂μ
      ≤ 3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2 := by
  -- a.e. transfer to the CLM coe-difference
  have hG4 := abs_pow4_trueIncr_ae hB hBmeas hδadap hδcont hδbdd hMeq n k
  rw [integral_congr_ae hG4]
  have hint4 : Integrable (fun ω ↦ (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) μ :=
    clmIncr_pow4_integrable hB hBmeas hδadap hδcont hδbdd hn k hk
  have hofR : ENNReal.ofReal (∫ ω, (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (processToLp T hBmeas hδadap hδcont hδbdd) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4 ∂μ)
      ≤ ENNReal.ofReal (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint4
      (Eventually.of_forall fun ω ↦ by positivity)]
    exact trueIncr_pow4_lintegral_le hB hBmeas hδadap hδcont hδbdd hn k hk
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg zero_le_three
      (sq_nonneg (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))))).mp hofR

/-- **The third-moment bound** for the true increment (the Taylor-remainder kernel of the
adapted assembly): `𝔼|ΔM|³ ≤ √(3·(D_δ²·cell)³) = O(cell^{3/2})`. Route: Cauchy–Schwarz
interpolation `∫|X|³ = ∫|X·X²| ≤ ‖X‖₂·‖X²‖₂` (the real `L²` pairing
`integral_abs_mul_le_sqrt_mul_sqrt`), the two factors from `trueIncr_sq_le` and `trueIncr_pow4_le`;
the `L²` memberships from `memLp_M` (for `X`) and from the `L⁴` integrability
(`integrable_norm_rpow_iff` + the pointwise `‖X²‖² = X⁴` identification) for `X²`. -/
theorem trueIncr_pow3_le {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    ∫ ω, |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 3 ∂μ
      ≤ Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3) := by
  -- the increment and its `L²` membership (from `memLp_M`)
  have hΔ2 : MemLp (fun ω ↦ M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) 2 μ :=
    (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n (k + 1))).sub
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n k))
  -- the two energy bounds
  have huv : unifPart T n k ≤ unifPart T n (k + 1) :=
    unifPart_mono T n (Nat.le_succ k)
  have hvT : unifPart T n (k + 1) ≤ T :=
    unifPart_le_T (Nat.lt_iff_add_one_le.mp hk)
  have hcellnn : (0:ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr huv)
  have hint2 : ∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
      ≤ Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
    trueIncr_sq_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq huv hvT
  -- the fourth moment in un-absolutized form, and its `Integrable` witness (for `X²`)
  have hint4M : Integrable (fun ω ↦
      (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4) μ :=
    (trueIncr_pow4_integrable hB hBmeas hδadap hδcont hδbdd hMeq hn k hk).congr
      (Eventually.of_forall fun ω ↦ Even.pow_abs ⟨2, rfl⟩ _)
  have hint4 : ∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4 ∂μ
      ≤ 3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2 := by
    refine le_trans (le_of_eq ?_)
      (trueIncr_pow4_le hB hBmeas hδadap hδcont hδbdd hMeq hn k hk)
    exact integral_congr_ae (μ := μ)
      (Eventually.of_forall fun ω ↦ (Even.pow_abs ⟨2, rfl⟩ _).symm)
  -- `L²` membership of `X²`: from the `L⁴` integrability via `integrable_norm_rpow_iff`
  have hΔsq2 : MemLp (fun ω ↦
      (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2) 2 μ :=
    (integrable_norm_rpow_iff (hΔ2.aestronglyMeasurable.pow 2) (by norm_num) (by simp)).mp
      (hint4M.congr (Eventually.of_forall fun ω ↦
        show (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4
          = ‖(M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2‖
              ^ ((2 : ℕ) : ℝ≥0∞).toReal from by
          -- the `(2 : ℝ) = ((2 : ℕ) : ℝ)` pre-rewrite unblocks `rpow_natCast`
          rw [show ((2 : ℕ) : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.norm_eq_abs,
            show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num, Real.rpow_natCast, abs_pow, sq_abs,
            ← pow_mul]))
  -- Cauchy–Schwarz interpolation and the two energy bounds
  calc ∫ ω, |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 3 ∂μ
      = ∫ ω, |(M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2| ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
        change |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 3
          = |(M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2|
        rw [abs_mul, abs_pow]
        ring
    _ ≤ Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
        * Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4 ∂μ) := by
        refine le_trans (integral_abs_mul_le_sqrt_mul_sqrt hΔ2 hΔsq2) ?_
        refine mul_le_mul le_rfl (Real.sqrt_le_sqrt (le_of_eq ?_))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        exact integral_congr_ae (μ := μ)
          (Eventually.of_forall fun ω ↦
            show ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2) ^ 2
              = (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4 from by
              rw [← pow_mul])
    _ ≤ Real.sqrt (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
        * Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hint2) (Real.sqrt_le_sqrt hint4)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
          * (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2)) :=
        (Real.sqrt_mul (mul_nonneg (sq_nonneg Dd) hcellnn)
          (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2)).symm
    _ = Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3) := by
        rw [show (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
              * (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2)
            = 3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3 from by ring]

end StageFiveB

end MathFin.ItoDriftConditional
