/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralL2
public import MathFin.Foundations.QuadraticVariationL2
public import MathFin.Foundations.GaussianMoments

/-! # The fourth moment of a bounded adapted Brownian sum

For a bounded integrand `φ j`, `𝓕_{s j}`-measurable along a monotone time grid `s`, the Itô sum
`∑_{k<N} φ_k (B_{s_{k+1}} − B_{s_k})` has fourth moment at most `3·(D²·total gap)²`
(`stepSum_pow4_le`, `D` the bound of `φ`, the total gap `s_N − s_0`). It is the fourth-moment
kernel of the discrete route to the Itô formula: `trueIncr_pow4_le` in `ItoDriftMomentBounds` is
this bound passed to the limit along the step approximants.

The proof is an induction on `N`. Writing the sum as `Z + y` with `Z` the first `N` terms and
`y = φ_N ΔB_N`, the expansion of `(Z + y)⁴` loses its odd terms to the vanishing odd Gaussian
moments of the independent increment (`integral_natMeasurable_mul_increment_pow3`, from
`integral_increment_pow3`); the middle term `6·E[Z²y²]` is the independence kernel at the
`𝓕_{s N}`-measurable weight `Z²φ_N²`, with `E[Z²]` the discrete Itô isometry; `E[y⁴]` is the
fourth-moment kernel `integral_natMeasurable_mul_increment_pow4` (`3(Δs)²`). The integrability the
odd terms need is Young's inequality `|a|³|b| ≤ 3a⁴/4 + b⁴/4` against fourth powers.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 ItoIsometryAdapted QuadraticVariationL2

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

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))

include hB hBmeas

omit hBmeas in
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
/-- **The step-sum fourth-moment recursion**: for a bounded integrand sampled along a
monotone time grid (`φ j` measurable in `𝓕_{s j}`, `|φ| ≤ D`), the fourth moment of the
Itô sum is at most `3·(D²·total gap)²`. -/
theorem stepSum_pow4_le {s : ℕ → ℝ≥0} (hsmono : Monotone s) {φ : ℕ → Ω → ℝ}
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

end MathFin.ItoDriftConditional
