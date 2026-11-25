/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Probability.Brownian.Ito.ItoIntegralL2
public import MathFin.Probability.Brownian.QuadraticVariationL2
public import MathFin.Probability.Gaussian.GaussianMoments
public import Mathlib.Tactic.Polynomial.Basic

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

## Main results

* `stepSum_pow4_le`: for a bounded integrand `φ j` (`|φ| ≤ D`), `𝓕_{s j}`-measurable along a
  monotone grid `s`, the fourth moment of `∑_{k<N} φ_k (B_{s_{k+1}} − B_{s_k})` is at most
  `3·(D²·total gap)²`.

## Tags

fourth moment, Itô sum, Gaussian moments, Brownian increments, moment estimate, Young inequality,
MSC 60H05, MSC 60E15, MSC 60J65
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 ItoIsometryAdapted QuadraticVariationL2

/-- Young's pointwise inequality `|a|³|b| ≤ 3a⁴/4 + b⁴/4`: from
`(a − b)²(2a² + (a+b)²) = 3a⁴ + b⁴ − 4a³b ≥ 0`, evaluated at `(|a|, |b|)`. -/
theorem young34 (a b : ℝ) : |a| ^ 3 * |b| ≤ 3 * a ^ 4 / 4 + b ^ 4 / 4 := by
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

section FourthPowers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The fourth power of an `L⁴` function is integrable. -/
private lemma integrable_pow_four_of_memLp {Z : Ω → ℝ} (hZ : MemLp Z 4 μ) :
    Integrable (fun ω ↦ Z ω ^ 4) μ :=
  (hZ.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)).congr (Eventually.of_forall fun ω ↦ by
    change ‖Z ω‖ ^ 4 = Z ω ^ 4
    rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)])

/-- `Z³Y` is integrable for `Z, Y ∈ L⁴`: Young's inequality `|a|³|b| ≤ 3a⁴/4 + b⁴/4` against
fourth powers. -/
private lemma integrable_cube_mul {Z Y : Ω → ℝ} (hZ : MemLp Z 4 μ) (hY : MemLp Y 4 μ) :
    Integrable (fun ω ↦ Z ω ^ 3 * Y ω) μ :=
  Integrable.mono' (((integrable_pow_four_of_memLp hZ).const_mul (3 / 4)).add
      ((integrable_pow_four_of_memLp hY).const_mul (1 / 4)))
    ((hZ.aestronglyMeasurable.pow 3).mul hY.aestronglyMeasurable)
    (ae_of_all μ fun ω ↦ by
      change ‖Z ω ^ 3 * Y ω‖ ≤ 3 / 4 * Z ω ^ 4 + 1 / 4 * Y ω ^ 4
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have := young34 (Z ω) (Y ω)
      linarith)

/-- `ZY³` is integrable for `Z, Y ∈ L⁴`. -/
private lemma integrable_mul_cube {Z Y : Ω → ℝ} (hZ : MemLp Z 4 μ) (hY : MemLp Y 4 μ) :
    Integrable (fun ω ↦ Z ω * Y ω ^ 3) μ :=
  Integrable.mono' (((integrable_pow_four_of_memLp hZ).const_mul (1 / 4)).add
      ((integrable_pow_four_of_memLp hY).const_mul (3 / 4)))
    (hZ.aestronglyMeasurable.mul (hY.aestronglyMeasurable.pow 3))
    (ae_of_all μ fun ω ↦ by
      change ‖Z ω * Y ω ^ 3‖ ≤ 1 / 4 * Z ω ^ 4 + 3 / 4 * Y ω ^ 4
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have := young34 (Y ω) (Z ω)
      linarith)

/-- `Z²Y²` is integrable for `Z, Y ∈ L⁴`: `2a²b² ≤ a⁴ + b⁴`. -/
private lemma integrable_sq_mul_sq {Z Y : Ω → ℝ} (hZ : MemLp Z 4 μ) (hY : MemLp Y 4 μ) :
    Integrable (fun ω ↦ Z ω ^ 2 * Y ω ^ 2) μ :=
  Integrable.mono' (((integrable_pow_four_of_memLp hZ).const_mul (1 / 2)).add
      ((integrable_pow_four_of_memLp hY).const_mul (1 / 2)))
    ((hZ.aestronglyMeasurable.pow 2).mul (hY.aestronglyMeasurable.pow 2))
    (ae_of_all μ fun ω ↦ by
      change ‖Z ω ^ 2 * Y ω ^ 2‖ ≤ 1 / 2 * Z ω ^ 4 + 1 / 2 * Y ω ^ 4
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg (Z ω ^ 2 - Y ω ^ 2)])

/-- **The fourth moment of a sum, with the odd cross terms vanishing**: for `Z, Y ∈ L⁴` with
`E[Z³Y] = E[ZY³] = 0`, `E[(Z + Y)⁴] = E[Z⁴] + 6 E[Z²Y²] + E[Y⁴]`. -/
private lemma integral_add_pow_four {Z Y : Ω → ℝ} (hZ : MemLp Z 4 μ) (hY : MemLp Y 4 μ)
    (h3 : ∫ ω, Z ω ^ 3 * Y ω ∂μ = 0) (h1 : ∫ ω, Z ω * Y ω ^ 3 ∂μ = 0) :
    ∫ ω, (Z ω + Y ω) ^ 4 ∂μ
      = ∫ ω, Z ω ^ 4 ∂μ + 6 * ∫ ω, Z ω ^ 2 * Y ω ^ 2 ∂μ + ∫ ω, Y ω ^ 4 ∂μ := by
  have i4 := integrable_pow_four_of_memLp hZ
  have j4 := integrable_pow_four_of_memLp hY
  have e1 : Integrable (fun ω ↦ Z ω ^ 4 + 4 * (Z ω ^ 3 * Y ω)) μ :=
    i4.add ((integrable_cube_mul hZ hY).const_mul 4)
  have e2 : Integrable (fun ω ↦ Z ω ^ 4 + 4 * (Z ω ^ 3 * Y ω) + 6 * (Z ω ^ 2 * Y ω ^ 2)) μ :=
    e1.add ((integrable_sq_mul_sq hZ hY).const_mul 6)
  have e3 : Integrable (fun ω ↦ Z ω ^ 4 + 4 * (Z ω ^ 3 * Y ω) + 6 * (Z ω ^ 2 * Y ω ^ 2)
      + 4 * (Z ω * Y ω ^ 3)) μ :=
    e2.add ((integrable_mul_cube hZ hY).const_mul 4)
  have hfun : (fun ω ↦ (Z ω + Y ω) ^ 4) = fun ω ↦ Z ω ^ 4 + 4 * (Z ω ^ 3 * Y ω)
      + 6 * (Z ω ^ 2 * Y ω ^ 2) + 4 * (Z ω * Y ω ^ 3) + Y ω ^ 4 := funext fun ω ↦ by ring
  rw [hfun, integral_add e3 j4, integral_add e2 ((integrable_mul_cube hZ hY).const_mul 4),
    integral_add e1 ((integrable_sq_mul_sq hZ hY).const_mul 6),
    integral_add i4 ((integrable_cube_mul hZ hY).const_mul 4), integral_const_mul,
    integral_const_mul, integral_const_mul, h3, h1]
  ring

end FourthPowers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))

/-! ### The step sum and its terms -/

/-- The `k`-th term `φ_k (B_{s_{k+1}} − B_{s_k})` of the Itô sum along the grid `s`. -/
private noncomputable def stepTerm {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (s : ℕ → ℝ≥0)
    (φ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  φ k ω * (B (s (k + 1)) ω - B (s k) ω)

/-- The Itô sum `∑_{k<N} φ_k (B_{s_{k+1}} − B_{s_k})` along the grid `s`. -/
private noncomputable def stepSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (s : ℕ → ℝ≥0)
    (φ : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N, stepTerm B s φ k ω

private lemma stepSum_succ {s : ℕ → ℝ≥0} {φ : ℕ → Ω → ℝ} (N : ℕ) (ω : Ω) :
    stepSum B s φ (N + 1) ω = stepSum B s φ N ω + stepTerm B s φ N ω :=
  Finset.sum_range_succ _ _

include hB hBmeas

omit hBmeas in
/-- Third moment of a Brownian increment: `E[(B_{t₁} − B_{t₀})³] = 0` for `t₀ ≤ t₁`
(the law-transfer of the vanishing odd Gaussian moment). -/
theorem integral_increment_pow3
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

omit hB in
/-- The step sum of the first `N` terms is measurable at the grid point `s N`. -/
private lemma measurable_stepSum {s : ℕ → ℝ≥0} (hsmono : Monotone s) {φ : ℕ → Ω → ℝ}
    (hφm : ∀ j, Measurable[natFiltration hBmeas (s j)] (φ j)) (N : ℕ) :
    Measurable[natFiltration hBmeas (s N)] (stepSum B s φ N) := by
  have hBle : ∀ {u : ℝ≥0}, u ≤ s N → Measurable[natFiltration hBmeas (s N)] (B u) := by
    intro u hu
    have hle : MeasurableSpace.comap (B u) (inferInstance : MeasurableSpace ℝ)
        ≤ natFiltration hBmeas (s N) := le_iSup₂_of_le u hu le_rfl
    exact (measurable_iff_comap_le.mpr le_rfl).mono hle le_rfl
  show Measurable[natFiltration hBmeas (s N)]
    (fun ω ↦ ∑ k ∈ Finset.range N, φ k ω * (B (s (k + 1)) ω - B (s k) ω))
  refine Finset.measurable_sum _ fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  exact ((hφm k).mono ((natFiltration hBmeas).mono (hsmono hk'.le)) le_rfl).mul
    ((hBle (hsmono (Nat.succ_le_of_lt hk'))).sub (hBle (hsmono hk'.le)))

/-- Each term of the step sum is in `L⁴`: the bounded integrand is independent of the increment,
whose fourth moment is finite. -/
private lemma memLp_stepTerm {s : ℕ → ℝ≥0} (hsmono : Monotone s) {φ : ℕ → Ω → ℝ}
    (hφm : ∀ j, Measurable[natFiltration hBmeas (s j)] (φ j))
    {D : ℝ} (hφbdd : ∀ j ω, |φ j ω| ≤ D) (k : ℕ) :
    MemLp (stepTerm B s φ k) 4 μ := by
    have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
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

/-- The step sum of the first `N` terms is in `L⁴`. -/
private lemma memLp_stepSum {s : ℕ → ℝ≥0} (hsmono : Monotone s) {φ : ℕ → Ω → ℝ}
    (hφm : ∀ j, Measurable[natFiltration hBmeas (s j)] (φ j))
    {D : ℝ} (hφbdd : ∀ j ω, |φ j ω| ≤ D) (N : ℕ) :
    MemLp (stepSum B s φ N) 4 μ :=
  memLp_finsetSum (f := stepTerm B s φ) _ fun k _ ↦ memLp_stepTerm hB hBmeas hsmono hφm hφbdd k

/-! ### The two odd kernels vanish -/

/-- `E[Z³Y] = 0` for `Z` the first `N` terms and `Y` the next: the weight `Z³φ_N` is
`𝓕_{s N}`-measurable and the increment is a centred independent one. -/
private lemma integral_stepSum_cube_mul_term {s : ℕ → ℝ≥0} (hsmono : Monotone s)
    {φ : ℕ → Ω → ℝ} (hφm : ∀ j, Measurable[natFiltration hBmeas (s j)] (φ j)) (N : ℕ) :
    ∫ ω, stepSum B s φ N ω ^ 3 * stepTerm B s φ N ω ∂μ = 0 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hZ3 : Measurable[natFiltration hBmeas (s N)] (fun ω ↦ stepSum B s φ N ω ^ 3 * φ N ω) :=
    ((measurable_stepSum hBmeas hsmono hφm N).pow_const 3).mul (hφm N)
  refine (integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)).trans
    (integral_adapted_mul_increment (hB.isFilteredPreBrownian hBmeas)
      (hsmono (Nat.le_succ N)) hZ3)
  simp only [stepTerm]
  ring

/-- `E[ZY³] = 0`: the odd Gaussian moment of the increment vanishes
(`integral_natMeasurable_mul_increment_pow3`). -/
private lemma integral_stepSum_mul_term_cube {s : ℕ → ℝ≥0} (hsmono : Monotone s)
    {φ : ℕ → Ω → ℝ} (hφm : ∀ j, Measurable[natFiltration hBmeas (s j)] (φ j)) (N : ℕ) :
    ∫ ω, stepSum B s φ N ω * stepTerm B s φ N ω ^ 3 ∂μ = 0 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hcoef : Measurable[natFiltration hBmeas (s N)]
      (fun ω ↦ stepSum B s φ N ω * φ N ω ^ 3) :=
    (measurable_stepSum hBmeas hsmono hφm N).mul ((hφm N).pow_const 3)
  refine (integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)).trans
    (integral_natMeasurable_mul_increment_pow3 hB hBmeas (hsmono (Nat.le_succ N)) hcoef)
  simp only [stepTerm]
  ring

/-! ### The three even terms -/

/-- The second moment of the first `N` terms is at most `D²` times the total gap: the discrete
Itô isometry. -/
private lemma integral_sq_stepSum_le {s : ℕ → ℝ≥0} (hsmono : Monotone s) {φ : ℕ → Ω → ℝ}
    (hφm : ∀ j, Measurable[natFiltration hBmeas (s j)] (φ j))
    {D : ℝ} (hφbdd : ∀ j ω, |φ j ω| ≤ D) (N : ℕ) :
    ∫ ω, stepSum B s φ N ω ^ 2 ∂μ
      ≤ D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hφL2 : ∀ k : ℕ, MemLp (φ k) 2 μ := fun k ↦
    MemLp.of_bound (((hφm k).mono ((natFiltration hBmeas).le _) le_rfl)).aestronglyMeasurable
      D (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hφbdd k ω)
  have hZ2 : ∫ ω, stepSum B s φ N ω ^ 2 ∂μ
      = ∑ k ∈ Finset.range N, (∫ ω, (φ k ω) ^ 2 ∂μ) * ((s (k + 1) : ℝ) - s k) :=
    ito_isometry_discrete (hB.isFilteredPreBrownian hBmeas) hsmono hφm hφL2
  rw [hZ2, Finset.mul_sum]
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

/-- The mixed term `E[Z²Y²]` is at most `D²·(D²·total gap)·Δs`: the independence kernel at the
`𝓕_{s N}`-measurable weight `Z²φ_N²`, with `E[Z²]` the discrete Itô isometry. -/
private lemma integral_sq_stepSum_mul_term_sq_le {s : ℕ → ℝ≥0} (hsmono : Monotone s)
    {φ : ℕ → Ω → ℝ} (hφm : ∀ j, Measurable[natFiltration hBmeas (s j)] (φ j))
    {D : ℝ} (hφbdd : ∀ j ω, |φ j ω| ≤ D) (N : ℕ) :
    ∫ ω, stepSum B s φ N ω ^ 2 * stepTerm B s φ N ω ^ 2 ∂μ
      ≤ (D ^ 2 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)))
        * ((s (N + 1) : ℝ) - s N) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hZ2adapt : Measurable[natFiltration hBmeas (s N)]
      (fun ω ↦ stepSum B s φ N ω ^ 2 * φ N ω ^ 2) :=
    ((measurable_stepSum hBmeas hsmono hφm N).pow_const 2).mul ((hφm N).pow_const 2)
  have hZY2 : ∫ ω, stepSum B s φ N ω ^ 2 * stepTerm B s φ N ω ^ 2 ∂μ
      = (∫ ω, stepSum B s φ N ω ^ 2 * φ N ω ^ 2 ∂μ) * ((s (N + 1) : ℝ) - s N) :=
    (integral_congr_ae (Eventually.of_forall fun ω ↦ by simp only [stepTerm]; ring)).trans
      (integral_adapted_mul_increment_sq (hB.isFilteredPreBrownian hBmeas)
        (hsmono (Nat.le_succ N)) hZ2adapt)
  have hintZ2 : Integrable (fun ω ↦ stepSum B s φ N ω ^ 2) μ :=
    ((memLp_stepSum hB hBmeas hsmono hφm hφbdd N).mono_exponent
      (by norm_num)).integrable_sq
  have hZ2phi2 : ∫ ω, stepSum B s φ N ω ^ 2 * φ N ω ^ 2 ∂μ
      ≤ D ^ 2 * ∫ ω, stepSum B s φ N ω ^ 2 ∂μ := by
    refine le_trans (integral_mono_of_nonneg (μ := μ)
      (Eventually.of_forall fun ω ↦
        show (0 : ℝ) ≤ stepSum B s φ N ω ^ 2 * φ N ω ^ 2 from by positivity)
      (hintZ2.const_mul (D ^ 2)) (ae_of_all μ fun ω ↦ ?_)) ?_
    · calc stepSum B s φ N ω ^ 2 * φ N ω ^ 2 ≤ stepSum B s φ N ω ^ 2 * D ^ 2 :=
            mul_le_mul_of_nonneg_left (sq_le_sq.mpr ((hφbdd N ω).trans (le_abs_self D)))
              (sq_nonneg _)
        _ = D ^ 2 * stepSum B s φ N ω ^ 2 := mul_comm _ _
    · rw [integral_const_mul]
  have hΔ : 0 ≤ (s (N + 1) : ℝ) - s N :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hsmono (Nat.le_succ N)))
  rw [hZY2]
  exact (mul_le_mul_of_nonneg_right hZ2phi2 hΔ).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (integral_sq_stepSum_le hB hBmeas hsmono hφm hφbdd N)
        (sq_nonneg D)) hΔ)

/-- The last term's fourth moment: `E[y⁴] ≤ 3(D²Δs)²`
(`integral_natMeasurable_mul_increment_pow4`). -/
private lemma integral_term_pow_four_le {s : ℕ → ℝ≥0} (hsmono : Monotone s)
    {φ : ℕ → Ω → ℝ} (hφm : ∀ j, Measurable[natFiltration hBmeas (s j)] (φ j))
    {D : ℝ} (hφbdd : ∀ j ω, |φ j ω| ≤ D) (N : ℕ) :
    ∫ ω, stepTerm B s φ N ω ^ 4 ∂μ ≤ 3 * (D ^ 2 * ((s (N + 1) : ℝ) - s N)) ^ 2 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hy4 : ∫ ω, stepTerm B s φ N ω ^ 4 ∂μ
      = (∫ ω, (φ N ω) ^ 4 ∂μ) * (3 * ((s (N + 1) : ℝ) - s N) ^ 2) :=
    (integral_congr_ae (Eventually.of_forall fun ω ↦ by simp only [stepTerm]; rw [mul_pow])).trans
      (integral_natMeasurable_mul_increment_pow4 hB hBmeas (hsmono (Nat.le_succ N))
        (χ := fun ω ↦ (φ N ω) ^ 4) ((hφm N).pow_const 4))
  have hφ4 : ∫ ω, (φ N ω) ^ 4 ∂μ ≤ D ^ 4 := by
    refine le_trans (integral_mono_of_nonneg (μ := μ)
      (Eventually.of_forall fun ω ↦ show (0:ℝ) ≤ φ N ω ^ 4 from by positivity)
      (integrable_const (D ^ 4)) (ae_of_all μ fun ω ↦ ?_)) ?_
    · exact (Even.pow_abs (n := 4) ⟨2, rfl⟩ _).symm.trans_le
        (pow_le_pow_left₀ (abs_nonneg _) (hφbdd N ω) 4)
    · rw [integral_const]
      simp
  rw [hy4]
  calc (∫ ω, (φ N ω) ^ 4 ∂μ) * (3 * ((s (N + 1) : ℝ) - s N) ^ 2)
      ≤ D ^ 4 * (3 * ((s (N + 1) : ℝ) - s N) ^ 2) :=
        mul_le_mul_of_nonneg_right hφ4 (mul_nonneg zero_le_three (sq_nonneg _))
    _ = 3 * (D ^ 2 * ((s (N + 1) : ℝ) - s N)) ^ 2 := by ring

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
  have hnn (n : ℕ) (ω : Ω) : (0 : ℝ) ≤ stepSum B s φ n ω ^ 4 := by positivity
  induction N with
  | zero => simp
  | succ N ihN =>
    have hZ4 := memLp_stepSum hB hBmeas hsmono hφm hφbdd N
    have hY4 := memLp_stepTerm hB hBmeas hsmono hφm hφbdd N
    -- the real form of the induction hypothesis
    have ihNreal : ∫ ω, stepSum B s φ N ω ^ 4 ∂μ
        ≤ 3 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)) ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
        ((ofReal_integral_eq_lintegral_ofReal (integrable_pow_four_of_memLp hZ4)
          (Eventually.of_forall (hnn N))).trans_le ihN)
    -- the expansion of `(Z + y)⁴`, odd terms zeroed
    have hexp := integral_add_pow_four hZ4 hY4
      (integral_stepSum_cube_mul_term hB hBmeas hsmono hφm N)
      (integral_stepSum_mul_term_cube hB hBmeas hsmono hφm N)
    have hreal : ∫ ω, stepSum B s φ (N + 1) ω ^ 4 ∂μ
        ≤ 3 * (D ^ 2 * ∑ k ∈ Finset.range (N + 1), ((s (k + 1) : ℝ) - s k)) ^ 2 := by
      have hfun (ω : Ω) : stepSum B s φ (N + 1) ω ^ 4
          = (stepSum B s φ N ω + stepTerm B s φ N ω) ^ 4 := by rw [stepSum_succ]
      rw [Finset.sum_range_succ, integral_congr_ae (Eventually.of_forall hfun), hexp]
      calc _ ≤ 3 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)) ^ 2
            + 6 * ((D ^ 2 * (D ^ 2 * ∑ k ∈ Finset.range N, ((s (k + 1) : ℝ) - s k)))
              * ((s (N + 1) : ℝ) - s N))
            + 3 * (D ^ 2 * ((s (N + 1) : ℝ) - s N)) ^ 2 :=
            add_le_add (add_le_add ihNreal
              (mul_le_mul_of_nonneg_left
                (integral_sq_stepSum_mul_term_sq_le hB hBmeas hsmono hφm hφbdd N)
                (by norm_num)))
              (integral_term_pow_four_le hB hBmeas hsmono hφm hφbdd N)
        _ = _ := by ring
    exact ((ofReal_integral_eq_lintegral_ofReal
      (integrable_pow_four_of_memLp (memLp_stepSum hB hBmeas hsmono hφm hφbdd (N + 1)))
      (Eventually.of_forall (hnn (N + 1)))).symm).trans_le (ENNReal.ofReal_le_ofReal hreal)

end MathFin.ItoDriftConditional
