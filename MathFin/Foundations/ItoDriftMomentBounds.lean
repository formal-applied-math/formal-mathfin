/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoDriftIncrementEnergy
public import MathFin.Foundations.ItoDriftWeightedIsometry
public import MathFin.Foundations.FiniteMeasureCauchySchwarz
public import MathFin.Foundations.ItoStepSumFourthMoment

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

section StageFiveB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  {M : ℝ≥0 → Ω → ℝ} (hD : IsAdaptedItoDrift hB hBmeas T δ Dd M)

include hD

/-- The step-approximant process value at a grid point of its own partition, as the
running Itô sum (the range form of `itoSimpleProcess_stepσ_incr`). -/
private theorem stepValue_eq_sum {m J : ℕ} (hJm : J ≤ m) (ω : Ω) :
    itoSimpleProcess hBmeas (stepσ hBmeas hD.adapted hD.bdd T m).val (unifPart T m J) ω
      = ∑ j ∈ Finset.range J, δ (unifPart T m j) ω
          * (B (unifPart T m (j + 1)) ω - B (unifPart T m j) ω) := by
  induction J with
  | zero =>
    rw [unifPart_zero]
    simp
  | succ J ihJ =>
    have hJm' : J < m := Nat.lt_of_succ_le hJm
    have hincr := itoSimpleProcess_stepσ_incr hBmeas hD.adapted hD.bdd T (n := m) (k := J) hJm' ω
    rw [Finset.sum_range_succ, ← ihJ (Nat.le_of_succ_le hJm)]
    rw [show itoSimpleProcess hBmeas (stepσ hBmeas hD.adapted hD.bdd T m).val
          (unifPart T m (J + 1)) ω
        = itoSimpleProcess hBmeas (stepσ hBmeas hD.adapted hD.bdd T m).val (unifPart T m J) ω
          + δ (unifPart T m J) ω
            * (B (unifPart T m (J + 1)) ω - B (unifPart T m J) ω) from by rw [← hincr]; ring]

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
              hD.integrand
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              hD.integrand : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) ∂μ
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
      (itoProcessCLM hB T t hBmeas (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)) : Ω → ℝ)
        =ᵐ[μ] itoSimpleProcess hBmeas (stepσ hBmeas hD.adapted hD.bdd T (n * 2 ^ p)).val t := by
    intro p t
    rw [show (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p))
          = simpleAssembly_T (μ := μ) T hBmeas
            (stepσ hBmeas hD.adapted hD.bdd T (n * 2 ^ p)) from rfl,
      itoProcessCLM_simpleAssembly_T hB T t hBmeas
        (stepσ hBmeas hD.adapted hD.bdd T (n * 2 ^ p))]
    exact (memLp_itoSimpleProcess hB hBmeas
      (stepσ hBmeas hD.adapted hD.bdd T (n * 2 ^ p)).val t).coeFn_toLp
  -- the refined step-sum identification (a.e.)
  have hsumae : ∀ (p : ℕ),
      (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)) : Ω → ℝ) ω)
        =ᵐ[μ] (fun ω ↦ ∑ j ∈ Finset.range (2 ^ p),
            δ (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω
              * (B (unifPart T (n * 2 ^ p) (2 ^ p * k + j + 1)) ω
                - B (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω)) := by
    intro p
    filter_upwards [hcoe p (unifPart T n (k + 1)), hcoe p (unifPart T n k)] with ω h1 h2
    rw [← hgrid p (k + 1)] at h1
    rw [← hgrid p k] at h2
    have hv1 := stepValue_eq_sum (T := T) hB hBmeas hD (hJ2le p) ω
    have hv0 := stepValue_eq_sum (T := T) hB hBmeas hD (hJ1le p) ω
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
      (fun j ↦ (hD.adapted (unifPart T (n * 2 ^ p) (2 ^ p * k + j))).measurable)
      (fun j ω ↦ hD.bdd (unifPart T (n * 2 ^ p) (2 ^ p * k + j)) ω) (2 ^ p)) ?_
    change ENNReal.ofReal (3 * (Dd ^ 2 * ∑ j ∈ Finset.range (2 ^ p),
        ((unifPart T (n * 2 ^ p) (2 ^ p * k + (j + 1)) : ℝ)
          - unifPart T (n * 2 ^ p) (2 ^ p * k + j))) ^ 2)
      ≤ ENNReal.ofReal
        (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2)
    rw [hgapsum p]
  -- the `L²` contraction convergence of the band increments
  have hconv : Tendsto (fun p : ℕ ↦
      ‖((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p))
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)))
        - (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            hD.integrand
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            hD.integrand) : Lp ℝ 2 μ)‖) atTop (𝓝 0) := by
    have hemb : Tendsto (fun p : ℕ ↦ n * 2 ^ p) atTop atTop := by
      refine Filter.tendsto_atTop_atTop.mpr fun j ↦ ⟨j, fun p hp ↦ ?_⟩
      calc j ≤ p := hp
        _ ≤ 2 ^ p := Nat.lt_two_pow_self.le
        _ ≤ n * 2 ^ p :=
          (Nat.le_mul_of_pos_right (2 ^ p) hn).trans_eq (Nat.mul_comm (2 ^ p) n)
    have hsub := deltaStepLp_tendsto (T := T) hB hBmeas hD.adapted hD.continuous hD.bdd
    have hFp : Tendsto (fun p : ℕ ↦
        ‖(deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
          - hD.integrand :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero.mp hsub).comp hemb
    refine squeeze_zero' (Eventually.of_forall fun _p ↦ norm_nonneg _)
      (Eventually.of_forall fun p ↦ ?_)
      (by simpa using hFp.mul (tendsto_const_nhds (x := (2 : ℝ))))
    have hdec : ∀ p : ℕ,
        ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p))
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)))
        - (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            hD.integrand
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            hD.integrand) : Lp ℝ 2 μ)
        = (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
              - hD.integrand)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
              - hD.integrand)) := by
      intro p
      simp only [map_sub]
      abel
    rw [hdec p]
    calc ‖(itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
              - hD.integrand)
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
              - hD.integrand) : Lp ℝ 2 μ)‖
        ≤ ‖itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
              - hD.integrand)‖
          + ‖itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
              - hD.integrand)‖ := norm_sub_le _ _
      _ ≤ ‖(deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
              - hD.integrand :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ * 2 := by
          have h1 := itoProcessCLM_norm_le hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
              - hD.integrand)
          have h2 := itoProcessCLM_norm_le hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
              - hD.integrand)
          have h3 : ‖(deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
                - hD.integrand :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ * 2
              = ‖(deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
                  - hD.integrand :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖
              + ‖(deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)
                  - hD.integrand :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ := by ring
          rw [h3]
          exact add_le_add h1 h2
      _ = _ := rfl
  -- convergence in measure, a.e. subsequence, Fatou
  have h2inst : Fact (1 ≤ 2) := ⟨by norm_num⟩
  have hLp : Tendsto (fun p : ℕ ↦
      (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p))
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)) : Lp ℝ 2 μ)) atTop
      (𝓝 (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          hD.integrand
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          hD.integrand : Lp ℝ 2 μ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hconv
  have htmi : TendstoInMeasure μ (fun p : ℕ ↦
      ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p))
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ p)) : Lp ℝ 2 μ) : Ω → ℝ)) atTop
      ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          hD.integrand
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          hD.integrand : Lp ℝ 2 μ) : Ω → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp (p := 2) hLp
  obtain ⟨ns, _hnsmono, hae⟩ := htmi.exists_seq_tendsto_ae
  -- the Fatou functions and their a.e. limit (coe-of-difference forms throughout)
  have hXmeas : ∀ i : ℕ, AEMeasurable
      (fun ω : Ω ↦ ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)) μ
                :=
    fun i ↦ (ENNReal.continuous_ofReal.measurable).comp_aemeasurable
      (AEMeasurable.pow_const
        (Lp.aestronglyMeasurable
          (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i)) :
            Lp ℝ 2 μ)).aemeasurable 4)
  have hbound : ∀ i : ℕ,
      ∫⁻ ω, ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) ∂μ
      ≤ ENNReal.ofReal (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
    intro i
    have hc : ∀ᵐ ω : Ω ∂μ, ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i))
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)
        = ENNReal.ofReal ((∑ j ∈ Finset.range (2 ^ ns i),
          δ (unifPart T (n * 2 ^ ns i) (2 ^ ns i * k + j)) ω
            * (B (unifPart T (n * 2 ^ ns i) (2 ^ ns i * k + j + 1)) ω
              - B (unifPart T (n * 2 ^ ns i) (2 ^ ns i * k + j)) ω)) ^ 4) := by
      filter_upwards [Lp.coeFn_sub
          (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i)))
          (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i))),
        hsumae (ns i)] with ω h1 h2
      rw [h1, Pi.sub_apply, h2]
    rw [lintegral_congr_ae hc]
    exact hperp (ns i)
  have hGmeas : AEMeasurable
      (fun ω : Ω ↦ ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              hD.integrand
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              hD.integrand : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4))
                μ :=
    (ENNReal.continuous_ofReal.measurable).comp_aemeasurable
      (AEMeasurable.pow_const
        (Lp.aestronglyMeasurable
          (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              hD.integrand
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              hD.integrand :
            Lp ℝ 2 μ)).aemeasurable 4)
  have hlimfun : ∀ᵐ ω : Ω ∂μ,
      ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              hD.integrand
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              hD.integrand : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4)
        = atTop.liminf (fun i : ℕ ↦ ENNReal.ofReal
          ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
                (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i))
              - itoProcessCLM hB T (unifPart T n k) hBmeas
                (deltaStepLp hBmeas hD.adapted hD.bdd (n * 2 ^ ns i)) : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4))
                  := by
    filter_upwards [hae] with ω hw
    have hcont : Continuous fun x : ℝ ↦ ENNReal.ofReal (x ^ 4) :=
      (ENNReal.continuous_ofReal).comp (continuous_pow (4 : ℕ))
    exact ((hcont.tendsto _).comp hw).liminf_eq.symm
  have hlimint : ∫⁻ ω, ENNReal.ofReal
        ((((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              hD.integrand
            - itoProcessCLM hB T (unifPart T n k) hBmeas
              hD.integrand : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) ∂μ
      ≤ ENNReal.ofReal (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
    rw [lintegral_congr_ae hlimfun]
    refine le_trans (lintegral_liminf_le' fun i ↦ hXmeas i) ?_
    exact Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hbound)
  -- the ∫⁻-bound is the conclusion of the lemma
  exact hlimint

/-- The CLM increment is in `L⁴` (coe-difference form): `AEStronglyMeasurable` from the
`Lp` structure, finiteness from the ∫⁻-bound of `trueIncr_pow4_lintegral_le`
(`hasFiniteIntegral_iff_ofReal` — note the elaboration-order trap of
`ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top …`: the `≠ ⊤` arguments force
`a := ENNReal.ofReal _`, so a lintegral LHS never unifies; stay in the `ofReal` world). -/
private theorem clmIncr_pow4_integrable {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    Integrable (fun ω ↦ (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            hD.integrand
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            hD.integrand : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) μ :=
  ⟨(Lp.aestronglyMeasurable
      (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          hD.integrand
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          hD.integrand :
        Lp ℝ 2 μ)).pow 4,
    by
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω ↦ by positivity)]
      exact lt_of_le_of_lt
        (trueIncr_pow4_lintegral_le hB hBmeas hD hn k hk)
        ENNReal.ofReal_lt_top⟩

/-- The fourth power of the true increment is a.e. the fourth power of the CLM coe-difference
(the a.e. transfer along `hD.ae_eq`, shared by `trueIncr_pow4_integrable` and `trueIncr_pow4_le`).
-/
private theorem abs_pow4_trueIncr_ae (n k : ℕ) :
    (fun ω ↦ |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4)
    =ᵐ[μ] (fun ω ↦ (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          hD.integrand
        - itoProcessCLM hB T (unifPart T n k) hBmeas
          hD.integrand : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) := by
  filter_upwards [hD.ae_eq (unifPart T n (k + 1)), hD.ae_eq (unifPart T n k),
    Lp.coeFn_sub
      (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
        hD.integrand)
      (itoProcessCLM hB T (unifPart T n k) hBmeas
        hD.integrand)] with ω h1 h0 hsub
  show |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4 = _
  rw [h1, h0, ← Pi.sub_apply, ← hsub, ← abs_pow]
  exact abs_of_nonneg (by positivity)

/-- The true increment is in `L⁴` (modifying-process form): the a.e. transfer of
`clmIncr_pow4_integrable` along the `hD.ae_eq` congruence. -/
theorem trueIncr_pow4_integrable {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    Integrable (fun ω ↦ |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4) μ := by
  have hG4 := abs_pow4_trueIncr_ae hB hBmeas hD n k
  exact (clmIncr_pow4_integrable hB hBmeas hD hn k hk).congr hG4.symm

/-- **The fourth moment of the true increment** over a uniform cell:
`𝔼[(M_{tₖ₊₁} − M_{tₖ})⁴] ≤ 3·(D_δ²·cell)²` — the a.e. transfer of the CLM ∫⁻-bound to the
modifying process `M`, with the real integral recovered from the ∫⁻-bound by
`ofReal`-injectivity (`ofReal_integral_eq_lintegral_ofReal` +
`ENNReal.ofReal_le_ofReal_iff`). -/
theorem trueIncr_pow4_le {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n) :
    ∫ ω, |M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω| ^ 4 ∂μ
      ≤ 3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2 := by
  -- a.e. transfer to the CLM coe-difference
  have hG4 := abs_pow4_trueIncr_ae hB hBmeas hD n k
  rw [integral_congr_ae hG4]
  have hint4 : Integrable (fun ω ↦ (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            hD.integrand
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            hD.integrand : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4) μ :=
    clmIncr_pow4_integrable hB hBmeas hD hn k hk
  have hofR : ENNReal.ofReal (∫ ω, (((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            hD.integrand
          - itoProcessCLM hB T (unifPart T n k) hBmeas
            hD.integrand : Lp ℝ 2 μ) : Ω → ℝ) ω) ^ 4 ∂μ)
      ≤ ENNReal.ofReal (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint4
      (Eventually.of_forall fun ω ↦ by positivity)]
    exact trueIncr_pow4_lintegral_le hB hBmeas hD hn k hk
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
    (memLp_M hB hBmeas hD (unifPart T n (k + 1))).sub
      (memLp_M hB hBmeas hD (unifPart T n k))
  -- the two energy bounds
  have huv : unifPart T n k ≤ unifPart T n (k + 1) :=
    unifPart_mono T n (Nat.le_succ k)
  have hvT : unifPart T n (k + 1) ≤ T :=
    unifPart_le_T (Nat.lt_iff_add_one_le.mp hk)
  have hcellnn : (0:ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr huv)
  have hint2 : ∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
      ≤ Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
    trueIncr_sq_le hB hBmeas hD huv hvT
  -- the fourth moment in un-absolutized form, and its `Integrable` witness (for `X²`)
  have hint4M : Integrable (fun ω ↦
      (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4) μ :=
    (trueIncr_pow4_integrable hB hBmeas hD hn k hk).congr
      (Eventually.of_forall fun ω ↦ Even.pow_abs ⟨2, rfl⟩ _)
  have hint4 : ∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 4 ∂μ
      ≤ 3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2 := by
    refine le_trans (le_of_eq ?_)
      (trueIncr_pow4_le hB hBmeas hD hn k hk)
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
