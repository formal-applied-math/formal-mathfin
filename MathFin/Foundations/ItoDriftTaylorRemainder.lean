/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoDriftIncrementEnergy
public import MathFin.Foundations.ItoDriftMomentBounds

/-! # The Taylor remainder of the adapted Itô–drift identity (the discrete route, stage 5f)

`taylorRemainderSum_tendsto`: the expected sum of Taylor remainders of the discrete Itô formula
tends to `0`, by the cubic Taylor bound `abs_discreteTaylorRemainder_le` and the third-moment
estimate `trueIncr_pow3_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
  ItoIntegralProcessGeneral ItoIntegralProcess QuadraticVariationL2 ItoIntegralBrownian
  AdaptedDrift

section StageFiveF

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  {M : ℝ≥0 → Ω → ℝ} (hD : IsAdaptedItoDrift hB hBmeas T δ Dd M)

include hD

set_option maxHeartbeats 1600000 in
-- a long estimate: elaborating the whole proof exceeds the default budget
/-- **The Taylor remainder dies**: the summed discrete Taylor remainders along the uniform
partition have expectation tending to `0` (the statement; the rate below is the proof's) —
each `|Rₖ| ≤ C₃·|ΔXₖ|³`
(`abs_discreteTaylorRemainder_le`) with `ΔXₖ = Δ(AdaptedDrift.driftPath β)ₖ + ΔMₖ` (the increment
decomposition), `(a+b)³ ≤ 4·(a³+b³)` (`add_pow_le`), the drift increment pointwise
`D_β·cell`, and the martingale increment `𝔼|ΔM|³ ≤ √(3·(D_δ²·cell)³)`
(`trueIncr_pow3_le`); the cells telescope to `T`, giving
`|𝔼[∑ₖ Rₖ]| ≤ 4·C₃·(4·D_β³·T³/(n+1)² + 2·√(3·(D_δ²·T)³)/√(n+1)) → 0`. -/
theorem taylorRemainderSum_tendsto (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    {β : ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + driftPath β t ω + M t ω)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C3 : ℝ} (hg3 : ∀ x, |f''' x| ≤ C3) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ∑ k ∈ Finset.range n,
        discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω) ∂μ) atTop (𝓝 0) := by
  have hC3 : (0 : ℝ) ≤ C3 := le_trans (abs_nonneg _) (hg3 0)
  have hβbdd' : ∀ t ω, |β t ω| ≤ |Db| := fun t ω ↦ (hβbdd t ω).trans (le_abs_self Db)
  have hfcont : Continuous f := Differentiable.continuous fun x ↦ (hf x).differentiableAt
  have hf'cont : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  have hf''cont : Continuous f'' := Differentiable.continuous fun x ↦ (hf'' x).differentiableAt
  -- measurability of the per-step remainder
  have hRmeas : ∀ n : ℕ, ∀ k : ℕ, Measurable (fun ω : Ω ↦ discreteTaylorRemainder f f' f''
      (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)) := by
    intro n k
    have hX0 : Measurable (X (unifPart T n k)) :=
      (hXadap (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    have hX1 : Measurable (X (unifPart T n (k + 1))) :=
      (hXadap (unifPart T n (k + 1))).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
    unfold discreteTaylorRemainder
    exact (((hfcont.measurable.comp hX1).sub (hfcont.measurable.comp hX0)).sub
      ((hf'cont.measurable.comp hX0).mul (hX1.sub hX0))).sub
      (((hf''cont.measurable.comp hX0).mul ((hX1.sub hX0).pow_const 2)).const_mul (1 / 2))
  -- per-cell: integrability of |Rₖ| and ∫|Rₖ| ≤ 4·C₃·((|Db|·cell)³ + √(3·(D_δ²·cell)³))
  have hcell : ∀ n : ℕ, 0 < n → ∀ k : ℕ, k < n →
      Integrable (fun ω ↦ |discreteTaylorRemainder f f' f''
          (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)|) μ ∧
      ∫ ω, |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω)| ∂μ
        ≤ 4 * C3 * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
          + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
            - unifPart T n k)) ^ 3)) := by
    intro n hn k hk
    have hcellnn : (0 : ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
      sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
    have hX0m : Measurable (X (unifPart T n k)) :=
      (hXadap (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    have hX1m : Measurable (X (unifPart T n (k + 1))) :=
      (hXadap (unifPart T n (k + 1))).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
    have hsubm : Measurable (fun ω : Ω ↦ X (unifPart T n (k + 1)) ω
        - X (unifPart T n k) ω) := hX1m.sub hX0m
    have hΔ : ∀ ω : Ω, X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω
        = (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
          + (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) := by
      intro ω
      rw [hXrel (unifPart T n (k + 1)), hXrel (unifPart T n k)]
      change (c + driftPath β (unifPart T n (k + 1)) ω
            + M (unifPart T n (k + 1)) ω)
          - (c + driftPath β (unifPart T n k) ω + M (unifPart T n k) ω) = _
      ring
    have hdIb : ∀ ω : Ω, |driftPath β (unifPart T n (k + 1)) ω
        - driftPath β (unifPart T n k) ω| ≤ |Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k) := fun ω ↦
      abs_driftPath_sub_le hβcont hβbdd'
        (unifPart_mono T n (Nat.le_succ k)) ω
    have hcub : ∀ ω : Ω, (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
        ≤ (4 : ℝ) * ((abs (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω)) ^ 3
            + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) := by
      intro ω
      have h1 : abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)
          ≤ abs (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω)
            + abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) := by
        rw [hΔ ω]
        exact abs_add_le _ _
      calc (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
          ≤ (abs (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)
              + abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 3
        _ ≤ (4 : ℝ) * ((abs (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω)) ^ 3
              + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) :=
          (add_pow_le (abs_nonneg _) (abs_nonneg _) 3).trans_eq (by norm_num)
    -- integrability of |ΔM|³ (dominated by |ΔM|⁴ + 1)
    have htdI3 : Integrable (fun ω ↦ (abs (M (unifPart T n (k + 1)) ω
          - M (unifPart T n k) ω)) ^ 3) μ := by
      refine Integrable.mono'
        (((trueIncr_pow4_integrable hB hBmeas hD hn k hk
          ).const_mul 1).add (integrable_const (1 : ℝ)))
        ((((memLp_M hB hBmeas hD
          (unifPart T n (k + 1))).sub
          (memLp_M hB hBmeas hD (unifPart T n k))).abs).aestronglyMeasurable.pow
          3)
        (Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs]
          set x := abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) with hxdef
          have hx0 : (0 : ℝ) ≤ x := abs_nonneg _
          have h3 : x ^ 3 ≤ x ^ 4 + 1 := by
            rcases le_total 1 x with h1 | h1
            · have hz : (0 : ℝ) ≤ x ^ 3 * (x - 1) :=
                mul_nonneg (pow_nonneg hx0 3) (sub_nonneg.mpr h1)
              nlinarith
            · refine le_trans (pow_le_pow_left₀ hx0 h1 3) ?_
              nlinarith [pow_nonneg hx0 4]
          simpa [hxdef, abs_of_nonneg hx0] using h3)
    have hmeasX3 : AEStronglyMeasurable
        (fun ω ↦ (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3) μ :=
      (hsubm.abs.aestronglyMeasurable).pow 3
    have htdA : Integrable (fun ω ↦ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k)) ^ 3)) μ :=
      (integrable_const ((|Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k)) ^ 3)).const_mul 4
    have htdB : Integrable (fun ω ↦ (4 : ℝ) *
        (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) μ :=
      htdI3.const_mul 4
    have htdom : Integrable (fun ω ↦ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k)) ^ 3)
        + (4 : ℝ) * (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) μ :=
      htdA.add htdB
    have hptX3 : ∀ ω : Ω, (abs (X (unifPart T n (k + 1)) ω
        - X (unifPart T n k) ω)) ^ 3
        ≤ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3)
          + (4 : ℝ) * (abs (M (unifPart T n (k + 1)) ω
          - M (unifPart T n k) ω)) ^ 3 := by
      intro ω
      refine le_trans (hcub ω) ?_
      rw [mul_add]
      exact add_le_add_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (hdIb ω) 3)
        (by norm_num : (0:ℝ) ≤ 4)) _
    have habsX3 : Integrable (fun ω ↦ (abs (X (unifPart T n (k + 1)) ω
        - X (unifPart T n k) ω)) ^ 3) μ := by
      refine Integrable.mono' htdom hmeasX3 (Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hptX3 ω
    have hRk3 : ∫ ω, (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3 ∂μ
        ≤ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
          + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
            - unifPart T n k)) ^ 3)) := by
      have hdI3 : ∫ ω, (abs (driftPath β (unifPart T n (k + 1)) ω
          - driftPath β (unifPart T n k) ω)) ^ 3 ∂μ
          ≤ (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3 := by
        refine le_trans (integral_mono_of_nonneg
          (Eventually.of_forall fun ω ↦ by positivity)
          (integrable_const ((|Db| * ((unifPart T n (k + 1) : ℝ)
            - unifPart T n k)) ^ 3))
          (Eventually.of_forall fun ω ↦ ?_)) ?_
        · exact pow_le_pow_left₀ (abs_nonneg _) (hdIb ω) 3
        · rw [integral_const]; simp
      have htI3 := trueIncr_pow3_le hB hBmeas hD hn k hk
      refine le_trans (integral_mono_of_nonneg
        (Eventually.of_forall fun ω ↦ by positivity) htdom
        (Eventually.of_forall fun ω ↦ by
          change (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
            ≤ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3)
              + (4 : ℝ) * (abs (M (unifPart T n (k + 1)) ω
              - M (unifPart T n k) ω)) ^ 3
          exact hptX3 ω)) ?_
      rw [integral_add htdA htdB, integral_const_mul, integral_const_mul, integral_const,
        measureReal_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one,
        smul_eq_mul, one_mul]
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_left le_rfl (by norm_num : (0:ℝ) ≤ 4))
        (mul_le_mul_of_nonneg_left htI3 (by norm_num : (0:ℝ) ≤ 4))
    -- |Rₖ| ≤ C₃·|ΔX|³ pointwise
    have hRb : ∀ ω : Ω, |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω)|
        ≤ C3 * (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3 :=
      fun ω ↦ abs_discreteTaylorRemainder_le hf hf' hf'' hg3 _ _
    refine ⟨?_, ?_⟩
    · refine Integrable.mono' (habsX3.const_mul C3)
        ((hRmeas n k).abs.aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ by
          change ‖|discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
            (X (unifPart T n (k + 1)) ω)|‖ ≤ _
          rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
          exact hRb ω)
    · calc ∫ ω, |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
            (X (unifPart T n (k + 1)) ω)| ∂μ
          ≤ ∫ ω, (C3 * (abs (X (unifPart T n (k + 1)) ω
              - X (unifPart T n k) ω)) ^ 3) ∂μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ abs_nonneg _)
              (habsX3.const_mul C3) (Eventually.of_forall fun ω ↦ hRb ω)
        _ = (C3 : ℝ) * ∫ ω, (abs (X (unifPart T n (k + 1)) ω
              - X (unifPart T n k) ω)) ^ 3 ∂μ := by rw [integral_const_mul]
        _ ≤ (C3 : ℝ) * ((4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ)
              - unifPart T n k)) ^ 3
              + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                - unifPart T n k)) ^ 3))) :=
              mul_le_mul_of_nonneg_left hRk3 hC3
        _ = 4 * C3 * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
              + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                - unifPart T n k)) ^ 3)) := by ring
  -- the summed bound and the squeeze
  have hintsum : ∀ n : ℕ, 0 < n → ∫ ω : Ω, (∑ k ∈ Finset.range n,
      |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω)|) ∂μ
      = ∑ k ∈ Finset.range n, (∫ ω : Ω,
      |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω)| ∂μ) := by
    intro n hn
    refine integral_finsetSum (μ := μ) (s := Finset.range n)
      (f := fun (k : ℕ) (ω : Ω) ↦ |discreteTaylorRemainder f f' f''
        (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)|)
      (fun k hk ↦ (hcell n hn k (Finset.mem_range.mp hk)).1)
  have hboundtendsto : Tendsto (fun n : ℕ ↦ |∫ ω : Ω, ∑ k ∈ Finset.range n,
      discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω) ∂μ|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n : ℕ ↦ (4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3))
        * ((1 / ((n : ℝ) + 1)) ^ 2)
      + (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)))
        * ((1 : ℝ) / Real.sqrt ((n : ℝ) + 1)))
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have hn0r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hcellen : ∀ k : ℕ, k ∈ Finset.range n →
          ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = ((T : ℝ) / (n : ℝ)) :=
        fun k _ ↦ unifPart_succ_sub T n k
      set gR : Ω → ℝ := fun ω : Ω ↦ ∑ k ∈ Finset.range n,
        discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
          (X (unifPart T n (k + 1)) ω) with hgR
      have hsum1 : (∑ k ∈ Finset.range n,
          (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3)
          = ((n : ℝ)) * (|Db| * ((T : ℝ) / (n : ℝ))) ^ 3 := by
        rw [Finset.sum_congr rfl fun k hk ↦ by rw [hcellen k hk], Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
      have hsum2 : (∑ k ∈ Finset.range n,
          Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
            - unifPart T n k)) ^ 3))
          = ((n : ℝ)) * Real.sqrt (3 * (Dd ^ 2 * ((T : ℝ) / (n : ℝ))) ^ 3) := by
        rw [Finset.sum_congr rfl fun k hk ↦ by rw [hcellen k hk], Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
      have hpart1 : ((n : ℝ)) * (|Db| * ((T : ℝ) / (n : ℝ))) ^ 3
          = |Db| ^ 3 * (T : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
        field_simp
      have hpart2 : ((n : ℝ)) * Real.sqrt (3 * (Dd ^ 2 * ((T : ℝ) / (n : ℝ))) ^ 3)
          = Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3) / Real.sqrt ((n : ℝ)) := by
        have hpos : (0 : ℝ) < Real.sqrt ((n : ℝ)) := Real.sqrt_pos.mpr hn0r
        have hXn : (3 * (Dd ^ 2 * ((T : ℝ) / (n : ℝ))) ^ 3) * (n : ℝ)
            = (3 * (Dd ^ 2 * (T : ℝ)) ^ 3) / (n : ℝ) ^ 2 := by
          field_simp
        rw [eq_div_iff hpos.ne', mul_assoc, ← Real.sqrt_mul
          (by positivity : (0 : ℝ) ≤ 3 * (Dd ^ 2 * ((T : ℝ) / (n : ℝ))) ^ 3),
          hXn, Real.sqrt_div (by positivity : (0 : ℝ) ≤
            3 * (Dd ^ 2 * (T : ℝ)) ^ 3), Real.sqrt_sq
            (by norm_num : (0 : ℝ) ≤ (n : ℝ))]
        field_simp
      have hB0 : (0 : ℝ) ≤ Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3) := Real.sqrt_nonneg _
      have hpos1 : (0 : ℝ) < Real.sqrt ((n : ℝ)) := Real.sqrt_pos.mpr hn0r
      have hpos2 : (0 : ℝ) < Real.sqrt (((n : ℝ)) + 1) :=
        Real.sqrt_pos.mpr (by linarith)
      have hstep : Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
          / Real.sqrt ((n : ℝ))
          ≤ (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))
            / Real.sqrt (((n : ℝ)) + 1) := by
        have h1 : Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
            / Real.sqrt ((n : ℝ))
            = Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
              * ((1 : ℝ) / Real.sqrt ((n : ℝ))) := by
          rw [one_div]; ring
        have h2 : Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
            * ((1 : ℝ) / Real.sqrt ((n : ℝ)))
          ≤ Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
            * (2 / Real.sqrt (((n : ℝ)) + 1)) :=
          mul_le_mul_of_nonneg_left (one_div_sqrt_le_two hn) hB0
        have h3 : Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
            * (2 / Real.sqrt (((n : ℝ)) + 1))
          = (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))
            / Real.sqrt (((n : ℝ)) + 1) := by
          ring
        exact le_trans (le_of_eq h1) (h2.trans h3.le)
      calc |∫ ω : Ω, gR ω ∂μ|
          ≤ ‖∫ ω : Ω, gR ω ∂μ‖ :=
            le_of_eq (by rw [Real.norm_eq_abs])
        _ ≤ ∫ ω : Ω, ‖gR ω‖ ∂μ := norm_integral_le_integral_norm gR
        _ = ∫ ω : Ω, |gR ω| ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
            change ‖gR ω‖ = |gR ω|
            rw [Real.norm_eq_abs]
        _ ≤ ∫ ω : Ω, (∑ k ∈ Finset.range n,
            |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
              (X (unifPart T n (k + 1)) ω)|) ∂μ :=
            integral_mono_of_nonneg
              (Eventually.of_forall fun ω ↦ abs_nonneg _)
              (integrable_finsetSum _ fun k hk ↦
                (hcell n hn k (Finset.mem_range.mp hk)).1)
              (Eventually.of_forall fun ω ↦
                Finset.abs_sum_le_sum_abs _ _)
        _ = ∑ k ∈ Finset.range n,
            ∫ ω, |discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
              (X (unifPart T n (k + 1)) ω)| ∂μ := hintsum n hn
        _ ≤ ∑ k ∈ Finset.range n, (4 * C3 * ((|Db| * ((unifPart T n (k + 1) : ℝ)
              - unifPart T n k)) ^ 3
              + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                - unifPart T n k)) ^ 3))) :=
            Finset.sum_le_sum fun k hk ↦
              (hcell n hn k (Finset.mem_range.mp hk)).2
        _ = (4 * C3) * ((∑ k ∈ Finset.range n,
              (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3)
              + (∑ k ∈ Finset.range n,
              Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                - unifPart T n k)) ^ 3))) := by
            have hsplit : ∀ k ∈ Finset.range n,
                (4 : ℝ) * C3 * (((|Db| * ((unifPart T n (k + 1) : ℝ)
                  - unifPart T n k)) ^ 3)
                + Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                  - unifPart T n k)) ^ 3))
                = (4 : ℝ) * C3 * ((|Db| * ((unifPart T n (k + 1) : ℝ)
                  - unifPart T n k)) ^ 3)
                + (4 : ℝ) * C3 * (Real.sqrt (3 * (Dd ^ 2 * ((unifPart T n (k + 1) : ℝ)
                  - unifPart T n k)) ^ 3)) := fun k _ ↦ by ring
            rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, mul_add,
              Finset.mul_sum, Finset.mul_sum]
        _ = (4 * C3) * ((|Db| ^ 3 * (T : ℝ) ^ 3 / (n : ℝ) ^ 2)
              + Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3) / Real.sqrt ((n : ℝ))) := by
            rw [hsum1, hsum2, hpart1, hpart2]
        _ ≤ (4 * C3) * ((4 * |Db| ^ 3 * (T : ℝ) ^ 3) / ((n : ℝ) + 1) ^ 2
              + (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))
              / Real.sqrt (((n : ℝ)) + 1)) := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_)
              (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC3)
            · have hnm : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
              have h2n : ((n : ℝ) + 1) ≤ 2 * (n : ℝ) := by linarith
              have hs : ((n : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 :=
                pow_le_pow_left₀ (by linarith) h2n 2
              rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ) ^ 2)
                (by positivity : (0:ℝ) < ((n : ℝ) + 1) ^ 2)]
              calc |Db| ^ 3 * (T : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2
                  ≤ |Db| ^ 3 * (T : ℝ) ^ 3 * ((2 * (n : ℝ)) ^ 2) :=
                    mul_le_mul_of_nonneg_left hs (by positivity)
                _ = 4 * |Db| ^ 3 * (T : ℝ) ^ 3 * (n : ℝ) ^ 2 := by ring
            · have hstep : Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)
                  / Real.sqrt ((n : ℝ))
                  ≤ (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))
                    / Real.sqrt (((n : ℝ)) + 1) := hstep
              exact hstep
        _ = (4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3)) * ((1 / ((n : ℝ) + 1)) ^ 2)
            + (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)))
            * ((1 : ℝ) / Real.sqrt ((n : ℝ) + 1)) := by
            have hn1 : ((n : ℝ) + 1) ≠ 0 := by linarith
            field_simp [hn1]
    · have hzero : ((4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3)) * (0 : ℝ)
          + (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))) * (0 : ℝ)) = 0 := by
        norm_num
      have h1 : Tendsto (fun n : ℕ ↦ ((1 / ((n : ℝ) + 1)) ^ 2)) atTop (𝓝 (0 : ℝ)) :=
        by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
      have hA : Tendsto (fun n : ℕ ↦ (4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3))
          * ((1 / ((n : ℝ) + 1)) ^ 2)) atTop
          (𝓝 ((4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3)) * (0 : ℝ))) :=
        (tendsto_const_nhds (x := (4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3)))).mul h1
      have hB : Tendsto (fun n : ℕ ↦ (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)))
          * ((1 : ℝ) / Real.sqrt ((n : ℝ) + 1))) atTop
          (𝓝 ((4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))) * (0 : ℝ))) :=
        (tendsto_const_nhds (x := (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3))))).mul
          tendsto_inv_sqrt_nat_add
      have hfin : Tendsto (fun n : ℕ ↦ (4 * C3 * (4 * |Db| ^ 3 * (T : ℝ) ^ 3))
          * ((1 / ((n : ℝ) + 1)) ^ 2)
          + (4 * C3 * (2 * Real.sqrt (3 * (Dd ^ 2 * (T : ℝ)) ^ 3)))
          * ((1 : ℝ) / Real.sqrt ((n : ℝ) + 1))) atTop (𝓝 0) := by
        have h := hA.add hB
        rw [hzero] at h
        exact h
      exact hfin
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr hboundtendsto


set_option maxHeartbeats 1600000 in
-- a long estimate: elaborating the whole proof exceeds the default budget
/-- **Per-cell Taylor-remainder integrability** (assembly input): along the adapted process
`X` with the decomposition `X t = c + AdaptedDrift.driftPath β t + M t`, the `k`-th cell's
discrete Taylor remainder is integrable — `|Rₖ| ≤ C₃·|ΔXₖ|³` (`abs_discreteTaylorRemainder_le`)
with `ΔXₖ = Δ(AdaptedDrift.driftPath β)ₖ + ΔMₖ` (pointwise, from `hXrel`), the drift
increment bounded
by `|D_β|·cell` (`AdaptedDrift.abs_driftPath_sub_le`), and the martingale increment in `L³` by the
fourth-moment bound `trueIncr_pow4_integrable` (the domination `x³ ≤ x⁴ + 1`). -/
theorem remainderCell_integrable {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k < n)
    {β : ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXrel : ∀ t : ℝ≥0, X t = fun ω : Ω ↦ c + driftPath β t ω + M t ω)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C3 : ℝ} (hg3 : ∀ x, |f''' x| ≤ C3) :
    Integrable (fun ω : Ω ↦ discreteTaylorRemainder f f' f''
      (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)) μ := by
  have hcellnn : (0 : ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
  have hβbdd' : ∀ t ω, |β t ω| ≤ |Db| := fun t ω ↦ (hβbdd t ω).trans (le_abs_self Db)
  have hfcont : Continuous f := Differentiable.continuous fun x ↦ (hf x).differentiableAt
  have hf'cont : Continuous f' := Differentiable.continuous fun x ↦ (hf' x).differentiableAt
  have hf''cont : Continuous f'' := Differentiable.continuous fun x ↦ (hf'' x).differentiableAt
  -- measurability of the endpoints and of the remainder
  have hX0m : Measurable (X (unifPart T n k)) :=
    (hXadap (unifPart T n k)).measurable.mono
      ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
  have hX1m : Measurable (X (unifPart T n (k + 1))) :=
    (hXadap (unifPart T n (k + 1))).measurable.mono
      ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
  have hRm : Measurable (fun ω : Ω ↦ discreteTaylorRemainder f f' f''
      (X (unifPart T n k) ω) (X (unifPart T n (k + 1)) ω)) := by
    unfold discreteTaylorRemainder
    exact (((hfcont.measurable.comp hX1m).sub (hfcont.measurable.comp hX0m)).sub
      ((hf'cont.measurable.comp hX0m).mul (hX1m.sub hX0m))).sub
      (((hf''cont.measurable.comp hX0m).mul ((hX1m.sub hX0m).pow_const 2)).const_mul (1 / 2))
  -- the increment decomposition and the pointwise drift bound
  have hΔ : ∀ ω : Ω, X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω
      = (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        + (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) := by
    intro ω
    rw [hXrel (unifPart T n (k + 1)), hXrel (unifPart T n k)]
    change (c + driftPath β (unifPart T n (k + 1)) ω + M (unifPart T n (k + 1)) ω)
        - (c + driftPath β (unifPart T n k) ω + M (unifPart T n k) ω) = _
    ring
  have hdIb : ∀ ω : Ω, |driftPath β (unifPart T n (k + 1)) ω
      - driftPath β (unifPart T n k) ω| ≤ |Db| * ((unifPart T n (k + 1) : ℝ)
      - unifPart T n k) := fun ω ↦
    abs_driftPath_sub_le hβcont hβbdd'
      (unifPart_mono T n (Nat.le_succ k)) ω
  -- `𝔼|ΔM|³ < ∞` (the `L⁴` bound via `trueIncr_pow4_integrable`, dominated by `x⁴ + 1`)
  have htdI3 : Integrable (fun ω ↦ (abs (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω)) ^ 3) μ := by
    refine Integrable.mono'
      (((trueIncr_pow4_integrable hB hBmeas hD hn k hk
        ).const_mul 1).add (integrable_const (1 : ℝ)))
      ((((memLp_M hB hBmeas hD
        (unifPart T n (k + 1))).sub
        (memLp_M hB hBmeas hD (unifPart T n k))).abs).aestronglyMeasurable.pow
        3)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]
        set x := abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) with hxdef
        have hx0 : (0 : ℝ) ≤ x := abs_nonneg _
        have h3 : x ^ 3 ≤ x ^ 4 + 1 := by
          rcases le_total 1 x with h1 | h1
          · have hz : (0 : ℝ) ≤ x ^ 3 * (x - 1) :=
              mul_nonneg (pow_nonneg hx0 3) (sub_nonneg.mpr h1)
            nlinarith
          · refine le_trans (pow_le_pow_left₀ hx0 h1 3) ?_
            nlinarith [pow_nonneg hx0 4]
        simpa [hxdef, abs_of_nonneg hx0] using h3)
  -- the cubic domination `|ΔX|³ ≤ 4·((|D_β|·cell)³ + |ΔM|³)` pointwise
  have hsubm : Measurable (fun ω : Ω ↦ X (unifPart T n (k + 1)) ω
      - X (unifPart T n k) ω) := hX1m.sub hX0m
  have hcub : ∀ ω : Ω, (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
      ≤ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
        + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) := by
    intro ω
    have h1 : abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)
        ≤ abs (driftPath β (unifPart T n (k + 1)) ω
            - driftPath β (unifPart T n k) ω)
          + abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) := by
      rw [hΔ ω]
      exact abs_add_le _ _
    calc (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
        ≤ (abs (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω)
            + abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 3
      _ ≤ (4 : ℝ) * ((abs (driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω)) ^ 3
            + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) :=
          (add_pow_le (abs_nonneg _) (abs_nonneg _) 3).trans_eq (by norm_num)
      _ ≤ (4 : ℝ) * (((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
            + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add_left (pow_le_pow_left₀ (abs_nonneg _) (hdIb ω) 3)
              (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 3))
            (by norm_num : (0 : ℝ) ≤ 4)
  have hdom : Integrable (fun ω ↦ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ)
      - unifPart T n k)) ^ 3)
      + (4 : ℝ) * (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) μ :=
    (integrable_const ((|Db| * ((unifPart T n (k + 1) : ℝ)
      - unifPart T n k)) ^ 3)).const_mul 4 |>.add (htdI3.const_mul 4)
  have habsX3 : Integrable (fun ω ↦ (abs (X (unifPart T n (k + 1)) ω
      - X (unifPart T n k) ω)) ^ 3) μ :=
    Integrable.mono' hdom ((hsubm.abs.aestronglyMeasurable).pow 3)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc (abs (X (unifPart T n (k + 1)) ω - X (unifPart T n k) ω)) ^ 3
            ≤ (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3
              + (abs (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)) ^ 3) := hcub ω
          _ = (4 : ℝ) * ((|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 3)
              + (4 : ℝ) * (abs (M (unifPart T n (k + 1)) ω
                - M (unifPart T n k) ω)) ^ 3 := by rw [mul_add])
  -- `|Rₖ| ≤ C₃·|ΔX|³` closes
  refine Integrable.mono' (habsX3.const_mul C3) hRm.aestronglyMeasurable
    (Eventually.of_forall fun ω ↦ by
      change ‖discreteTaylorRemainder f f' f'' (X (unifPart T n k) ω)
        (X (unifPart T n (k + 1)) ω)‖ ≤ C3 * (abs (X (unifPart T n (k + 1)) ω
          - X (unifPart T n k) ω)) ^ 3
      rw [Real.norm_eq_abs]
      exact abs_discreteTaylorRemainder_le hf hf' hf'' hg3 _ _)

end StageFiveF

end MathFin.ItoDriftConditional
