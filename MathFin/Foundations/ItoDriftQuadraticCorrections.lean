/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoDriftIncrementEnergy
public import MathFin.Foundations.ItoDriftWeightedIsometry
public import MathFin.Foundations.ItoDriftMomentBounds
public import MathFin.Foundations.ItoDriftBlock

/-! # The quadratic corrections of the adapted Itô–drift identity (the discrete route, stage 5e)

The two corrections of the quadratic block that tend to `0`: the drift² corrections
`quadDriftSqSum_tendsto` and the drift–martingale cross corrections `quadCrossSum_tendsto`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 ItoIntegralCLM ItoIntegralProcessGeneral
  QuadraticVariationL2 ItoIntegralBrownian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

section StageFiveD

open MeasureTheory ProbabilityTheory Filter Topology ItoIntegralProcessGeneral
open ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
open ItoIntegralProcess QuadraticVariationL2 ItoIntegralBrownian AdaptedDrift MathFin
open scoped NNReal ENNReal

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


/-! #### Stage 5e — the dying blocks of the assembly

Three convergences consumed by `itoDrift_expectation_identity_adapted`; each statement gives
only the limit `0`, and the bounds below are what the proofs establish:

* `quadDriftSqSum_tendsto` — the drift² corrections `O(mesh)`:
  `∑ₖ |𝔼[g (X tₖ)·(Δ(AdaptedDrift.driftPath β))ₖ²]| ≤ 2·C₂·D_β²·T²/(n+1) → 0`;
* `quadCrossSum_tendsto` — the drift–martingale cross corrections `O(√mesh)`:
  `∑ₖ |𝔼[g (X tₖ)·Δ(AdaptedDrift.driftPath β)ₖ·ΔMₖ]| ≤ 2·C₂·D_β·|D_δ|·T·√T/√(n+1) → 0`
  (the `D_β·cell`-bounded drift increment paired against the `D_δ²·cell`-energy
  martingale increment, `trueIncr_sq_le`);
* `taylorRemainderSum_tendsto` — the Taylor remainder: `|𝔼[∑ₖ Rₖ]|` is at most
  `4·C₃·(4·D_β³·T³/(n+1)² + 2·√(3·(D_δ²·T)³)/√(n+1)) → 0`
  (`abs_discreteTaylorRemainder_le` + `pow3_add_le` + `trueIncr_pow3_le`). -/

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The `(n+1)`-divergence and the `1/(n+1)` null sequence over the naturals. -/
private theorem tendsto_nat_add_one_atTop :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun x ↦ ⟨Nat.ceil x, fun n hn ↦ ?_⟩
  have h2 : (x : ℝ) ≤ ((Nat.ceil x : ℕ) : ℝ) := Nat.le_ceil x
  have h3 : ((Nat.ceil x : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hn
  linarith

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
private theorem tendsto_one_div_nat_add :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  refine tendsto_nat_add_one_atTop.inv_tendsto_atTop.congr'
    (Eventually.of_forall fun n ↦ ?_)
  change ((n : ℝ) + 1)⁻¹ = (1 : ℝ) / ((n : ℝ) + 1)
  rw [one_div]

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The `1/√(n+1)` null sequence over the naturals. -/
theorem tendsto_inv_sqrt_nat_add :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt ((1 : ℝ) / ((n : ℝ) + 1))) atTop
      (𝓝 (Real.sqrt 0)) :=
    ((Real.continuous_sqrt.tendsto (0 : ℝ)).comp tendsto_one_div_nat_add).congr'
      (Eventually.of_forall fun n ↦ rfl)
  have hsqrt2 : Tendsto (fun n : ℕ ↦ Real.sqrt ((1 : ℝ) / ((n : ℝ) + 1))) atTop
      (𝓝 (0 : ℝ)) := by
    simpa [Real.sqrt_zero] using hsqrt
  refine hsqrt2.congr' (Eventually.of_forall fun n ↦ ?_)
  change Real.sqrt ((1 : ℝ) / ((n : ℝ) + 1)) = (1 : ℝ) / Real.sqrt ((n : ℝ) + 1)
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- **The drift² corrections of the quadratic block die**: the statement is the limit `0`.
The proof bounds the summed absolute expectations of the frozen weight against the
drift-increment squares by `2·C₂·D_β²·T²/(n+1)` (`O(mesh)`) — each drift increment is
pointwise `D_β·cell` (`AdaptedDrift.abs_driftPath_sub_le`) and the cells telescope to `T`. -/
theorem quadDriftSqSum_tendsto (hBmeas : ∀ t, Measurable (B t)) {β : ℝ≥0 → Ω → ℝ}
    {X : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    {g : ℝ → ℝ} {C2 : ℝ} (hgcont : Continuous g) (hg2 : ∀ x, |g x| ≤ C2) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hC2 : (0 : ℝ) ≤ C2 := le_trans (abs_nonneg _) (hg2 0)
  -- per-cell absolute bound
  have hcell : ∀ n : ℕ, ∀ k : ℕ,
      |∫ ω, g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ|
        ≤ C2 * Db ^ 2 * ((T : ℝ) / (n : ℝ)) ^ 2 := by
    intro n k
    have hXk : Measurable (X (unifPart T n k)) :=
      (hXadap (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    have hdpm : Measurable (driftPath β (unifPart T n (k + 1))) :=
      (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd
        (unifPart T n (k + 1))).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
    have hdp0 : Measurable (driftPath β (unifPart T n k)) :=
      (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd
        (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    have hmeas : Measurable (fun ω ↦ g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2) :=
      (hgcont.measurable.comp hXk).mul ((hdpm.sub hdp0).pow_const 2)
    have hbound : ∀ ω : Ω,
        |g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2|
        ≤ C2 * Db ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2 := by
      intro ω
      have h1 : |g (X (unifPart T n k) ω)| ≤ C2 := hg2 _
      have h2 : |driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω|
          ≤ Db * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
        abs_driftPath_sub_le hβcont hβbdd
          (unifPart_mono T n (Nat.le_succ k)) ω
      have hcellnn : (0 : ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
        sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
      have h3 : (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2
          ≤ (Db * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2 := by
        refine (sq_le_sq).mpr ?_
        rw [abs_mul, abs_of_nonneg hcellnn]
        rcases le_total 0 Db with hDb | hDb
        · rw [abs_of_nonneg hDb]; exact h2
        · rw [abs_of_nonpos hDb]
          have habs : (0 : ℝ) ≤ |driftPath β (unifPart T n (k + 1)) ω
              - driftPath β (unifPart T n k) ω| := abs_nonneg _
          have hnonpos : Db * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hDb hcellnn
          linarith
      rw [abs_mul, abs_pow (a := driftPath β (unifPart T n (k + 1)) ω
        - driftPath β (unifPart T n k) ω) 2, sq_abs]
      calc |g (X (unifPart T n k) ω)|
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2
          ≤ C2 * (Db * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2 :=
            mul_le_mul h1 h3 (sq_nonneg _) hC2
        _ = C2 * Db ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2 := by ring
    have hint : Integrable (fun ω ↦ g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2) μ :=
      Integrable.of_bound hmeas.aestronglyMeasurable
        (C2 * Db ^ 2 * ((T : ℝ) / (n : ℝ)) ^ 2 + 1)
        (Eventually.of_forall fun ω ↦ by
          change ‖g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω
                - driftPath β (unifPart T n k) ω) ^ 2‖ ≤ _
          rw [Real.norm_eq_abs]
          have h := hbound ω
          rw [unifPart_succ_sub T n k] at h
          linarith)
    calc |∫ ω, g (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ|
        ≤ ∫ ω, |g (X (unifPart T n k) ω)
            * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C2 * Db ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2) ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ abs_nonneg _)
            (integrable_const _) (Eventually.of_forall fun ω ↦ hbound ω)
      _ = C2 * Db ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2 := by
          rw [integral_const]; simp
      _ = C2 * Db ^ 2 * ((T : ℝ) / (n : ℝ)) ^ 2 := by rw [unifPart_succ_sub T n k]
  -- squeeze: the absolute sums die, hence the signed sums die
  have hboundtendsto : Tendsto (fun n : ℕ ↦ |∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n : ℕ ↦ 2 * C2 * Db ^ 2 * (T : ℝ) ^ 2 / ((n : ℝ) + 1))
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      calc |∑ k ∈ Finset.range n,
            ∫ ω, g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ|
          ≤ ∑ k ∈ Finset.range n,
            |∫ ω, g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n, (C2 * Db ^ 2 * ((T : ℝ) / (n : ℝ)) ^ 2) :=
            Finset.sum_le_sum fun k _ ↦ hcell n k
        _ = (n : ℝ) * (C2 * Db ^ 2 * ((T : ℝ) / (n : ℝ)) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = C2 * Db ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) := by
            field_simp
        _ ≤ 2 * C2 * Db ^ 2 * (T : ℝ) ^ 2 / ((n : ℝ) + 1) := by
            rw [div_le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))
              (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
            have hK : (0 : ℝ) ≤ C2 * Db ^ 2 * (T : ℝ) ^ 2 := by positivity
            have hnm : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            nlinarith
    · have hzero : ((2 * C2 * Db ^ 2 * (T : ℝ) ^ 2) * (0 : ℝ)) = (0 : ℝ) := mul_zero _
      have h2' : Tendsto (fun n : ℕ ↦ (2 * C2 * Db ^ 2 * (T : ℝ) ^ 2) / ((n : ℝ) + 1))
          atTop (𝓝 ((2 * C2 * Db ^ 2 * (T : ℝ) ^ 2) * 0)) := by
        refine ((tendsto_const_nhds
          (x := (2 * C2 * Db ^ 2 * (T : ℝ) ^ 2))).mul
          tendsto_nat_add_one_atTop.inv_tendsto_atTop).congr'
          (Eventually.of_forall fun n ↦ ?_)
        change (2 * C2 * Db ^ 2 * (T : ℝ) ^ 2) * ((n : ℝ) + 1)⁻¹
          = (2 * C2 * Db ^ 2 * (T : ℝ) ^ 2) / ((n : ℝ) + 1)
        rw [div_eq_mul_inv]
      rwa [hzero] at h2'
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  refine hboundtendsto.congr' (Eventually.of_forall fun n ↦ ?_)
  change |∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ|
    = dist (∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω) ^ 2 ∂μ) 0
  rw [Real.dist_eq, sub_zero]

omit hB hBmeas hδadap hδcont hδbdd hMadap hMeq in
/-- The `1/√n ≤ 2/√(n+1)` comparison for `n ≥ 1`. -/
theorem one_div_sqrt_le_two {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / Real.sqrt ((n : ℝ)) ≤ 2 / Real.sqrt (((n : ℝ)) + 1) := by
  have hne : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpos1 : (0 : ℝ) < Real.sqrt ((n : ℝ)) := Real.sqrt_pos.mpr hne
  have hpos2 : (0 : ℝ) < Real.sqrt (((n : ℝ)) + 1) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (((n : ℝ)) + 1) ≤ 2 * Real.sqrt ((n : ℝ)) := by
    have hnm : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    refine le_trans (Real.sqrt_le_sqrt (show ((n : ℝ)) + 1 ≤ 4 * (n : ℝ) from by nlinarith)) ?_
    rw [show (2 : ℝ) * Real.sqrt ((n : ℝ)) = Real.sqrt (4 * (n : ℝ)) from by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num]
  rw [div_le_div_iff₀ hpos1 hpos2]
  simpa using hsq

set_option maxHeartbeats 1600000 in
-- a long estimate: elaborating the whole proof exceeds the default budget
/-- **The drift–martingale cross corrections of the quadratic block die**: the statement is
the limit `0`. The proof bounds the summed absolute expectations of the frozen weight against
`Δ(AdaptedDrift.driftPath β)ₖ·ΔMₖ` by `2·C₂·|D_β|·|D_δ|·T·√T/√(n+1)` (`O(√mesh)`) —
Cauchy–Schwarz pairs the
`D_β·cell`-bounded drift increment (`AdaptedDrift.abs_driftPath_sub_le`) against the
`D_δ²·cell`-energy martingale increment (`trueIncr_sq_le`), and the cells telescope to `T`. -/
theorem quadCrossSum_tendsto {β : ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hβadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (β t))
    (hβcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ β s ω)
    {Db : ℝ} (hβbdd : ∀ t ω, |β t ω| ≤ Db)
    (hXadap : ∀ t, StronglyMeasurable[natFiltration hBmeas t] (X t))
    {g : ℝ → ℝ} {C2 : ℝ} (hgcont : Continuous g) (hg2 : ∀ x, |g x| ≤ C2) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ)
      atTop (𝓝 0) := by
  have hC2 : (0 : ℝ) ≤ C2 := le_trans (abs_nonneg _) (hg2 0)
  have hβbdd' : ∀ t ω, |β t ω| ≤ |Db| := fun t ω ↦ (hβbdd t ω).trans (le_abs_self Db)
  -- per-cell absolute bound
  have hcell : ∀ n : ℕ, ∀ k : ℕ, k < n →
      |∫ ω, g (X (unifPart T n k) ω)
          * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ|
        ≤ C2 * |Db| * |Dd| * (((unifPart T n (k + 1) : ℝ) - unifPart T n k)
          * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) := by
    intro n k hk
    have hcellnn : (0 : ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k :=
      sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k)))
    have hXk : Measurable (X (unifPart T n k)) :=
      (hXadap (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    have hdpm : Measurable (driftPath β (unifPart T n (k + 1))) :=
      (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd
        (unifPart T n (k + 1))).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n (k + 1))) le_rfl
    have hdp0 : Measurable (driftPath β (unifPart T n k)) :=
      (stronglyMeasurable_driftPath hBmeas hβadap hβcont hβbdd
        (unifPart T n k)).measurable.mono
        ((natFiltration hBmeas).le (unifPart T n k)) le_rfl
    set dI : Ω → ℝ := fun ω ↦ driftPath β (unifPart T n (k + 1)) ω
      - driftPath β (unifPart T n k) ω with hdIdef
    set tI : Ω → ℝ := fun ω ↦ M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω with htIdef
    -- the drift increment: bounded pointwise by `|Db|·cell`, `L²`
    have hdIb : ∀ ω : Ω, |dI ω| ≤ |Db| * ((unifPart T n (k + 1) : ℝ)
        - unifPart T n k) := fun ω ↦
      abs_driftPath_sub_le hβcont hβbdd'
        (unifPart_mono T n (Nat.le_succ k)) ω
    have hdImem : MemLp dI 2 μ := by
      have hdIm : Measurable dI := by
        rw [hdIdef]
        exact hdpm.sub hdp0
      exact MemLp.of_bound hdIm.aestronglyMeasurable
        (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
        (Eventually.of_forall fun ω ↦ by
          change ‖dI ω‖ ≤ _
          rw [Real.norm_eq_abs]
          exact hdIb ω)
    have htImem : MemLp tI 2 μ :=
      (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq
        (unifPart T n (k + 1))).sub
        (memLp_M hB hBmeas hδadap hδcont hδbdd hMeq (unifPart T n k))
    -- the mean-integrability inputs
    have hone : MemLp (fun _ : Ω ↦ (1 : ℝ)) 2 μ :=
      MemLp.of_bound (stronglyMeasurable_const.aestronglyMeasurable) 1
        (Eventually.of_forall fun ω ↦ by norm_num)
    have hnorm1 : ∫ ω, |tI ω| ∂μ ≤ Real.sqrt (∫ ω, tI ω ^ 2 ∂μ) := by
      have h1 := integral_abs_mul_le_L2L2 (htImem.norm) hone
      have hA : (∫ ω, abs (‖tI ω‖ * 1) ∂μ) = ∫ ω, |tI ω| ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
        change abs (‖tI ω‖ * 1) = |tI ω|
        rw [Real.norm_eq_abs, mul_one, abs_abs]
      have hB : (∫ ω, ‖tI ω‖ ^ 2 ∂μ) = ∫ ω, tI ω ^ 2 ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
        change ‖tI ω‖ ^ 2 = tI ω ^ 2
        rw [Real.norm_eq_abs, sq_abs]
      rw [hA, hB] at h1
      simpa using h1
    have htI2 := trueIncr_sq_le hB hBmeas hδadap hδcont hδbdd hMadap hMeq
      (unifPart_mono T n (Nat.le_succ k)) (unifPart_le_T (Nat.lt_iff_add_one_le.mp hk))
    have hsqrtT : Real.sqrt (∫ ω, tI ω ^ 2 ∂μ) ≤ |Dd| * Real.sqrt
        ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
      have h2 : Real.sqrt (∫ ω, tI ω ^ 2 ∂μ)
          ≤ Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω
            - M (unifPart T n k) ω) ^ 2 ∂μ) := by
        refine Real.sqrt_le_sqrt ?_
        simp only [htIdef]
        exact le_refl _
      refine le_trans (le_trans h2 (Real.sqrt_le_sqrt htI2)) ?_
      rw [Real.sqrt_mul (sq_nonneg Dd), Real.sqrt_sq_eq_abs]
    -- integrability of the full product
    have hprodint : Integrable (fun ω ↦ g (X (unifPart T n k) ω) * dI ω * tI ω) μ := by
      refine Integrable.mono'
        ((htImem.norm.integrable one_le_two).const_mul (C2 * |Db| * ((unifPart T n (k + 1) : ℝ)
          - unifPart T n k)))
        (((hgcont.measurable.comp hXk).aestronglyMeasurable.mul
          (MemLp.aestronglyMeasurable hdImem)).mul (MemLp.aestronglyMeasurable htImem))
        (Eventually.of_forall fun ω ↦ by
          change ‖g (X (unifPart T n k) ω) * dI ω * tI ω‖ ≤ _
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
          calc |g (X (unifPart T n k) ω)| * |dI ω| * |tI ω|
              ≤ (C2 * (|Db| * ((unifPart T n (k + 1) : ℝ)
                - unifPart T n k))) * |tI ω| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul (hg2 _) (hdIb ω) (abs_nonneg _) hC2)
                  (abs_nonneg _)
            _ = _ := by ring)
    -- pointwise domination `|g·dI·tI| ≤ K·|tI|`
    have hptmono : ∀ ω : Ω, |g (X (unifPart T n k) ω) * dI ω * tI ω|
        ≤ (C2 * (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) * |tI ω| := by
      intro ω
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hg2 _) (hdIb ω) (abs_nonneg _) hC2) (abs_nonneg _)
    set K : ℝ := C2 * (|Db| * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) with hKdef
    have hK0 : (0 : ℝ) ≤ K := by
      rw [hKdef]
      exact mul_nonneg hC2 (mul_nonneg (abs_nonneg Db) hcellnn)
    calc |∫ ω, g (X (unifPart T n k) ω) * dI ω * tI ω ∂μ|
        ≤ ∫ ω, |g (X (unifPart T n k) ω) * dI ω * tI ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (K * |tI ω|) ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ abs_nonneg _)
            ((htImem.norm.integrable one_le_two).const_mul K)
            (Eventually.of_forall hptmono)
      _ = K * ∫ ω, |tI ω| ∂μ := by rw [integral_const_mul]
      _ ≤ K * (|Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ)
            - unifPart T n k)) :=
            mul_le_mul_of_nonneg_left (le_trans hnorm1 hsqrtT) hK0
      _ = C2 * |Db| * |Dd| * (((unifPart T n (k + 1) : ℝ) - unifPart T n k)
            * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) := by
          rw [hKdef]; ring
  -- squeeze
  have hboundtendsto : Tendsto (fun n : ℕ ↦ |∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n : ℕ ↦ 2 * C2 * |Db| * |Dd| * (T : ℝ)
      * Real.sqrt (T : ℝ) * (1 / Real.sqrt (((n : ℝ)) + 1)))
      (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have hTnn : ((n : ℝ)) * ((T : ℝ) / (n : ℝ)) = (T : ℝ) := by
        field_simp
      have hsum : ∑ k ∈ Finset.range n,
          (((unifPart T n (k + 1) : ℝ) - unifPart T n k)
            * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
          = (T : ℝ) * Real.sqrt ((T : ℝ) / (n : ℝ)) := by
        have hstep : ∀ k : ℕ, k ∈ Finset.range n →
            (((unifPart T n (k + 1) : ℝ) - unifPart T n k)
              * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
            = ((T : ℝ) / (n : ℝ)) * Real.sqrt ((T : ℝ) / (n : ℝ)) := fun k _ ↦ by
          rw [unifPart_succ_sub T n k]
        have hsumlast : ((n : ℝ)) * (((T : ℝ) / (n : ℝ)) * Real.sqrt ((T : ℝ) / (n : ℝ)))
            = (T : ℝ) * Real.sqrt ((T : ℝ) / (n : ℝ)) := by
          field_simp
        rw [Finset.sum_congr rfl hstep, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, hsumlast]
      have hsplit : ((T : ℝ)) * Real.sqrt ((T : ℝ) / (n : ℝ))
          = ((T : ℝ)) * Real.sqrt (T : ℝ) * (1 / Real.sqrt ((n : ℝ))) := by
        rw [Real.sqrt_div (by exact_mod_cast NNReal.coe_nonneg T : (0 : ℝ) ≤ (T : ℝ)),
          one_div]
        ring
      have hTs0 : (0 : ℝ) ≤ ((T : ℝ)) * Real.sqrt (T : ℝ) :=
        mul_nonneg (NNReal.coe_nonneg T) (Real.sqrt_nonneg _)
      have hK0 : (0 : ℝ) ≤ C2 * |Db| * |Dd| := by positivity
      calc |∑ k ∈ Finset.range n,
            ∫ ω, g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ|
          ≤ ∑ k ∈ Finset.range n,
            |∫ ω, g (X (unifPart T n k) ω)
              * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
              * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n, (C2 * |Db| * |Dd| * (((unifPart T n (k + 1) : ℝ)
              - unifPart T n k) * Real.sqrt ((unifPart T n (k + 1) : ℝ)
              - unifPart T n k))) :=
            Finset.sum_le_sum fun k hk ↦ hcell n k (Finset.mem_range.mp hk)
        _ = C2 * |Db| * |Dd| * ((T : ℝ) * Real.sqrt ((T : ℝ) / (n : ℝ))) := by
            rw [← Finset.mul_sum, hsum]
        _ = C2 * |Db| * |Dd| * (((T : ℝ)) * Real.sqrt (T : ℝ)
              * (1 / Real.sqrt ((n : ℝ)))) := by rw [hsplit]
        _ ≤ C2 * |Db| * |Dd| * (((T : ℝ)) * Real.sqrt (T : ℝ)
              * (2 / Real.sqrt (((n : ℝ)) + 1))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (one_div_sqrt_le_two hn) hTs0) hK0
        _ = 2 * C2 * |Db| * |Dd| * ((T : ℝ)) * Real.sqrt (T : ℝ)
              * (1 / Real.sqrt (((n : ℝ)) + 1)) := by ring
    · have hzero : ((2 * C2 * |Db| * |Dd| * (T : ℝ) * Real.sqrt (T : ℝ)) * (0 : ℝ))
          = (0 : ℝ) := mul_zero _
      have h2' : Tendsto (fun n : ℕ ↦ (2 * C2 * |Db| * |Dd| * (T : ℝ)
            * Real.sqrt (T : ℝ)) * (1 / Real.sqrt (((n : ℝ)) + 1)))
          atTop (𝓝 ((2 * C2 * |Db| * |Dd| * (T : ℝ) * Real.sqrt (T : ℝ)) * 0)) :=
        (tendsto_const_nhds (x := (2 * C2 * |Db| * |Dd| * (T : ℝ)
          * Real.sqrt (T : ℝ)))).mul tendsto_inv_sqrt_nat_add
      rwa [hzero] at h2'
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  refine hboundtendsto.congr' (Eventually.of_forall fun n ↦ ?_)
  change |∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ|
    = dist (∑ k ∈ Finset.range n,
      ∫ ω, g (X (unifPart T n k) ω)
        * (driftPath β (unifPart T n (k + 1)) ω - driftPath β (unifPart T n k) ω)
        * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ∂μ) 0
  rw [Real.dist_eq, sub_zero]

end StageFiveD

end MathFin.ItoDriftConditional
