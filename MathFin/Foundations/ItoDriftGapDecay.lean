/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Foundations.ItoDriftIncrementEnergy
public import MathFin.Foundations.ItoDriftWeightedIsometry
public import MathFin.Foundations.FiniteMeasureCauchySchwarz

/-! # The gap decay of the weighted increment isometry (the discrete route, stage 5a)

Discharges the `hgap` hypothesis of `quadraticSqSum_tendsto` for the hypothesized `M`
(`gapSum_le`, `quadraticSqSum_tendsto'`): the per-cell Cauchy–Schwarz pairing of the error
increment against the cell energy, summed through the band energies of `clm_band_energy`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MathFin.ItoDriftConditional

open MathFin ItoIntegralL2 ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted
  ItoIntegralProcessGeneral ItoIntegralProcess QuadraticVariationL2 ItoIntegralBrownian
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The real `L²` triangle inequality at the integral level: `‖a + b‖₂ ≤ ‖a‖₂ + ‖b‖₂`. -/
private theorem sqrtIntegral_sq_add_le {a b : Ω → ℝ}
    (ham : MemLp a 2 μ) (hbm : MemLp b 2 μ) :
    √(∫ ω, (a ω + b ω) ^ 2 ∂μ) ≤ √(∫ ω, a ω ^ 2 ∂μ) + √(∫ ω, b ω ^ 2 ∂μ) := by
  have h {f : Ω → ℝ} (hf : MemLp f 2 μ) : √(∫ ω, f ω ^ 2 ∂μ) = ‖hf.toLp f‖ := by
    refine (congrArg Real.sqrt ?_).trans (Real.sqrt_sq (norm_nonneg _))
    rw [lp_two_norm_sq]
    exact integral_congr_ae (hf.coeFn_toLp.mono fun ω hω ↦ by simp only [hω])
  refine (h (ham.add hbm)).trans_le ?_
  rw [h ham, h hbm, MemLp.toLp_add]
  exact norm_add_le _ _

/-- Generic weighted-square transfer: if `f =ᵐ g`, `g²` is integrable with energy `E`,
and `|w| ≤ C`, then `𝔼[(w·f)²] ≤ C²·E`. -/
private theorem weighted_sq_le_of_congr {f g w : Ω → ℝ} {C E : ℝ}
    (hwb : ∀ ω, |w ω| ≤ C) (hcongr : f =ᵐ[μ] g)
    (hint2 : Integrable (fun ω ↦ g ω ^ 2) μ) (hE : ∫ ω, g ω ^ 2 ∂μ = E) :
    ∫ ω, (w ω * f ω) ^ 2 ∂μ ≤ C ^ 2 * E :=
  calc ∫ ω, (w ω * f ω) ^ 2 ∂μ
      = ∫ ω, (w ω * g ω) ^ 2 ∂μ :=
        integral_congr_ae (by filter_upwards [hcongr] with ω hω; rw [hω])
    _ ≤ ∫ ω, C ^ 2 * g ω ^ 2 ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
          (hint2.const_mul (C ^ 2)) (Eventually.of_forall fun ω ↦ ?_)
        have hw := abs_le.mp (hwb ω)
        change (w ω * g ω) ^ 2 ≤ C ^ 2 * g ω ^ 2
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (sq_le_sq' hw.1 hw.2) (sq_nonneg _)
    _ = C ^ 2 * E := by rw [integral_const_mul, hE]

variable [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-! #### Stage 5a — the gap decay, discharging `hgap` (for the hypothesized `M`)

The per-cell Cauchy–Schwarz pairing of the error increment `δεₖ = ΔMₖ − δ(tₖ)·ΔBₖ`
against the cell energy. The error increment is the band increment of the CLM process of
the integrand error `ψₙ = φ − δⁿ` (linearity of the CLM map + the per-cell step
identification), so its band energy is `∫_{bandₖ} ψₙ²` (`clm_band_energy`) and the summed
band energies telescope to `‖ψₙ‖²_{L²(trim)}` (`uniform_band_split` + the `Lp` norm).
The pairing gives exactly the constant `2·|C_w|·|D_δ|·√T` of `quadraticSqSum_tendsto`'s
`hgap`, and `deltaStepLp_tendsto` makes the bound a null sequence. -/

section StageFiveA

variable (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
  {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
  {M : ℝ≥0 → Ω → ℝ} (hD : IsAdaptedItoDrift hB hBmeas T δ Dd M)

/-- Coe-linearity of the CLM process in the integrand class (the a.e. form). -/
private theorem clm_coe_sub_ae (T t : ℝ≥0)
    (φ₁ φ₂ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ((itoProcessCLM hB T t hBmeas (φ₁ - φ₂) : Lp ℝ 2 μ) : Ω → ℝ)
      =ᵐ[μ] (fun ω ↦ (itoProcessCLM hB T t hBmeas φ₁ : Ω → ℝ) ω
        - (itoProcessCLM hB T t hBmeas φ₂ : Ω → ℝ) ω) := by
  rw [map_sub]
  exact Lp.coeFn_sub _ _

include hD in
/-- The per-cell error increment `δεₖ := ΔMₖ − δ(tₖ)·ΔBₖ` is a.e. the band increment of the
CLM process of the integrand error `φ − δⁿ`. -/
private theorem errorIncr_ae {n k : ℕ} (hk : k < n) :
    (fun ω ↦ M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
        - δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
      =ᵐ[μ] (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
              (hD.integrand
                - deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
              (hD.integrand
                - deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω) := by
  have h1 := hD.ae_eq (unifPart T n (k + 1))
  have h0 := hD.ae_eq (unifPart T n k)
  have hsub1 := clm_coe_sub_ae (μ := μ) hB hBmeas T (unifPart T n (k + 1))
    hD.integrand (deltaStepLp hBmeas hD.adapted hD.bdd n)
  have hsub0 := clm_coe_sub_ae (μ := μ) hB hBmeas T (unifPart T n k)
    hD.integrand (deltaStepLp hBmeas hD.adapted hD.bdd n)
  have hstep : (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω)
      =ᵐ[μ] (fun ω ↦ δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) :=
    stepIncr_stepCLM_ae (μ := μ) (B := B) (hB := hB) (hBmeas := hBmeas)
    (hδadap := hD.adapted) (hδbdd := hD.bdd) (T := T) (n := n) (k := k) hk
  filter_upwards [h1, h0, hsub1, hsub0, hstep] with ω h1 h0 hsub1 hsub0 hstep
  calc M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
        - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)
      = (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          hD.integrand : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
          hD.integrand : Ω → ℝ) ω
        - ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω
          - (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω) := by
        rw [h1, h0, ← hstep]
    _ = ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            hD.integrand : Ω → ℝ) ω
          - (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω)
        - ((itoProcessCLM hB T (unifPart T n k) hBmeas
            hD.integrand : Ω → ℝ) ω
          - (itoProcessCLM hB T (unifPart T n k) hBmeas
            (deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω) := by ring
    _ = (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
          (hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
          (hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω := by
        rw [hsub1, hsub0]

include hD in
/-- **Weighted error energy**: the second moment of `w·δεₖ` is at most `C_w²` cell-band
energies of the integrand error (`|w| ≤ C_w` pointwise). -/
private theorem weightedErrorIncr_sq_le {n k : ℕ} (hk : k < n) {w : Ω → ℝ} {Cw : ℝ}
    (hwb : ∀ ω, |w ω| ≤ Cw) :
    ∫ ω, (w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
        - δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))) ^ 2 ∂μ
      ≤ Cw ^ 2 * ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
            (Set.univ : Set Ω),
          ((hD.integrand
              - deltaStepLp hBmeas hD.adapted hD.bdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  -- the CLM error increment and its square integrability
  have hDmem : MemLp
      (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
            (hD.integrand
              - deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω
        - (itoProcessCLM hB T (unifPart T n k) hBmeas
          (hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω) 2 μ :=
    (Lp.memLp (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
      (hD.integrand
        - deltaStepLp hBmeas hD.adapted hD.bdd n))).sub
      (Lp.memLp (itoProcessCLM hB T (unifPart T n k) hBmeas
        (hD.integrand
          - deltaStepLp hBmeas hD.adapted hD.bdd n)))
  -- the energy of the CLM error increment is the band energy
  have hbandE : ∫ ω, ((itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
        (hD.integrand
          - deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (hD.integrand
          - deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω) ^ 2 ∂μ
      = ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
          ((hD.integrand
              - deltaStepLp hBmeas hD.adapted hD.bdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
    (clm_band_energy hB hBmeas
      (hD.integrand - deltaStepLp hBmeas hD.adapted hD.bdd
        n)
      (unifPart_mono T n (Nat.le_succ k))
      (unifPart_le_T hk))
  exact weighted_sq_le_of_congr hwb
    (errorIncr_ae hB hBmeas hD hk)
    hDmem.integrable_sq hbandE

include hD

/-- **Per-cell gap bound**: the absolute difference over one cell between the expectations
of the weighted true-increment square and of the weighted rectangle square — the
Cauchy–Schwarz pairing of the
error increment `δεₖ` against the cell energy `ΔMₖ + δ(tₖ)ΔBₖ`, each factor bounded by the
weighted error energy (`weightedErrorIncr_sq_le`) and the `2·|D_δ|·√cell` cell energy
(`trueIncr_sq_le` + the rectangle second moment). -/
private theorem cellGap_le {n k : ℕ} (hk : k < n) {w : Ω → ℝ} {Cw : ℝ}
    (hwm : Measurable[natFiltration hBmeas (unifPart T n k)] w)
    (hwb : ∀ ω, |w ω| ≤ Cw) :
    |∫ ω, w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∫ ω, w ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ|
      ≤ 2 * |Cw| * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
        * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
            (Set.univ : Set Ω),
          ((hD.integrand
              - deltaStepLp hBmeas hD.adapted hD.bdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
  have huv : unifPart T n k ≤ unifPart T n (k + 1) := unifPart_mono T n (Nat.le_succ k)
  have hδm : Measurable (δ (unifPart T n k)) :=
    ((hD.adapted (unifPart T n k)).measurable.mono ((natFiltration hBmeas).le _) le_rfl)
  have hdBm : Measurable (fun ω ↦ B (unifPart T n (k + 1)) ω
      - B (unifPart T n k) ω) := (hBmeas _).sub (hBmeas _)
  have hwm' : Measurable w := hwm.mono ((natFiltration hBmeas).le _) le_rfl
  have hsmeas : Measurable (fun ω ↦ δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) := hδm.mul hdBm
  have hMsub : MemLp (fun ω ↦ M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) 2 μ :=
    (memLp_M hB hBmeas hD (unifPart T n (k + 1))).sub
      (memLp_M hB hBmeas hD (unifPart T n k))
  have hMsub2 : Integrable (fun ω ↦ (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2) μ := hMsub.integrable_sq
  have hdB : MemLp (fun ω ↦ B (unifPart T n (k + 1)) ω
      - B (unifPart T n k) ω) 2 μ := hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  -- the rectangle increment `s = δ(tₖ)·ΔBₖ` is `L²`
  have hs : MemLp (fun ω ↦ δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) 2 μ :=
    MemLp.mono' (hdB.const_mul (|Dd|)).abs
      hsmeas.aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by
        change ‖δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)‖
          ≤ |(|Dd| * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))|
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (abs_nonneg Dd)]
        exact mul_le_mul_of_nonneg_right (le_trans (hD.bdd (unifPart T n k) ω)
          (le_abs_self Dd)) (abs_nonneg _))
  -- measurability of the true increment
  have hM1m : Measurable (M (unifPart T n (k + 1))) :=
    ((hD.adaptedM (unifPart T n (k + 1))).measurable.mono ((natFiltration hBmeas).le _) le_rfl)
  have hM0m : Measurable (M (unifPart T n k)) :=
    ((hD.adaptedM (unifPart T n k)).measurable.mono ((natFiltration hBmeas).le _) le_rfl)
  have hMsubm : Measurable (fun ω ↦ M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) := hM1m.sub hM0m
  -- integrability of the two weighted terms
  have hwM2 : Integrable (fun ω ↦ w ω * (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2) μ := by
    refine Integrable.mono' (hMsub2.const_mul Cw)
      (hwm'.mul (hMsubm.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (sq_nonneg (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω))]
        exact mul_le_mul_of_nonneg_right (hwb ω) (sq_nonneg _))
  have hws2 : Integrable (fun ω ↦ w ω * (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2) μ := by
    refine Integrable.mono' ((hdB.integrable_sq).const_mul (Cw * Dd ^ 2))
      (hwm'.mul (hsmeas.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_mul]
        have hδ2 : |δ (unifPart T n k) ω| ≤ |Dd| :=
          le_trans (hD.bdd (unifPart T n k) ω) (le_abs_self Dd)
        have hAB : |δ (unifPart T n k) ω| * |B (unifPart T n (k + 1)) ω
            - B (unifPart T n k) ω| ≤ |Dd| * |B (unifPart T n (k + 1)) ω
            - B (unifPart T n k) ω| :=
          mul_le_mul_of_nonneg_right hδ2 (abs_nonneg _)
        have h2 := sq_le_sq' (by
          have hB0 := mul_nonneg (abs_nonneg (|Dd|))
            (abs_nonneg (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
          have hA0 := mul_nonneg (abs_nonneg (δ (unifPart T n k) ω))
            (abs_nonneg (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
          linarith) hAB
        have h3 : (|Dd| * |B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω|) ^ 2
            = Dd ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 := by
          rw [mul_pow, sq_abs, sq_abs]
        calc |w ω| * (|δ (unifPart T n k) ω| * |B (unifPart T n (k + 1)) ω
                - B (unifPart T n k) ω|) ^ 2
            ≤ |w ω| * ((|Dd| * |B (unifPart T n (k + 1)) ω
              - B (unifPart T n k) ω|) ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          _ ≤ Cw * ((|Dd| * |B (unifPart T n (k + 1)) ω
              - B (unifPart T n k) ω|) ^ 2) :=
              mul_le_mul_of_nonneg_right (hwb ω) (sq_nonneg _)
          _ = Cw * Dd ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 := by
              rw [h3]; ring)
  -- the square identity and the integral form of the gap
  have key : ∫ ω, w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∫ ω, w ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ
      = ∫ ω, w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))
          * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ∂μ := by
    rw [← integral_sub hwM2 hws2]
    exact integral_congr_ae (Eventually.of_forall fun ω ↦ by ring)
  -- the Cauchy–Schwarz pairing
  have hDmem : MemLp (fun ω ↦ (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
        (hD.integrand
          - deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω
      - (itoProcessCLM hB T (unifPart T n k) hBmeas
        (hD.integrand
          - deltaStepLp hBmeas hD.adapted hD.bdd n) : Ω → ℝ) ω) 2 μ :=
    (Lp.memLp (itoProcessCLM hB T (unifPart T n (k + 1)) hBmeas
      (hD.integrand
        - deltaStepLp hBmeas hD.adapted hD.bdd n))).sub
      (Lp.memLp (itoProcessCLM hB T (unifPart T n k) hBmeas
        (hD.integrand
          - deltaStepLp hBmeas hD.adapted hD.bdd n)))
  have haede := errorIncr_ae hB hBmeas hD hk
  have hδεsm : AEStronglyMeasurable (fun ω ↦ M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω
      - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) μ :=
    AEStronglyMeasurable.congr hDmem.aestronglyMeasurable haede.symm
  have hpair : ∫ ω, |w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
          - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))
        * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
          + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))| ∂μ
      ≤ Real.sqrt (∫ ω, (w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
            - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))) ^ 2 ∂μ)
        * Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
          + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
    integral_abs_mul_le_sqrt_mul_sqrt
      (MemLp.mono' ((hDmem.abs).const_mul (|Cw|))
        (hwm'.aestronglyMeasurable.mul hδεsm)
        (by
          filter_upwards [haede] with ω hω
          rw [Real.norm_eq_abs, abs_mul, hω]
          exact mul_le_mul_of_nonneg_right (le_trans (hwb ω) (le_abs_self Cw))
            (abs_nonneg _)))
      (hMsub.add hs)
  -- the two energy factors
  have hwde := weightedErrorIncr_sq_le hB hBmeas hD hk hwb
  have htri : Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
        + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)
      ≤ Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
        + Real.sqrt (∫ ω, (δ (unifPart T n k) ω
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
    sqrtIntegral_sq_add_le hMsub hs
  have hM2le := trueIncr_sq_le hB hBmeas hD huv
    (unifPart_le_T hk)
  have hs2le : ∫ ω, (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ
      ≤ Dd ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    have hdom : Integrable (fun ω ↦ Dd ^ 2
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) μ :=
      (hdB.integrable_sq.const_mul (Dd ^ 2)).congr
        (Eventually.of_forall fun ω ↦ by ring)
    refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
      hdom (ae_of_all _ fun ω ↦ ?_)) ?_
    · change (δ (unifPart T n k) ω
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ≤ _
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq).mpr (le_trans (hD.bdd (unifPart T n k) ω) (le_abs_self Dd))) (sq_nonneg _)
    · rw [integral_const_mul]
      have hΔ : ∫ ω, (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 ∂μ
          = ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
        integral_increment_sq hB (unifPart_mono T n (Nat.le_succ k))
      rw [hΔ]
  -- the two sqrt bounds
  have hsqrtM : Real.sqrt (∫ ω, (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2 ∂μ) ≤ |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ)
      - unifPart T n k) := by
    refine le_trans (Real.sqrt_le_sqrt hM2le) ?_
    rw [Real.sqrt_mul (sq_nonneg Dd), Real.sqrt_sq_eq_abs]
  have hsqrts : Real.sqrt (∫ ω, (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)
      ≤ |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    refine le_trans (Real.sqrt_le_sqrt hs2le) ?_
    rw [Real.sqrt_mul (sq_nonneg Dd), Real.sqrt_sq_eq_abs]
  have hsqrttri : Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
        + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)
      ≤ 2 * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    have h1 := htri
    have h2 := hsqrtM
    have h3 := hsqrts
    nlinarith [Real.sqrt_nonneg (∫ ω, (M (unifPart T n (k + 1)) ω
      - M (unifPart T n k) ω) ^ 2 ∂μ), Real.sqrt_nonneg (∫ ω, (δ (unifPart T n k) ω
      * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)]
  -- assembly
  calc |∫ ω, w ω * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
          - ∫ ω, w ω * (δ (unifPart T n k) ω
              * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ|
      = |∫ ω, w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
              - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))
            * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
              + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ∂μ| :=
        by rw [key]
    _ ≤ ∫ ω, |w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
              - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))
            * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
              + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ Real.sqrt (∫ ω, (w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
              - δ (unifPart T n k) ω
                * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)))) ^ 2 ∂μ)
          * Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
        hpair
    _ ≤ (|Cw| * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
              (Set.univ : Set Ω),
            ((hD.integrand
                - deltaStepLp hBmeas hD.adapted hD.bdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas)))
          * Real.sqrt (∫ ω, ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω)
            + δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_right
          (by
            calc Real.sqrt (∫ ω, (w ω * ((M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω
                      - δ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω
                        - B (unifPart T n k) ω)))) ^ 2 ∂μ)
                ≤ Real.sqrt (Cw ^ 2 * ∫ z in Set.Ioc (unifPart T n k)
                    (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  ((hD.integrand
                      - deltaStepLp hBmeas hD.adapted hD.bdd n :
                        Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
                  ∂(trimMeasure_T (μ := μ) T hBmeas)) := Real.sqrt_le_sqrt hwde
              _ = |Cw| * Real.sqrt (∫ z in Set.Ioc (unifPart T n k)
                    (unifPart T n (k + 1)) ×ˢ (Set.univ : Set Ω),
                  ((hD.integrand
                      - deltaStepLp hBmeas hD.adapted hD.bdd n :
                        Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
                  ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
                  rw [Real.sqrt_mul (sq_nonneg Cw), Real.sqrt_sq_eq_abs])
          (Real.sqrt_nonneg _)
    _ ≤ (|Cw| * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
              (Set.univ : Set Ω),
            ((hD.integrand
                - deltaStepLp hBmeas hD.adapted hD.bdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas)))
          * (2 * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) :=
        mul_le_mul_of_nonneg_left hsqrttri
          (mul_nonneg (abs_nonneg Cw) (Real.sqrt_nonneg _))
    _ = 2 * |Cw| * |Dd| * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
          * Real.sqrt (∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
              (Set.univ : Set Ω),
            ((hD.integrand
                - deltaStepLp hBmeas hD.adapted hD.bdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
            ∂(trimMeasure_T (μ := μ) T hBmeas)) := by ring

/-- **The summed gap bound** (the `hgap` witness of `quadraticSqSum_tendsto`, proved for the
hypothesized `M` of `hD.adaptedM`, `hD.ae_eq`): the absolute difference between the summed weighted
second moments and the frozen rectangle sum is at most `2·|C_w|·|D_δ|·√T` times the `L²`
norm of the integrand error `φ − δⁿ` — per-cell Cauchy–Schwarz (`cellGap_le`), then
finite-sum Cauchy–Schwarz against the cell lengths (telescoping to `T`) and the summed band
energies of the error class (telescoping to `‖φ − δⁿ‖²` via `uniform_band_split` and the
`Lp` norm). -/
theorem gapSum_le (n : ℕ) (hn : 0 < n) {w : ℝ≥0 → Ω → ℝ} {Cw : ℝ}
    (hwadap : ∀ t, Measurable[natFiltration hBmeas t] (w t))
    (hwbdd : ∀ t ω, |w t ω| ≤ Cw) :
    |∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
      - ∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
      ≤ 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ)
        * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
          ((hD.integrand
              - deltaStepLp hBmeas hD.adapted hD.bdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
  -- the cell lengths and the band energies of the integrand error
  set cell : ℕ → ℝ := fun k ↦ ((unifPart T n (k + 1) : ℝ) - unifPart T n k) with hcelldef
  set bandE : ℕ → ℝ := fun k ↦ ∫ z in Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) ×ˢ
      (Set.univ : Set Ω),
      ((hD.integrand
          - deltaStepLp hBmeas hD.adapted hD.bdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
      ∂(trimMeasure_T (μ := μ) T hBmeas) with hbandEdef
  -- bridge the frozen sum to the rectangle sum (the per-cell weighted identity)
  have hsumbridge : ∑ k ∈ Finset.range n,
      (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ) * cell k
      = ∑ k ∈ Finset.range n, ∫ ω, w (unifPart T n k) ω
          * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ :=
    Finset.sum_congr rfl fun k _ ↦
      (weightedCellSq_step hB hBmeas hD.adapted (hwadap (unifPart T n k))).symm
  -- per-cell gap bounds
  have hpercell : ∀ k ∈ Finset.range n,
      |∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ|
        ≤ 2 * |Cw| * |Dd| * Real.sqrt (cell k) * Real.sqrt (bandE k) :=
    fun k hk ↦ cellGap_le hB hBmeas hD (Finset.mem_range.mp hk)
      (hwadap (unifPart T n k)) (hwbdd (unifPart T n k))
  -- the cell lengths telescope to `T`; the band energies telescope to `‖φ − δⁿ‖²`
  have hsumcell : ∑ k ∈ Finset.range n, cell k = (T : ℝ) := by
    rw [Finset.sum_range_sub (fun k ↦ ((unifPart T n k : ℝ)))]
    have hnT : unifPart T n n = T := unifPart_self T hn.ne'
    have h0 : unifPart T n 0 = 0 := unifPart_zero T n
    rw [hnT, h0]; simp
  have hbandsum : ∑ k ∈ Finset.range n, bandE k
      = ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas) :=
    (uniform_band_split hBmeas hn
      (hFint := (Lp.memLp (hD.integrand
        - deltaStepLp hBmeas hD.adapted hD.bdd n)).integrable_sq)).symm
  -- finite-sum Cauchy–Schwarz on the cell/band pairing
  have hf2 : ∀ k : ℕ, (Real.sqrt (cell k)) ^ 2 = cell k := fun k ↦
    Real.sq_sqrt (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (unifPart_mono T n (Nat.le_succ k))))
  have hg2 : ∀ k : ℕ, (Real.sqrt (bandE k)) ^ 2 = bandE k := fun k ↦
    Real.sq_sqrt (integral_nonneg fun z ↦ sq_nonneg _)
  have hsq : (∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k))) ^ 2
      ≤ (T : ℝ) * ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    have key := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
      (f := fun k : ℕ ↦ Real.sqrt (cell k)) (g := fun k : ℕ ↦ Real.sqrt (bandE k))
    rw [Finset.sum_congr rfl fun k _ ↦ hf2 k, Finset.sum_congr rfl fun k _ ↦ hg2 k,
      hsumcell, hbandsum] at key
    exact key
  have hpair : ∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k))
      ≤ Real.sqrt (T : ℝ) * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
    have hX0 : 0 ≤ ∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k)) :=
      Finset.sum_nonneg fun k _ ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc ∑ k ∈ Finset.range n, (Real.sqrt (cell k) * Real.sqrt (bandE k))
        ≤ Real.sqrt ((∑ k ∈ Finset.range n,
          (Real.sqrt (cell k) * Real.sqrt (bandE k))) ^ 2) := by
          rw [Real.sqrt_sq hX0]
      _ ≤ Real.sqrt ((T : ℝ) * ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
          ((hD.integrand
              - deltaStepLp hBmeas hD.adapted hD.bdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (T : ℝ) * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
          ((hD.integrand
              - deltaStepLp hBmeas hD.adapted hD.bdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)) := by
          rw [Real.sqrt_mul (NNReal.coe_nonneg T)]
  -- assembly
  calc |∑ k ∈ Finset.range n,
          ∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
        - ∑ k ∈ Finset.range n,
            (∫ ω, w (unifPart T n k) ω * δ (unifPart T n k) ω ^ 2 ∂μ) * cell k|
      = |∑ k ∈ Finset.range n,
          (∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
          - ∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ)| := by
        rw [hsumbridge, ← Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ Finset.range n,
          |∫ ω, w (unifPart T n k) ω
            * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ
          - ∫ ω, w (unifPart T n k) ω * (δ (unifPart T n k) ω
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2 ∂μ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, 2 * |Cw| * |Dd| * (Real.sqrt (cell k)
          * Real.sqrt (bandE k)) :=
        Finset.sum_le_sum fun k hk ↦ by
          rw [show (2:ℝ) * |Cw| * |Dd| * (Real.sqrt (cell k) * Real.sqrt (bandE k))
              = 2 * |Cw| * |Dd| * Real.sqrt (cell k) * Real.sqrt (bandE k) from by ring]
          exact hpercell k hk
    _ = 2 * |Cw| * |Dd| * ∑ k ∈ Finset.range n,
          (Real.sqrt (cell k) * Real.sqrt (bandE k)) := by
        rw [← Finset.mul_sum]
    _ ≤ 2 * |Cw| * |Dd| * (Real.sqrt (T : ℝ) * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ
          (Set.univ : Set Ω),
        ((hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas))) :=
        mul_le_mul_of_nonneg_left hpair
          (mul_nonneg (mul_nonneg zero_le_two (abs_nonneg Cw)) (abs_nonneg Dd))
    _ = 2 * |Cw| * |Dd| * Real.sqrt (T : ℝ)
          * Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas)) := by ring

end StageFiveA

/-- **The convergence of the quadratic block, gap hypothesis discharged** (the `hgap`
hypothesis of `quadraticSqSum_tendsto` discharged by `gapSum_le` + `deltaStepLp_tendsto`). Not
unconditional: `M` is still a hypothesized version of `δ●B` (`hD.adaptedM`, `hD.ae_eq`). -/
theorem quadraticSqSum_tendsto' (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t))
    {T : ℝ≥0} {δ : ℝ≥0 → Ω → ℝ} {Dd : ℝ}
    {M : ℝ≥0 → Ω → ℝ} (hD : IsAdaptedItoDrift hB hBmeas T δ Dd M)
    {w : ℝ≥0 → Ω → ℝ} {Cw : ℝ}
    (hwadap : ∀ t, Measurable[natFiltration hBmeas t] (w t))
    (hwcont : ∀ᵐ ω ∂μ, Continuous fun s : ℝ≥0 ↦ w s ω)
    (hwbdd : ∀ s ω, |w s ω| ≤ Cw) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        ∫ ω, w (unifPart T n k) ω
          * (M (unifPart T n (k + 1)) ω - M (unifPart T n k) ω) ^ 2 ∂μ)
      atTop (𝓝 (∫ s in Set.Ioc 0 T,
          (∫ ω, w s ω * (δ s ω * δ s ω) ∂μ) ∂ItoIntegralL2.timeMeasure)) := by
  refine quadraticSqSum_tendsto hB hBmeas hD hwadap hwcont hwbdd
    ⟨fun n ↦ Real.sqrt (∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
      ((hD.integrand
          - deltaStepLp hBmeas hD.adapted hD.bdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
      ∂(trimMeasure_T (μ := μ) T hBmeas)), ?_, ?_⟩
  · -- `r n` is squeezed by `‖φ − δⁿ‖ → 0` (the band integral is at most the full norm²)
    have htend := deltaStepLp_tendsto (T := T) hB hBmeas hD.adapted hD.continuous hD.bdd
    have hnorm := (tendsto_iff_norm_sub_tendsto_zero.mp htend).congr'
      (Eventually.of_forall fun n ↦ by rw [norm_sub_rev])
    refine squeeze_zero' (Eventually.of_forall fun n ↦ Real.sqrt_nonneg _) ?_ hnorm
    filter_upwards [] with n
    refine le_trans (Real.sqrt_le_sqrt ?_)
      (le_of_eq (show Real.sqrt (‖(hD.integrand
          - deltaStepLp hBmeas hD.adapted hD.bdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ ^ 2)
        = ‖(hD.integrand
          - deltaStepLp hBmeas hD.adapted hD.bdd n :
            Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ from
        Real.sqrt_sq (norm_nonneg _)))
    have hsqint : Integrable (fun z ↦
        ((hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
        (trimMeasure_T (μ := μ) T hBmeas) :=
      (Lp.memLp (hD.integrand
        - deltaStepLp hBmeas hD.adapted hD.bdd n)).integrable_sq
    have hintband : IntegrableOn (fun z ↦
        ((hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
        (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)) (trimMeasure_T (μ := μ) T hBmeas) :=
      hsqint.mono_measure Measure.restrict_le_self
    have hbandmsP : MeasurableSet[(natFiltration hBmeas).predictable]
        (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)) :=
      measurableSet_predictable_Ioc_prod (0:ℝ≥0) T MeasurableSet.univ
    have hbandms : MeasurableSet (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)) :=
      MeasurableSet.prod (measurableSet_Ioc (α := ℝ≥0)) MeasurableSet.univ
    have hintInd : Integrable ((Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)).indicator
        (fun z ↦ ((hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2))
        (trimMeasure_T (μ := μ) T hBmeas) :=
      (integrable_indicator_iff (μ := trimMeasure_T (μ := μ) T hBmeas)
        (f := fun z : ℝ≥0 × Ω ↦
          ((hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
        hbandmsP).mpr hintband
    calc ∫ z in Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω),
        ((hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
        ∂(trimMeasure_T (μ := μ) T hBmeas)
        = ∫ z, (Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)).indicator
            (fun z ↦ ((hD.integrand
              - deltaStepLp hBmeas hD.adapted hD.bdd n :
                Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2) z
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
          (integral_indicator (μ := trimMeasure_T (μ := μ) T hBmeas)
            (f := fun z : ℝ≥0 × Ω ↦
              ((hD.integrand
                - deltaStepLp hBmeas hD.adapted hD.bdd n :
                  Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2)
            hbandmsP).symm
      _ ≤ ∫ z, ((hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) : ℝ≥0 × Ω → ℝ) z ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) :=
          integral_mono hintInd hsqint (fun z ↦ by
            by_cases hz : z ∈ Set.Ioc (0:ℝ≥0) T ×ˢ (Set.univ : Set Ω)
            · rw [Set.indicator_of_mem hz]
            · rw [Set.indicator_of_notMem hz]
              exact sq_nonneg _)
      _ = ‖(hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n :
              Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))‖ ^ 2 :=
          (lp_two_norm_sq (hD.integrand
            - deltaStepLp hBmeas hD.adapted hD.bdd n)).symm
  · exact fun n hn ↦ gapSum_le hB hBmeas hD n hn hwadap hwbdd

end MathFin.ItoDriftConditional
