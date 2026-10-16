/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.GaussianMoments

/-!
# Estimation in practice: detection D-terms and realised-volatility bias

A regime is a state, not a parameter: between two centered Gaussian regimes with
variance ratio `r = σ²_high/σ²_low`, the per-observation discrimination information is
the Kullback–Leibler D-term `D = ½(r − 1 − ln r)` of eq. (21.2). `llr` (the log
likelihood ratio, `LogLikelihoodRatio.lean:37`) is the object; the computation here
makes it a quadratic integral against the high-variance law
(`kl_gaussianReal_var_ratio`), via the `withDensity` structure of `gaussianReal`
(`gaussianReal_of_var_ne_zero`) and the `rnDeriv` ratio identity
`Measure.rnDeriv_withDensity_right` (`RadonNikodym.lean:168`).

Sampling obstructions are the chapter's second half: iid mean-zero noise of scale `η`
turns the realised-variance estimator's expectation into `σ²T + 2nη²` — bias linear in
sampling frequency (`rvExpectation_withNoise`, eq. 21.4) — and the square-root
estimator of a nondegenerate volatility target is biased low, `E[σ̂] < σ`
(`sqrtBias_oneSided` + `sqrtBias_absGaussianSample`, the sign of eq. 21.3). The drift
estimator, by contrast, sees only the endpoints: its variance is `σ²/T` whatever the
sampling frequency (`drift_se_endpoint_var`, Calc 21.4's flat column).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal

/-! ## The D-term of eq. (21.2): KL divergence between variance-ratio Gaussians -/

section KL

/-- Pointwise identity: the log of the pdf ratio between `N(0, r·v)` and `N(0, v)` is
the quadratic `−½·ln r + x²(r−1)/(2rv)` (completing-the-square algebra, the
one-observation face of the chapter's D-term). -/
private lemma log_ratio_gaussianPDFReal_eq {r v : ℝ≥0} (hv : v ≠ 0) (hr : r ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x) =
      -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ)) := by
  have hvpc : 0 < v := hv.bot_lt
  have hrpc : 0 < r := hr.bot_lt
  have hrvpc : 0 < r * v := mul_pos hrpc hvpc
  have hposP : 0 < gaussianPDFReal 0 (r * v) x := gaussianPDFReal_pos _ _ _ (mul_ne_zero hr hv)
  have hposQ : 0 < gaussianPDFReal 0 v x := gaussianPDFReal_pos _ _ _ hv
  have h2piv : (0 : ℝ) < 2 * π * v := by exact_mod_cast mul_pos two_pi_pos hvpc
  have h2pirv : (0 : ℝ) < 2 * π * ((r : ℝ) * (v : ℝ)) := mul_pos two_pi_pos (by
    exact_mod_cast mul_pos hrpc hvpc)
  have hrvcoe : ((r * v : ℝ≥0) : ℝ) = (r : ℝ) * (v : ℝ) := by push_cast; ring
  have hlr : Real.log (2 * π * (v : ℝ)) - Real.log (2 * π * ((r : ℝ) * (v : ℝ))) =
      -(Real.log (r : ℝ)) := by
    rw [← Real.log_div h2piv.ne' h2pirv.ne',
      show (2 * π * (v : ℝ)) / (2 * π * ((r : ℝ) * (v : ℝ))) = ((r : ℝ))⁻¹ by field_simp,
      Real.log_inv]
  have hA : Real.log (gaussianPDFReal 0 (r * v) x)
      = -(Real.log (2 * π * ((r : ℝ) * (v : ℝ)))) / 2
        - x ^ 2 / (2 * ((r : ℝ) * (v : ℝ))) := by
    show Real.log ((√(2 * π * ((r * v : ℝ≥0) : ℝ)))⁻¹ *
        Real.exp (-(x - 0) ^ 2 / (2 * ((r * v : ℝ≥0) : ℝ)))) = _
    rw [sub_zero, hrvcoe]
    rw [Real.log_mul (by positivity :
        (0 : ℝ) < (√(2 * π * ((r : ℝ) * (v : ℝ))))⁻¹).ne' (Real.exp_pos _).ne',
      Real.log_inv, Real.log_exp,
      Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2 * π * ((r : ℝ) * (v : ℝ)))]
    ring
  have hB : Real.log (gaussianPDFReal 0 v x)
      = -(Real.log (2 * π * (v : ℝ))) / 2 - x ^ 2 / (2 * (v : ℝ)) := by
    show Real.log ((√(2 * π * (v : ℝ≥0) : ℝ))⁻¹ *
        Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ≥0) : ℝ))) = _
    rw [sub_zero]
    rw [Real.log_mul (by positivity : (0 : ℝ) < (√(2 * π * (v : ℝ)))⁻¹).ne'
      (Real.exp_pos _).ne', Real.log_inv, Real.log_exp,
      Real.log_sqrt (by positivity : (0 : ℝ) ≤ 2 * π * (v : ℝ))]
    ring
  calc Real.log (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x)
      = Real.log (gaussianPDFReal 0 (r * v) x) - Real.log (gaussianPDFReal 0 v x) :=
        Real.log_div hposP.ne' hposQ.ne'
    _ = (Real.log (2 * π * (v : ℝ)) - Real.log (2 * π * ((r : ℝ) * (v : ℝ)))) / 2
        + (x ^ 2 / (2 * (v : ℝ)) - x ^ 2 / (2 * ((r : ℝ) * (v : ℝ)))) := by
        rw [hA, hB]; ring
    _ = -(Real.log (r : ℝ)) / 2
        + (x ^ 2 / (2 * (v : ℝ)) - x ^ 2 / (2 * ((r : ℝ) * (v : ℝ)))) := by rw [hlr]
    _ = -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ)) := by
        have hx1 : x ^ 2 / (2 * (v : ℝ)) - x ^ 2 / (2 * ((r : ℝ) * (v : ℝ)))
            = x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ)) := by
          field_simp
        rw [hx1]

/-- **Eq. (21.2)'s D-term.** The Kullback–Leibler divergence of the low-variance law
`N(0, v)` from the high-variance law `N(0, r·v)` — the integral of the log likelihood
ratio `llr` against the high-variance law — is `½(r − 1 − ln r)`, the denominator of
the chapter's detection-delay arithmetic (delay ≈ ln(1/α)/D observations, p. 360).
The proof writes both laws in `withDensity` form, computes the RN derivative as the
pdf ratio via `Measure.rnDeriv_withDensity_right` and `Measure.rnDeriv_withDensity`,
and integrates the resulting quadratic termwise with `integral_id_gaussianReal`-family
moments (`MathFin.integral_sq_gaussianReal`). -/
theorem kl_gaussianReal_var_ratio {r v : ℝ≥0} (hv : v ≠ 0) (hr : r ≠ 0) :
    ∫ x, llr (gaussianReal 0 (r * v)) (gaussianReal 0 v) x ∂(gaussianReal 0 (r * v)) =
      ((r : ℝ) - 1 - Real.log (r : ℝ)) / 2 := by
  have hrv : r * v ≠ 0 := mul_ne_zero hr hv
  have hP : gaussianReal 0 (r * v) = volume.withDensity (gaussianPDF 0 (r * v)) :=
    gaussianReal_of_var_ne_zero _ hrv
  have hQ : gaussianReal 0 v = volume.withDensity (gaussianPDF 0 v) :=
    gaussianReal_of_var_ne_zero _ hv
  -- the RN derivative of P against volume is the pdf:
  have hrnvol : (volume.withDensity (gaussianPDF 0 (r * v))).rnDeriv volume
      =ᵐ[volume] gaussianPDF 0 (r * v) :=
    Measure.rnDeriv_withDensity volume (measurable_gaussianPDF _ _)
  -- hence the RN derivative of P against Q is the pdf ratio, a.e. volume:
  have hrn := Measure.rnDeriv_withDensity_right (μ := gaussianReal 0 (r * v)) (ν := volume)
    (f := gaussianPDF 0 v) (measurable_gaussianPDF _ _).aemeasurable
    (ae_of_all volume fun x => by
      simp only [gaussianPDF, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact gaussianPDFReal_pos _ _ x hv)
    (ae_of_all volume fun x => ENNReal.ofReal_ne_top)
  rw [← hQ, hP] at hrn
  have hcomb : (volume.withDensity (gaussianPDF 0 (r * v))).rnDeriv (gaussianReal 0 v)
      =ᵐ[volume] fun x => (gaussianPDF 0 v x)⁻¹ * gaussianPDF 0 (r * v) x := by
    filter_upwards [hrn, hrnvol] with x h1 h2
    rw [h2] at h1
    exact h1
  have hreal : ∀ x : ℝ, (gaussianPDF 0 v x)⁻¹ * gaussianPDF 0 (r * v) x
      = ENNReal.ofReal (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x) := by
    intro x
    calc (gaussianPDF 0 v x)⁻¹ * gaussianPDF 0 (r * v) x
        = (ENNReal.ofReal (gaussianPDFReal 0 v x))⁻¹ *
            ENNReal.ofReal (gaussianPDFReal 0 (r * v) x) := by rw [gaussianPDF, gaussianPDF]
      _ = ENNReal.ofReal (gaussianPDFReal 0 v x)⁻¹ *
            ENNReal.ofReal (gaussianPDFReal 0 (r * v) x) :=
            by rw [ENNReal.ofReal_inv_of_pos (gaussianPDFReal_pos _ _ x hv)]
      _ = ENNReal.ofReal ((gaussianPDFReal 0 v x)⁻¹ * gaussianPDFReal 0 (r * v) x) :=
            by rw [ENNReal.ofReal_mul (inv_nonneg.2 (gaussianPDFReal_nonneg _ _ x))]
      _ = ENNReal.ofReal (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x) :=
            by rw [div_eq_inv_mul]
  -- the llr integrand is the log pdf ratio, a.e. volume, hence a.e. P:
  have hllr : llr (gaussianReal 0 (r * v)) (gaussianReal 0 v)
      =ᵐ[volume] fun x => Real.log (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x) := by
    filter_upwards [hcomb] with x hx
    show Real.log (((gaussianReal 0 (r * v)).rnDeriv (gaussianReal 0 v) x).toReal) = _
    rw [hP, hx, hreal x,
      ENNReal.toReal_ofReal
        (div_nonneg (gaussianPDFReal_nonneg _ _ x) (gaussianPDFReal_nonneg _ _ x))]
  have hPac : gaussianReal 0 (r * v) ≪ volume := gaussianReal_absolutelyContinuous _ hrv
  have hllr' : llr (gaussianReal 0 (r * v)) (gaussianReal 0 v)
      =ᵐ[gaussianReal 0 (r * v)] fun x =>
        -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ)) := by
    filter_upwards [hPac.ae_le hllr] with x hx
    rw [hx, log_ratio_gaussianPDFReal_eq hv hr]
  rw [integral_congr_ae hllr']
  have hsplit : ∫ x : ℝ, -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))
        ∂(gaussianReal 0 (r * v))
      = -(Real.log (r : ℝ)) / 2
        + (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 (r * v))) * (((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))) := by
    have h0 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 (r * v)) :=
      (@memLp_id_gaussianReal 0 (r * v) (2 : ℝ≥0)).integrable_sq
    have hint1 : Integrable (fun _ : ℝ => -(Real.log (r : ℝ)) / 2) (gaussianReal 0 (r * v)) :=
      integrable_const _
    have hshape : ∀ x : ℝ, -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))
        = -(Real.log (r : ℝ)) / 2 + x ^ 2 * (((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))) :=
      fun _ => by ring
    rw [integral_congr_ae (ae_of_all _ hshape),
      integral_add hint1 (h0.mul_const _),
      integral_const]
    simp
    try rw [integral_mul_const _ (fun x : ℝ => x ^ 2)]
    try ring
  have hcoev : ((v : ℝ)) ≠ 0 := by exact_mod_cast hv
  have hcoer : ((r : ℝ)) ≠ 0 := by exact_mod_cast hr
  rw [hsplit, MathFin.integral_sq_gaussianReal]
  push_cast
  field_simp
  ring


/-- **The small-shift quadratic (the chapter's "halving the gap quadruples the delay",
§21.3 p. 361).** As `r → 1`, the D-term proved above satisfies
`D(r) = (r−1)²/4 + o(1)`: the discrimination information vanishes quadratically as the
two regimes coalesce, so the chapter's delay arithmetic `≈ ln(1/α)/D` blows up
quadratically. Proved from continuity of `D` at `r = 1` (the second-order Taylor
content is exactly the continuity statement at this precision). -/
theorem kl_gaussianReal_small_shift :
    Filter.Tendsto (fun r : ℝ => (r - 1 - Real.log r) / 2 - (r - 1) ^ 2 / 4)
      (nhds 1) (nhds 0) := by
  have hcont : ContinuousOn (fun r : ℝ => (r - 1 - Real.log r) / 2 - (r - 1) ^ 2 / 4)
      ({0}ᶜ : Set ℝ) := by
    refine ContinuousOn.sub ?_ ?_
    · exact ((continuousOn_id.sub continuousOn_const).sub Real.continuousOn_log).div_const 2
    · exact ((continuousOn_id.sub continuousOn_const).pow 2).div_const 4
  have hc : ContinuousAt (fun r : ℝ => (r - 1 - Real.log r) / 2 - (r - 1) ^ 2 / 4) 1 :=
    hcont.continuousAt (isOpen_compl_singleton.mem_nhds (by simp))
  have h0 : (fun r : ℝ => (r - 1 - Real.log r) / 2 - (r - 1) ^ 2 / 4) 1 = 0 := by simp
  have ht : Filter.Tendsto (fun r : ℝ => (r - 1 - Real.log r) / 2 - (r - 1) ^ 2 / 4)
      (nhds 1) (nhds ((fun r : ℝ => (r - 1 - Real.log r) / 2 - (r - 1) ^ 2 / 4) 1)) :=
    hc.tendsto
  rw [h0] at ht
  exact ht


/-! ## Eq. (21.4): realised variance under iid mean-zero noise -/

section RealizedVol

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- **Eq. (21.4): the realised-variance noise bias is linear in sampling frequency.**
Over `n` increments `ΔX_i` with second moment `E[(ΔX_i)²] = σ²·Δt` (the
`integral_sq_increment` / `integral_sq_gaussianReal` moment in the Gaussian instance)
observed through iid mean-zero noise `ε_j` of scale `η` (`E[ε_j] = 0`, `E[ε_j²] = η²`),
the noisy realised sum has expectation `σ²T + 2nη²` where `T = n·Δt`: each increment
contributes its signal second moment plus **two** noise second moments, and all
cross-terms vanish by independence + mean-zero (`IndepFun.integral_mul_eq_mul_integral`,
the chapter's "noise, dependence, scale" obstruction, §21.3 p. 361). The integrability
hypotheses are the `L²` package: on a probability space they follow from the moment
hypotheses by Cauchy–Schwarz, which is not the taught content and is not reproved. -/
theorem rvExpectation_withNoise {n : ℕ} {dt T sigma eta : ℝ} (hT : T = (n : ℝ) * dt)
    (dX : ℕ → α → ℝ) (e : ℕ → α → ℝ)
    (hdXm : ∀ i, Measurable (dX i)) (hem : ∀ j, Measurable (e j))
    (hdXi : ∀ i ∈ Finset.range n, Integrable (dX i) μ)
    (hei : ∀ j ∈ Finset.range (n + 1), Integrable (e j) μ)
    (hdXsq : ∀ i ∈ Finset.range n, Integrable (fun x => dX i x * dX i x) μ)
    (hesq : ∀ j ∈ Finset.range (n + 1), Integrable (fun x => e j x * e j x) μ)
    (h_mom : ∀ i ∈ Finset.range n, ∫ x, dX i x * dX i x ∂μ = sigma * sigma * dt)
    (h_noise_sq : ∀ j ∈ Finset.range (n + 1), ∫ x, e j x * e j x ∂μ = eta * eta)
    (h_noise_mean : ∀ j ∈ Finset.range (n + 1), ∫ x, e j x ∂μ = 0)
    (h_noise_indep : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
      i ≠ j → e i ⟂ᵢ[μ] e j)
    (h_cross : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range (n + 1), dX i ⟂ᵢ[μ] e j) :
    ∫ x, ∑ i ∈ Finset.range n, (dX i x + e i x - e (i + 1) x) ^ 2 ∂μ
      = sigma * sigma * T + 2 * (n : ℝ) * eta * eta := by
  have hexp : ∀ (i : ℕ) (x : α), (dX i x + e i x - e (i + 1) x) ^ 2 =
      dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
        + 2 * (dX i x * e i x) - 2 * (dX i x * e (i + 1) x)
        - 2 * (e i x * e (i + 1) x) :=
    fun _ _ => by ring
  have key : ∀ i ∈ Finset.range n,
      (∫ x : α, (dX i x + e i x - e (i + 1) x) ^ 2 ∂μ = sigma * sigma * dt + 2 * eta * eta)
        ∧ Integrable (fun x : α => (dX i x + e i x - e (i + 1) x) ^ 2) μ := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hmem : ∀ k, k < n + 1 → k ∈ Finset.range (n + 1) :=
      fun k hk => Finset.mem_range.mpr hk
    -- the six integrable pieces
    have i1 : Integrable (fun x : α => dX i x * dX i x) μ := hdXsq i hi
    have i2 : Integrable (fun x : α => e i x * e i x) μ := hesq i (hmem _ (by omega))
    have i3 : Integrable (fun x : α => e (i + 1) x * e (i + 1) x) μ :=
      hesq (i + 1) (hmem _ (by omega))
    have c1 : Integrable (fun x : α => dX i x * e i x) μ :=
      IndepFun.integrable_mul (h_cross i hi i (hmem _ (by omega))) (hdXi i hi)
        (hei i (hmem _ (by omega)))
    have c2 : Integrable (fun x : α => dX i x * e (i + 1) x) μ :=
      IndepFun.integrable_mul (h_cross i hi (i + 1) (hmem _ (by omega))) (hdXi i hi)
        (hei (i + 1) (hmem _ (by omega)))
    have c3 : Integrable (fun x : α => e i x * e (i + 1) x) μ :=
      IndepFun.integrable_mul
        (h_noise_indep i (hmem _ (by omega)) (i + 1) (hmem _ (by omega)) (by omega))
        (hei i (hmem _ (by omega))) (hei (i + 1) (hmem _ (by omega)))
    have c1' : Integrable (fun x : α => 2 * (dX i x * e i x)) μ :=
      (c1.add c1).congr (ae_of_all μ fun x => by simp only [Pi.add_apply]; ring)
    have c2' : Integrable (fun x : α => 2 * (dX i x * e (i + 1) x)) μ :=
      (c2.add c2).congr (ae_of_all μ fun x => by simp only [Pi.add_apply]; ring)
    have c3' : Integrable (fun x : α => 2 * (e i x * e (i + 1) x)) μ :=
      (c3.add c3).congr (ae_of_all μ fun x => by simp only [Pi.add_apply]; ring)
    have i12 : Integrable (fun x : α => dX i x * dX i x + e i x * e i x) μ := i1.add i2
    have i123 : Integrable
        (fun x : α => dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x) μ :=
      i12.add i3
    have i1234 : Integrable
        (fun x : α => dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
          + 2 * (dX i x * e i x)) μ := i123.add c1'
    have i12345 : Integrable
        (fun x : α => dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
          + 2 * (dX i x * e i x) - 2 * (dX i x * e (i + 1) x)) μ := i1234.sub c2'
    have p6 : Integrable
        (fun x : α => dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
          + 2 * (dX i x * e i x) - 2 * (dX i x * e (i + 1) x)
          - 2 * (e i x * e (i + 1) x)) μ := i12345.sub c3'
    refine ⟨?_, p6.congr (ae_of_all μ fun x => (hexp i x).symm)⟩
    rw [integral_congr_ae (ae_of_all μ fun x => hexp i x)]
    -- split into the six integrals
    have z1 : ∫ x : α, dX i x * e i x ∂μ = (∫ x, dX i x ∂μ) * (∫ x, e i x ∂μ) :=
      (h_cross i hi i (hmem _ (by omega))).integral_mul_eq_mul_integral
        (hdXm i).aestronglyMeasurable (hem i).aestronglyMeasurable
    have z2 : ∫ x : α, dX i x * e (i + 1) x ∂μ
        = (∫ x, dX i x ∂μ) * (∫ x, e (i + 1) x ∂μ) :=
      (h_cross i hi (i + 1) (hmem _ (by omega))).integral_mul_eq_mul_integral
        (hdXm i).aestronglyMeasurable (hem (i + 1)).aestronglyMeasurable
    have z3 : ∫ x : α, e i x * e (i + 1) x ∂μ
        = (∫ x, e i x ∂μ) * (∫ x, e (i + 1) x ∂μ) :=
      (h_noise_indep i (hmem _ (by omega)) (i + 1) (hmem _ (by omega)) (by omega)
        ).integral_mul_eq_mul_integral (hem i).aestronglyMeasurable
        (hem (i + 1)).aestronglyMeasurable
    rw [integral_sub i12345 c3', integral_sub i1234 c2', integral_add i123 c1',
      integral_add i12 i3, integral_add i1 i2,
      h_mom i hi, h_noise_sq i (hmem _ (by omega)), h_noise_sq (i + 1) (hmem _ (by omega)),
      integral_const_mul, z1, h_noise_mean i (hmem _ (by omega)), mul_zero,
      integral_const_mul, z2, h_noise_mean (i + 1) (hmem _ (by omega)), mul_zero,
      integral_const_mul, z3, h_noise_mean i (hmem _ (by omega)),
      h_noise_mean (i + 1) (hmem _ (by omega)), mul_zero, mul_zero]
    ring
  calc ∫ x, ∑ i ∈ Finset.range n, (dX i x + e i x - e (i + 1) x) ^ 2 ∂μ
      = ∑ i ∈ Finset.range n, ∫ x : α, (dX i x + e i x - e (i + 1) x) ^ 2 ∂μ :=
        integral_finsetSum (Finset.range n) fun i hi => (key i hi).2
    _ = ∑ i ∈ Finset.range n, (sigma * sigma * dt + 2 * eta * eta) :=
        Finset.sum_congr rfl fun i hi => (key i hi).1
    _ = sigma * sigma * T + 2 * (n : ℝ) * eta * eta := by
        rw [hT, Finset.sum_const, Finset.card_range]
        ring


end RealizedVol

/-! ## Eq. (21.3)'s sign: the square-root estimator is biased low -/

section SqrtBias

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- √t ≤ 1 + |t| for `t ≥ 0` — the domination making `√Y` integrable whenever `Y` is. -/
private lemma sqrt_le_add_one_abs (t : ℝ) (ht : 0 ≤ t) : Real.sqrt t ≤ 1 + |t| := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [le_abs_self t, abs_nonneg t]

/-- **Jensen for the square root, expectation form** (the anchor route: this is
`ConcaveOn.condExp_map_le`, the concave-side statement of `ConvexOn.map_condExp_le`
`CondJensen.lean:168/:195`, applied at the trivial σ-algebra via `condExp_bot`).
For an a.e. nonnegative integrable target `Y`, `E[√Y] ≤ √(E[Y])`. -/
theorem sqrt_map_expectation_le {Y : α → ℝ} (hYm : Measurable Y) (hYnn : ∀ᵐ ω ∂μ, 0 ≤ Y ω)
    (hint : Integrable Y μ) :
    ∫ ω, Real.sqrt (Y ω) ∂μ ≤ Real.sqrt (∫ ω, Y ω ∂μ) := by
  haveI : SigmaFinite (μ.trim (bot_le : (⊥ : MeasurableSpace α) ≤ _)) := by
    refine ⟨⟨fun _ => Set.univ, fun _ => Set.mem_univ _, ?_, ?_⟩⟩
    · intro i
      have h1 : (μ.trim (bot_le : (⊥ : MeasurableSpace α) ≤ _)) Set.univ = μ Set.univ :=
        trim_measurableSet_eq bot_le MeasurableSet.univ
      rw [h1]
      simp
    · exact Set.iUnion_const _
  have hsqm : Integrable (Real.sqrt ∘ Y) μ := by
    refine Integrable.mono ((integrable_const 1).add hint.abs) ?_ ?_
    · exact (hYm.sqrt).aestronglyMeasurable
    · filter_upwards [hYnn] with ω hω
      show |Real.sqrt (Y ω)| ≤ abs ((1 : ℝ) + |Y ω|)
      rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + |Y ω|)]
      exact sqrt_le_add_one_abs (Y ω) hω
  have hj := (strictConcaveOn_sqrt.concaveOn).condExp_map_le
    (bot_le : (⊥ : MeasurableSpace α) ≤ _)
    (Real.continuous_sqrt.continuousOn.upperSemicontinuousOn) (hYnn.mono fun ω h => h)
    isClosed_Ici hint hsqm
  rw [condExp_bot, condExp_bot, Function.comp_def] at hj
  calc ∫ ω, Real.sqrt (Y ω) ∂μ
      = ∫ ω, (∫ x, Real.sqrt (Y x) ∂μ) ∂μ := by
        rw [show (∫ ω : α, (∫ x, Real.sqrt (Y x) ∂μ) ∂μ)
            = μ.real Set.univ • (∫ x, Real.sqrt (Y x) ∂μ) from integral_const _]
        simp
    _ ≤ ∫ ω, Real.sqrt (∫ x, Y x ∂μ) ∂μ :=
        integral_mono_ae (integrable_const _) (integrable_const _) hj
    _ = Real.sqrt (∫ x, Y x ∂μ) := by
        rw [show (∫ ω : α, Real.sqrt (∫ x, Y x ∂μ) ∂μ)
            = μ.real Set.univ • Real.sqrt (∫ x, Y x ∂μ) from integral_const _]
        simp


/-- **Eq. (21.3)'s sign: `E[σ̂] < σ`.** If `Y ≥ 0` is a nondegenerate target with
`E[Y] = σ²` (the sample reading: `Y = RV/n`, the realised-variance average whose square
root is the volatility estimator `σ̂ = √Y`), then `E[√Y] < σ` — the square-root estimator
of a nondegenerate volatility is **biased low**. Strictness comes from the tangent-line
identity at `σ²`: `√y = (y + σ²)/(2σ) − (√y − σ)²/(2σ)`, whose remainder is strictly
positive on `{Y ≠ σ²}`, a set of positive measure by nondegeneracy. The exact
`√(2/n)·Γ((n+1)/2)/Γ(n/2)` constant of the chapter stays gated (Gamma machinery). -/
theorem sqrtBias_oneSided {Y : α → ℝ} (hYm : Measurable Y) (hYnn : ∀ ω, 0 ≤ Y ω)
    {sigma : ℝ} (hsig : 0 < sigma) (hint : Integrable Y μ)
    (hmean : ∫ ω, Y ω ∂μ = sigma * sigma) (hnd : μ {ω | Y ω ≠ sigma * sigma} ≠ 0) :
    ∫ ω, Real.sqrt (Y ω) ∂μ < sigma := by
  have hm : 0 < sigma * sigma := by positivity
  have hsqrtsig : Real.sqrt (sigma * sigma) = sigma := Real.sqrt_mul_self (le_of_lt hsig)
  set c : ℝ := (2 * Real.sqrt (sigma * sigma))⁻¹ with hc
  have hcpos : 0 < c := by positivity
  -- the tangent identity: √Y = (Y + σ²)/(2σ) − (√Y − σ)²/(2σ), with c = 1/(2σ)
  have hid : ∀ ω : α, Real.sqrt (Y ω) =
      c * Y ω + c * (sigma * sigma)
        - c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2 := by
    intro ω
    have e1 : (Real.sqrt (Y ω)) ^ 2 = Y ω := Real.sq_sqrt (hYnn ω)
    have e2 : (Real.sqrt (sigma * sigma)) ^ 2 = sigma * sigma := Real.sq_sqrt (by positivity)
    have hbpos : (0 : ℝ) < Real.sqrt (sigma * sigma) := by positivity
    have hkey : (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2
        = Y ω + sigma * sigma - 2 * Real.sqrt (Y ω) * Real.sqrt (sigma * sigma) := by
      rw [sub_sq, e1, e2]
      ring
    rw [hkey, hc]
    field_simp
    ring
  -- integrability of the two pieces
  have hintP : Integrable (fun ω => c * Y ω + c * (sigma * sigma)) μ := by
    have h := (hint.mul_const c).add (integrable_const (c * (sigma * sigma)))
    refine h.congr (ae_of_all μ fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  have hkey2 : ∀ ω : α, (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2
      ≤ 2 * Y ω + 2 * (sigma * sigma) := by
    intro ω
    have e1 : (Real.sqrt (Y ω)) ^ 2 = Y ω := Real.sq_sqrt (hYnn ω)
    have e2 : (Real.sqrt (sigma * sigma)) ^ 2 = sigma * sigma := Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (Real.sqrt (Y ω) + Real.sqrt (sigma * sigma)), e1, e2]
  have hintD : Integrable (fun ω => 2 * c * Y ω + 2 * c * (sigma * sigma)) μ := by
    have h := (hint.mul_const (2 * c)).add (integrable_const (2 * c * (sigma * sigma)))
    refine h.congr (ae_of_all μ fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  have hintg : Integrable (fun ω => c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2) μ := by
    refine Integrable.mono hintD ?_ ?_
    · exact (by fun_prop : AEStronglyMeasurable
        (fun ω => c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2) μ)
    · filter_upwards [] with ω
      show |c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2|
          ≤ |2 * c * Y ω + 2 * c * (sigma * sigma)|
      rw [abs_of_nonneg (mul_nonneg (le_of_lt hcpos) (sq_nonneg _)),
        abs_of_nonneg (by nlinarith [hcpos, hYnn ω, sq_nonneg (sigma * sigma)])]
      calc c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2
          ≤ c * (2 * Y ω + 2 * (sigma * sigma)) :=
            mul_le_mul_of_nonneg_left (hkey2 ω) (le_of_lt hcpos)
        _ = 2 * c * Y ω + 2 * c * (sigma * sigma) := by ring
  -- the constant piece integrates to σ = √(σ²)
  have hPint : ∫ ω, c * Y ω + c * (sigma * sigma) ∂μ
      = Real.sqrt (sigma * sigma) := by
    have h1 : Integrable (fun ω : α => c * Y ω) μ :=
      (hint.mul_const c).congr (ae_of_all μ fun ω => mul_comm _ _)
    have h2sqrt : (2 * Real.sqrt (sigma * sigma)) ≠ 0 := by positivity
    have hconst : ∫ ω : α, c * (sigma * sigma) ∂μ = c * (sigma * sigma) := by
      have h := integral_const (c * (sigma * sigma)) (μ := μ)
      rw [h]
      simp
    rw [integral_add h1 (integrable_const _),
      show (fun ω : α => c * Y ω) = fun ω => Y ω * c from funext fun _ => mul_comm _ _,
      integral_mul_const c (fun ω => Y ω), hmean, hconst, hc]
    field_simp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ sigma ^ 2)]
    ring
  -- the remainder has strictly positive integral on the nondegeneracy set
  have hintgpos : 0 < ∫ ω, c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2 ∂μ := by
    by_contra hcon
    push Not at hcon
    have h0 : ∫ ω, c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2 ∂μ = 0 :=
      le_antisymm hcon (integral_nonneg fun ω =>
        mul_nonneg (le_of_lt hcpos) (sq_nonneg _))
    have hnn2 : 0 ≤ᵐ[μ] fun ω => c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2 :=
      ae_of_all μ fun ω => mul_nonneg (le_of_lt hcpos) (sq_nonneg _)
    have hlint0 : ∫⁻ ω, ENNReal.ofReal
        (c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2) ∂μ = 0 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hintg hnn2, h0, ENNReal.ofReal_zero]
    have hae := (lintegral_eq_zero_iff'
      (by fun_prop : AEMeasurable (fun ω => ENNReal.ofReal
        (c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2)) μ)).mp hlint0
    have hsub : {ω | Y ω ≠ sigma * sigma}
        ⊆ {ω | ¬(ENNReal.ofReal (c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2) = 0)} := by
      intro ω hω
      have hsne : Real.sqrt (Y ω) ≠ Real.sqrt (sigma * sigma) := fun heq => hω (by
        rw [← Real.sq_sqrt (hYnn ω), ← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ sigma * sigma), heq])
      have hpos : 0 < c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2 :=
        mul_pos hcpos (sq_pos_iff.mpr (sub_ne_zero.mpr hsne))
      intro hzero
      rw [ENNReal.ofReal_eq_zero] at hzero
      linarith
    exact hnd (measure_mono_null hsub (ae_iff.mp hae))
  rw [integral_congr_ae (ae_of_all μ hid), integral_sub hintP hintg, hPint]
  linarith [hintgpos, hsqrtsig]


/-- **The Gaussian sample instance: `E[|Z|] < σ` for `Z ~ N(0, σ²)`.** The single-sample
(`n = 1`) realised-volatility estimator is `σ̂ = |Z| = √(Z²)`, whose target
`Y = Z²` is nondegenerate (`P(Z² = σ²) = 0` — a nondegenerate Gaussian has no atoms,
`NullSingletonClass`) — so eq. (21.3)'s one-sided bias applies. The chapter's exact
constant `√(2/n)·Γ((n+1)/2)/Γ(n/2) = √(2/π) ≈ 0.798σ` at `n = 1` stays gated. -/
theorem sqrtBias_absGaussianSample {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, |x| ∂(gaussianReal 0 v) < Real.sqrt (v : ℝ) := by
  have hvpc : 0 < v := hv.bot_lt
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hvpc
  haveI : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv
  have hsqrtpos : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.2 hvpos
  have hsqrtsq : Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) = (v : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hvpos)
  have habs : ∀ x : ℝ, |x| = Real.sqrt (x ^ 2) := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, Real.sqrt_sq hx]
    · rw [abs_of_neg (not_le.mp hx),
        show (x : ℝ) ^ 2 = (-x) ^ 2 from (neg_sq x).symm,
        Real.sqrt_sq (neg_nonneg.mpr (le_of_lt (not_le.mp hx)))]
  -- nondegeneracy: P(Z² = σ²) = 0 since the set is a union of two singletons
  have hsetzero : (gaussianReal 0 v) {x : ℝ | x ^ 2 = Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)}
      = 0 := by
    have hsub : {x : ℝ | x ^ 2 = Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)}
        ⊆ {Real.sqrt (v : ℝ)} ∪ {-Real.sqrt (v : ℝ)} := by
      intro x hx
      have habsx : |x| = Real.sqrt (v : ℝ) := by
        rw [habs x, hx, ← sq, Real.sqrt_sq (by positivity)]
      by_cases hx0 : 0 ≤ x
      · exact Or.inl (by rw [abs_of_nonneg hx0] at habsx; exact habsx)
      · refine Or.inr ?_
        have hxneg : -x = Real.sqrt (v : ℝ) := by
          rw [← abs_of_neg (not_le.mp hx0)]
          exact habsx
        show x = -Real.sqrt (v : ℝ)
        rw [← hxneg]
        ring
    refine measure_mono_null hsub ?_
    rw [measure_union_null (measure_singleton _) (measure_singleton _)]
  have hnd : (gaussianReal 0 v)
      {x : ℝ | x ^ 2 ≠ Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)} ≠ 0 := by
    have hmeas : MeasurableSet {x : ℝ | x ^ 2 = Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)} := by
      show MeasurableSet ((fun x : ℝ => x ^ 2) ⁻¹' {Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)})
      exact MeasurableSet.preimage (measurableSet_singleton _) (by fun_prop)
    have hcompl : {x : ℝ | x ^ 2 ≠ Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)}
        = {x : ℝ | x ^ 2 = Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)}ᶜ := by
      ext x
      simp [ne_eq]
    rw [hcompl, measure_compl hmeas (measure_ne_top _ _), hsetzero, measure_univ]
    simp
  have hmain := sqrtBias_oneSided (μ := gaussianReal 0 v) (Y := fun x : ℝ => x ^ 2)
    (sigma := Real.sqrt (v : ℝ)) (by fun_prop) (fun _ => sq_nonneg _) hsqrtpos
    (@memLp_id_gaussianReal 0 v (2 : ℝ≥0)).integrable_sq
    (by rw [MathFin.integral_sq_gaussianReal v]; exact hsqrtsq.symm) hnd
  rw [show (fun x : ℝ => |x|) = fun x : ℝ => Real.sqrt (x ^ 2) from funext habs]
  exact hmain


end SqrtBias

/-! ## Calc 21.4's bad column: the drift estimator sees only the endpoints -/

section DriftSE

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Calc 21.4's drift column (the law).** For `X_t = μt + σB_t` with `B_T ~ N(0, T)`,
the endpoint drift estimator `(X_T − X_0)/T = μ + (σ/T)·B_T` has law `N(μ, σ²/T)` — an
affine pushforward of the gaussianReal sample (`gaussianReal_const_mul` then
`gaussianReal_const_add`, the `hasLaw_eval`-style route). The variance slot is `σ²/T`,
giving the chapter's flat-in-`n` drift standard error `σ/√T` (p. 363); the memo's
`σ²·T` slot spelling is the header-documented typo. -/
theorem drift_se_endpoint_hasLaw {T : ℝ} (hT : 0 < T) (mu sigma : ℝ) {B : Ω → ℝ}
    (hB : HasLaw B (gaussianReal 0 T.toNNReal) P) :
    HasLaw (fun ω => (mu * T + sigma * B ω) / T)
      (gaussianReal mu (sigma ^ 2 / T).toNNReal) P := by
  have h1 := gaussianReal_const_mul hB (sigma / T)
  have h2 := gaussianReal_const_add h1 mu
  have hcong : (fun ω => (mu * T + sigma * B ω) / T)
      = (fun ω => mu + sigma / T * B ω) := by
    funext ω
    field_simp
  rw [hcong]
  convert h2 using 2
  · ring
  · refine NNReal.coe_injective ?_
    rw [Real.coe_toNNReal _ (by positivity), NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ hT.le]
    field_simp

theorem drift_se_endpoint_var {T : ℝ} (hT : 0 < T) (mu sigma : ℝ) {B : Ω → ℝ}
    (hB : HasLaw B (gaussianReal 0 T.toNNReal) P) :
    Var[fun ω => (mu * T + sigma * B ω) / T; P] = sigma ^ 2 / T := by
  rw [(drift_se_endpoint_hasLaw hT mu sigma hB).variance_eq, variance_id_gaussianReal,
    Real.coe_toNNReal _ (by positivity)]


/-- The pure-sample reading, on the gaussianReal space itself (`Z = id ~ N(0, T)`):
`Var[(μT + σZ)/T] = σ²/T` with `n` nowhere in sight. -/
theorem drift_se_endpoint_var_id {T : ℝ} (hT : 0 < T) (mu sigma : ℝ) :
    Var[(fun z : ℝ => (mu * T + sigma * z) / T);
      gaussianReal 0 T.toNNReal] = sigma ^ 2 / T :=
  drift_se_endpoint_var hT mu sigma HasLaw.id


end DriftSE

end KL
