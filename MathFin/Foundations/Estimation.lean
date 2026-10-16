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
likelihood ratio, `MeasureTheory.llr`) is the object; the computation here
makes it a quadratic integral against the high-variance law
(`kl_gaussianReal_var_ratio`), via the `withDensity` structure of `gaussianReal`
(`gaussianReal_of_var_ne_zero`) and the `rnDeriv` ratio identity
`MeasureTheory.Measure.rnDeriv_withDensity_right`.

Sampling obstructions are the chapter's second half: iid mean-zero noise of scale `η`,
independent of the signal, turns the realised-variance estimator's expectation into
`σ²T + 2nη²` — bias linear in sampling frequency (`rvExpectation_withNoise`, eq. 21.4) —
and the square-root estimator of a nondegenerate volatility target is biased low, `E[σ̂] < σ`
(`sqrtBias_oneSided` + `sqrtBias_absGaussianSample`, the sign of eq. 21.3). The drift
estimator, by contrast, sees only the endpoints: its variance is `σ²/T` whatever the
sampling frequency (`drift_se_endpoint_var`, Calc 21.4's flat column). Spec correction:
the dispatch memo wrote this variance slot as `σ²·T`, contradicting its own `σ/√T`
conclusion; the chapter-consistent and proved form is `σ²/T`.

## Scope

Proved: the D-term itself and its small-shift expansion `D(r) = (r−1)²/4 + O(|r−1|³)`
(`kl_gaussianReal_small_shift`), the noise-bias expectation, the sign of the square-root
bias, and the endpoint drift-estimator law. Not proved here: the SPRT delay law
`ln(1/α)/D` (only its D-ingredient is formalised), the Bayesian regime-filter recursion,
totally inaccessible stopping times, the exact `√(2/n)·Γ((n+1)/2)/Γ(n/2)` bias constant,
Marchenko–Pastur and eigenvalue cleaning, the two-scale / realised-kernel estimators, the
2D Heston measure change, and measure-invariance of pathwise quadratic variation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal

namespace MathFin

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

/-- **Eq. (21.2)'s D-term.** `KL(N(0, r·v) ‖ N(0, v))` — the integral of the log
likelihood ratio `llr` against `N(0, r·v)` (the high-variance law when `r > 1`) — is
`½(r − 1 − ln r)`, the denominator of
the chapter's detection-delay arithmetic (delay ≈ ln(1/α)/D observations, p. 360).
The proof writes both laws in `withDensity` form, computes the RN derivative as the
pdf ratio via `Measure.rnDeriv_withDensity_right` and `Measure.rnDeriv_withDensity`,
and integrates the resulting quadratic termwise with the second moment
`MathFin.integral_sq_gaussianReal`. -/
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
    (ae_of_all volume fun x ↦ by
      simp only [gaussianPDF, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact gaussianPDFReal_pos _ _ x hv)
    (ae_of_all volume fun x ↦ ENNReal.ofReal_ne_top)
  rw [← hQ, hP] at hrn
  have hcomb : (volume.withDensity (gaussianPDF 0 (r * v))).rnDeriv (gaussianReal 0 v)
      =ᵐ[volume] fun x ↦ (gaussianPDF 0 v x)⁻¹ * gaussianPDF 0 (r * v) x := by
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
            ENNReal.ofReal (gaussianPDFReal 0 (r * v) x) := by
          rw [ENNReal.ofReal_inv_of_pos (gaussianPDFReal_pos _ _ x hv)]
      _ = ENNReal.ofReal ((gaussianPDFReal 0 v x)⁻¹ * gaussianPDFReal 0 (r * v) x) := by
          rw [ENNReal.ofReal_mul (inv_nonneg.2 (gaussianPDFReal_nonneg _ _ x))]
      _ = ENNReal.ofReal (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x) := by
          rw [div_eq_inv_mul]
  -- the llr integrand is the log pdf ratio, a.e. volume, hence a.e. P:
  have hllr : llr (gaussianReal 0 (r * v)) (gaussianReal 0 v)
      =ᵐ[volume] fun x ↦ Real.log (gaussianPDFReal 0 (r * v) x / gaussianPDFReal 0 v x) := by
    filter_upwards [hcomb] with x hx
    show Real.log (((gaussianReal 0 (r * v)).rnDeriv (gaussianReal 0 v) x).toReal) = _
    rw [hP, hx, hreal x,
      ENNReal.toReal_ofReal
        (div_nonneg (gaussianPDFReal_nonneg _ _ x) (gaussianPDFReal_nonneg _ _ x))]
  have hPac : gaussianReal 0 (r * v) ≪ volume := gaussianReal_absolutelyContinuous _ hrv
  have hllr' : llr (gaussianReal 0 (r * v)) (gaussianReal 0 v)
      =ᵐ[gaussianReal 0 (r * v)] fun x ↦
        -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ)) := by
    filter_upwards [hPac.ae_le hllr] with x hx
    rw [hx, log_ratio_gaussianPDFReal_eq hv hr]
  rw [integral_congr_ae hllr']
  have hsplit : ∫ x : ℝ, -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))
        ∂(gaussianReal 0 (r * v))
      = -(Real.log (r : ℝ)) / 2
        + (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 (r * v)))
          * (((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))) := by
    have h0 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 (r * v)) :=
      (memLp_id_gaussianReal 2).integrable_sq
    have hint1 : Integrable (fun _ : ℝ ↦ -(Real.log (r : ℝ)) / 2) (gaussianReal 0 (r * v)) :=
      integrable_const _
    have hshape : ∀ x : ℝ, -(Real.log (r : ℝ)) / 2 + x ^ 2 * ((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))
        = -(Real.log (r : ℝ)) / 2 + x ^ 2 * (((r : ℝ) - 1) / (2 * (r : ℝ) * (v : ℝ))) :=
      fun _ ↦ by ring
    rw [integral_congr_ae (ae_of_all _ hshape),
      integral_add hint1 (h0.mul_const _),
      integral_const, integral_mul_const, probReal_univ, one_smul]
  rw [hsplit, MathFin.integral_sq_gaussianReal]
  push_cast
  field_simp
  ring

/-- **The small-shift quadratic (§21.3 p. 361: halving the gap between the regimes
quarters the information and quadruples the delay).** Near `r = 1` the D-term proved
above is `(r−1)²/4` up to a cubic remainder: `|D(r) − (r−1)²/4| ≤ |r−1|³` whenever
`|r − 1| ≤ ½`. So the discrimination information vanishes quadratically as the two
regimes coalesce, and the chapter's delay arithmetic `≈ ln(1/α)/D` grows like
`1/(r−1)²`. From the second-order log-series bound `Real.abs_log_sub_add_sum_range_le` at `x = 1 − r`. -/
theorem kl_gaussianReal_small_shift {r : ℝ} (hr : |r - 1| ≤ 1 / 2) :
    |(r - 1 - Real.log r) / 2 - (r - 1) ^ 2 / 4| ≤ |r - 1| ^ 3 := by
  have h := abs_log_sub_add_sum_range_le (x := 1 - r) (by rw [abs_sub_comm]; linarith) 2
  rw [sub_sub_cancel, abs_sub_comm] at h
  have hsum : ∑ i ∈ Finset.range 2, (1 - r) ^ (i + 1) / (i + 1) = (1 - r) + (1 - r) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at h
  have hb : |r - 1| ^ 3 / (1 - |r - 1|) ≤ 2 * |r - 1| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (pow_nonneg (abs_nonneg (r - 1)) 3)
      (by linarith : (0 : ℝ) ≤ 1 / 2 - |r - 1|)]
  rw [show (r - 1 - Real.log r) / 2 - (r - 1) ^ 2 / 4
      = -((1 - r) + (1 - r) ^ 2 / 2 + Real.log r) / 2 by ring, abs_div, abs_neg, abs_two]
  linarith

end KL

/-! ## Eq. (21.4): realised variance under iid mean-zero noise -/

section RealizedVol

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Eq. (21.4): the realised-variance noise bias is linear in sampling frequency.**
Over `n` increments `ΔX_i` with second moment `E[(ΔX_i)²] = σ²·Δt` (the
`MathFin.integral_sq_gaussianReal` moment in the Gaussian instance)
observed through mean-zero noise `ε_j` of scale `η` (`E[ε_j] = 0`, `E[ε_j²] = η²`), so that
the observed increment is `ΔY_i = ΔX_i + (ε_{i+1} − ε_i)` (the chapter's `Y = X + ε`,
p. 366), the noisy realised sum has expectation `σ²T + 2nη²` where `T = n·Δt`: each
increment contributes its signal second moment plus **two** noise second moments, and
all cross-terms vanish by independence + mean-zero
(`IndepFun.integral_mul_eq_mul_integral`, the chapter's "noise, dependence, scale"
obstruction, §21.3 p. 361). Only the independences the cross-terms use are assumed —
each increment against its two noise draws, and adjacent noise draws pairwise — so iid
noise independent of the signal is a special case. No probability hypothesis on `μ` is
needed; the integrability hypotheses are kept explicit. -/
theorem rvExpectation_withNoise {n : ℕ} {dt T sigma eta : ℝ} (hT : T = (n : ℝ) * dt)
    (dX : ℕ → α → ℝ) (e : ℕ → α → ℝ)
    (hdXi : ∀ i ∈ Finset.range n, Integrable (dX i) μ)
    (hei : ∀ j ∈ Finset.range (n + 1), Integrable (e j) μ)
    (hdXsq : ∀ i ∈ Finset.range n, Integrable (fun x ↦ dX i x * dX i x) μ)
    (hesq : ∀ j ∈ Finset.range (n + 1), Integrable (fun x ↦ e j x * e j x) μ)
    (h_mom : ∀ i ∈ Finset.range n, ∫ x, dX i x * dX i x ∂μ = sigma * sigma * dt)
    (h_noise_sq : ∀ j ∈ Finset.range (n + 1), ∫ x, e j x * e j x ∂μ = eta * eta)
    (h_noise_mean : ∀ j ∈ Finset.range (n + 1), ∫ x, e j x ∂μ = 0)
    (h_noise_indep : ∀ i ∈ Finset.range n, e i ⟂ᵢ[μ] e (i + 1))
    (h_cross : ∀ i ∈ Finset.range n, dX i ⟂ᵢ[μ] e i ∧ dX i ⟂ᵢ[μ] e (i + 1)) :
    ∫ x, ∑ i ∈ Finset.range n, (dX i x + (e (i + 1) x - e i x)) ^ 2 ∂μ
      = sigma * sigma * T + 2 * (n : ℝ) * eta * eta := by
  have hexp : ∀ (i : ℕ) (x : α), (dX i x + (e (i + 1) x - e i x)) ^ 2 =
      dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
        + 2 * (dX i x * e (i + 1) x) - 2 * (dX i x * e i x)
        - 2 * (e i x * e (i + 1) x) :=
    fun _ _ ↦ by ring
  have key : ∀ i ∈ Finset.range n,
      (∫ x : α, (dX i x + (e (i + 1) x - e i x)) ^ 2 ∂μ = sigma * sigma * dt + 2 * eta * eta)
        ∧ Integrable (fun x : α ↦ (dX i x + (e (i + 1) x - e i x)) ^ 2) μ := by
    intro i hi
    have h0 : i ∈ Finset.range (n + 1) := by simp at hi ⊢; omega
    have h1 : i + 1 ∈ Finset.range (n + 1) := by simp at hi ⊢; omega
    -- the six integrable pieces
    have i1 : Integrable (fun x : α ↦ dX i x * dX i x) μ := hdXsq i hi
    have i2 : Integrable (fun x : α ↦ e i x * e i x) μ := hesq i h0
    have i3 : Integrable (fun x : α ↦ e (i + 1) x * e (i + 1) x) μ := hesq (i + 1) h1
    have c1 : Integrable (fun x : α ↦ dX i x * e i x) μ :=
      (h_cross i hi).1.integrable_mul (hdXi i hi) (hei i h0)
    have c2 : Integrable (fun x : α ↦ dX i x * e (i + 1) x) μ :=
      (h_cross i hi).2.integrable_mul (hdXi i hi) (hei (i + 1) h1)
    have c3 : Integrable (fun x : α ↦ e i x * e (i + 1) x) μ :=
      (h_noise_indep i hi).integrable_mul (hei i h0) (hei (i + 1) h1)
    have c1' : Integrable (fun x : α ↦ 2 * (dX i x * e i x)) μ := c1.const_mul 2
    have c2' : Integrable (fun x : α ↦ 2 * (dX i x * e (i + 1) x)) μ := c2.const_mul 2
    have c3' : Integrable (fun x : α ↦ 2 * (e i x * e (i + 1) x)) μ := c3.const_mul 2
    have i12 : Integrable (fun x : α ↦ dX i x * dX i x + e i x * e i x) μ := i1.add i2
    have i123 : Integrable
        (fun x : α ↦ dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x) μ :=
      i12.add i3
    have i1234 : Integrable
        (fun x : α ↦ dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
          + 2 * (dX i x * e (i + 1) x)) μ := i123.add c2'
    have i12345 : Integrable
        (fun x : α ↦ dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
          + 2 * (dX i x * e (i + 1) x) - 2 * (dX i x * e i x)) μ := i1234.sub c1'
    have p6 : Integrable
        (fun x : α ↦ dX i x * dX i x + e i x * e i x + e (i + 1) x * e (i + 1) x
          + 2 * (dX i x * e (i + 1) x) - 2 * (dX i x * e i x)
          - 2 * (e i x * e (i + 1) x)) μ := i12345.sub c3'
    refine ⟨?_, p6.congr (ae_of_all μ fun x ↦ (hexp i x).symm)⟩
    rw [integral_congr_ae (ae_of_all μ fun x ↦ hexp i x)]
    -- split into the six integrals; each cross-term factors and vanishes
    have z1 : ∫ x : α, dX i x * e i x ∂μ = (∫ x, dX i x ∂μ) * (∫ x, e i x ∂μ) :=
      (h_cross i hi).1.integral_mul_eq_mul_integral (hdXi i hi).1 (hei i h0).1
    have z2 : ∫ x : α, dX i x * e (i + 1) x ∂μ
        = (∫ x, dX i x ∂μ) * (∫ x, e (i + 1) x ∂μ) :=
      (h_cross i hi).2.integral_mul_eq_mul_integral (hdXi i hi).1 (hei (i + 1) h1).1
    have z3 : ∫ x : α, e i x * e (i + 1) x ∂μ
        = (∫ x, e i x ∂μ) * (∫ x, e (i + 1) x ∂μ) :=
      (h_noise_indep i hi).integral_mul_eq_mul_integral (hei i h0).1 (hei (i + 1) h1).1
    rw [integral_sub i12345 c3', integral_sub i1234 c1', integral_add i123 c2',
      integral_add i12 i3, integral_add i1 i2,
      h_mom i hi, h_noise_sq i h0, h_noise_sq (i + 1) h1,
      integral_const_mul, z2, h_noise_mean (i + 1) h1, mul_zero,
      integral_const_mul, z1, h_noise_mean i h0, mul_zero,
      integral_const_mul, z3, h_noise_mean i h0, h_noise_mean (i + 1) h1, mul_zero, mul_zero]
    ring
  calc ∫ x, ∑ i ∈ Finset.range n, (dX i x + (e (i + 1) x - e i x)) ^ 2 ∂μ
      = ∑ i ∈ Finset.range n, ∫ x : α, (dX i x + (e (i + 1) x - e i x)) ^ 2 ∂μ :=
        integral_finsetSum (Finset.range n) fun i hi ↦ (key i hi).2
    _ = ∑ i ∈ Finset.range n, (sigma * sigma * dt + 2 * eta * eta) :=
        Finset.sum_congr rfl fun i hi ↦ (key i hi).1
    _ = sigma * sigma * T + 2 * (n : ℝ) * eta * eta := by
        rw [hT, Finset.sum_const, Finset.card_range]
        ring

end RealizedVol

/-! ## Eq. (21.3)'s sign: the square-root estimator is biased low -/

section SqrtBias

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- **Eq. (21.3)'s sign: `E[σ̂] < σ`.** If `Y ≥ 0` is a nondegenerate target with
`E[Y] = σ²` (the sample reading: `Y = RV/n`, the realised-variance average whose square
root is the volatility estimator `σ̂ = √Y`), then `E[√Y] < σ` — the square-root estimator
of a nondegenerate volatility is **biased low**. Strictness comes from the tangent-line
identity at `σ²`: `√y = (y + σ²)/(2σ) − (√y − σ)²/(2σ)`, whose remainder is strictly
positive on `{Y ≠ σ²}`, a set of positive measure by nondegeneracy. The exact
`√(2/n)·Γ((n+1)/2)/Γ(n/2)` constant of the chapter stays gated (Gamma machinery). -/
theorem sqrtBias_oneSided {Y : α → ℝ} (hYnn : ∀ ω, 0 ≤ Y ω)
    {sigma : ℝ} (hsig : 0 < sigma) (hint : Integrable Y μ)
    (hmean : ∫ ω, Y ω ∂μ = sigma * sigma) (hnd : μ {ω | Y ω ≠ sigma * sigma} ≠ 0) :
    ∫ ω, Real.sqrt (Y ω) ∂μ < sigma := by
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
    have hkey : (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2
        = Y ω + sigma * sigma - 2 * Real.sqrt (Y ω) * Real.sqrt (sigma * sigma) := by
      rw [sub_sq, e1, e2]
      ring
    rw [hkey, hc]
    field_simp
    ring
  -- integrability of the two pieces
  have hintP : Integrable (fun ω ↦ c * Y ω + c * (sigma * sigma)) μ := by
    have h := (hint.mul_const c).add (integrable_const (c * (sigma * sigma)))
    refine h.congr (ae_of_all μ fun ω ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have hkey2 : ∀ ω : α, (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2
      ≤ 2 * Y ω + 2 * (sigma * sigma) := by
    intro ω
    have e1 : (Real.sqrt (Y ω)) ^ 2 = Y ω := Real.sq_sqrt (hYnn ω)
    have e2 : (Real.sqrt (sigma * sigma)) ^ 2 = sigma * sigma := Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (Real.sqrt (Y ω) + Real.sqrt (sigma * sigma)), e1, e2]
  have hintD : Integrable (fun ω ↦ 2 * c * Y ω + 2 * c * (sigma * sigma)) μ := by
    have h := (hint.mul_const (2 * c)).add (integrable_const (2 * c * (sigma * sigma)))
    refine h.congr (ae_of_all μ fun ω ↦ ?_)
    simp only [Pi.add_apply]
    ring
  have hintg : Integrable (fun ω ↦ c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2) μ := by
    refine Integrable.mono hintD ?_ ?_
    · have := hint.1
      fun_prop
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
    have h1 : Integrable (fun ω : α ↦ c * Y ω) μ :=
      (hint.mul_const c).congr (ae_of_all μ fun ω ↦ mul_comm _ _)
    have hconst : ∫ ω : α, c * (sigma * sigma) ∂μ = c * (sigma * sigma) := by
      have h := integral_const (c * (sigma * sigma)) (μ := μ)
      rw [h]
      simp
    rw [integral_add h1 (integrable_const _),
      show (fun ω : α ↦ c * Y ω) = fun ω ↦ Y ω * c from funext fun _ ↦ mul_comm _ _,
      integral_mul_const c (fun ω ↦ Y ω), hmean, hconst, hc]
    field_simp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ sigma ^ 2)]
    ring
  -- the remainder has strictly positive integral on the nondegeneracy set
  have hintgpos : 0 < ∫ ω, c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2 ∂μ := by
    by_contra hcon
    push Not at hcon
    have h0 : ∫ ω, c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2 ∂μ = 0 :=
      le_antisymm hcon (integral_nonneg fun ω ↦
        mul_nonneg (le_of_lt hcpos) (sq_nonneg _))
    have hnn2 : 0 ≤ᵐ[μ] fun ω ↦ c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2 :=
      ae_of_all μ fun ω ↦ mul_nonneg (le_of_lt hcpos) (sq_nonneg _)
    have hlint0 : ∫⁻ ω, ENNReal.ofReal
        (c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2) ∂μ = 0 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hintg hnn2, h0, ENNReal.ofReal_zero]
    have hae := (lintegral_eq_zero_iff' hintg.1.aemeasurable.ennreal_ofReal).mp hlint0
    have hsub : {ω | Y ω ≠ sigma * sigma}
        ⊆ {ω | ¬(ENNReal.ofReal (c * (Real.sqrt (Y ω) - Real.sqrt (sigma * sigma)) ^ 2) = 0)} := by
      intro ω hω
      have hsne : Real.sqrt (Y ω) ≠ Real.sqrt (sigma * sigma) := fun heq ↦ hω (by
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
constant `√(2/n)·Γ((n+1)/2)/Γ(n/2) = √(2/π) ≈ 0.798` at `n = 1` (so `E|Z| ≈ 0.798σ`)
stays gated. -/
theorem sqrtBias_absGaussianSample {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, |x| ∂(gaussianReal 0 v) < Real.sqrt (v : ℝ) := by
  have hvpc : 0 < v := hv.bot_lt
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hvpc
  have : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv
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
        linarith
    refine measure_mono_null hsub ?_
    rw [measure_union_null (measure_singleton _) (measure_singleton _)]
  have hnd : (gaussianReal 0 v)
      {x : ℝ | x ^ 2 ≠ Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)} ≠ 0 := by
    have hmeas : MeasurableSet {x : ℝ | x ^ 2 = Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)} := by
      show MeasurableSet ((fun x : ℝ ↦ x ^ 2) ⁻¹' {Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)})
      exact MeasurableSet.preimage (measurableSet_singleton _) (by fun_prop)
    have hcompl : {x : ℝ | x ^ 2 ≠ Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)}
        = {x : ℝ | x ^ 2 = Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ)}ᶜ := by
      ext x
      simp [ne_eq]
    rw [hcompl, measure_compl hmeas (measure_ne_top _ _), hsetzero, measure_univ]
    simp
  have hmain := sqrtBias_oneSided (μ := gaussianReal 0 v) (Y := fun x : ℝ ↦ x ^ 2)
    (sigma := Real.sqrt (v : ℝ)) (fun _ ↦ sq_nonneg _) hsqrtpos
    (memLp_id_gaussianReal 2).integrable_sq
    (by rw [MathFin.integral_sq_gaussianReal v]; exact hsqrtsq.symm) hnd
  rw [show (fun x : ℝ ↦ |x|) = fun x : ℝ ↦ Real.sqrt (x ^ 2) from funext habs]
  exact hmain

end SqrtBias

/-! ## Calc 21.4's bad column: the drift estimator sees only the endpoints -/

section DriftSE

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Calc 21.4's drift column (the law).** For `X_t = μt + σB_t` with `B_T ~ N(0, T)`,
the endpoint drift estimator `(X_T − X_0)/T = μ + (σ/T)·B_T` has law `N(μ, σ²/T)` — an
affine pushforward of the gaussianReal sample (`gaussianReal_const_mul` then
`gaussianReal_const_add`). The variance slot is `σ²/T`,
giving the chapter's flat-in-`n` drift standard error `σ/√T` (p. 363). -/
theorem drift_se_endpoint_hasLaw {T : ℝ} (hT : 0 < T) (mu sigma : ℝ) {B : Ω → ℝ}
    (hB : HasLaw B (gaussianReal 0 T.toNNReal) P) :
    HasLaw (fun ω ↦ (mu * T + sigma * B ω) / T)
      (gaussianReal mu (sigma ^ 2 / T).toNNReal) P := by
  have h1 := gaussianReal_const_mul hB (sigma / T)
  have h2 := gaussianReal_const_add h1 mu
  have hcong : (fun ω ↦ (mu * T + sigma * B ω) / T)
      = (fun ω ↦ mu + sigma / T * B ω) := by
    funext ω
    field_simp
  rw [hcong]
  convert h2 using 2
  · ring
  · refine NNReal.coe_injective ?_
    rw [Real.coe_toNNReal _ (by positivity), NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ hT.le]
    field_simp

/-- **Calc 21.4's drift column (the variance).** `Var[(X_T − X_0)/T] = σ²/T`: the drift
estimator's standard error is `σ/√T`, independent of the sampling frequency `n` — "the
estimator sees only the endpoints" (p. 363). Via `HasLaw.variance_eq` and
`variance_id_gaussianReal`. -/
theorem drift_se_endpoint_var {T : ℝ} (hT : 0 < T) (mu sigma : ℝ) {B : Ω → ℝ}
    (hB : HasLaw B (gaussianReal 0 T.toNNReal) P) :
    Var[fun ω ↦ (mu * T + sigma * B ω) / T; P] = sigma ^ 2 / T := by
  rw [(drift_se_endpoint_hasLaw hT mu sigma hB).variance_eq, variance_id_gaussianReal,
    Real.coe_toNNReal _ (by positivity)]

/-- The pure-sample reading, on the gaussianReal space itself (`Z = id ~ N(0, T)`):
`Var[(μT + σZ)/T] = σ²/T` with `n` nowhere in sight. -/
theorem drift_se_endpoint_var_id {T : ℝ} (hT : 0 < T) (mu sigma : ℝ) :
    Var[(fun z : ℝ ↦ (mu * T + sigma * z) / T);
      gaussianReal 0 T.toNNReal] = sigma ^ 2 / T :=
  drift_se_endpoint_var hT mu sigma HasLaw.id

end DriftSE

end MathFin
