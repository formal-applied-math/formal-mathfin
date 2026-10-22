/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.Call
public import MathFin.Foundations.GaussianPartialMoments

/-!
# Bachelier model option pricing

The Bachelier (1900) model is the historical predecessor of Black-Scholes:
asset prices follow an **arithmetic** Brownian motion `S_T = S_0 + σ · W_T`
(no exponential, no log-normality). Used today for short-tenor / negative-rate
markets where lognormality is inappropriate.

Under `BachelierHyp`, the discounted call price is

    V_bach = (S_0 - K) · Φ(d) + σ √T · ϕ(d),

where `d = (S_0 - K) / (σ √T)`, `Φ` and `ϕ` are the standard normal CDF and
PDF. The proof structure parallels `bs_call_formula`: HasLaw transfer +
indicator decomposition on the exercise region `Ioi(-d)` + a truncated-mean
identity for the Gaussian first moment.

The truncated mean of `N(0, 1)`, `∫ z in Ioi a, z · ϕ(z) dz = ϕ(a)`, is
`integral_id_mul_gaussianPDFReal_Ioi` in `Foundations/GaussianPartialMoments`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal ENNReal Topology

/-! ### Bachelier model hypothesis -/

/-- Bachelier model risk-neutral hypothesis: the terminal price `S_T = S_0 + σ √T · Z`
with `Z ~ N(0, 1)`. The asset follows arithmetic Brownian motion (no exponential). -/
structure BachelierHyp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (S_0 K σ T : ℝ) (Z : Ω → ℝ) : Prop where
  K_pos : 0 < K
  σ_pos : 0 < σ
  T_pos : 0 < T
  Z_law : HasLaw Z (gaussianReal 0 1) Q

/-- Bachelier `d`: dimensionless distance to the strike. -/
noncomputable def bachelierD (S_0 K σ T : ℝ) : ℝ :=
  (S_0 - K) / (σ * Real.sqrt T)

/-- Bachelier terminal price `S_T(z) = S_0 + σ √T · z`. -/
noncomputable def bachelierTerminal (S_0 σ T : ℝ) (z : ℝ) : ℝ :=
  S_0 + σ * Real.sqrt T * z

/-- Exercise-region identification for the Bachelier model: `S_T(z) > K ↔ z > -d`. -/
private lemma bachelierTerminal_gt_K_iff {S_0 K σ T : ℝ}
    (_hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (z : ℝ) :
    bachelierTerminal S_0 σ T z > K ↔ z > -bachelierD S_0 K σ T := by
  have h_σsqT_pos : 0 < σ * Real.sqrt T := mul_pos hσ (Real.sqrt_pos.mpr hT)
  unfold bachelierTerminal bachelierD
  have h_neg_eq : -((S_0 - K) / (σ * Real.sqrt T)) = (K - S_0) / (σ * Real.sqrt T) := by
    field_simp; ring
  constructor
  · intro h
    rw [h_neg_eq, gt_iff_lt, div_lt_iff₀ h_σsqT_pos, mul_comm]
    linarith
  · intro h
    rw [h_neg_eq, gt_iff_lt, div_lt_iff₀ h_σsqT_pos, mul_comm] at h
    linarith

/-- `max(S_T(z) - K, 0)` as an indicator on `Ioi(-d)`. -/
private lemma bachelier_max_payoff_eq_indicator {S_0 K σ T : ℝ}
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (z : ℝ) :
    max (bachelierTerminal S_0 σ T z - K) 0 =
      (Set.Ioi (-bachelierD S_0 K σ T)).indicator
        (fun z' ↦ bachelierTerminal S_0 σ T z' - K) z := by
  by_cases h : z ∈ Set.Ioi (-bachelierD S_0 K σ T)
  · rw [Set.indicator_of_mem h]
    have hST : bachelierTerminal S_0 σ T z > K :=
      (bachelierTerminal_gt_K_iff hK hσ hT z).mpr h
    exact max_eq_left (sub_nonneg.mpr hST.le)
  · rw [Set.indicator_of_notMem h]
    have hz_le : z ≤ -bachelierD S_0 K σ T := not_lt.mp h
    have hST_le : bachelierTerminal S_0 σ T z ≤ K := by
      by_contra hcontra
      exact h ((bachelierTerminal_gt_K_iff hK hσ hT z).mp (not_le.mp hcontra))
    exact max_eq_right (sub_nonpos.mpr hST_le)

/-! ### Bachelier call pricing formula -/

/-- **Bachelier European call pricing formula.**

For an asset whose risk-neutral dynamics are arithmetic Brownian motion
(`bachelierTerminal(z) = S_0 + σ √T · z` with `Z ~ N(0, 1)`),
the expected payoff of the European call `max(S_T - K, 0)` is

    E_Q[max(S_T - K, 0)] = (S_0 - K) · Φ(d) + σ √T · ϕ(d),

where `d = (S_0 - K) / (σ √T)`.

Real derivation: HasLaw transfer to standard normal,
`max(S_T - K, 0) = 1_{Ioi(-d)}(z) · σ √T · (z + d)`,
then split into `σ √T · ϕ(d)` (the truncated first moment via FTC) and
`(S_0 - K) · Φ(d)` (the cumulative-tail probability). -/
theorem bachelier_call_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K σ T : ℝ} {Z : Ω → ℝ}
    (h : BachelierHyp Q S_0 K σ T Z) :
    ∫ ω, max (bachelierTerminal S_0 σ T (Z ω) - K) 0 ∂Q
      = (S_0 - K) * Phi (bachelierD S_0 K σ T) +
        σ * Real.sqrt T * gaussianPDFReal 0 1 (bachelierD S_0 K σ T) := by
  obtain ⟨hK, hσ, hT, hZ⟩ := h
  set d : ℝ := bachelierD S_0 K σ T
  have hsqrT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_σsqT_pos : 0 < σ * Real.sqrt T := mul_pos hσ hsqrT_pos
  have h_σsqT_ne : σ * Real.sqrt T ≠ 0 := h_σsqT_pos.ne'
  have h_payoff_meas : Measurable fun z : ℝ ↦ max (bachelierTerminal S_0 σ T z - K) 0 := by
    unfold bachelierTerminal; fun_prop
  -- HasLaw transfer + convert to volume integral
  rw [show (fun ω ↦ max (bachelierTerminal S_0 σ T (Z ω) - K) 0)
        = (fun z ↦ max (bachelierTerminal S_0 σ T z - K) 0) ∘ Z from rfl,
      hZ.integral_comp h_payoff_meas.aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- max → indicator on Ioi(-d)
  rw [show (fun z : ℝ ↦ gaussianPDFReal 0 1 z • max (bachelierTerminal S_0 σ T z - K) 0)
        = (Set.Ioi (-d)).indicator
            (fun z ↦ gaussianPDFReal 0 1 z * (bachelierTerminal S_0 σ T z - K)) from
      funext (fun z ↦ by
        rw [smul_eq_mul, bachelier_max_payoff_eq_indicator hK hσ hT z]
        by_cases hz : z ∈ Set.Ioi (-d)
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero])]
  rw [integral_indicator measurableSet_Ioi]
  -- Rewrite pdf · (S_T(z) - K) = pdf · (σ√T · z + (S_0 - K))
  --                            = σ√T · z · pdf + (S_0 - K) · pdf
  have h_split : ∀ z : ℝ,
      gaussianPDFReal 0 1 z * (bachelierTerminal S_0 σ T z - K)
        = σ * Real.sqrt T * (z * gaussianPDFReal 0 1 z) +
          (S_0 - K) * gaussianPDFReal 0 1 z := by
    intro z; unfold bachelierTerminal; ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun z _ ↦ h_split z)]
  -- Integrability and split
  have h_int_pdf : IntegrableOn (gaussianPDFReal 0 1) (Set.Ioi (-d)) volume :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have h_int_z_pdf : IntegrableOn (fun z : ℝ ↦ z * gaussianPDFReal 0 1 z)
      (Set.Ioi (-d)) volume := integrable_id_mul_gaussianPDFReal_volume.integrableOn
  rw [integral_add (h_int_z_pdf.const_mul _) (h_int_pdf.const_mul _)]
  rw [integral_const_mul, integral_const_mul]
  -- ∫ pdf on Ioi(-d) = Φ(d), ∫ z·pdf on Ioi(-d) = pdf(0,1,-d) = pdf(0,1,d)
  rw [integral_id_mul_gaussianPDFReal_Ioi]
  have h_pdf_int_eq :
      ∫ z in Set.Ioi (-d), gaussianPDFReal 0 1 z = Phi d := by
    rw [setIntegral_gaussianPDFReal_eq_toReal measurableSet_Ioi (0 : ℝ),
        gaussianReal_Ioi_toReal, neg_neg]
  rw [h_pdf_int_eq]
  -- Final: σ√T · pdf(0,1,-d) + (S_0 - K) · Φ(d), and pdf(0,1,-d) = pdf(0,1,d)
  have h_pdf_neg : gaussianPDFReal 0 1 (-d) = gaussianPDFReal 0 1 d :=
    gaussianPDFReal_zero_one_neg d
  rw [h_pdf_neg]
  ring

end MathFin
