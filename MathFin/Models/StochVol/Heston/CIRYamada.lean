/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Models.StochVol.Heston.CIRNonneg
public import MathFin.Models.StochVol.Heston.YamadaCalculus

/-!
# The Yamada–Watanabe estimate and pathwise uniqueness for CIR-type equations

For two Itô processes `X, Y` with the same initial value, drifts `κ(θ - X)`, `κ(θ - Y)` (`κ ≥ 0`)
and diffusion integrands satisfying `(H₁ - H₂)² ≤ A |X - Y| + c`, Dynkin's formula applied to the
Yamada function `φ` (`|φ'| ≤ 1`, `φ'' = ψ(|·|)`, `ψ(u) u ≤ 2/m`, `ψ ≤ 2/(m a)`) gives

`E|X_t - Y_t| ≤ b + (A/m + c/(m a)) t`

for all Yamada parameters `a < b`, `m = log (b/a)`.  The drift contributes `-κ φ'(Δ) Δ ≤ 0`, so no
Gronwall argument is needed.  With `c = 0` and `b ↓ 0`, `m ↑ ∞` this is pathwise uniqueness
(`(√x⁺ - √y⁺)² ≤ |x - y|`); with `c = 4ξ²(ε+δ)` it is the Cauchy estimate for the regularized CIR
solutions.

## Main definitions

* `yamadaParamsOf`

## Main results

* `cirRegularizedDiffusion_cross_sq_le`
* `cir_pathwise_unique`
* `cir_regularized_cauchy`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace MathFin.Heston
open MathFin.FilteredIto
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open MathFin MathFin.ItoIntegralL2 MathFin.ItoIntegralCLM MathFin.ItoIntegralProcessGeneral
open MathFin.ItoIntegralProcessContinuousModification MathFin.ItoFormulaAdapted
open MathFin.AdaptedDrift MathFin.ItoIntegralAgainstMartingale

/-! ## Facts about the Yamada function -/

theorem yamada_psi_le_two_div_ma (p : YamadaParams) (x : ℝ) :
    yamadaPsi p x ≤ 2 / (yamadaM p * p.a) := by
  have hm := yamada_m_pos p
  by_cases hx : p.a ≤ x
  · have hxpos : 0 < x := lt_of_lt_of_le p.ha_pos hx
    calc yamadaPsi p x ≤ 2 / (yamadaM p * x) := yamada_psi_le_two_div_mx p hxpos
      _ ≤ 2 / (yamadaM p * p.a) :=
        div_le_div_of_nonneg_left (by norm_num) (mul_pos hm p.ha_pos)
          (mul_le_mul_of_nonneg_left hx hm.le)
  · rw [yamada_psi_of_lt p (lt_of_not_ge hx)]
    exact div_nonneg (by norm_num) (mul_pos hm p.ha_pos).le

theorem abs_yamada_psi_abs_le (p : YamadaParams) (x : ℝ) :
    |yamadaPsi p (|x|)| ≤ 2 / (yamadaM p * p.a) := by
  rw [abs_of_nonneg (yamada_psi_nonneg p _)]
  exact yamada_psi_le_two_div_ma p _

theorem yamada_psi_abs_mul_abs_le (p : YamadaParams) (x : ℝ) :
    yamadaPsi p |x| * |x| ≤ 2 / yamadaM p := by
  have hm := yamada_m_pos p
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [abs_zero, mul_zero]
    exact div_nonneg (by norm_num) hm.le
  · have hpos : 0 < |x| := abs_pos.mpr hx
    calc yamadaPsi p |x| * |x| ≤ 2 / (yamadaM p * |x|) * |x| :=
          mul_le_mul_of_nonneg_right (yamada_psi_abs_le_two_div_m_abs p hx) hpos.le
      _ = 2 / yamadaM p := by
          rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hpos.ne']

theorem yamada_phiPrime_mul_self_nonneg (p : YamadaParams) (x : ℝ) :
    0 ≤ yamadaPhiPrime p x * x := by
  rcases le_or_gt 0 x with hx | hx
  · exact mul_nonneg (yamada_phiPrime_nonneg_of_nonneg p hx) hx
  · have h1 := yamada_phiPrime_neg p (-x)
    rw [neg_neg] at h1
    have h2 : 0 ≤ yamadaPhiPrime p (-x) := yamada_phiPrime_nonneg_of_nonneg p (by linarith)
    rw [h1]
    nlinarith

/-- Yamada parameters with prescribed `b` and logarithmic length `m`: `a = b e^{-m}`. -/
def yamadaParamsOf (b m : ℝ) (hb : 0 < b) (hm : 0 < m) : YamadaParams where
  a := b / Real.exp m
  b := b
  ha_pos := div_pos hb (Real.exp_pos m)
  hab := div_lt_self hb (Real.one_lt_exp_iff.mpr hm)

@[simp] theorem yamadaParamsOf_b {b m : ℝ} (hb : 0 < b) (hm : 0 < m) :
    (yamadaParamsOf b m hb hm).b = b := rfl

theorem yamada_m_yamadaParamsOf {b m : ℝ} (hb : 0 < b) (hm : 0 < m) :
    yamadaM (yamadaParamsOf b m hb hm) = m := by
  show Real.log (b / (b / Real.exp m)) = m
  rw [div_div_cancel₀ hb.ne', Real.log_exp]

/-! ## Elementary integral bounds -/

theorem setIntegral_le_of_ae_le_const {F : ℝ≥0 → ℝ} {K : ℝ} (hK : 0 ≤ K) {t : ℝ≥0}
    (h : ∀ᵐ s ∂timeMeasure.restrict (Set.Ioc 0 t), F s ≤ K) :
    ∫ s in Set.Ioc 0 t, F s ∂timeMeasure ≤ K * t := by
  have : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)) :=
    inferInstanceAs (IsFiniteMeasure (timeMeasureHorizon t))
  have hconst : ∫ s in Set.Ioc (0 : ℝ≥0) t, K ∂timeMeasure = K * t := by
    have := setIntegral_timeMeasure_Ioc_eq (fun _ => K) t
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at this
    rw [this, mul_comm]
  by_cases hi : Integrable F (timeMeasure.restrict (Set.Ioc 0 t))
  · calc ∫ s in Set.Ioc 0 t, F s ∂timeMeasure
        ≤ ∫ s in Set.Ioc (0 : ℝ≥0) t, K ∂timeMeasure :=
          integral_mono_ae hi (integrable_const K) h
      _ = K * t := hconst
  · rw [integral_undef hi]
    exact mul_nonneg hK t.coe_nonneg

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

theorem integral_le_of_ae_le_const {f : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ᵐ ω ∂μ, f ω ≤ K) : ∫ ω, f ω ∂μ ≤ K := by
  by_cases hi : Integrable f μ
  · calc ∫ ω, f ω ∂μ ≤ ∫ _ω, K ∂μ := integral_mono_ae hi (integrable_const K) h
      _ = K := by simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  · rw [integral_undef hi]
    exact hK

section Yamada
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

include hB hBcont in
/-- The `L²` Itô process is a.s. linear in its data, simultaneously for all times. -/
theorem l2ItoProcess_sub (x₀ x₀' : ℝ) (β γ β' γ' : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, l2ItoProcess T hBmeas (x₀ - x₀') (β - β') (γ - γ') t ω
      = l2ItoProcess T hBmeas x₀ β γ t ω - l2ItoProcess T hBmeas x₀' β' γ' t ω := by
  refine ae_forall_eq_of_continuousOn T
    (ae_continuousOn_l2ItoProcess hB T hBmeas hBcont _ _ _) ?_ ?_
  · filter_upwards [ae_continuousOn_l2ItoProcess hB T hBmeas hBcont x₀ β γ,
      ae_continuousOn_l2ItoProcess hB T hBmeas hBcont x₀' β' γ'] with ω h1 h2
    exact h1.sub h2
  · intro t ht
    filter_upwards [driftContinuousMod_sub_ae T hBmeas β β' ht,
      itoContinuousMod_modification hB T hBmeas hBcont (γ - γ') ht,
      itoContinuousMod_modification hB T hBmeas hBcont γ ht,
      itoContinuousMod_modification hB T hBmeas hBcont γ' ht,
      Lp.coeFn_sub (itoProcessCLM hB T t hBmeas γ) (itoProcessCLM hB T t hBmeas γ')]
      with ω hd hi hi1 hi2 hsub
    simp only [l2ItoProcess]
    rw [hd, hi, map_sub, hsub, Pi.sub_apply, ← hi1, ← hi2]
    ring

include hB hBcont in
/-- **The Yamada estimate.** -/
theorem yamada_estimate (p : YamadaParams) {x₀ κ θ A c : ℝ} (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hc : 0 ≤ c) (G₁ H₁ G₂ H₂ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hG₁ : ⇑G₁ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => κ * (θ - l2ItoProcess T hBmeas x₀ G₁ H₁ z.1 z.2))
    (hG₂ : ⇑G₂ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => κ * (θ - l2ItoProcess T hBmeas x₀ G₂ H₂ z.1 z.2))
    (hH : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), (H₁ z - H₂ z) ^ 2
      ≤ A * |l2ItoProcess T hBmeas x₀ G₁ H₁ z.1 z.2 - l2ItoProcess T hBmeas x₀ G₂ H₂ z.1 z.2| + c)
    {t : ℝ≥0} (htT : t ≤ T) :
    ∫ ω, |l2ItoProcess T hBmeas x₀ G₁ H₁ t ω - l2ItoProcess T hBmeas x₀ G₂ H₂ t ω| ∂μ
      ≤ p.b + (A / yamadaM p + c / (yamadaM p * p.a)) * t := by
  set X := l2ItoProcess T hBmeas x₀ G₁ H₁ with hX
  set Y := l2ItoProcess T hBmeas x₀ G₂ H₂ with hY
  set D := l2ItoProcess T hBmeas (x₀ - x₀) (G₁ - G₂) (H₁ - H₂) with hD
  have hDXY : ∀ᵐ ω ∂μ, ∀ s ≤ T, D s ω = X s ω - Y s ω :=
    l2ItoProcess_sub hB T hBmeas hBcont x₀ x₀ G₁ H₁ G₂ H₂
  have hm := yamada_m_pos p
  have ha := p.ha_pos
  set K := A / yamadaM p + c / (yamadaM p * p.a) with hK
  have hK0 : 0 ≤ K := add_nonneg (div_nonneg hA hm.le) (div_nonneg hc (mul_pos hm ha).le)
  have hI := ito_formula_L2_integral hB T hBmeas hBcont (x₀ - x₀) (G₁ - G₂) (H₁ - H₂)
    (yamada_hasDerivAt_phi p) (yamada_hasDerivAt_phiPrime p)
    ((yamada_continuous_psi p).comp continuous_abs) (yamada_abs_phiPrime_le_one p)
    (abs_yamada_psi_abs_le p) htT
  rw [← hD] at hI
  have hslice : ∀ᵐ ω ∂μ, ∫ s in Set.Ioc 0 t, (yamadaPhiPrime p (D s ω) * (G₁ - G₂) (s, ω)
      + 1 / 2 * (yamadaPsi p |D s ω| * (H₁ - H₂) (s, ω) ^ 2)) ∂timeMeasure ≤ K * t := by
    filter_upwards [ae_ae_of_ae_trim T hBmeas hG₁, ae_ae_of_ae_trim T hBmeas hG₂,
      ae_ae_of_ae_trim T hBmeas hH, ae_ae_of_ae_trim T hBmeas (Lp.coeFn_sub G₁ G₂),
      ae_ae_of_ae_trim T hBmeas (Lp.coeFn_sub H₁ H₂), hDXY] with ω h1 h2 h3 h4 h5 h6
    refine setIntegral_le_of_ae_le_const hK0 ?_
    rw [← timeMeasure_T_restrict_Ioc T htT]
    refine ae_restrict_of_ae ?_
    filter_upwards [h1, h2, h3, h4, h5, ae_le_T_timeMeasure_T T] with s e1 e2 e3 e4 e5 hsT
    have e1' : G₁ (s, ω) = κ * (θ - X s ω) := e1
    have e2' : G₂ (s, ω) = κ * (θ - Y s ω) := e2
    have e3' : (H₁ (s, ω) - H₂ (s, ω)) ^ 2 ≤ A * |X s ω - Y s ω| + c := e3
    rw [e4, e5, Pi.sub_apply, Pi.sub_apply, e1', e2']
    have hDs : D s ω = X s ω - Y s ω := h6 s hsT
    have hdrift : yamadaPhiPrime p (D s ω) * (κ * (θ - X s ω) - κ * (θ - Y s ω)) ≤ 0 := by
      have heq : κ * (θ - X s ω) - κ * (θ - Y s ω) = -κ * D s ω := by rw [hDs]; ring
      rw [heq]
      have := yamada_phiPrime_mul_self_nonneg p (D s ω)
      nlinarith
    have hψ0 : 0 ≤ yamadaPsi p |D s ω| := yamada_psi_nonneg p _
    have hdiff : yamadaPsi p |D s ω| * (H₁ (s, ω) - H₂ (s, ω)) ^ 2
        ≤ yamadaPsi p |D s ω| * (A * |D s ω| + c) := by
      refine mul_le_mul_of_nonneg_left ?_ hψ0
      rw [hDs]
      exact e3'
    have hb1 : yamadaPsi p |D s ω| * |D s ω| ≤ 2 / yamadaM p := yamada_psi_abs_mul_abs_le p _
    have hb2 : yamadaPsi p |D s ω| ≤ 2 / (yamadaM p * p.a) := yamada_psi_le_two_div_ma p _
    have hcomb : yamadaPsi p |D s ω| * (A * |D s ω| + c)
        ≤ A * (2 / yamadaM p) + c * (2 / (yamadaM p * p.a)) := by
      have k1 := mul_le_mul_of_nonneg_left hb1 hA
      have k2 := mul_le_mul_of_nonneg_left hb2 hc
      nlinarith
    have hKeq : K = 1 / 2 * (A * (2 / yamadaM p) + c * (2 / (yamadaM p * p.a))) := by
      rw [hK]; ring
    rw [hKeq]
    linarith
  have hφ0 : yamadaPhi p (x₀ - x₀) = 0 := by rw [sub_self, yamada_phi_zero]
  have hE : ∫ ω, yamadaPhi p (D t ω) ∂μ ≤ K * t := by
    have hI' := hI
    simp only [hφ0, sub_zero] at hI'
    rw [hI']
    exact integral_le_of_ae_le_const (mul_nonneg hK0 t.coe_nonneg) hslice
  have hφint : Integrable (fun ω => yamadaPhi p (D t ω)) μ := by
    have := integrable_comp_at hB T hBmeas hBcont (x₀ - x₀) (G₁ - G₂) (H₁ - H₂)
      (yamada_hasDerivAt_phi p) (yamada_abs_phiPrime_le_one p) htT
    rw [← hD] at this
    simpa only [hφ0, sub_zero] using this
  have hDint : Integrable (fun ω => |D t ω|) μ := by
    have := integrable_comp_at hB T hBmeas hBcont (x₀ - x₀) (G₁ - G₂) (H₁ - H₂)
      (f := id) (f' := fun _ => 1) (fun x => hasDerivAt_id x) (C₁ := 1) (fun _ => by norm_num) htT
    rw [← hD] at this
    refine this.abs.congr (ae_of_all _ fun ω => ?_)
    simp only [id, sub_self, sub_zero]
  calc ∫ ω, |X t ω - Y t ω| ∂μ = ∫ ω, |D t ω| ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hDXY] with ω h
        rw [h t htT]
    _ ≤ ∫ ω, (yamadaPhi p (D t ω) + p.b) ∂μ :=
        integral_mono hDint (hφint.add (integrable_const _)) (fun ω => by
          have := yamada_sub_le_phi p (D t ω)
          dsimp only
          linarith)
    _ = ∫ ω, yamadaPhi p (D t ω) ∂μ + p.b := by
        rw [integral_add hφint (integrable_const _)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ K * t + p.b := by linarith [hE]
    _ = p.b + K * t := by ring

include hB hBcont in
/-- **Pathwise uniqueness** under the Yamada condition `(H₁ - H₂)² ≤ A |X - Y|`. -/
theorem pathwise_unique_of_yamada {x₀ κ θ A : ℝ} (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (G₁ H₁ G₂ H₂ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hG₁ : ⇑G₁ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => κ * (θ - l2ItoProcess T hBmeas x₀ G₁ H₁ z.1 z.2))
    (hG₂ : ⇑G₂ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => κ * (θ - l2ItoProcess T hBmeas x₀ G₂ H₂ z.1 z.2))
    (hH : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), (H₁ z - H₂ z) ^ 2
      ≤ A * |l2ItoProcess T hBmeas x₀ G₁ H₁ z.1 z.2 - l2ItoProcess T hBmeas x₀ G₂ H₂ z.1 z.2|) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T,
      l2ItoProcess T hBmeas x₀ G₁ H₁ t ω = l2ItoProcess T hBmeas x₀ G₂ H₂ t ω := by
  have hH' : ∀ᵐ z ∂(trimMeasure (μ := μ) T hBmeas), (H₁ z - H₂ z) ^ 2
      ≤ A * |l2ItoProcess T hBmeas x₀ G₁ H₁ z.1 z.2 - l2ItoProcess T hBmeas x₀ G₂ H₂ z.1 z.2|
        + 0 := by
    filter_upwards [hH] with z hz
    rwa [add_zero]
  have hfix : ∀ t ≤ T, (fun ω => l2ItoProcess T hBmeas x₀ G₁ H₁ t ω)
      =ᵐ[μ] fun ω => l2ItoProcess T hBmeas x₀ G₂ H₂ t ω := by
    intro t htT
    have hbound : ∀ n : ℕ, ∫ ω, |l2ItoProcess T hBmeas x₀ G₁ H₁ t ω
        - l2ItoProcess T hBmeas x₀ G₂ H₂ t ω| ∂μ ≤ (1 + A * t) * (1 / ((n : ℝ) + 1)) := by
      intro n
      have hb : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h := yamada_estimate hB T hBmeas hBcont (yamadaParamsOf _ _ hb hm) hκ hA le_rfl
        G₁ H₁ G₂ H₂ hG₁ hG₂ hH' htT
      rw [yamada_m_yamadaParamsOf, yamadaParamsOf_b, zero_div, add_zero] at h
      calc _ ≤ _ := h
        _ = (1 + A * t) * (1 / ((n : ℝ) + 1)) := by ring
    have hlim : Tendsto (fun n : ℕ => (1 + A * t) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 + A * (t : ℝ))
    have h0 : ∫ ω, |l2ItoProcess T hBmeas x₀ G₁ H₁ t ω
        - l2ItoProcess T hBmeas x₀ G₂ H₂ t ω| ∂μ ≤ 0 := ge_of_tendsto' hlim hbound
    have hint : Integrable (fun ω => |l2ItoProcess T hBmeas x₀ G₁ H₁ t ω
        - l2ItoProcess T hBmeas x₀ G₂ H₂ t ω|) μ := by
      have h1 := integrable_comp_at hB T hBmeas hBcont x₀ G₁ H₁
        (f := id) (f' := fun _ => 1) (fun x => hasDerivAt_id x) (C₁ := 1) (fun _ => by norm_num) htT
      have h2 := integrable_comp_at hB T hBmeas hBcont x₀ G₂ H₂
        (f := id) (f' := fun _ => 1) (fun x => hasDerivAt_id x) (C₁ := 1) (fun _ => by norm_num) htT
      refine (h1.sub h2).abs.congr (ae_of_all _ fun ω => ?_)
      simp only [Pi.sub_apply, id]
      congr 1
      ring
    have hzero := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _) hint).1
      (le_antisymm h0 (integral_nonneg fun ω => abs_nonneg _))
    filter_upwards [hzero] with ω hω
    exact sub_eq_zero.1 (abs_eq_zero.1 hω)
  exact ae_forall_eq_of_continuousOn T (ae_continuousOn_l2ItoProcess hB T hBmeas hBcont x₀ G₁ H₁)
    (ae_continuousOn_l2ItoProcess hB T hBmeas hBcont x₀ G₂ H₂) hfix

end Yamada

/-! ## The CIR specialisations -/

theorem cirSqrtDiffusion_sub_sq_le (p : Parameters) (x y : ℝ) :
    (cirSqrtDiffusion p x - cirSqrtDiffusion p y) ^ 2 ≤ p.xi ^ 2 * |x - y| := by
  unfold cirSqrtDiffusion
  rw [← mul_sub, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact (sqrt_holder_sq _ _ (le_max_right _ _) (le_max_right _ _)).trans
    (abs_max_sub_max_le_abs x y 0)

theorem cirRegularizedDiffusion_cross_sq_le (p : Parameters) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hδ : 0 ≤ δ) (x y : ℝ) :
    (cirRegularizedDiffusion p ε x - cirRegularizedDiffusion p δ y) ^ 2
      ≤ 2 * p.xi ^ 2 * |x - y| + 4 * p.xi ^ 2 * (ε + δ) := by
  unfold cirRegularizedDiffusion
  rw [← mul_sub, mul_pow]
  have h := cirApproxDiff_cross_sq_le hε hδ x y
  have hx := sq_nonneg p.xi
  nlinarith

section CIR
variable (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
  (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)

include hB hBcont in
/-- **Pathwise uniqueness for the CIR equation** `dV = κ(θ - V) dt + ξ √(V⁺) dB`. -/
theorem cir_pathwise_unique (p : Parameters) (hκ : 0 ≤ p.kappa) {v₀ : ℝ}
    (G₁ H₁ G₂ H₂ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hG₁ : ⇑G₁ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirDrift p (l2ItoProcess T hBmeas v₀ G₁ H₁ z.1 z.2))
    (hG₂ : ⇑G₂ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirDrift p (l2ItoProcess T hBmeas v₀ G₂ H₂ z.1 z.2))
    (hH₁ : ⇑H₁ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirSqrtDiffusion p (l2ItoProcess T hBmeas v₀ G₁ H₁ z.1 z.2))
    (hH₂ : ⇑H₂ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirSqrtDiffusion p (l2ItoProcess T hBmeas v₀ G₂ H₂ z.1 z.2)) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T,
      l2ItoProcess T hBmeas v₀ G₁ H₁ t ω = l2ItoProcess T hBmeas v₀ G₂ H₂ t ω :=
  pathwise_unique_of_yamada hB T hBmeas hBcont hκ (sq_nonneg p.xi) G₁ H₁ G₂ H₂
    (by simpa only [cirDrift] using hG₁) (by simpa only [cirDrift] using hG₂) (by
      filter_upwards [hH₁, hH₂] with z h1 h2
      rw [h1, h2]
      exact cirSqrtDiffusion_sub_sq_le p _ _)

include hB hBcont in
/-- **Cauchy estimate** for two regularized CIR solutions. -/
theorem cir_regularized_cauchy (p : Parameters) (hκ : 0 ≤ p.kappa) {ε δ v₀ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (q : YamadaParams)
    (G₁ H₁ G₂ H₂ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hG₁ : ⇑G₁ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirDrift p (l2ItoProcess T hBmeas v₀ G₁ H₁ z.1 z.2))
    (hG₂ : ⇑G₂ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirDrift p (l2ItoProcess T hBmeas v₀ G₂ H₂ z.1 z.2))
    (hH₁ : ⇑H₁ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirRegularizedDiffusion p ε (l2ItoProcess T hBmeas v₀ G₁ H₁ z.1 z.2))
    (hH₂ : ⇑H₂ =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z => cirRegularizedDiffusion p δ (l2ItoProcess T hBmeas v₀ G₂ H₂ z.1 z.2))
    {t : ℝ≥0} (htT : t ≤ T) :
    ∫ ω, |l2ItoProcess T hBmeas v₀ G₁ H₁ t ω - l2ItoProcess T hBmeas v₀ G₂ H₂ t ω| ∂μ
      ≤ q.b + (2 * p.xi ^ 2 / yamadaM q
        + 4 * p.xi ^ 2 * (ε + δ) / (yamadaM q * q.a)) * t :=
  yamada_estimate hB T hBmeas hBcont q hκ (by positivity) (by positivity) G₁ H₁ G₂ H₂
    (by simpa only [cirDrift] using hG₁) (by simpa only [cirDrift] using hG₂) (by
      filter_upwards [hH₁, hH₂] with z h1 h2
      rw [h1, h2]
      exact cirRegularizedDiffusion_cross_sq_le p hε hδ _ _) htT

end CIR

end MathFin.Heston
