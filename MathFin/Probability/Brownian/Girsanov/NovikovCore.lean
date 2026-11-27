/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Novikov's criterion: the analytic core (unit mean of the limit exponential)

Novikov's condition makes the Doléans exponential `Z = exp(M − ½A)` a unit-mean variable. This
file proves the *analytic* half of that statement, with no stochastic calculus in it: a statement
about sequences of real random variables `Mₙ → M'`, `Aₙ → A'` whose exponentials
`exp(c·Mₙ − c²/2·Aₙ)` all have unit mean (for every real `c`). These are the hypotheses the
bounded Girsanov theorem supplies for the bounded truncations `cθₙ` of an unbounded integrand
(`integral_ZTpred_eq_one`); `NovikovIto` checks that this file's hypotheses are met by those
truncations of a predictable `θ` and concludes `E exp(−∫θ dB − ½∫θ² ds) = 1`
(`integral_contDoleansExp_eq_one_of_novikov`).

The argument is the classical "`p`-exponential" trick (Karatzas–Shreve §3.5; Revuz–Yor §VIII.1),
run on the truncations so that no stopping times are needed:

1. **Fatou.** `E exp(c·M' − c²/2·A') ≤ 1` for every `c` (`lintegral_limit_le_one`).
2. **Hölder for exponentials.** `E exp(a·U + b·V) ≤ (E eᵁ)ᵃ (E eⱽ)ᵇ` for `a + b = 1`
   (`lintegral_ofReal_exp_add_le`).
3. **A uniform `Lʳ` bound.** For `0 < p < 1` and `r = 1 + (1−p)²/3`, the densities
   `exp(p·Mₙ − p²/2·Aₙ)` are bounded in `Lʳ` by `K^{1−p}`, `K = E exp(½A')`
   (`lintegral_rpow_exp_le`); this is where Novikov's condition is used.
4. **Unit mean at `p < 1`.** A truncation estimate (`E(Z − min(Z,R)) ≤ R^{1−r} E Zʳ`) turns a.e.
   convergence plus the `Lʳ` bound into `1 ≤ E exp(p·M' − p²/2·A')`
   (`one_le_lintegral_of_tendsto_of_rpow_le`).
5. **`p ↑ 1`.** Hölder with weights `p²`, `1 − p²` and a second Hölder step bound
   `1 ≤ (E Z)^{p²}·K^{(1−p²)/2}`; letting `p → 1` gives `1 ≤ E Z`.

## Main results

* `lintegral_ofReal_exp_add_le`: Hölder's inequality for exponentials of two measurable functions.
* `lintegral_limit_le_one`: Fatou, `E exp(c·M' − c²/2·A') ≤ 1` for the a.e. limit.
* `lintegral_exp_eq_one_of_novikov`: if `E exp(½A') < ∞`, `0 ≤ Aₙ ≤ A'`, `Mₙ → M'`, `Aₙ → A'` a.e.,
  and every `exp(c·Mₙ − c²/2·Aₙ)` has unit mean, then `E exp(M' − ½A') = 1`.
* `integral_exp_eq_one_of_novikov`: the same as a Bochner integral.

## What is not here

This module is analytic: no Itô integral appears in it (the link is `NovikovIto`). It is not
Girsanov's theorem for unbounded `θ`: it does not show that `t ↦ Z_t` is a martingale and does not
transfer the exponential-martingale property to `Q = Z·μ`. Those steps are what remains of the
frontier node `thm:novikov-girsanov`.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991],
  §3.5
* [D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*][RevuzYor], §VIII.1

## Tags

Novikov condition, Doléans exponential, Girsanov theorem, Hölder inequality, uniform integrability,
Fatou lemma, MSC 60G44, MSC 60H05
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MathFin

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma measurable_ofReal_exp {g : Ω → ℝ} (hg : Measurable g) :
    Measurable fun ω ↦ ENNReal.ofReal (Real.exp (g ω)) :=
  (Real.measurable_exp.comp hg).ennreal_ofReal

/-- **Hölder's inequality for exponentials.** For weights `a, b > 0` with `a + b = 1` and measurable
`U, V`, `E exp(a·U + b·V) ≤ (E exp U)ᵃ · (E exp V)ᵇ` (as `ℝ≥0∞`-valued integrals). Hölder with the
conjugate exponents `1/a`, `1/b` applied to `exp(a·U)` and `exp(b·V)`. -/
theorem lintegral_ofReal_exp_add_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    {U V : Ω → ℝ} (hU : Measurable U) (hV : Measurable V) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * U ω + b * V ω)) ∂P ≤
      (∫⁻ ω, ENNReal.ofReal (Real.exp (U ω)) ∂P) ^ a *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (V ω)) ∂P) ^ b := by
  have hpq : (1 / a).HolderConjugate (1 / b) := Real.holderConjugate_one_div ha hb hab
  have hf : AEMeasurable (fun ω ↦ ENNReal.ofReal (Real.exp (a * U ω))) P :=
    (measurable_ofReal_exp (hU.const_mul a)).aemeasurable
  have hg : AEMeasurable (fun ω ↦ ENNReal.ofReal (Real.exp (b * V ω))) P :=
    (measurable_ofReal_exp (hV.const_mul b)).aemeasurable
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hf hg
  have hpow : ∀ {c : ℝ}, 0 < c → ∀ x : ℝ,
      ENNReal.ofReal (Real.exp (c * x)) ^ (1 / c) = ENNReal.ofReal (Real.exp x) := by
    intro c hc x
    have hc' : c ≠ 0 := hc.ne'
    have hc1 : 0 ≤ 1 / c := by positivity
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hc1, ← Real.exp_mul,
      show c * x * (1 / c) = x by field_simp]
  have hlhs : ∀ ω, ENNReal.ofReal (Real.exp (a * U ω + b * V ω)) =
      ENNReal.ofReal (Real.exp (a * U ω)) * ENNReal.ofReal (Real.exp (b * V ω)) := fun ω ↦ by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  simp only [Pi.mul_apply, hpow ha, hpow hb, one_div_one_div] at key
  simp_rw [hlhs]
  exact key

/-- **Fatou for the exponentials.** If `Mₙ → M'` and `Aₙ → A'` a.e. and every
`exp(c·Mₙ − c²/2·Aₙ)` has (`ℝ≥0∞`-)integral `1`, then `E exp(c·M' − c²/2·A') ≤ 1`. -/
theorem lintegral_limit_le_one {M A : ℕ → Ω → ℝ} {M' A' : Ω → ℝ}
    (hM : ∀ n, Measurable (M n)) (hA : ∀ n, Measurable (A n))
    (hmart : ∀ n (c : ℝ),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (c * M n ω - c ^ 2 / 2 * A n ω)) ∂P = 1)
    (hMlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ M n ω) atTop (𝓝 (M' ω)))
    (hAlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ A n ω) atTop (𝓝 (A' ω))) (c : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (c * M' ω - c ^ 2 / 2 * A' ω)) ∂P ≤ 1 := by
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (c * M' ω - c ^ 2 / 2 * A' ω)) ∂P
      = ∫⁻ ω, liminf (fun n ↦
          ENNReal.ofReal (Real.exp (c * M n ω - c ^ 2 / 2 * A n ω))) atTop ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hMlim, hAlim] with ω h1 h2
        exact (((ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp
          ((h1.const_mul c).sub (h2.const_mul (c ^ 2 / 2))))).liminf_eq).symm
    _ ≤ liminf (fun n ↦
          ∫⁻ ω, ENNReal.ofReal (Real.exp (c * M n ω - c ^ 2 / 2 * A n ω)) ∂P) atTop :=
        lintegral_liminf_le fun n ↦
          measurable_ofReal_exp (((hM n).const_mul c).sub ((hA n).const_mul _))
    _ = 1 := by simp only [hmart]; exact liminf_const 1

/-- The pointwise truncation estimate `z ≤ min(z,R) + R^{-(r-1)}·zʳ` for `z ≥ 0`, `R > 0`,
`r > 1`. -/
lemma le_min_add_rpow_neg {z R r : ℝ} (hz : 0 ≤ z) (hR : 0 < R) (hr : 1 < r) :
    z ≤ min z R + R ^ (-(r - 1)) * z ^ r := by
  have hnn : 0 ≤ R ^ (-(r - 1)) * z ^ r := by positivity
  rcases le_total z R with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]
    have hzpos : 0 < z := hR.trans_le h
    have h1 : R ^ (r - 1) ≤ z ^ (r - 1) := Real.rpow_le_rpow hR.le h (by linarith)
    have hRpos : 0 < R ^ (r - 1) := Real.rpow_pos_of_pos hR _
    have h2 : z ^ r = z ^ (r - 1) * z := by
      rw [← Real.rpow_add_one hzpos.ne', sub_add_cancel]
    have h3 : R ^ (-(r - 1)) = (R ^ (r - 1))⁻¹ := Real.rpow_neg hR.le _
    have h4 : 1 ≤ (R ^ (r - 1))⁻¹ * z ^ (r - 1) := by
      rw [← div_eq_inv_mul, one_le_div hRpos]; exact h1
    rw [h3, h2]
    nlinarith [mul_le_mul_of_nonneg_right h4 hzpos.le]

/-- **A unit-mean sequence bounded in `Lʳ` (`r > 1`) keeps mean `≥ 1` in an a.e. limit.** If
`zₙ ≥ 0` has `E zₙ = 1`, `E zₙʳ ≤ C < ∞`, and `zₙ → g` a.e., then `1 ≤ E g` (with `E g = 1` once
Fatou is added). The truncation `E zₙ ≤ E min(zₙ,R) + R^{1-r}·C` is passed to the limit by dominated
convergence, then `R → ∞`. -/
theorem one_le_lintegral_of_tendsto_of_rpow_le [IsProbabilityMeasure P] {z : ℕ → Ω → ℝ}
    {g : Ω → ℝ} (hz : ∀ n, Measurable (z n)) (hz0 : ∀ n ω, 0 ≤ z n ω)
    (h1 : ∀ n, ∫⁻ ω, ENNReal.ofReal (z n ω) ∂P = 1) {r : ℝ} (hr : 1 < r) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hbd : ∀ n, ∫⁻ ω, ENNReal.ofReal (z n ω) ^ r ∂P ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ z n ω) atTop (𝓝 (g ω))) :
    1 ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂P := by
  have key : ∀ R : ℝ, 0 < R →
      1 ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂P + ENNReal.ofReal (R ^ (-(r - 1))) * C := by
    intro R hR
    have hFm : ∀ n, Measurable fun ω ↦ ENNReal.ofReal (min (z n ω) R) := fun n ↦
      ((hz n).min measurable_const).ennreal_ofReal
    have hbound : ∀ n, 1 ≤ ∫⁻ ω, ENNReal.ofReal (min (z n ω) R) ∂P
        + ENNReal.ofReal (R ^ (-(r - 1))) * C := by
      intro n
      calc (1 : ℝ≥0∞) = ∫⁻ ω, ENNReal.ofReal (z n ω) ∂P := (h1 n).symm
        _ ≤ ∫⁻ ω, (ENNReal.ofReal (min (z n ω) R)
              + ENNReal.ofReal (R ^ (-(r - 1))) * ENNReal.ofReal (z n ω) ^ r) ∂P := by
          refine lintegral_mono fun ω ↦ ?_
          have hRr : 0 ≤ R ^ (-(r - 1)) := Real.rpow_nonneg hR.le _
          have hzr : 0 ≤ z n ω ^ r := Real.rpow_nonneg (hz0 n ω) _
          have hr0 : 0 ≤ r := by linarith
          rw [ENNReal.ofReal_rpow_of_nonneg (hz0 n ω) hr0,
            ← ENNReal.ofReal_mul hRr, ← ENNReal.ofReal_add (le_min (hz0 n ω) hR.le)
              (mul_nonneg hRr hzr)]
          exact ENNReal.ofReal_le_ofReal (le_min_add_rpow_neg (hz0 n ω) hR hr)
        _ = ∫⁻ ω, ENNReal.ofReal (min (z n ω) R) ∂P
              + ENNReal.ofReal (R ^ (-(r - 1))) * ∫⁻ ω, ENNReal.ofReal (z n ω) ^ r ∂P := by
          rw [lintegral_add_left (hFm n),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ∫⁻ ω, ENNReal.ofReal (min (z n ω) R) ∂P
              + ENNReal.ofReal (R ^ (-(r - 1))) * C :=
          add_le_add_left (mul_le_mul_left' (hbd n) _) _
    have hmin_lim : Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (min (z n ω) R) ∂P) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (min (g ω) R) ∂P)) := by
      refine tendsto_lintegral_of_dominated_convergence (fun _ ↦ ENNReal.ofReal R) hFm
        (fun n ↦ ae_of_all _ fun ω ↦ ENNReal.ofReal_le_ofReal (min_le_right _ _)) (by simp) ?_
      filter_upwards [hlim] with ω hω
      exact (ENNReal.continuous_ofReal.tendsto _).comp (hω.min tendsto_const_nhds)
    have hge := ge_of_tendsto (hmin_lim.add_const (ENNReal.ofReal (R ^ (-(r - 1))) * C))
      (Eventually.of_forall hbound)
    exact hge.trans (add_le_add_right
      (lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _)) _)
  have h0 : Tendsto (fun R : ℝ ↦ ENNReal.ofReal (R ^ (-(r - 1)))) atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_rpow_neg_atTop (by linarith : 0 < r - 1))
    simpa using this
  have hδ : Tendsto (fun R : ℝ ↦ ENNReal.ofReal (R ^ (-(r - 1))) * C) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hC)
  have := ge_of_tendsto (hδ.const_add (∫⁻ ω, ENNReal.ofReal (g ω) ∂P))
    ((eventually_gt_atTop (0 : ℝ)).mono key)
  simpa using this

/-- **The uniform `Lʳ` bound at `p < 1` (the use of Novikov's condition).** Let `A ≥ 0`,
`0 < p < 1`, and `r > 1` with `p·r·(r−p) ≤ 1−p`. If `E exp(r·M − r²/2·A) ≤ 1` and
`E exp(½A) ≤ K`, then `E (exp(p·M − p²/2·A))ʳ ≤ K^{1−p}`. Hölder with weights `p`, `1−p` splits
`exp(r p M − r p²/2 A) = (exp(r M − r²/2 A))ᵖ · (exp(c A))^{1−p}`, `c ≤ ½`. -/
theorem lintegral_rpow_exp_le {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hr1 : 1 < r)
    (hr : p * r * (r - p) ≤ 1 - p) {M A : Ω → ℝ} (hM : Measurable M) (hA : Measurable A)
    (hA0 : ∀ ω, 0 ≤ A ω) {K : ℝ≥0∞}
    (h1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (r * M ω - r ^ 2 / 2 * A ω)) ∂P ≤ 1)
    (hK : ∫⁻ ω, ENNReal.ofReal (Real.exp (2⁻¹ * A ω)) ∂P ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (p * M ω - p ^ 2 / 2 * A ω)) ^ r ∂P ≤ K ^ (1 - p) := by
  have hb : 0 < 1 - p := by linarith
  have hb' : (1 - p) ≠ 0 := hb.ne'
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = p * r * (r - p) / 2 / (1 - p) := ⟨_, rfl⟩
  have hcm : (1 - p) * c = p * r * (r - p) / 2 := by
    rw [hcdef]
    first | (field_simp; done) | (field_simp; ring)
  have hc_le : c ≤ 2⁻¹ :=
    le_of_mul_le_mul_left (by rw [hcm]; linarith) hb
  have hH := lintegral_ofReal_exp_add_le (P := P) hp0 hb (by ring : p + (1 - p) = 1)
    (U := fun ω ↦ r * M ω - r ^ 2 / 2 * A ω) (V := fun ω ↦ c * A ω)
    ((hM.const_mul r).sub (hA.const_mul _)) (hA.const_mul c)
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (p * M ω - p ^ 2 / 2 * A ω)) ^ r =
      ENNReal.ofReal (Real.exp (p * (r * M ω - r ^ 2 / 2 * A ω) + (1 - p) * (c * A ω))) := by
    intro ω
    have hr0 : 0 ≤ r := by linarith
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hr0, ← Real.exp_mul,
      show (p * M ω - p ^ 2 / 2 * A ω) * r
        = p * (r * M ω - r ^ 2 / 2 * A ω) + (1 - p) * (c * A ω) by
          linear_combination (-(A ω)) * hcm]
  have e1 : (∫⁻ ω, ENNReal.ofReal (Real.exp (r * M ω - r ^ 2 / 2 * A ω)) ∂P) ^ p ≤ 1 :=
    (ENNReal.rpow_le_rpow h1 hp0.le).trans_eq (ENNReal.one_rpow p)
  have e2 : (∫⁻ ω, ENNReal.ofReal (Real.exp (c * A ω)) ∂P) ^ (1 - p) ≤ K ^ (1 - p) :=
    ENNReal.rpow_le_rpow
      ((lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hc_le (hA0 ω)))).trans hK) hb.le
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (p * M ω - p ^ 2 / 2 * A ω)) ^ r ∂P
      = ∫⁻ ω, ENNReal.ofReal
          (Real.exp (p * (r * M ω - r ^ 2 / 2 * A ω) + (1 - p) * (c * A ω))) ∂P :=
        lintegral_congr hpt
    _ ≤ _ := hH
    _ ≤ 1 * K ^ (1 - p) := mul_le_mul' e1 e2
    _ = K ^ (1 - p) := one_mul _

/-- **Novikov's criterion, analytic core.** Let `Mₙ → M'`, `Aₙ → A'` almost surely, with
`0 ≤ Aₙ` and `Aₙ ≤ A'` almost surely, and `E exp(½A') < ∞` (Novikov's condition), and suppose every
`exp(c·Mₙ − c²/2·Aₙ)` has unit mean, `c ∈ ℝ`. Then the limit exponential has unit mean:
`E exp(M' − ½A') = 1`. (This is a statement about real random variables; it is not the stochastic
statement, which needs `Mₙ`, `Aₙ` to be the truncated Itô integrals and quadratic variations.) -/
theorem lintegral_exp_eq_one_of_novikov [IsProbabilityMeasure P] {M A : ℕ → Ω → ℝ}
    {M' A' : Ω → ℝ} (hM : ∀ n, Measurable (M n)) (hA : ∀ n, Measurable (A n))
    (hM' : Measurable M') (hA' : Measurable A') (hA0 : ∀ n ω, 0 ≤ A n ω)
    (hAle : ∀ᵐ ω ∂P, ∀ n, A n ω ≤ A' ω)
    (hmart : ∀ n (c : ℝ),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (c * M n ω - c ^ 2 / 2 * A n ω)) ∂P = 1)
    (hMlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ M n ω) atTop (𝓝 (M' ω)))
    (hAlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ A n ω) atTop (𝓝 (A' ω)))
    (hNov : ∫⁻ ω, ENNReal.ofReal (Real.exp (2⁻¹ * A' ω)) ∂P ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (M' ω - 2⁻¹ * A' ω)) ∂P = 1 := by
  have hA'0 : ∀ᵐ ω ∂P, 0 ≤ A' ω := hAle.mono fun ω h ↦ (hA0 0 ω).trans (h 0)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ≥0∞,
      K = ∫⁻ ω, ENNReal.ofReal (Real.exp (2⁻¹ * A' ω)) ∂P := ⟨_, rfl⟩
  rw [← hKdef] at hNov
  have hKle : ∀ n, ∫⁻ ω, ENNReal.ofReal (Real.exp (2⁻¹ * A n ω)) ∂P ≤ K := fun n ↦ by
    rw [hKdef]
    refine lintegral_mono_ae (hAle.mono fun ω h ↦ ?_)
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (h n) (by norm_num)))
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    calc (1 : ℝ≥0∞) = ∫⁻ _ : Ω, 1 ∂P := by simp
      _ ≤ _ := lintegral_mono_ae (hA'0.mono fun ω h ↦
        ENNReal.one_le_ofReal.mpr (Real.one_le_exp (mul_nonneg (by norm_num) h)))
  have hK0 : K ≠ 0 := (zero_lt_one.trans_le hK1).ne'
  have hfat := lintegral_limit_le_one hM hA hmart hMlim hAlim
  have hI : ∫⁻ ω, ENNReal.ofReal (Real.exp (M' ω - 2⁻¹ * A' ω)) ∂P ≤ 1 := by
    simpa only [one_mul, one_pow, one_div] using hfat 1
  refine le_antisymm hI ?_
  -- unit mean of `exp(p M' - p²/2 A')` for `0 < p < 1`
  have hlow : ∀ p : ℝ, 0 < p → p < 1 →
      1 ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (p * M' ω - p ^ 2 / 2 * A' ω)) ∂P := by
    intro p hp0 hp1
    have hu : 0 < 1 - p := by linarith
    obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = 1 + (1 - p) ^ 2 / 3 := ⟨_, rfl⟩
    have hr1 : 1 < r := by rw [hrdef]; have := pow_pos hu 2; linarith
    have hr : p * r * (r - p) ≤ 1 - p := by
      rw [hrdef]
      nlinarith [pow_pos hu 2, pow_pos hu 4, pow_pos hu 5]
    refine one_le_lintegral_of_tendsto_of_rpow_le
      (z := fun n ω ↦ Real.exp (p * M n ω - p ^ 2 / 2 * A n ω))
      (g := fun ω ↦ Real.exp (p * M' ω - p ^ 2 / 2 * A' ω))
      (fun n ↦ Real.measurable_exp.comp (((hM n).const_mul p).sub ((hA n).const_mul _)))
      (fun n ω ↦ (Real.exp_pos _).le) (fun n ↦ hmart n p) hr1
      (C := K ^ (1 - p)) (ENNReal.rpow_ne_top_of_nonneg hu.le hNov)
      (fun n ↦ lintegral_rpow_exp_le hp0 hp1 hr1 hr (hM n) (hA n) (hA0 n)
        (le_of_eq (hmart n r)) (hKle n)) ?_
    filter_upwards [hMlim, hAlim] with ω h1 h2
    exact (Real.continuous_exp.tendsto _).comp
      ((h1.const_mul p).sub (h2.const_mul (p ^ 2 / 2)))
  -- Hölder with weights `p²`, `1 - p²`, then a second Hölder step for `exp(s M')`
  have hup : ∀ p : ℝ, 0 < p → p < 1 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (p * M' ω - p ^ 2 / 2 * A' ω)) ∂P ≤
        (∫⁻ ω, ENNReal.ofReal (Real.exp (M' ω - 2⁻¹ * A' ω)) ∂P) ^ (p ^ 2) *
          (K ^ (2⁻¹ : ℝ)) ^ (1 - p ^ 2) := by
    intro p hp0 hp1
    have hp2 : 0 < p ^ 2 := by positivity
    have hq : 0 < 1 - p ^ 2 := by nlinarith [mul_pos hp0 (sub_pos.mpr hp1)]
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = p / (1 + p) := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    have hs1 : s ≤ 2⁻¹ := by rw [hs, div_le_iff₀ (by positivity)]; linarith
    have hsm : (1 - p ^ 2) * s = p - p ^ 2 := by
      have h1p : (1 + p) ≠ 0 := by positivity
      rw [hs]
      first | (field_simp; done) | (field_simp; ring)
    have hs2 : 2 * s ^ 2 ≤ 2⁻¹ := by nlinarith
    have hV : ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * s ^ 2 * A' ω)) ∂P ≤ K := by
      rw [hKdef]
      exact lintegral_mono_ae (hA'0.mono fun ω h ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hs2 h)))
    have hexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (s * M' ω)) ∂P ≤ K ^ (2⁻¹ : ℝ) := by
      have hH := lintegral_ofReal_exp_add_le (P := P) (a := 2⁻¹) (b := 2⁻¹)
        (by norm_num) (by norm_num) (by norm_num)
        (U := fun ω ↦ 2 * s * M' ω - (2 * s) ^ 2 / 2 * A' ω)
        (V := fun ω ↦ 2 * s ^ 2 * A' ω)
        ((hM'.const_mul _).sub (hA'.const_mul _)) (hA'.const_mul _)
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp (s * M' ω)) ∂P
          = ∫⁻ ω, ENNReal.ofReal (Real.exp (2⁻¹ * (2 * s * M' ω - (2 * s) ^ 2 / 2 * A' ω)
              + 2⁻¹ * (2 * s ^ 2 * A' ω))) ∂P :=
            lintegral_congr fun ω ↦ by
              rw [show s * M' ω = 2⁻¹ * (2 * s * M' ω - (2 * s) ^ 2 / 2 * A' ω)
                + 2⁻¹ * (2 * s ^ 2 * A' ω) by ring]
        _ ≤ _ := hH
        _ ≤ 1 ^ (2⁻¹ : ℝ) * K ^ (2⁻¹ : ℝ) :=
            mul_le_mul' (ENNReal.rpow_le_rpow (hfat (2 * s)) (by norm_num))
              (ENNReal.rpow_le_rpow hV (by norm_num))
        _ = K ^ (2⁻¹ : ℝ) := by rw [ENNReal.one_rpow, one_mul]
    have hH2 := lintegral_ofReal_exp_add_le (P := P) hp2 hq (by ring : p ^ 2 + (1 - p ^ 2) = 1)
      (U := fun ω ↦ M' ω - 2⁻¹ * A' ω) (V := fun ω ↦ s * M' ω)
      (hM'.sub (hA'.const_mul _)) (hM'.const_mul s)
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (p * M' ω - p ^ 2 / 2 * A' ω)) ∂P
        = ∫⁻ ω, ENNReal.ofReal (Real.exp (p ^ 2 * (M' ω - 2⁻¹ * A' ω)
            + (1 - p ^ 2) * (s * M' ω))) ∂P :=
          lintegral_congr fun ω ↦ by
            rw [show p * M' ω - p ^ 2 / 2 * A' ω
              = p ^ 2 * (M' ω - 2⁻¹ * A' ω) + (1 - p ^ 2) * (s * M' ω) by
                linear_combination (-(M' ω)) * hsm]
      _ ≤ _ := hH2
      _ ≤ _ := mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hexp hq.le)
  generalize hIdef : ∫⁻ ω, ENNReal.ofReal (Real.exp (M' ω - 2⁻¹ * A' ω)) ∂P = I at hI hup ⊢
  have hIne : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hI
  have hk : 0 < K.toReal := ENNReal.toReal_pos hK0 hNov
  have hb : 0 < K.toReal ^ (2⁻¹ : ℝ) := Real.rpow_pos_of_pos hk _
  have hreal : ∀ p : ℝ, 0 < p → p < 1 →
      1 ≤ I.toReal ^ (p ^ 2) * (K.toReal ^ (2⁻¹ : ℝ)) ^ (1 - p ^ 2) := by
    intro p hp0 hp1
    have hq : 0 ≤ 1 - p ^ 2 := by nlinarith [mul_pos hp0 (sub_pos.mpr hp1)]
    have hfin : I ^ (p ^ 2) * (K ^ (2⁻¹ : ℝ)) ^ (1 - p ^ 2) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hIne)
        (ENNReal.rpow_ne_top_of_nonneg hq (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hNov))
    have h := ENNReal.toReal_mono hfin ((hlow p hp0 hp1).trans (hup p hp0 hp1))
    simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_rpow] at h
    exact h
  have h1le : 1 ≤ I.toReal := by
    rcases eq_or_ne I.toReal 0 with h0 | h0
    · exfalso
      have h := hreal (1 / 2) (by norm_num) (by norm_num)
      rw [h0, Real.zero_rpow (x := ((1 : ℝ) / 2) ^ 2) (by norm_num)] at h
      norm_num at h
    · have hGc : Continuous fun p : ℝ ↦ I.toReal ^ (p ^ 2) * (K.toReal ^ (2⁻¹ : ℝ)) ^ (1 - p ^ 2) :=
        (Continuous.rpow (f := fun _ : ℝ ↦ I.toReal) (g := fun p : ℝ ↦ p ^ 2) continuous_const
          (continuous_pow 2) fun _ ↦ Or.inl h0).mul
          (Continuous.rpow (f := fun _ : ℝ ↦ K.toReal ^ (2⁻¹ : ℝ))
            (g := fun p : ℝ ↦ 1 - p ^ 2) continuous_const
            (continuous_const.sub (continuous_pow 2)) fun _ ↦ Or.inl hb.ne')
      have hlim := hGc.continuousAt (x := 1) |>.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
      have hev : ∀ᶠ p in 𝓝[<] (1 : ℝ),
          1 ≤ I.toReal ^ (p ^ 2) * (K.toReal ^ (2⁻¹ : ℝ)) ^ (1 - p ^ 2) :=
        Filter.eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
          fun p hp ↦ hreal p hp.1 hp.2
      have := ge_of_tendsto hlim hev
      simpa using this
  have : (1 : ℝ≥0∞).toReal ≤ I.toReal := by simpa using h1le
  exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hIne).mp this

/-- **Novikov's criterion, analytic core, as a Bochner integral:** under the hypotheses of
`lintegral_exp_eq_one_of_novikov`, `∫ exp(M' − ½A') dP = 1`. -/
theorem integral_exp_eq_one_of_novikov [IsProbabilityMeasure P] {M A : ℕ → Ω → ℝ}
    {M' A' : Ω → ℝ} (hM : ∀ n, Measurable (M n)) (hA : ∀ n, Measurable (A n))
    (hM' : Measurable M') (hA' : Measurable A') (hA0 : ∀ n ω, 0 ≤ A n ω)
    (hAle : ∀ᵐ ω ∂P, ∀ n, A n ω ≤ A' ω)
    (hmart : ∀ n (c : ℝ),
      ∫⁻ ω, ENNReal.ofReal (Real.exp (c * M n ω - c ^ 2 / 2 * A n ω)) ∂P = 1)
    (hMlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ M n ω) atTop (𝓝 (M' ω)))
    (hAlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ A n ω) atTop (𝓝 (A' ω)))
    (hNov : ∫⁻ ω, ENNReal.ofReal (Real.exp (2⁻¹ * A' ω)) ∂P ≠ ⊤) :
    ∫ ω, Real.exp (M' ω - 2⁻¹ * A' ω) ∂P = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ (Real.exp_pos _).le)
    (Real.measurable_exp.comp (hM'.sub (hA'.const_mul _))).aestronglyMeasurable,
    lintegral_exp_eq_one_of_novikov hM hA hM' hA' hA0 hAle hmart hMlim hAlim hNov,
    ENNReal.toReal_one]

end MathFin
