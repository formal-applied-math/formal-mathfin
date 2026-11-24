/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.CommonItoFormula
public import MathFin.Models.StochVol.Heston.LaplaceGenerator

/-!
# Calculus for affine Itô test functions

Generic facts: compactly supported `C²` functions are Itô test functions, and partial
derivatives can be read off from derivatives along coordinate lines.  Riccati facts: the
global Laplace coefficients `C, D` are `C²` on a neighbourhood `(-δ, ∞)` of `[0, ∞)`.

## Main results

* `exists_riccatiDenominator_ne_zero`
* `contDiffAt_globalLaplaceD`
* `contDiffOn_globalLaplace`

## References

* [S. Heston, *A closed-form solution for options with stochastic volatility*][Heston1993]

## Tags

Heston model, stochastic volatility, MSC 91G20, JEL G13
-/

@[expose] public section

noncomputable section
namespace MathFin.Heston
open MathFin.FilteredIto
namespace CommonAffine

open MeasureTheory Filter Topology Set
open MathFin.FilteredIto.CommonIto
open scoped NNReal ENNReal

/-! ### Generic facts -/

section Generic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Operator norm of a bilinear form on `ι → ℝ` (sup norm) is at most the sum of the absolute
values of its entries. -/
lemma opNorm_bilinear_le_sum (A : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ i, ∑ k, |A (Pi.single i 1) (Pi.single k 1)| := by
  have hM : 0 ≤ ∑ i, ∑ k, |A (Pi.single i 1) (Pi.single k 1)| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (norm_nonneg v)) fun w => ?_
  have hexp : A v w = ∑ i, ∑ k, v i * w k * A (Pi.single i 1) (Pi.single k 1) := by
    rw [clm_apply_eq_sum A v, _root_.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.smul_apply, clm_apply_eq_sum (A (Pi.single i 1)) w, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_eq_mul]
    ring
  rw [hexp, Real.norm_eq_abs]
  calc |∑ i, ∑ k, v i * w k * A (Pi.single i 1) (Pi.single k 1)|
      ≤ ∑ i, ∑ k, |v i * w k * A (Pi.single i 1) (Pi.single k 1)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ k, ‖v‖ * ‖w‖ * |A (Pi.single i 1) (Pi.single k 1)| := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_mul]
        have hv : |v i| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
        have hw : |w k| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w k
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hv hw (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
    _ = (∑ i, ∑ k, |A (Pi.single i 1) (Pi.single k 1)|) * ‖v‖ * ‖w‖ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

/-- A compactly supported `C²` function is an Itô test function. -/
theorem itoTest_of_hasCompactSupport {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ∃ C₁ C₂, ItoTest f C₁ C₂ := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right one_add_one_eq_two.le
  have hc1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ f)) := h1.continuous_fderiv one_ne_zero
  have hs1 : HasCompactSupport (fderiv ℝ f) := hc.fderiv (𝕜 := ℝ)
  have hs2 : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) := hs1.fderiv (𝕜 := ℝ)
  obtain ⟨C₁, hC₁⟩ := hs1.exists_bound_of_continuous hc1
  -- the matrix of second partial derivatives
  set Hm : (ι → ℝ) → (ι × ι → ℝ) := fun y ik ↦ pd2 f ik.1 ik.2 y with hHm
  have hHc : Continuous Hm := continuous_pi fun ik =>
    (hc2.clm_apply continuous_const).clm_apply continuous_const
  have hHs : HasCompactSupport Hm := by
    refine hs2.mono fun y hy => ?_
    intro h0
    apply hy
    funext ik
    simp only [hHm, pd2, h0, _root_.zero_apply, Pi.zero_apply]
  obtain ⟨K, hK⟩ := hHs.exists_bound_of_continuous hHc
  have hentry : ∀ y i k, |pd2 f i k y| ≤ K := fun y i k => by
    have := norm_le_pi_norm (Hm y) (i, k)
    rw [Real.norm_eq_abs] at this
    exact this.trans (hK y)
  set N : ℝ := (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) with hN
  have hsum_const : ∀ c : ℝ, ∑ _i : ι, ∑ _k : ι, c = N * c := fun c => by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]; ring
  refine ⟨C₁, N * K, hf, hC₁, fun y => ?_, fun ε hε => ?_⟩
  · refine (opNorm_bilinear_le_sum _).trans ?_
    calc ∑ i, ∑ k, |fderiv ℝ (fderiv ℝ f) y (Pi.single i 1) (Pi.single k 1)|
        ≤ ∑ _i : ι, ∑ _k : ι, K :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hentry y i k
      _ = N * K := hsum_const K
  · have hu := hHs.uniformContinuous_of_continuous hHc
    have hN0 : 0 ≤ N := by positivity
    set ε' := ε / (N + 1) with hε'
    have hε'pos : 0 < ε' := div_pos hε (by linarith)
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 hu ε' hε'pos
    refine ⟨δ, hδ, fun y z hyz => ?_⟩
    have hd := h (show dist y z < δ by rwa [dist_eq_norm])
    have hcomp : ∀ i k, |pd2 f i k y - pd2 f i k z| < ε' := fun i k => by
      have := dist_le_pi_dist (Hm y) (Hm z) (i, k)
      rw [Real.dist_eq] at this
      exact lt_of_le_of_lt this hd
    refine (opNorm_bilinear_le_sum _).trans_lt ?_
    calc ∑ i, ∑ k, |(fderiv ℝ (fderiv ℝ f) y - fderiv ℝ (fderiv ℝ f) z)
          (Pi.single i 1) (Pi.single k 1)|
        = ∑ i, ∑ k, |pd2 f i k y - pd2 f i k z| := by
          simp only [_root_.sub_apply, pd2]
      _ ≤ ∑ _i : ι, ∑ _k : ι, ε' :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => (hcomp i k).le
      _ = N * ε' := hsum_const ε'
      _ < ε := by
          rw [hε', mul_div_assoc']
          rw [div_lt_iff₀ (by linarith)]
          nlinarith

lemma hasDerivAt_line (y : ι → ℝ) (i : ι) :
    HasDerivAt (fun s : ℝ ↦ y + s • (Pi.single i 1 : ι → ℝ)) (Pi.single i 1) 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : ι → ℝ)).const_add y

/-- A first partial derivative is the derivative along the coordinate line. -/
lemma pd_eq_of_hasDerivAt {f : (ι → ℝ) → ℝ} {y : ι → ℝ} (hf : DifferentiableAt ℝ f y) {i : ι}
    {d : ℝ} (h : HasDerivAt (fun s : ℝ ↦ f (y + s • (Pi.single i 1 : ι → ℝ))) d 0) :
    pd f i y = d := by
  have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) (hasDerivAt_line y i)
    (by simp)
  exact h2.unique h

/-- A second partial derivative `∂ᵢ∂ₖ f` is the derivative of `∂ₖ f` along the `i`-th line. -/
lemma pd2_eq_of_hasDerivAt {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {y : ι → ℝ} {i k : ι}
    {d : ℝ} (h : HasDerivAt (fun s : ℝ ↦ pd f k (y + s • (Pi.single i 1 : ι → ℝ))) d 0) :
    pd2 f i k y = d := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right one_add_one_eq_two.le
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y := (h1.differentiable one_ne_zero) y
  have hg : HasFDerivAt (fun y' ↦ fderiv ℝ f y' (Pi.single k 1))
      ((fderiv ℝ (fderiv ℝ f) y).flip (Pi.single k 1)) y := by
    have := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single k (1 : ℝ) : ι → ℝ) y)
    simpa using this
  have h2 := hg.comp_hasDerivAt_of_eq (x := (0 : ℝ)) (hasDerivAt_line y i) (by simp)
  have h3 := h2.unique h
  simpa [pd2, ContinuousLinearMap.flip_apply] using h3

end Generic

/-! ### Smoothness of the global Riccati coefficients -/

section Riccati
variable (p : Parameters) (u w : ℂ)

theorem contDiff_riccati_pair :
    ContDiff ℝ 2 (riccatiNumerator p u w) ∧ ContDiff ℝ 2 (riccatiDenominator p u w) := by
  set N := riccatiNumerator p u w with hNdef
  set Q := riccatiDenominator p u w with hQdef
  have hN : ∀ t, HasDerivAt N (laplaceB p u * N t + laplaceConstant u * Q t) t :=
    hasDerivAt_riccatiNumerator p u w
  have hQ : ∀ t, HasDerivAt Q (-(laplaceA p : ℂ) * N t) t := hasDerivAt_riccatiDenominator p u w
  have dN : deriv N = fun t ↦ laplaceB p u * N t + laplaceConstant u * Q t :=
    funext fun t => (hN t).deriv
  have dQ : deriv Q = fun t ↦ -(laplaceA p : ℂ) * N t := funext fun t => (hQ t).deriv
  have diffN : Differentiable ℝ N := fun t => (hN t).differentiableAt
  have diffQ : Differentiable ℝ Q := fun t => (hQ t).differentiableAt
  have c1N : ContDiff ℝ 1 N := contDiff_one_iff_deriv.2 ⟨diffN, by
    rw [dN]; exact (continuous_const.mul diffN.continuous).add (continuous_const.mul
          diffQ.continuous)⟩
  have c1Q : ContDiff ℝ 1 Q := contDiff_one_iff_deriv.2 ⟨diffQ, by
    rw [dQ]; exact continuous_const.mul diffN.continuous⟩
  refine ⟨?_, ?_⟩
  · have : ContDiff ℝ (1 + 1) N := contDiff_succ_iff_deriv.2 ⟨diffN, fun h => by simp at h, by
      rw [dN]; exact (contDiff_const.mul c1N).add (contDiff_const.mul c1Q)⟩
    rwa [one_add_one_eq_two] at this
  · have : ContDiff ℝ (1 + 1) Q := contDiff_succ_iff_deriv.2 ⟨diffQ, fun h => by simp at h, by
      rw [dQ]; exact contDiff_const.mul c1N⟩
    rwa [one_add_one_eq_two] at this

/-- The Riccati denominator does not vanish on a neighbourhood `(-δ, ∞)` of `[0, ∞)`. -/
theorem exists_riccatiDenominator_ne_zero (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1)
    (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0) :
    ∃ δ > 0, ∀ t : ℝ, -δ < t → riccatiDenominator p u w t ≠ 0 := by
  have hcont : Continuous (riccatiDenominator p u w) := (contDiff_riccati_pair p u w).2.continuous
  have h0 : riccatiDenominator p u w 0 ≠ 0 := by
    rw [riccatiDenominator_zero]; exact one_ne_zero
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.continuousAt.eventually_ne h0)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  rcases lt_or_ge t 0 with htn | htp
  · exact hball (by rw [Real.dist_eq, sub_zero, abs_of_neg htn]; linarith)
  · exact riccatiDenominator_ne_zero p u w hξ hρ hu hw t htp

theorem contDiffAt_globalLaplaceD {t : ℝ} (ht : riccatiDenominator p u w t ≠ 0) :
    ContDiffAt ℝ 2 (globalLaplaceD p u w) t := by
  have h := contDiff_riccati_pair p u w
  have hD : globalLaplaceD p u w =
      fun s ↦ riccatiNumerator p u w s * (riccatiDenominator p u w s)⁻¹ := by
    funext s; rw [globalLaplaceD, div_eq_mul_inv]
  rw [hD]
  exact h.1.contDiffAt.mul (h.2.contDiffAt.inv ht)

/-- On `(-δ, ∞)` both global Laplace coefficients are `C²`, and `C' = (r - q) u + κθ D`. -/
theorem contDiffOn_globalLaplace (hξ : 0 < p.xi) (hρ : |p.rho| ≤ 1)
    (hu : inClosedLaplaceStrip u) (hw : w.re ≤ 0) :
    ∃ δ > 0, ContDiffOn ℝ 2 (globalLaplaceD p u w) (Ioi (-δ)) ∧
      ContDiffOn ℝ 2 (globalLaplaceC p u w) (Ioi (-δ)) ∧
      ∀ t ∈ Ioi (-δ), HasDerivAt (globalLaplaceC p u w)
        (laplaceCarry p u + modelA p * globalLaplaceD p u w t) t := by
  obtain ⟨δ, hδ, hQ⟩ := exists_riccatiDenominator_ne_zero p u w hξ hρ hu hw
  have hDon : ContDiffOn ℝ 2 (globalLaplaceD p u w) (Ioi (-δ)) := fun t ht =>
    (contDiffAt_globalLaplaceD p u w (hQ t ht)).contDiffWithinAt
  have hDcont : ContinuousOn (globalLaplaceD p u w) (Ioi (-δ)) := hDon.continuousOn
  have hderiv : ∀ t ∈ Ioi (-δ), HasDerivAt (globalLaplaceC p u w)
      (laplaceCarry p u + modelA p * globalLaplaceD p u w t) t := by
    intro t ht
    have hsub : uIcc 0 t ⊆ Ioi (-δ) := by
      intro x hx
      have := hx.1
      simp only [mem_Ioi] at ht ⊢
      rcases le_total 0 t with h | h
      · rw [min_eq_left h] at this; linarith
      · rw [min_eq_right h] at this; linarith
    have hint : IntervalIntegrable (globalLaplaceD p u w) volume 0 t :=
      (hDcont.mono hsub).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter (globalLaplaceD p u w) (𝓝 t) :=
      hDcont.stronglyMeasurableAtFilter isOpen_Ioi t ht
    have hca : ContinuousAt (globalLaplaceD p u w) t := hDcont.continuousAt (isOpen_Ioi.mem_nhds ht)
    have hI := intervalIntegral.integral_hasDerivAt_right hint hmeas hca
    have hlin : HasDerivAt (fun s : ℝ ↦ laplaceCarry p u * (s : ℂ)) (laplaceCarry p u) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (laplaceCarry p u)
    have := hlin.add (hI.const_mul (modelA p))
    exact this
  refine ⟨δ, hδ, hDon, ?_, hderiv⟩
  have hdiff : DifferentiableOn ℝ (globalLaplaceC p u w) (Ioi (-δ)) := fun t ht =>
    (hderiv t ht).differentiableAt.differentiableWithinAt
  have hdC : ContDiffOn ℝ 1 (deriv (globalLaplaceC p u w)) (Ioi (-δ)) := by
    have h1 : ContDiffOn ℝ 1 (fun t ↦ laplaceCarry p u + modelA p * globalLaplaceD p u w t)
        (Ioi (-δ)) := contDiffOn_const.add (contDiffOn_const.mul (hDon.of_le (by norm_num)))
    exact h1.congr fun t ht => (hderiv t ht).deriv
  have : ContDiffOn ℝ (1 + 1) (globalLaplaceC p u w) (Ioi (-δ)) :=
    (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).2 ⟨hdiff, fun h => by simp at h, hdC⟩
  rwa [one_add_one_eq_two] at this

end Riccati

end CommonAffine
end MathFin.Heston
