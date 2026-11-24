/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import MathFin.Probability.Brownian.Ito.Filtered.FilteredBrownian
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Correlated Noise

Independent Brownian drivers on a common filtration and their correlated
rotation. All hypotheses describe the noise and filtration, not stochastic
integrals, Heston solutions, local martingales or transform identities.

## Main definitions

* `linearNoise`
* `orthogonalWeight`
* `correlatedNoise`

## Main results

* `sq_add_orthogonalWeight_sq`
* `IndependentPair.correlated_brownian`
* `IndependentPair.covariance_correlated`

## References

* [I. Karatzas and S. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]

## Tags

Brownian motion, stochastic integration, MSC 60H05
-/

@[expose] public section

noncomputable section
namespace MathFin.FilteredIto
namespace CommonNoise
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B Z : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 mΩ}

/-- Primitive assumptions for a two-dimensional standard Brownian noise.
The joint independence condition excludes filtrations revealing future joint
information even when individual future components remain independent. -/
structure IndependentPair (ℱ : Filtration ℝ≥0 mΩ)
    (B Z : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) : Prop where
  left_law : IsPreBrownianReal B μ
  right_law : IsPreBrownianReal Z μ
  left_adapted : StronglyAdapted ℱ B
  right_adapted : StronglyAdapted ℱ Z
  paths_independent : IndepFun (fun ω t => B t ω) (fun ω t => Z t ω) μ
  joint_future_independent : ∀ (s : ℝ≥0), ∀ {f : Ω → ℝ}, Measurable[ℱ s] f →
    IndepFun f (fun ω => (fun u => B (s+u) ω - B s ω, fun u => Z (s+u) ω - Z s ω)) μ

theorem IndependentPair.left (h : IndependentPair ℱ B Z μ) : BrownianOn ℱ B μ := by
  refine ⟨h.left_law, h.left_adapted, ?_⟩
  intro s f hf
  exact (h.joint_future_independent s hf).comp measurable_id measurable_fst

theorem IndependentPair.right (h : IndependentPair ℱ B Z μ) : BrownianOn ℱ Z μ := by
  refine ⟨h.right_law, h.right_adapted, ?_⟩
  intro s f hf
  exact (h.joint_future_independent s hf).comp measurable_id measurable_snd

theorem IndependentPair.joint_independent (h : IndependentPair ℱ B Z μ)
    {s t : ℝ≥0} (hst : s ≤ t) {f : Ω → ℝ} (hf : Measurable[ℱ s] f) :
    IndepFun f (fun ω => (B t ω - B s ω, Z t ω - Z s ω)) μ := by
  have hi := (h.joint_future_independent s hf).comp measurable_id
    (show Measurable (fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => (p.1 (t-s), p.2 (t-s))) by fun_prop)
  simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst] using hi

theorem IndependentPair.independent_eval (h : IndependentPair ℱ B Z μ) (s t : ℝ≥0) :
    IndepFun (B s) (Z t) μ :=
  h.paths_independent.comp (measurable_pi_apply s) (measurable_pi_apply t)

theorem IndependentPair.independent_increment (h : IndependentPair ℱ B Z μ)
    (s t u v : ℝ≥0) :
    IndepFun (fun ω => B t ω - B s ω) (fun ω => Z v ω - Z u ω) μ :=
  h.paths_independent.comp ((measurable_pi_apply t).sub (measurable_pi_apply s))
    ((measurable_pi_apply v).sub (measurable_pi_apply u))

/-- Independent noise components have zero mixed increment moment. -/
theorem IndependentPair.integral_increment_mul (h : IndependentPair ℱ B Z μ)
    (s t u v : ℝ≥0) :
    (∫ ω, (B t ω - B s ω) * (Z v ω - Z u ω) ∂μ) = 0 := by
  rw [(h.independent_increment s t u v).integral_fun_mul_eq_mul_integral
    ((h.left.measurable t).sub (h.left.measurable s)).aestronglyMeasurable
    ((h.right.measurable v).sub (h.right.measurable u)).aestronglyMeasurable]
  rw [h.left.integral_increment s t, zero_mul]

/-- The genuinely adapted mixed kernel: coefficients may depend on the past
of BOTH drivers.  This is the diagonal input to the mixed integral isometry. -/
theorem IndependentPair.integral_adapted_cross (h : IndependentPair ℱ B Z μ)
    {s t : ℝ≥0} (hst : s ≤ t) {f : Ω → ℝ} (hf : Measurable[ℱ s] f) :
    (∫ ω, f ω * ((B t ω - B s ω) * (Z t ω - Z s ω)) ∂μ) = 0 := by
  have hi := (h.joint_independent hst hf).comp measurable_id
    (show Measurable (fun z : ℝ × ℝ => z.1 * z.2) by fun_prop)
  have hm : Measurable (fun ω => (B t ω - B s ω) * (Z t ω - Z s ω)) :=
    ((h.left.measurable t).sub (h.left.measurable s)).mul
      ((h.right.measurable t).sub (h.right.measurable s))
  have he := hi.integral_fun_mul_eq_mul_integral
    (hf.mono (ℱ.le s) le_rfl).aestronglyMeasurable hm.aestronglyMeasurable
  simpa only [Function.comp_def, id_eq, h.integral_increment_mul s t s t, mul_zero]
    using he

/-- Linear combination of the two Brownian drivers. -/
def linearNoise (a b : ℝ) (B Z : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => a * B t ω + b * Z t ω

theorem IndependentPair.linear_gaussian (h : IndependentPair ℱ B Z μ) (a b : ℝ) :
    IsGaussianProcess (linearNoise a b B Z) μ := by
  constructor
  intro I
  have hx := (h.left_law.isGaussianProcess.smul (fun _ => a)).hasGaussianLaw I
  have hy := (h.right_law.isGaussianProcess.smul (fun _ => b)).hasGaussianLaw I
  have hi := h.paths_independent.comp
    (show Measurable (fun p : ℝ≥0 → ℝ => fun t : I => a * p t) by fun_prop)
    (show Measurable (fun p : ℝ≥0 → ℝ => fun t : I => b * p t) by fun_prop)
  simpa only [linearNoise, Function.comp_def, Pi.add_def, Pi.smul_def,
    smul_eq_mul, Finset.restrict] using! iIndepFun.hasGaussianLaw_fun_add hx hy hi

theorem IndependentPair.covariance_linear (h : IndependentPair ℱ B Z μ)
    (a b c d : ℝ) (s t : ℝ≥0) :
    cov[linearNoise a b B Z s, linearNoise c d B Z t; μ] =
      (a * c + b * d) * (min s t : ℝ≥0) := by
  haveI : IsProbabilityMeasure μ := h.left_law.isGaussianProcess.isProbabilityMeasure
  have hBs := (h.left_law.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hBt := (h.left_law.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hZs := (h.right_law.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hZt := (h.right_law.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  change cov[(fun ω => a * B s ω) + (fun ω => b * Z s ω),
    (fun ω => c * B t ω) + (fun ω => d * Z t ω); μ] = _
  rw [covariance_add_left (hBs.const_mul a) (hZs.const_mul b)
      ((hBt.const_mul c).add (hZt.const_mul d)),
    covariance_add_right (hBs.const_mul a) (hBt.const_mul c) (hZt.const_mul d),
    covariance_add_right (hZs.const_mul b) (hBt.const_mul c) (hZt.const_mul d)]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    h.left_law.covariance_eval s t, h.right_law.covariance_eval s t,
    (h.independent_eval s t).covariance_eq_zero hBs hZt,
    (h.independent_eval t s).symm.covariance_eq_zero hZs hBt]
  ring

/-- A unit rotation is Brownian relative to the SAME filtration. -/
theorem IndependentPair.linear_brownian (h : IndependentPair ℱ B Z μ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    BrownianOn ℱ (linearNoise a b B Z) μ := by
  haveI : IsProbabilityMeasure μ := h.left_law.isGaussianProcess.isProbabilityMeasure
  have hlaw : IsPreBrownianReal (linearNoise a b B Z) μ := by
    apply (h.linear_gaussian a b).isPreBrownianReal_of_covariance
    · intro t
      simp only [linearNoise]
      rw [integral_add ((h.left_law.integrable_eval t).const_mul a)
        ((h.right_law.integrable_eval t).const_mul b), integral_const_mul,
        integral_const_mul, h.left_law.integral_eval t, h.right_law.integral_eval t]
      ring
    · intro s t hst
      rw [h.covariance_linear a b a b s t, min_eq_left hst]
      rw [← pow_two, ← pow_two, hab, one_mul]
  refine ⟨hlaw, ?_, ?_⟩
  · intro t
    exact ((h.left_adapted t).const_mul a).add ((h.right_adapted t).const_mul b)
  · intro s f hf
    have hi := (h.joint_future_independent s hf).comp measurable_id
      (show Measurable (fun z : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => fun u => a * z.1 u + b * z.2 u) by
            fun_prop)
    have he : (fun ω u => linearNoise a b B Z (s+u) ω - linearNoise a b B Z s ω) =
        (fun ω u => a * (B (s+u) ω - B s ω) + b * (Z (s+u) ω - Z s ω)) := by
      funext ω u
      dsimp [linearNoise]
      ring
    rw [he]
    exact hi

/-- Weight of the independent driver in the correlated rotation. -/
def orthogonalWeight (ρ : ℝ) : ℝ := Real.sqrt (1 - ρ ^ 2)

theorem sq_add_orthogonalWeight_sq {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    ρ ^ 2 + orthogonalWeight ρ ^ 2 = 1 := by
  have hh : 0 ≤ 1 - ρ ^ 2 := by
    rcases abs_le.mp hρ with ⟨hl, hu⟩
    nlinarith [mul_nonneg (show 0 ≤ 1 - ρ by linarith) (show 0 ≤ 1 + ρ by linarith)]
  rw [orthogonalWeight, Real.sq_sqrt hh]
  ring

/-- Brownian driver constructed by rotating an independent pair to correlation ρ. -/
def correlatedNoise (ρ : ℝ) (B Z : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  linearNoise ρ (orthogonalWeight ρ) B Z

theorem IndependentPair.correlated_brownian (h : IndependentPair ℱ B Z μ)
    {ρ : ℝ} (hρ : |ρ| ≤ 1) : BrownianOn ℱ (correlatedNoise ρ B Z) μ :=
  h.linear_brownian ρ (orthogonalWeight ρ) (sq_add_orthogonalWeight_sq hρ)

theorem IndependentPair.covariance_correlated (h : IndependentPair ℱ B Z μ)
    (ρ : ℝ) (s t : ℝ≥0) :
    cov[correlatedNoise ρ B Z s, B t; μ] = ρ * (min s t : ℝ≥0) := by
  have he := h.covariance_linear ρ (orthogonalWeight ρ) 1 0 s t
  have hid : linearNoise 1 0 B Z t = B t := by
    funext ω
    simp [linearNoise]
  rw [hid] at he
  simpa only [correlatedNoise, one_mul, zero_mul, mul_zero, add_zero, mul_one] using he

end CommonNoise
end MathFin.FilteredIto
