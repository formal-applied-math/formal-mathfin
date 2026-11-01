/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.GaussianMoments
public import MathFin.Foundations.QuadraticVariationL2
public import MathFin.Foundations.DiscreteIto

/-! # The Itô–Taylor remainder: the cubic bound and Brownian sixth moments

The third (remainder) term of the discrete Itô formula `discrete_ito_formula` is `O(|ΔBₖ|³)`
for `f ∈ C³` with bounded `f‴` (order-2 Taylor bound, `abs_discreteTaylorRemainder_le`), so
its square is controlled by the Brownian sixth moment `E[(ΔB)⁶] = 15 (Δt)³`
(`integral_increment_pow6`, from the Gaussian `integral_pow6_gaussianReal`). The summed
remainder along the uniform partition is shown to vanish in `L²` by
`tendsto_ito_remainder_td` (`ItoFormulaTDRemainder`), of which the time-independent case is the
instance `f_t = 0`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter QuadraticVariationL2
open scoped NNReal Topology

/-- **Cubic Taylor bound on the discrete remainder.** For `f ∈ C³` with `|f‴| ≤ Cf3`,
the order-2 Taylor remainder `R = f y − f x − f′x·(y−x) − ½f″x·(y−x)²` is `O(|y−x|³)`:
`|R| ≤ Cf3·|y−x|³`. Proved by three applications of the convex mean-value bound on the
segment `[[x,y]]` — bounding `f″−f″x`, then the primitive defect `f′−f′x−f″x·(·−x)`, then
the full remainder — each level gaining one power of `|y−x|`. (The sharp constant `Cf3/6`
is not needed; any cubic bound drives the `L²` limit.) -/
theorem abs_discreteTaylorRemainder_le {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x) {Cf3 : ℝ} (hf3 : ∀ x, |f''' x| ≤ Cf3)
    (x y : ℝ) : |discreteTaylorRemainder f f' f'' x y| ≤ Cf3 * |y - x| ^ 3 := by
  have hCf3 : 0 ≤ Cf3 := le_trans (abs_nonneg _) (hf3 0)
  have hmem : ∀ t ∈ Set.uIcc x y, |t - x| ≤ |y - x| := by
    intro t ht
    rcases le_total x y with hxy | hyx
    · rw [Set.uIcc_of_le hxy] at ht
      rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - x),
        abs_of_nonneg (by linarith [hxy] : (0 : ℝ) ≤ y - x)]
      linarith [ht.2]
    · rw [Set.uIcc_of_ge hyx] at ht
      rw [abs_of_nonpos (by linarith [ht.2] : t - x ≤ 0),
        abs_of_nonpos (by linarith [hyx] : y - x ≤ 0)]
      linarith [ht.1]
  -- Level 2: `|f″ t − f″ x| ≤ Cf3·|y−x|`
  have hL2 : ∀ t ∈ Set.uIcc x y, |f'' t - f'' x| ≤ Cf3 * |y - x| := by
    intro t ht
    have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ ↦ (hf'' u).hasDerivWithinAt) (fun u _ ↦ by rw [Real.norm_eq_abs]; exact hf3 u)
      Set.left_mem_uIcc ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hmem t ht) hCf3)
  -- Level 1: `|f′ t − f′ x − f″ x·(t−x)| ≤ Cf3·|y−x|²`
  have hd1 : ∀ u, HasDerivAt (fun s ↦ f' s - f' x - f'' x * (s - x)) (f'' u - f'' x) u :=
    fun u ↦ by
      have h := ((hf' u).sub_const (f' x)).sub
        (((hasDerivAt_id u).sub_const x).const_mul (f'' x))
      simp only [id_eq] at h
      convert h using 1 <;> first | rfl | ring
  have hL1 : ∀ t ∈ Set.uIcc x y, |f' t - f' x - f'' x * (t - x)| ≤ Cf3 * |y - x| ^ 2 := by
    intro t ht
    have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ ↦ (hd1 u).hasDerivWithinAt)
      (fun u hu ↦ by rw [Real.norm_eq_abs]; exact hL2 u hu)
      Set.left_mem_uIcc ht
    simp only [Real.norm_eq_abs, sub_self, mul_zero, sub_zero] at h
    calc |f' t - f' x - f'' x * (t - x)| ≤ Cf3 * |y - x| * |t - x| := h
      _ ≤ Cf3 * |y - x| * |y - x| :=
          mul_le_mul_of_nonneg_left (hmem t ht) (mul_nonneg hCf3 (abs_nonneg _))
      _ = Cf3 * |y - x| ^ 2 := by ring
  -- Level 0: the remainder itself
  have hd0 : ∀ u, HasDerivAt (fun s ↦ f s - f x - f' x * (s - x) - 1 / 2 * f'' x * (s - x) ^ 2)
      (f' u - f' x - f'' x * (u - x)) u := fun u ↦ by
    have h := (((hf u).sub_const (f x)).sub
        (((hasDerivAt_id u).sub_const x).const_mul (f' x))).sub
        ((((hasDerivAt_id u).sub_const x).pow 2).const_mul (1 / 2 * f'' x))
    simp only [id_eq] at h
    convert h using 1 <;> first | rfl | ring
  have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ ↦ (hd0 u).hasDerivWithinAt)
    (fun u hu ↦ by rw [Real.norm_eq_abs]; exact hL1 u hu)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs] at h
  rw [show f y - f x - f' x * (y - x) - 1 / 2 * f'' x * (y - x) ^ 2
        - (f x - f x - f' x * (x - x) - 1 / 2 * f'' x * (x - x) ^ 2)
      = discreteTaylorRemainder f f' f'' x y from by unfold discreteTaylorRemainder; ring] at h
  exact h.trans_eq (by ring)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  (hB : IsPreBrownianReal B μ)

include hB

/-- **Sixth moment of a Brownian increment**: `E[(B_{t₁} − B_{t₀})⁶] = 15(t₁ − t₀)³`
for `t₀ ≤ t₁` (law-transfer of the Gaussian identity `integral_pow6_gaussianReal`). -/
theorem integral_increment_pow6 {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) :
    ∫ ω, (B t₁ ω - B t₀ ω) ^ 6 ∂μ = 15 * ((t₁ : ℝ) - t₀) ^ 3 := by
  have hcomp := (hasLaw_increment hB ht).integral_comp (f := fun x : ℝ ↦ x ^ 6)
    (measurable_id.pow_const 6).aestronglyMeasurable
  simp only [Function.comp_def] at hcomp
  rw [hcomp, integral_pow6_gaussianReal, NNReal.coe_sub ht]

/-- The sixth power of a Brownian increment is integrable (all Gaussian moments are
finite); the companion to `integral_increment_pow6`. -/
theorem integrable_increment_pow6 (t₀ t₁ : ℝ≥0) :
    Integrable (fun ω ↦ (B t₁ ω - B t₀ ω) ^ 6) μ := by
  have hg : Integrable (fun x : ℝ ↦ x ^ 6) (gaussianReal 0 (nndist (t₁ : ℝ) (t₀ : ℝ))) := by
    have h :=
        (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := nndist (t₁ : ℝ) (t₀ : ℝ)) 6).integrable_norm_pow
      (p := 6) (by norm_num)
    simp only [id_eq, Real.norm_eq_abs] at h
    have hfe : (fun x : ℝ ↦ |x| ^ 6) = fun x : ℝ ↦ x ^ 6 :=
      funext fun x ↦ by rw [pow_abs, abs_of_nonneg (by positivity)]
    rwa [hfe] at h
  have hmap : Integrable (fun x : ℝ ↦ x ^ 6) (Measure.map (B t₁ - B t₀) μ) := by
    rw [(hB.hasLaw_sub t₁ t₀).map_eq]; exact hg
  exact (integrable_map_measure hmap.aestronglyMeasurable (hB.hasLaw_sub t₁ t₀).aemeasurable).mp
      hmap

end MathFin
