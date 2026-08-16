/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-! # Multiplication by `f` as an isometry `L²(f²·ν) → L²(ν)`

Multiplying by a fixed measurable `f` carries the weighted space `L²(f²·ν)` isometrically
into `L²(ν)`:

  `∫ |f·ψ|² dν = ∫ |ψ|²·f² dν = ∫ |ψ|² d(f²·ν)`,

so `‖f·ψ‖_{L²(ν)} = ‖ψ‖_{L²(f²·ν)}`. This is the analytic content behind "the Itô integral
against `M = φ●B` is the Itô integral against `B` of `ψφ`": the bracket measure `d⟨M⟩ = φ²ds`
is the weight, and the chain rule is this isometry composed with `itoIntegralCLM_T`.

Mathlib carries only the `p = 1` case, `withDensitySMulLI`, where the density and the
multiplier coincide; at `p = 2` the multiplier is the *square root* of the density, which is
what makes the norm come out right. The general-`p` statement
`‖f·ψ‖_{L^p(ν)} = ‖ψ‖_{L^p(‖f‖ᵖ·ν)}` is the natural home for this and is an upstreaming
candidate; only `p = 2` is built here, since that is the only exponent the Itô tower uses.

## The well-definedness point

`Lp ℝ 2 (sqWeight ν f)` is a space of classes modulo `(f²·ν)`-null sets, which is **coarser**
than modulo `ν`-null sets: `{f = 0}` is `(f²·ν)`-null but in general not `ν`-null. So two
representatives of one class can disagree on a `ν`-non-null set, and the map `ψ ↦ f·ψ` is
still well defined — on `{f ≠ 0}` the representatives agree, and on `{f = 0}` both products
vanish. Each linearity proof below therefore ends in a case split on `f x = 0`, exactly as
Mathlib's `withDensitySMulLI` does. This is the step at which a naive attempt breaks.

## Result

* `sqWeight` — the weighted measure `f²·ν`.
* `lintegral_sqWeight` — the change-of-density identity for lower integrals.
* `eLpNorm_mul_eq` — the norm identity, for an arbitrary function.
* `integral_sqWeight`, `setIntegral_sqWeight` — the Bochner transfer, and its set form.
* `sqWeight_ae_ne_zero` — `f²·ν` is carried by `{f ≠ 0}`.
* `memLp_mul` — `ψ ∈ L²(f²·ν)` implies `f·ψ ∈ L²(ν)`.
* `mulLM`, `mulLI` — the map as a linear map and as a `LinearIsometry`, with `coeFn_mulLM`
  the characterising a.e. identity.
-/

@[expose] public section

namespace MathFin
namespace LpMulIsometry

open MeasureTheory Filter
open scoped ENNReal NNReal

variable {α : Type*} {m : MeasurableSpace α} {ν : Measure α} {f : α → ℝ}

/-- The measure `f²·ν`. For `f` the diffusion coefficient of an Itô integral this is the
bracket measure `d⟨M⟩ = f² ds ⊗ dμ`. -/
noncomputable def sqWeight (ν : Measure α) (f : α → ℝ) : Measure α :=
  ν.withDensity fun x ↦ ‖f x‖ₑ ^ 2

lemma measurable_sqDensity (hf : Measurable f) : Measurable fun x ↦ ‖f x‖ₑ ^ 2 :=
  hf.enorm.pow_const 2

lemma sqDensity_ne_top (x : α) : ‖f x‖ₑ ^ 2 ≠ ⊤ := by
  simp [enorm_ne_top]

/-- The density is nonzero exactly where `f` is, which is what turns an a.e. statement for
`sqWeight ν f` into one for `ν` restricted to `{f ≠ 0}`. -/
lemma sqDensity_ne_zero {x : α} (hx : f x ≠ 0) : ‖f x‖ₑ ^ 2 ≠ 0 :=
  pow_ne_zero 2 (by simpa using hx)

/-- **Change of density for lower integrals.** Integrating against `f²·ν` is integrating
against `ν` with the integrand scaled by `‖f‖ₑ²`. -/
lemma lintegral_sqWeight (hf : Measurable f) (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂(sqWeight ν f) = ∫⁻ x, ‖f x‖ₑ ^ 2 * g x ∂ν := by
  rw [sqWeight, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (measurable_sqDensity hf) (Eventually.of_forall fun x ↦ (sqDensity_ne_top x).lt_top)]
  rfl

/-- **The norm identity.** `‖f·g‖_{L²(ν)} = ‖g‖_{L²(f²·ν)}`, for an arbitrary `g` — no
integrability is needed, both sides being lower integrals. -/
lemma eLpNorm_mul_eq (hf : Measurable f) (g : α → ℝ) :
    eLpNorm (fun x ↦ f x * g x) 2 ν = eLpNorm g 2 (sqWeight ν f) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), lintegral_sqWeight hf]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ≥0∞).toReal)]
  congr 1
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

/-- `(‖r‖ₑ²).toReal = r²` — the real form of the density, used to turn a `withDensity`
transfer into an honest multiplication by `f²`. -/
lemma enorm_sq_toReal (r : ℝ) : (‖r‖ₑ ^ 2).toReal = r ^ 2 := by
  rw [ENNReal.toReal_pow, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg r),
    sq_abs]

/-- **Bochner transfer.** Integrating `u` against `f²·ν` is integrating `f²·u` against `ν`. -/
lemma integral_sqWeight (hf : Measurable f) (u : α → ℝ) :
    ∫ x, u x ∂(sqWeight ν f) = ∫ x, f x ^ 2 * u x ∂ν := by
  rw [sqWeight, integral_withDensity_eq_integral_toReal_smul (measurable_sqDensity hf)
    (Eventually.of_forall fun x ↦ (sqDensity_ne_top x).lt_top)]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by
    simp only [smul_eq_mul, enorm_sq_toReal])

/-- The set-integral form of `integral_sqWeight`. -/
lemma setIntegral_sqWeight (hf : Measurable f) {R : Set α} (hR : MeasurableSet R) (u : α → ℝ) :
    ∫ x in R, u x ∂(sqWeight ν f) = ∫ x in R, f x ^ 2 * u x ∂ν := by
  rw [sqWeight, restrict_withDensity hR,
    integral_withDensity_eq_integral_toReal_smul (measurable_sqDensity hf)
      (Eventually.of_forall fun x ↦ (sqDensity_ne_top x).lt_top)]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by
    simp only [smul_eq_mul, enorm_sq_toReal])

/-- `f²·ν` is carried by `{f ≠ 0}`: the weight kills the rest. This is what turns "`f²·g = 0`
`ν`-a.e." into "`g = 0` a.e. for the weighted measure". -/
lemma sqWeight_ae_ne_zero (hf : Measurable f) : ∀ᵐ x ∂(sqWeight ν f), f x ≠ 0 := by
  rw [sqWeight, ae_withDensity_iff (measurable_sqDensity hf)]
  filter_upwards with x hx hfx
  exact hx (by simp [hfx])

/-- `ψ ∈ L²(f²·ν)` implies `f·ψ ∈ L²(ν)`. The measurability is not transported across the
measures — an `Lp` element carries a genuinely `StronglyMeasurable` representative
(`Lp.stronglyMeasurable`), so it is measurable for every measure at once. -/
lemma memLp_mul (hf : Measurable f) (ψ : Lp ℝ 2 (sqWeight ν f)) :
    MemLp (fun x ↦ f x * ψ x) 2 ν :=
  ⟨hf.aestronglyMeasurable.mul (Lp.stronglyMeasurable ψ).aestronglyMeasurable,
    by rw [eLpNorm_mul_eq hf]; exact Lp.eLpNorm_lt_top ψ⟩

/-- **Multiplication by `f` as a linear map** `L²(f²·ν) →ₗ[ℝ] L²(ν)`. -/
noncomputable def mulLM (ν : Measure α) (hf : Measurable f) :
    Lp ℝ 2 (sqWeight ν f) →ₗ[ℝ] Lp ℝ 2 ν where
  toFun ψ := (memLp_mul hf ψ).toLp _
  map_add' ψ₁ ψ₂ := by
    refine Lp.ext ?_
    filter_upwards [(ae_withDensity_iff (measurable_sqDensity hf)).1 (Lp.coeFn_add ψ₁ ψ₂),
      (memLp_mul hf (ψ₁ + ψ₂)).coeFn_toLp,
      Lp.coeFn_add ((memLp_mul hf ψ₁).toLp _) ((memLp_mul hf ψ₂).toLp _),
      (memLp_mul hf ψ₁).coeFn_toLp, (memLp_mul hf ψ₂).coeFn_toLp] with x hadd h h' h₁ h₂
    rw [h, h', Pi.add_apply, h₁, h₂]
    rcases eq_or_ne (f x) 0 with hx | hx
    · simp [hx]
    · rw [hadd (sqDensity_ne_zero hx), Pi.add_apply, mul_add]
  map_smul' r ψ := by
    refine Lp.ext ?_
    filter_upwards [(ae_withDensity_iff (measurable_sqDensity hf)).1 (Lp.coeFn_smul r ψ),
      (memLp_mul hf (r • ψ)).coeFn_toLp,
      Lp.coeFn_smul r ((memLp_mul hf ψ).toLp _), (memLp_mul hf ψ).coeFn_toLp] with x hs h h' h₁
    rw [RingHom.id_apply, h, h', Pi.smul_apply, h₁]
    rcases eq_or_ne (f x) 0 with hx | hx
    · simp [hx]
    · rw [hs (sqDensity_ne_zero hx), Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      ring

/-- **The characterising a.e. identity** — without it the map is opaque. -/
lemma coeFn_mulLM (ν : Measure α) (hf : Measurable f) (ψ : Lp ℝ 2 (sqWeight ν f)) :
    ⇑(mulLM ν hf ψ) =ᵐ[ν] fun x ↦ f x * ψ x :=
  (memLp_mul hf ψ).coeFn_toLp

/-- **Multiplication by `f`, bundled as an isometry** `L²(f²·ν) →ₗᵢ[ℝ] L²(ν)`. -/
noncomputable def mulLI (ν : Measure α) (hf : Measurable f) :
    Lp ℝ 2 (sqWeight ν f) →ₗᵢ[ℝ] Lp ℝ 2 ν where
  toLinearMap := mulLM ν hf
  norm_map' ψ := by
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_mulLM ν hf ψ), eLpNorm_mul_eq hf]

@[simp]
lemma mulLI_toLinearMap (ν : Measure α) (hf : Measurable f) :
    (mulLI ν hf).toLinearMap = mulLM ν hf := rfl

/-- `coeFn_mulLM` for the bundled isometry. -/
lemma coeFn_mulLI (ν : Measure α) (hf : Measurable f) (ψ : Lp ℝ 2 (sqWeight ν f)) :
    ⇑(mulLI ν hf ψ) =ᵐ[ν] fun x ↦ f x * ψ x :=
  coeFn_mulLM ν hf ψ

end LpMulIsometry
end MathFin
