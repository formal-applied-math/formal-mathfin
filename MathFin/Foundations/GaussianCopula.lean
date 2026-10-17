/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.Sklar
public import MathFin.Foundations.NormalQuantile

/-!
# The one-factor Gaussian copula

The **one-factor Gaussian copula** on `n` names with factor loading `ρ ∈ [−1, 1]` is the copula of
the latent vector
`Xᵢ = ρ Z₀ + √(1 − ρ²) Zᵢ`, `i : Fin n`,
where the systematic factor `Z₀` and the idiosyncratic factors `Z₁, …, Zₙ` are independent standard
normals. Every `Xᵢ` is standard normal, and `Xᵢ, Xⱼ` (`i ≠ j`) have correlation `ρ²`. This is the
latent-variable model behind the Vasicek large-pool model and standard CDO tranche pricing: name
`i` defaults by time `t` when `Xᵢ ≤ Φ⁻¹(pᵢ(t))`.

We take the factors as a point `(z₀, z) : ℝ × (Fin n → ℝ)` under the product of standard normal
laws (`stdNormalFactors`), with the systematic factor in the first slot, so that every name is
treated symmetrically. (A common bivariate construction instead writes the pair as
`(Z₁, ρ Z₁ + √(1 − ρ²) Z₂)`, correlation `ρ`; the symmetric model here always has pairwise
correlation `ρ²` (never `ρ`), so even at `n = 2` it does not coincide with that bivariate
construction for any `ρ < 0`, nor for `ρ ∈ (0, 1)` without reparametrising `ρ ↦ √ρ`.)

The copula is defined via `copulaOf`, so being a copula is Sklar's theorem.

## Main results

* `gaussianFactorCopula`, `isCopula_gaussianFactorCopula`, `gaussianFactorCopula_real_Iic`.
* `gaussianFactorCopula_zero`: `ρ = 0` gives the independence copula `Π`.
* `gaussianFactorCopula_one`: `ρ = 1` gives the comonotonicity copula `M`.

The countermonotonicity copula `W` is only a copula in dimension two and is not a member of the
symmetric family (pairwise correlations `ρ²` are nonnegative), so there is no `ρ = −1` analogue.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The law of two independent standard normals `(Z₁, Z₂)`. -/
noncomputable abbrev stdNormal2 : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- A unit-norm combination `a Z₁ + b Z₂` of independent standard normals is standard normal. -/
lemma map_stdNormal2_linComb {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    stdNormal2.map (fun z ↦ a * z.1 + b * z.2) = gaussianReal 0 1 := by
  have h1 : stdNormal2.map (fun z ↦ a * z.1) = gaussianReal 0 ⟨a ^ 2, sq_nonneg a⟩ := by
    rw [show (fun z : ℝ × ℝ ↦ a * z.1) = (a * ·) ∘ Prod.fst from rfl,
      ← Measure.map_map (measurable_const_mul a) measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul, gaussianReal_map_const_mul, mul_zero, mul_one]
    rfl
  have h2 : stdNormal2.map (fun z ↦ b * z.2) = gaussianReal 0 ⟨b ^ 2, sq_nonneg b⟩ := by
    rw [show (fun z : ℝ × ℝ ↦ b * z.2) = (b * ·) ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_const_mul b) measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul, gaussianReal_map_const_mul, mul_zero, mul_one]
    rfl
  have h := gaussianReal_add_gaussianReal_of_indepFun
    (indepFun_prod (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
      (measurable_const_mul a) (measurable_const_mul b)) h1 h2
  rw [show (⟨a ^ 2, sq_nonneg a⟩ + ⟨b ^ 2, sq_nonneg b⟩ : ℝ≥0) = 1 from NNReal.eq hab,
    add_zero] at h
  exact h

variable {n : ℕ} {ρ : ℝ}

/-- The law of the factors of the one-factor model: a systematic standard normal `Z₀` and `n`
idiosyncratic standard normals, all independent. -/
noncomputable abbrev stdNormalFactors (n : ℕ) : Measure (ℝ × (Fin n → ℝ)) :=
  (gaussianReal 0 1).prod (Measure.pi fun _ ↦ gaussianReal 0 1)

/-- The **one-factor Gaussian latent vector** `Xᵢ = ρ z₀ + √(1 − ρ²) zᵢ`. -/
noncomputable def gaussianFactorVec (ρ : ℝ) (z : ℝ × (Fin n → ℝ)) : Fin n → ℝ :=
  fun i ↦ ρ * z.1 + √(1 - ρ ^ 2) * z.2 i

@[fun_prop] lemma measurable_gaussianFactorVec (ρ : ℝ) :
    Measurable (gaussianFactorVec (n := n) ρ) :=
  measurable_pi_iff.2 fun i ↦ by unfold gaussianFactorVec; fun_prop

/-- `(Z₀, Zᵢ)` is a pair of independent standard normals. -/
lemma map_stdNormalFactors_pair (i : Fin n) :
    (stdNormalFactors n).map (fun z ↦ (z.1, z.2 i)) = stdNormal2 := by
  rw [show (fun z : ℝ × (Fin n → ℝ) ↦ (z.1, z.2 i)) = Prod.map id (fun w ↦ w i) from rfl,
    ← Measure.map_prod_map _ _ measurable_id (measurable_pi_apply i), Measure.map_id,
    (measurePreserving_eval (fun _ ↦ gaussianReal 0 1) i).map_eq]

/-- For `ρ ∈ [−1, 1]` every coordinate of the latent vector is standard normal. -/
lemma map_gaussianFactorVec (hρ : ρ ∈ Icc (-1) 1) (i : Fin n) :
    (stdNormalFactors n).map (fun z ↦ gaussianFactorVec ρ z i) = gaussianReal 0 1 := by
  rw [show (fun z ↦ gaussianFactorVec ρ z i) =
      (fun p : ℝ × ℝ ↦ ρ * p.1 + √(1 - ρ ^ 2) * p.2) ∘ (fun z ↦ (z.1, z.2 i)) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), map_stdNormalFactors_pair]
  refine map_stdNormal2_linComb ?_
  rw [Real.sq_sqrt (by nlinarith [hρ.1, hρ.2])]
  ring

/-- `Φ` is measurable. -/
@[fun_prop] lemma measurable_Phi : Measurable Phi := continuous_Phi.measurable

/-- `Φ` pushes the standard normal law to the uniform law on `(0, 1)`. -/
lemma map_Phi_gaussianReal : (gaussianReal 0 1).map Phi = volume.restrict (Ioo 0 1) := by
  simpa [cdf_gaussianReal_zero_one] using (hasLaw_cdf (μ := gaussianReal 0 1) HasLaw.id
    (by rw [cdf_gaussianReal_zero_one]; exact continuous_Phi)).map_eq

/-! ### The copula -/

/-- The **one-factor Gaussian copula** on `n` names with loading `ρ`: the copula of
`gaussianFactorVec ρ`. It is a copula for `ρ ∈ [−1, 1]` (`isCopula_gaussianFactorCopula`). -/
noncomputable def gaussianFactorCopula (n : ℕ) (ρ : ℝ) : Measure (Fin n → ℝ) :=
  copulaOf (gaussianFactorVec ρ) (stdNormalFactors n)

lemma continuous_cdf_gaussianFactorVec (hρ : ρ ∈ Icc (-1) 1) (i : Fin n) :
    Continuous (cdf ((stdNormalFactors n).map fun z ↦ gaussianFactorVec ρ z i)) := by
  rw [map_gaussianFactorVec hρ, cdf_gaussianReal_zero_one]
  exact continuous_Phi

/-- For `ρ ∈ [−1, 1]` the copula is the law of `(Φ(X₁), …, Φ(Xₙ))`. -/
lemma gaussianFactorCopula_eq_map (hρ : ρ ∈ Icc (-1) 1) :
    gaussianFactorCopula n ρ =
      (stdNormalFactors n).map fun z i ↦ Phi (gaussianFactorVec ρ z i) := by
  simp only [gaussianFactorCopula, copulaOf, map_gaussianFactorVec hρ, cdf_gaussianReal_zero_one]

/-- **The one-factor Gaussian copula is a copula** for every `ρ ∈ [−1, 1]`. -/
theorem isCopula_gaussianFactorCopula (hρ : ρ ∈ Icc (-1) 1) : IsCopula (gaussianFactorCopula n ρ) :=
  isCopula_copulaOf (measurable_gaussianFactorVec ρ).aemeasurable
    (continuous_cdf_gaussianFactorVec hρ)

/-- **Distribution function**: on `(0, 1)ⁿ`, `C(u) = P(Xᵢ ≤ Φ⁻¹(uᵢ) for all i)`. -/
theorem gaussianFactorCopula_real_Iic (hρ : ρ ∈ Icc (-1) 1) (u : Fin n → ℝ)
    (hu : ∀ i, u i ∈ Ioo 0 1) :
    (gaussianFactorCopula n ρ).real (Iic u) =
      (stdNormalFactors n).real {z | gaussianFactorVec ρ z ≤ fun i ↦ PhiInv (u i)} := by
  rw [measureReal_le_eq_copulaOf (measurable_gaussianFactorVec ρ).aemeasurable
    (continuous_cdf_gaussianFactorVec hρ)]
  simp only [map_gaussianFactorVec hρ, cdf_gaussianReal_zero_one]
  rw [show (fun i ↦ Phi (PhiInv (u i))) = u from funext fun i ↦ Phi_PhiInv (hu i)]
  rfl

/-! ### The independence and comonotone members -/

/-- **`ρ = 0` gives the independence copula** `Π`. -/
theorem gaussianFactorCopula_zero : gaussianFactorCopula n 0 = independenceCopula (Fin n) := by
  have hf : (fun z : ℝ × (Fin n → ℝ) ↦ fun i ↦ Phi (gaussianFactorVec 0 z i)) =
      (fun w i ↦ Phi (w i)) ∘ Prod.snd := by
    ext z i; simp [gaussianFactorVec]
  rw [gaussianFactorCopula_eq_map (by norm_num), hf,
    ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod, measure_univ, one_smul,
    Measure.pi_map_pi (fun _ ↦ measurable_Phi.aemeasurable)]
  simp [map_Phi_gaussianReal, independenceCopula]

/-- **`ρ = 1` gives the comonotonicity copula** `M`: every name loads only on `Z₀`. -/
theorem gaussianFactorCopula_one : gaussianFactorCopula n 1 = comonotoneCopula (Fin n) := by
  have hf : (fun z : ℝ × (Fin n → ℝ) ↦ fun i ↦ Phi (gaussianFactorVec 1 z i)) =
      (fun t _ ↦ t) ∘ Phi ∘ Prod.fst := by
    ext z i; simp [gaussianFactorVec]
  rw [gaussianFactorCopula_eq_map (by norm_num), hf,
    ← Measure.map_map (by fun_prop) (measurable_Phi.comp measurable_fst),
    ← Measure.map_map measurable_Phi measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  simp [map_Phi_gaussianReal, comonotoneCopula]

end MathFin
