/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.FixedIncome.CVA
public import MathFin.RiskMeasures.GaussianValueAtRisk

/-!
# Expected negative exposure, exposure VaR, and netting subadditivity

Three exposure measures built directly on `MathFin.CVA.expectedExposure` (`V : ℝ → Ω₁ → ℝ` an
actual exposure process, `ν` its measure), never on a bare closed-form definition:

* `expectedNegativeExposure` — `ENE(s) = E_ν[(-V_s)⁺]`, a genuine integral parallel to
  `CVA.expectedExposure`. `expectedNegativeExposure_eq_sub_integral` proves (not `unfold`+`ring`)
  `ENE = EE - E[V]` from the pointwise identity `(-x)⁺ = x⁺ - x` and integral linearity;
  `expectedNegativeExposure_gaussian` is its Gaussian closed form, a corollary of
  `CVA.expectedExposure_gaussian` composed with that identity.
* `potentialFutureExposure` (PFE) — the value-at-risk of the exposure process at a fixed time,
  `PFE_α(s) = VaR_α(V_s)` (`MathFin.valueAtRisk`, the genuine `α`-quantile of `V_s`'s law, not a
  new definition). `potentialFutureExposure_gaussian` derives the closed form for the Gaussian
  exposure model of `CVA.cva_gaussian` by composing two already-real pieces: the law of
  `V_s = m + σ√s Z` (from the Gaussian-stability lemmas `gaussianReal_const_mul`,
  `gaussianReal_const_add`) and `valueAtRisk_of_hasLaw_gaussianReal`.
* `integral_posPart_finsetSum_le` — netting reduces exposure: for a finite family
  `V : ι → Ω → ℝ` of integrable exposures on a common measure, `E[(Σᵢ Vᵢ)⁺] ≤ Σᵢ E[Vᵢ⁺]`. Proved
  via the pointwise subadditivity of `max (·) 0` (`max_add_add_le_max_add_max` with the second
  pair at `0`), summed by `le_sum_of_subadditive`, then integrated (`integral_mono`,
  `integral_finsetSum`, `Integrable.pos_part`).

## References

* J. C. Hull, *Options, Futures, and Other Derivatives* (CVA/exposure chapter): EE, ENE, PFE.
* McNeil, Frey, Embrechts, *Quantitative Risk Management* (netting of credit exposures).
-/

@[expose] public section

namespace MathFin.CVA

open MeasureTheory Real ProbabilityTheory Set

variable {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {ν : Measure Ω₁}

/-- Expected negative exposure `ENE(s) = E_ν[(-V_s)⁺]`, the mirror of `expectedExposure`. -/
noncomputable def expectedNegativeExposure (V : ℝ → Ω₁ → ℝ) (ν : Measure Ω₁) (s : ℝ) : ℝ :=
  ∫ ω, max (-(V s ω)) 0 ∂ν

/-- Pointwise: `(-x)⁺ = x⁺ - x` for any real `x`. -/
private lemma max_neg_zero_eq (x : ℝ) : max (-x) 0 = max x 0 - x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring

/-- **ENE = EE − E[V]**: a genuine measure-theoretic identity, from `(-x)⁺ = x⁺ - x` pointwise
and integral linearity (not `unfold` + `ring` on closed forms). -/
theorem expectedNegativeExposure_eq_sub_integral {V : ℝ → Ω₁ → ℝ} {s : ℝ}
    (hV : Integrable (V s) ν) :
    expectedNegativeExposure V ν s = expectedExposure V ν s - ∫ ω, V s ω ∂ν := by
  unfold expectedNegativeExposure expectedExposure
  simp_rw [max_neg_zero_eq]
  exact integral_sub hV.pos_part hV

/-- **Gaussian expected negative exposure**: for `Z ~ N(0,1)`, `s > 0`, `b > 0`,
`E[(a + b√s Z)⁻] = E[(a+b√s Z)⁺] - a`, specializing `expectedNegativeExposure_eq_sub_integral`
to the exposure model of `CVA.expectedExposure_gaussian`, since `E[a + b√s Z] = a`. -/
theorem expectedNegativeExposure_gaussian [IsProbabilityMeasure ν] {Z : Ω₁ → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) ν) {a b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    expectedNegativeExposure (fun s ω ↦ a + b * √s * Z ω) ν s
      = a * Phi (a / (b * √s)) + b * √s * gaussianPDFReal 0 1 (a / (b * √s)) - a := by
  have hZi : Integrable Z ν := by
    have : Integrable id (ν.map Z) := hZ.map_eq ▸ (memLp_id_gaussianReal 1).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id hZ.aemeasurable).mp this
  have hVi : Integrable (fun ω ↦ a + b * √s * Z ω) ν :=
    (integrable_const a).add (hZi.const_mul (b * √s))
  have hmean : ∫ ω, (a + b * √s * Z ω) ∂ν = a := by
    rw [integral_add (integrable_const a) (hZi.const_mul (b * √s)), integral_const, probReal_univ,
      one_smul, integral_const_mul, hZ.integral_eq, integral_id_gaussianReal, mul_zero, add_zero]
  rw [expectedNegativeExposure_eq_sub_integral hVi, hmean]
  change ∫ ω, max (a + b * √s * Z ω) 0 ∂ν - a = _
  rw [expectedExposure_gaussian hZ hb hs]

/-- **Potential future exposure**: the `α`-level value-at-risk of the exposure process at time
`s`, `PFE_α(s) = VaR_α(V_s)` — the genuine quantile of `V_s`'s law, not a bare closed form. -/
noncomputable def potentialFutureExposure (V : ℝ → Ω₁ → ℝ) (ν : Measure Ω₁) (s α : ℝ) : ℝ :=
  MathFin.valueAtRisk (V s) ν α

/-- **Gaussian PFE**: for the exposure model of `CVA.cva_gaussian`, `PFE_α(s)` is the Gaussian
value-at-risk closed form at `V_s`'s own law `N(m, (σ√s)²)` — a corollary composing the law of
`V_s` (`gaussianReal_const_mul`, `gaussianReal_const_add`) with
`valueAtRisk_of_hasLaw_gaussianReal`. -/
theorem potentialFutureExposure_gaussian [IsProbabilityMeasure ν] {Z : Ω₁ → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) ν) (m σ s α : ℝ) (hσ : 0 < σ) (hs : 0 < s)
    (hα : α ∈ Ioo 0 1) :
    potentialFutureExposure (fun _ ω ↦ m + σ * √s * Z ω) ν s α
      = gaussianVaR m (σ * √s) (PhiInv α) := by
  have hL : HasLaw (fun ω ↦ m + σ * √s * Z ω)
      (gaussianReal m (NNReal.mk ((σ * √s) ^ 2) (sq_nonneg _))) ν := by
    simpa using gaussianReal_const_add (gaussianReal_const_mul hZ (σ * √s)) m
  unfold potentialFutureExposure
  rw [MathFin.valueAtRisk_of_hasLaw_gaussianReal hL hα]
  congr 2
  rw [NNReal.coe_mk, Real.sqrt_sq (by positivity : (0:ℝ) ≤ σ * √s)]

/-- **Netting reduces exposure**: `E[(∑ᵢ Vᵢ)⁺] ≤ ∑ᵢ E[Vᵢ⁺]` for a finite family of integrable
real-valued exposures on a common measure. Proved via pointwise subadditivity of `max (·) 0`
(`max_add_add_le_max_add_max`), summed (`le_sum_of_subadditive`), then integrated
(`integral_mono`, `integral_finsetSum`, `Integrable.pos_part`). -/
theorem integral_posPart_finsetSum_le {ι : Type*} (s : Finset ι) {V : ι → Ω₁ → ℝ}
    (hV : ∀ i ∈ s, Integrable (V i) ν) :
    ∫ ω, max (∑ i ∈ s, V i ω) 0 ∂ν ≤ ∑ i ∈ s, ∫ ω, max (V i ω) 0 ∂ν := by
  have hpt : ∀ ω, max (∑ i ∈ s, V i ω) 0 ≤ ∑ i ∈ s, max (V i ω) 0 := fun ω ↦
    Finset.le_sum_of_subadditive (fun x ↦ max x 0) (max_self (0:ℝ)).le (fun a b ↦ by
      simpa using max_add_add_le_max_add_max (a := a) (b := b) (c := 0) (d := 0)) s (fun i ↦ V i ω)
  have hLi : Integrable (fun ω ↦ max (∑ i ∈ s, V i ω) 0) ν := (integrable_finsetSum s hV).pos_part
  have hRi : Integrable (fun ω ↦ ∑ i ∈ s, max (V i ω) 0) ν :=
    integrable_finsetSum s fun i hi ↦ (hV i hi).pos_part
  calc ∫ ω, max (∑ i ∈ s, V i ω) 0 ∂ν
      ≤ ∫ ω, ∑ i ∈ s, max (V i ω) 0 ∂ν := integral_mono hLi hRi hpt
    _ = ∑ i ∈ s, ∫ ω, max (V i ω) 0 ∂ν := integral_finsetSum s fun i hi ↦ (hV i hi).pos_part

end MathFin.CVA
