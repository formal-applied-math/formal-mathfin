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

Three exposure-measure results on the CVA exposure-process substrate (`V : ℝ → Ω₁ → ℝ` an
actual exposure process, `ν` its measure): ENE (via `CVA.expectedExposure`), PFE (via
`MathFin.valueAtRisk`), and netting subadditivity:

* `expectedNegativeExposure` — `ENE(s) = E_ν[(-V_s)⁺]`, a genuine integral parallel to
  `CVA.expectedExposure`. `expectedNegativeExposure_eq_sub_integral` proves
  `ENE = EE - E[V]` for integrable `V_s`, from the pointwise identity `(-x)⁺ = x⁺ - x` and
  integral linearity;
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

/-- **ENE = EE − E[V]**: for `V_s` integrable, a genuine measure-theoretic identity from
`(-x)⁺ = x⁺ - x` pointwise and integral linearity. -/
theorem expectedNegativeExposure_eq_sub_integral {V : ℝ → Ω₁ → ℝ} {s : ℝ}
    (hV : Integrable (V s) ν) :
    expectedNegativeExposure V ν s = expectedExposure V ν s - ∫ ω, V s ω ∂ν := by
  rw [expectedNegativeExposure, expectedExposure, ← integral_sub hV.pos_part hV]
  congr with ω
  linarith [max_zero_sub_max_neg_zero_eq_self (V s ω)]

/-- **Gaussian expected negative exposure**: for `Z ~ N(0,1)`, `s > 0`, `b > 0`,
`E[(a + b√s Z)⁻] = E[(a+b√s Z)⁺] - a`, specializing `expectedNegativeExposure_eq_sub_integral`
to the exposure model of `CVA.expectedExposure_gaussian`, since `E[a + b√s Z] = a`. -/
theorem expectedNegativeExposure_gaussian [IsProbabilityMeasure ν] {Z : Ω₁ → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) ν) {a b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    expectedNegativeExposure (fun s ω ↦ a + b * √s * Z ω) ν s
      = a * Phi (a / (b * √s)) + b * √s * gaussianPDFReal 0 1 (a / (b * √s)) - a := by
  have hZi : Integrable Z ν := hZ.hasGaussianLaw.integrable
  have hVi : Integrable (fun ω ↦ a + b * √s * Z ω) ν :=
    (integrable_const a).add (hZi.const_mul (b * √s))
  have hmean : ∫ ω, (a + b * √s * Z ω) ∂ν = a := by
    rw [(gaussianReal_const_add (gaussianReal_const_mul hZ (b * √s)) a).integral_eq,
      integral_id_gaussianReal]
    ring
  rw [expectedNegativeExposure_eq_sub_integral hVi, hmean, expectedExposure,
    expectedExposure_gaussian hZ hb hs]

/-- **Potential future exposure**: the `α`-level value-at-risk of the exposure process at time
`s`, `PFE_α(s) = VaR_α(V_s)` — the genuine quantile of `V_s`'s law, not a bare closed form.
**Scope**: this is the raw `α`-quantile of `V_s`, which matches Hull's "quantile of the exposure
`V_s⁺`" only when that quantile is nonnegative (e.g. the Gaussian closed form below can be
negative). -/
noncomputable def potentialFutureExposure (V : ℝ → Ω₁ → ℝ) (ν : Measure Ω₁) (s α : ℝ) : ℝ :=
  MathFin.valueAtRisk (V s) ν α

/-- **Gaussian PFE**: for the exposure process `V_s = m + σ√s Z` of `CVA.cva_gaussian`, `PFE_α(s)`
is the Gaussian value-at-risk closed form at `V_s`'s own law `N(m, (σ√s)²)` — a corollary composing
the law of `V_s` (`gaussianReal_const_mul`, `gaussianReal_const_add`) with
`valueAtRisk_of_hasLaw_gaussianReal`. -/
theorem potentialFutureExposure_gaussian {Z : Ω₁ → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) ν) (m σ s α : ℝ) (hσ : 0 ≤ σ)
    (hα : α ∈ Ioo 0 1) :
    potentialFutureExposure (fun s ω ↦ m + σ * √s * Z ω) ν s α
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
    ∫ ω, max (∑ i ∈ s, V i ω) 0 ∂ν ≤ ∑ i ∈ s, ∫ ω, max (V i ω) 0 ∂ν :=
  (integral_mono (integrable_finsetSum s hV).pos_part
    (integrable_finsetSum s fun i hi ↦ (hV i hi).pos_part) fun ω ↦
      Finset.le_sum_of_subadditive (fun x ↦ max x 0) (max_self (0:ℝ)).le (fun a b ↦ by
        simpa using max_add_add_le_max_add_max (a := a) (b := b) (c := 0) (d := 0)) s
        fun i ↦ V i ω).trans_eq
    (integral_finsetSum s fun i hi ↦ (hV i hi).pos_part)

end MathFin.CVA
