/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Using the library: default correlation in a credit portfolio

A worked use of the library from outside it, the way a credit desk reads the dependence between
the defaults in a loan pool. The pool is modelled by the one-factor Gaussian threshold model:
obligor `i` defaults when its asset value `√ρ F + √(1 − ρ) εᵢ` falls below `Φ⁻¹(π)`, where the
systematic factor `F` and the idiosyncratic terms `εᵢ` are independent standard normals. This file

1. records the pool as data (its size, the default probability `π` of each obligor and the asset
   correlation `ρ`), with where the numbers come from and what the model leaves out;
2. proves that each obligor defaults with probability exactly `π`
   (`IsModel.measureReal_default`);
3. proves that every group of obligors defaults jointly with probability `E[Q^k]`, a moment of the
   mixing variable `Q = p(F)`, the default probability conditional on the factor, where `k` is the
   size of the group (`IsModel.measureReal_iInter_default`);
4. computes the default correlation `ρ_D = (π₂ − π²)/(π − π²)` of two distinct obligors as
   `Var(Q)/(π(1 − π))`, and proves it nonnegative (`IsModel.defaultCorrelation_eq_and_nonneg`).
   Since `π(1 − π) > 0`, this says that two defaults together are never less likely than they
   would be if the obligors were independent;
5. exhibits a realization of the model, the coordinates of a product of standard normal laws
   (`isModel_stdNormalFactors`), so the statements are not vacuous;
6. states all this for an illustrative pool of `100` obligors with `π = 2%` and `ρ = 0.2`.

`sample_checked` is the single statement the build certifies. Apart from the realization it
exhibits, it holds for every realization of the model, on any probability space: every `F` and
`εᵢ` that are independent standard normals.

## What the library supplies

* `MathFin.oneFactorPD`: the conditional default probability
  `p(f) = Φ((Φ⁻¹(π) − √ρ f)/√(1 − ρ))`.
* `MathFin.oneFactor_measureReal_default`: each obligor defaults with probability `π`.
* `MathFin.oneFactor_bernoulliMixture`: the one-factor model is a Bernoulli mixture, with mixing
  variable `p(F)` and uniforms `Φ(εᵢ)`.
* `MathFin.oneFactor_measureReal_iInter_default`: so the joint default probabilities are the
  moments `∫ p(x)^k dN(0,1)(x)` (`measureReal_iInter_default_eq_integral_pow`).
* `MathFin.oneFactor_measureReal_inter_default_sub_mul`: and the default covariance is
  `Var(p(F))` (`measureReal_inter_default_sub_mul`). The correlation and its sign are computed
  here from it, in the shape of `defaultCorrelation_eq` and `defaultCorrelation_nonneg`.
* `MathFin.stdNormalFactors` and its coordinate lemmas (`RiskMeasures/OneFactorCopula.lean`): the
  realization.

## What it does not

The model has one factor, the same default probability and asset correlation for every obligor,
and one horizon. It says nothing about recoveries, exposures or the timing of defaults, and the
parameters are taken as known. The joint default probabilities stay integrals: no numerical value
of `π₂` or of the default correlation is proved here, only that the correlation is nonnegative.
The numbers `π = 2%` and `ρ = 0.2` enter the check only through the model: nonnegativity holds in
every Bernoulli mixture, and the strict positivity of the correlation for `ρ > 0` is not proved.

## Source

The model is McNeil–Frey–Embrechts, *Quantitative Risk Management* (2015), §11.2. The shape of
the file follows the capped-call example (`MathFinExamples/Applications/CappedCall.lean`). The
numbers below are illustrative.
-/

namespace MathFin.Examples.CreditCorrelation

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### The pool, as data -/

/-- A pool of loans in the one-factor Gaussian threshold model: the number of obligors, the
default probability of each, and the correlation of their asset values, with where the numbers
come from and what the model leaves out. -/
structure Pool where
  /-- The number of obligors. -/
  size : ℕ
  /-- The default probability of each obligor over the horizon. -/
  pd : ℝ
  /-- The asset correlation `ρ`: the share of each asset value's variance that is systematic. -/
  assetCorr : ℝ
  pd_mem : pd ∈ Ioo 0 1
  assetCorr_mem : assetCorr ∈ Ico 0 1
  /-- Where the numbers come from. -/
  sources : List String
  /-- What the model leaves out. -/
  unmodelled : List String

namespace Pool

/-- Obligor `i` defaults when its asset value `√ρ F + √(1 − ρ) εᵢ` falls below `Φ⁻¹(π)`. -/
def Default (c : Pool) (F : Ω → ℝ) (ε : Fin c.size → Ω → ℝ) (i : Fin c.size) : Set Ω :=
  {ω | √c.assetCorr * F ω + √(1 - c.assetCorr) * ε i ω ≤ PhiInv c.pd}

/-- The mixing variable `Q = p(F)`: the default probability of each obligor given the factor. -/
noncomputable def mixing (c : Pool) (F : Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ oneFactorPD c.pd c.assetCorr (F ω)

/-- **A realization of the model**: the factor and the idiosyncratic terms are independent
standard normals. -/
structure IsModel (c : Pool) (P : Measure Ω) (F : Ω → ℝ) (ε : Fin c.size → Ω → ℝ) : Prop where
  factor : HasLaw F (gaussianReal 0 1) P
  idio (i : Fin c.size) : HasLaw (ε i) (gaussianReal 0 1) P
  indep : iIndepFun ε P
  indep_factor : F ⟂ᵢ[P] fun ω i ↦ ε i ω

variable [IsProbabilityMeasure P] {c : Pool} {F : Ω → ℝ} {ε : Fin c.size → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- **Each obligor defaults with probability `π`** (`oneFactor_measureReal_default`). -/
theorem IsModel.measureReal_default (h : c.IsModel P F ε) (i : Fin c.size) :
    P.real (c.Default F ε i) = c.pd :=
  oneFactor_measureReal_default h.factor (h.idio i)
    (h.indep_factor.comp measurable_id (measurable_pi_apply i)) c.pd_mem c.assetCorr_mem.1
    c.assetCorr_mem.2.le

/-- **Joint defaults are moments of the mixing variable**: every group `s` of obligors defaults
jointly with probability `E[Q^|s|]` (`oneFactor_measureReal_iInter_default`). -/
theorem IsModel.measureReal_iInter_default (h : c.IsModel P F ε) (s : Finset (Fin c.size)) :
    P.real (⋂ i ∈ s, c.Default F ε i) = P[c.mixing F ^ s.card] := by
  simp only [Default]
  rw [oneFactor_measureReal_iInter_default h.factor h.idio h.indep h.indep_factor
    c.assetCorr_mem.2 s]
  exact (h.factor.integral_comp
    ((measurable_oneFactorPD _ _).pow_const _).aestronglyMeasurable).symm

/-- **The default correlation** of two distinct obligors, `ρ_D = (π₂ − π²)/(π − π²)`, is
`Var(Q)/(π(1 − π))`, and it is nonnegative. The default covariance `π₂ − π²` is the variance of
the mixing variable (`oneFactor_measureReal_inter_default_sub_mul`). -/
theorem IsModel.defaultCorrelation_eq_and_nonneg (h : c.IsModel P F ε) {i j : Fin c.size}
    (hij : i ≠ j) :
    (P.real (c.Default F ε i ∩ c.Default F ε j) - c.pd ^ 2) / (c.pd - c.pd ^ 2) =
        Var[c.mixing F; P] / (c.pd * (1 - c.pd)) ∧
      0 ≤ (P.real (c.Default F ε i ∩ c.Default F ε j) - c.pd ^ 2) / (c.pd - c.pd ^ 2) := by
  have hcov := oneFactor_measureReal_inter_default_sub_mul (π := c.pd) h.factor h.idio h.indep
    h.indep_factor c.assetCorr_mem.2 hij
  have hπ₂ : P.real (c.Default F ε i ∩ c.Default F ε j) - c.pd ^ 2 = Var[c.mixing F; P] := by
    rw [show c.pd ^ 2 = P.real (c.Default F ε i) * P.real (c.Default F ε j) by
      rw [h.measureReal_default, h.measureReal_default, sq]]
    exact hcov
  have hden : c.pd - c.pd ^ 2 = c.pd * (1 - c.pd) := by ring
  rw [hπ₂, hden]
  exact ⟨rfl, div_nonneg (variance_nonneg _ _)
    (mul_nonneg c.pd_mem.1.le (sub_nonneg.2 c.pd_mem.2.le))⟩

/-- **The model has a realization**: on the factor space `stdNormalFactors n`, a standard normal
times `n` independent standard normals, the coordinates are a factor and idiosyncratic terms
that are independent standard normals. -/
theorem isModel_stdNormalFactors (c : Pool) :
    c.IsModel (stdNormalFactors c.size) Prod.fst fun i z ↦ z.2 i :=
  ⟨hasLaw_fst_stdNormalFactors, hasLaw_snd_apply_stdNormalFactors, iIndepFun_snd_stdNormalFactors,
    indepFun_fst_snd_stdNormalFactors⟩

end Pool

/-- An illustrative pool: `100` obligors, each defaulting with probability `2%` over the horizon,
with asset correlation `0.2`. -/
noncomputable def sample : Pool where
  size := 100
  pd := 0.02
  assetCorr := 0.2
  pd_mem := by norm_num
  assetCorr_mem := by norm_num
  sources := ["illustrative default probability and asset correlation for a pool of 100 loans"]
  unmodelled :=
    ["recoveries and exposures at default", "differences between obligors",
      "more than one systematic factor", "the timing of defaults within the horizon",
      "estimation error in the default probability and the asset correlation"]

/-! ### The check -/

/-- **The correlation check for `sample`**, the statement this file's build certifies. In every
realization of the model, with `F` and the `εᵢ` independent standard normals and `Q = p(F)`
(and one such realization exists, on `stdNormalFactors 100`):
- each of the `100` obligors defaults with probability `0.02`;
- every group of `k` obligors defaults jointly with probability `E[Q^k]`;
- two distinct obligors have default correlation `Var(Q)/(0.02 · 0.98)`, which is nonnegative. -/
theorem sample_checked :
    sample.IsModel (stdNormalFactors 100) Prod.fst (fun i z ↦ z.2 i) ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (F : Ω → ℝ)
      (ε : Fin 100 → Ω → ℝ), sample.IsModel P F ε →
      (∀ i, P.real (sample.Default F ε i) = 0.02) ∧
      (∀ s : Finset (Fin 100),
        P.real (⋂ i ∈ s, sample.Default F ε i) = P[sample.mixing F ^ s.card]) ∧
      ∀ i j : Fin 100, i ≠ j →
        (P.real (sample.Default F ε i ∩ sample.Default F ε j) - 0.02 ^ 2) / (0.02 - 0.02 ^ 2) =
            Var[sample.mixing F; P] / (0.02 * (1 - 0.02)) ∧
          0 ≤ (P.real (sample.Default F ε i ∩ sample.Default F ε j) - 0.02 ^ 2) /
            (0.02 - 0.02 ^ 2) := by
  refine ⟨sample.isModel_stdNormalFactors, ?_⟩
  intro Ω _ P _ F ε h
  exact ⟨h.measureReal_default, h.measureReal_iInter_default,
    fun _ _ hij ↦ h.defaultCorrelation_eq_and_nonneg hij⟩

end MathFin.Examples.CreditCorrelation
