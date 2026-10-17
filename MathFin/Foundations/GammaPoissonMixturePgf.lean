/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# CreditRisk+ sector probability-generating function (Poisson–Gamma mixture)

CreditRisk+ (Credit Suisse First Boston, 1997) models each sector's systematic
risk factor as a random intensity `Λ ∼ Gamma(a, r)` (shape `a`, Mathlib's
*rate* parametrisation `r = 1/β` for the technical document's scale `β`).
Conditional on `Λ = λ`, the sector default count `N` is Poisson(`λ`), with
conditional pgf `E[z^N | Λ = λ] = exp(λ(z−1))` (the Poisson pgf of
`Foundations/PoissonPgf.lean`, `integral_pow_poissonMeasure`; this file does not import it, since
the mixing hypothesis below substitutes the pgf's closed form `exp(λ(z−1))` directly rather than
invoking that lemma).

**Mixing hypothesis.** This file does not build `N` and `Λ` as random
variables on a common probability space with a measure-theoretic conditional
law; instead it states the conditional-independence / mixing structure as an
explicit mathematical fact used by the tower property: the *unconditional*
sector pgf is obtained by integrating the conditional pgf `λ ↦ exp(λ(z−1))`
against the law of `Λ`,

  `G_N(z) = E_Λ[E[z^N | Λ]] = ∫ λ, exp(λ(z−1)) ∂(Gamma(a,r))`.

That this tower-property substitution is valid is exactly the hypothesis "`N`
is conditionally Poisson(`Λ`) given `Λ`, with `Λ` drawn from the stated Gamma
law" — stated here, not silently assumed. The content proved is the resulting
integral: it is the moment-generating function of the Gamma law evaluated at
`z − 1`, which has the closed negative-binomial-style form.

The loss-banding approximation that turns the exact per-sector/portfolio pgf
into CreditRisk+'s practical recursion is **out of scope** here; only the
exact pre-banding pgf is proved.

## Main results

* `integral_exp_mul_gammaMeasure`: the Gamma(`a`, `r`) moment-generating
  function, `∫ λ, exp(s·λ) ∂Gamma(a,r) = (r / (r − s)) ^ a` for `s < r`.
* `sectorPgf`: the Poisson–Gamma-mixture sector pgf, an instance of the above
  at `s = z − 1`.
* `sectorPgf_negBinomial_form`: the same pgf in the technical document's
  `p = β / (1 + β)` scale parametrisation, `((1 − p) / (1 − p·z)) ^ a`.
* `portfolioPgf`: the portfolio pgf before loss-banding is the product across
  sectors of the per-sector pgf (independent sectors, stated as the product
  identity rather than built from a joint sum random variable).
* `poissonMeasure_real_compl_singleton_zero`: `PD_i = 1 − e^{−λ_i}`, i.e.
  `P(N_i ≠ 0) = 1 − e^{−λ_i}` for `N_i ∼ Poisson(λ_i)`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace GammaPoissonMixturePgf

/-- **Gamma moment-generating function.** For `Λ ∼ Gamma(a, r)` (shape `a`,
rate `r`) and `s < r`, `E[exp(s·Λ)] = (r / (r − s)) ^ a`. Proved the same way
Mathlib normalises the Gamma pdf (`lintegral_gammaPDF_eq_one`): factor the
pdf's `exp(−r·λ)` against `exp(s·λ)` into `exp(−(r−s)·λ)` and apply the Gamma
integral `integral_rpow_mul_exp_neg_mul_Ioi` at rate `r − s`. -/
theorem integral_exp_mul_gammaMeasure {a r s : ℝ} (ha : 0 < a) (hr : 0 < r) (hs : s < r) :
    ∫ lam, rexp (s * lam) ∂(gammaMeasure a r) = (r / (r - s)) ^ a := by
  have hrs : 0 < r - s := by linarith
  have hmeasg : Measurable (fun lam : ℝ ↦ ENNReal.ofReal (rexp (s * lam))) :=
    ((measurable_id'.const_mul s).exp).ennreal_ofReal
  have hmeasf : Measurable (gammaPDF a r) :=
    (measurable_gammaPDFReal a r).ennreal_ofReal
  have hmeasF : Measurable
      (fun lam : ℝ ↦ r ^ a / Gamma a * lam ^ (a - 1) * exp (-((r - s) * lam))) :=
    ((measurable_id'.pow_const (a - 1)).const_mul _).mul
      (measurable_id'.const_mul (r - s)).neg.exp
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun lam ↦ (Real.exp_pos _).le)
      ((measurable_id'.const_mul s).exp.aestronglyMeasurable)]
  have hL : ∫⁻ lam, ENNReal.ofReal (rexp (s * lam)) ∂(gammaMeasure a r)
      = ∫⁻ lam in Ici (0 : ℝ), ENNReal.ofReal
          (r ^ a / Gamma a * lam ^ (a - 1) * exp (-((r - s) * lam))) := by
    rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hmeasf hmeasg,
      ← lintegral_add_compl _ measurableSet_Ici, compl_Ici]
    have hleft : ∫⁻ lam in Iio (0 : ℝ),
        (gammaPDF a r * fun lam ↦ ENNReal.ofReal (rexp (s * lam))) lam = 0 := by
      rw [setLIntegral_congr_fun (g := fun _ ↦ (0 : ℝ≥0∞)) measurableSet_Iio]
      · simp
      · intro lam (hlam : lam < 0)
        simp [Pi.mul_apply, gammaPDF_of_neg hlam]
    have hright : ∫⁻ lam in Ici (0 : ℝ),
        (gammaPDF a r * fun lam ↦ ENNReal.ofReal (rexp (s * lam))) lam
        = ∫⁻ lam in Ici (0 : ℝ), ENNReal.ofReal
            (r ^ a / Gamma a * lam ^ (a - 1) * exp (-((r - s) * lam))) := by
      refine setLIntegral_congr_fun measurableSet_Ici (fun lam (hlam : 0 ≤ lam) ↦ ?_)
      simp only [Pi.mul_apply, gammaPDF_of_nonneg hlam]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show -((r - s) * lam) = -(r * lam) + s * lam by ring, Real.exp_add]
      ring
    rw [hright, hleft, add_zero]
  rw [hL, ← integral_eq_lintegral_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ici).mpr
        (ae_of_all _ fun lam (hlam : 0 ≤ lam) ↦ by positivity))
      hmeasF.aestronglyMeasurable]
  have hF : (fun lam : ℝ ↦ r ^ a / Gamma a * lam ^ (a - 1) * exp (-((r - s) * lam)))
      = fun lam : ℝ ↦ (r ^ a / Gamma a) * (lam ^ (a - 1) * exp (-((r - s) * lam))) := by
    funext lam; ring
  rw [hF, MeasureTheory.integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_rpow_mul_exp_neg_mul_Ioi ha hrs]
  have hGpos : (0 : ℝ) < Gamma a := Gamma_pos_of_pos ha
  rw [mul_comm ((1 / (r - s)) ^ a) (Gamma a), ← mul_assoc, div_mul_cancel₀ _ hGpos.ne',
    ← Real.mul_rpow hr.le (by positivity), mul_one_div]

/-- **CreditRisk+ sector pgf** (Poisson–Gamma mixture, exact, pre-loss-banding):
`G_{N(s)}(z) = ∫ λ, exp(λ(z−1)) ∂(Gamma(a,r))`, valid for `z < r + 1`. See the module docstring
for the conditional-independence mixing hypothesis this instantiates `integral_exp_mul_gammaMeasure`
under. -/
theorem sectorPgf {a r z : ℝ} (ha : 0 < a) (hr : 0 < r) (hz : z < r + 1) :
    ∫ lam, rexp (lam * (z - 1)) ∂(gammaMeasure a r) = (r / (r - (z - 1))) ^ a := by
  have := integral_exp_mul_gammaMeasure ha hr (show z - 1 < r by linarith)
  simpa [mul_comm] using this

/-- **Sector pgf, negative-binomial-style `p`-form.** With `β > 0` the mixture scale and
`p = β / (1 + β)`, the sector pgf is `((1 − p) / (1 − p·z)) ^ a`, matching the CreditRisk+
technical document's parametrisation. Mathlib's `gammaMeasure` is rate-parametrised, so the
Gamma law used is `gammaMeasure a (1 / β)`. -/
theorem sectorPgf_negBinomial_form {a β z : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hz : z < 1 + 1 / β) :
    ∫ lam, rexp (lam * (z - 1)) ∂(gammaMeasure a (1 / β))
      = ((1 - β / (1 + β)) / (1 - β / (1 + β) * z)) ^ a := by
  have hr : (0 : ℝ) < 1 / β := by positivity
  rw [sectorPgf ha hr (by rw [add_comm]; linarith)]
  congr 1
  have hβ1 : (1 : ℝ) + β ≠ 0 := by positivity
  field_simp
  ring

/-- **Portfolio pgf before loss-banding**: the product across sectors of the per-sector pgf
(sectors independent, stated as the product identity itself rather than constructed from a joint
sum random variable — see the module docstring). -/
theorem portfolioPgf {ι : Type*} (sectors : Finset ι) (a r : ι → ℝ) (z : ℝ)
    (ha : ∀ i ∈ sectors, 0 < a i) (hr : ∀ i ∈ sectors, 0 < r i)
    (hz : ∀ i ∈ sectors, z < r i + 1) :
    ∏ i ∈ sectors, ∫ lam, rexp (lam * (z - 1)) ∂(gammaMeasure (a i) (r i))
      = ∏ i ∈ sectors, (r i / (r i - (z - 1))) ^ (a i) :=
  Finset.prod_congr rfl fun i hi ↦ sectorPgf (ha i hi) (hr i hi) (hz i hi)

/-- **`PD_i = 1 − e^{−λ_i}`**: for `N ∼ Poisson(λ)`, the default probability `P(N ≠ 0)` equals
`1 − e^{−λ}`, since `P(N = 0) = e^{−λ}` and probabilities sum to `1`. -/
theorem poissonMeasure_real_compl_singleton_zero (lam : ℝ≥0) :
    (poissonMeasure lam).real {0}ᶜ = 1 - rexp (-(lam : ℝ)) := by
  have h0 : (poissonMeasure lam).real {0} = rexp (-(lam : ℝ)) := by
    rw [poissonMeasure_real_singleton]; simp
  have huniv : (poissonMeasure lam).real Set.univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [measureReal_compl (MeasurableSet.singleton 0), huniv, h0]

end GammaPoissonMixturePgf

end MathFin
