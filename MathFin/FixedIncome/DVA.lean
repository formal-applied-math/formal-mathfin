/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.RiskMeasures.ExposureMeasures

/-!
# DVA as a CVA mirror

Debt valuation adjustment is the counterparty's expected loss on the bank's *own* default, a gain
to the bank: `CVA.cva` applied to the bank's own default time and hazard and to the exposure seen
from the bank's side, `-V`. In `cva`'s convention `V > 0` means the counterparty owes the bank; the
bank owes the counterparty when `V < 0`, the regime `-V > 0`. On the bank's own default the
counterparty does not recover that liability in full, a loss to the counterparty booked as a gain
to the bank, whose liability is extinguished. The file defines `dva` from `cva` and derives its
integral and Gaussian forms from `cva`'s.

`cva`'s independence hypothesis (the default time independent of the exposure, no wrong-way risk)
carries over unchanged, read as "the bank's own default is independent of the exposure". The
bank's and the counterparty's default times are not jointly modelled, so nothing is stated about a
correlated bilateral picture (both defaults together, wrong-way risk on either leg); that needs
their joint law and is out of scope.

## Main results

* `dva`: the bank's own-default mirror of `CVA.cva`.
* `dva_eq_integral_expectedNegativeExposure`: with the bank's default independent of the
  exposure and a deterministic continuous hazard,
  `DVA = LGD_B · ∫₀ᵀ D(s) · ENE(s) · λ(s)Q(s) ds`, the integral of the expected negative exposure
  (`CVA.integral_exposure_eq` at `-V`).
* `dva_gaussian`: the Gaussian closed form, from `CVA.cva_gaussian` at the mirrored exposure
  `-(m(s) + σ(s)√s Z) = -m(s) + σ(s)√s·(-Z)`, with `gaussianReal_neg` keeping the driver standard
  normal.

## References

* J. C. Hull, *Options, Futures, and Other Derivatives* (bilateral CVA/DVA).
-/

@[expose] public section

namespace MathFin.CVA

open MeasureTheory Real ProbabilityTheory MathFin.DefaultDensity

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {ν : Measure Ω₁} {μ : Measure Ω₂}

/-- **DVA**: the bank's own-default mirror of `cva`, at the bank's own default time `τBank` and
the exposure `-V` seen from the bank's side. Default is independent of the exposure because `cva`
is an integral over the product measure `ν.prod μ`. -/
noncomputable def dva (LGDBank : ℝ) (D : ℝ → ℝ) (V : ℝ → Ω₁ → ℝ) (τBank : Ω₂ → ℝ) (T : ℝ)
    (ν : Measure Ω₁) (μ : Measure Ω₂) : ℝ :=
  cva LGDBank D (fun s ω ↦ -(V s ω)) τBank T ν μ

/-- **DVA is the integral of the expected negative exposure**: with the bank's default time
`τBank` of deterministic continuous hazard `h ≥ 0` (CDF hypothesis `hcdf`), measurable `D`,
jointly measurable `V`, `T ≥ 0` and the integrand jointly integrable,
`DVA = LGD_B · ∫₀ᵀ D(s) · ENE(s) · λ(s)Q(s) ds`. This is `integral_exposure_eq` at `-V`, whose
expected exposure is `expectedNegativeExposure V`. -/
theorem dva_eq_integral_expectedNegativeExposure [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] {h : ℝ → ℝ} (hh : Continuous h) (hnn : ∀ s, 0 ≤ h s)
    {τBank : Ω₂ → ℝ} (hτ : Measurable τBank)
    (hcdf : ∀ a, 0 ≤ a → μ {ω | τBank ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a))
    {D : ℝ → ℝ} (hD : Measurable D) {V : ℝ → Ω₁ → ℝ} (hV : Measurable (Function.uncurry V))
    (LGDBank : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hint : Integrable (fun p : Ω₁ × Ω₂ ↦
      (Set.Iic T).indicator D (τBank p.2) * max (-V (τBank p.2) p.1) 0) (ν.prod μ)) :
    dva LGDBank D V τBank T ν μ
      = LGDBank * ∫ s in (0:ℝ)..T, D s * expectedNegativeExposure V ν s * defaultDensity h s :=
  congrArg (LGDBank * ·)
    (integral_exposure_eq (V := fun s ω ↦ -(V s ω)) hh hnn hτ hcdf hD hV.neg hT hint)

/-- **DVA with Gaussian exposure, no wrong-way risk**: `dva` equals `LGDBank · ∫₀..T D(s) ·
[(-m(s))·Φ((-m(s))/(σ(s)√s)) + σ(s)√s·φ((-m(s))/(σ(s)√s))] · defaultDensity h s ds` —
`cva_gaussian`'s right-hand side with `m` replaced by `-m`, from `cva_gaussian` at the mirrored
exposure `-(m(s) + σ(s)√s Z) = -m(s) + σ(s)√s·(-Z)`; `gaussianReal_neg` keeps the driver `-Z`
standard normal. -/
theorem dva_gaussian [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {h : ℝ → ℝ} (hh : Continuous h) (hnn : ∀ s, 0 ≤ h s) {τBank : Ω₂ → ℝ}
    (hτ : Measurable τBank)
    (hcdf : ∀ a, 0 ≤ a → μ {ω | τBank ω ≤ a} = 1 - ENNReal.ofReal (hazardSurvival h a))
    {D : ℝ → ℝ} (hD : Measurable D) {C : ℝ} (hDb : ∀ s, |D s| ≤ C) {m σ : ℝ → ℝ}
    (hm : Measurable m) (hσ : Measurable σ) {M S : ℝ} (hmb : ∀ s, |m s| ≤ M)
    (hσpos : ∀ s, 0 < σ s) (hσb : ∀ s, σ s ≤ S) {Z : Ω₁ → ℝ} (hZm : Measurable Z)
    (hZ : HasLaw Z (gaussianReal 0 1) ν) (LGDBank : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    dva LGDBank D (fun s ω ↦ m s + σ s * √s * Z ω) τBank T ν μ
      = LGDBank * ∫ s in (0:ℝ)..T, D s * ((-m s) * Phi ((-m s) / (σ s * √s))
          + σ s * √s * gaussianPDFReal 0 1 ((-m s) / (σ s * √s))) * defaultDensity h s := by
  have hZ' : HasLaw (fun ω ↦ -(Z ω)) (gaussianReal 0 1) ν :=
    (neg_zero : -(0:ℝ) = 0) ▸ gaussianReal_neg hZ
  have heq : (fun s ω ↦ -(m s + σ s * √s * Z ω)) = fun s ω ↦ (-m s) + σ s * √s * (-(Z ω)) := by
    funext s ω; ring
  have hmb' : ∀ s, |(-m s)| ≤ M := fun s ↦ (abs_neg (m s)).le.trans (hmb s)
  rw [dva, heq]
  exact cva_gaussian hh hnn hτ hcdf hD hDb hm.neg hσ hmb' hσpos hσb hZm.neg hZ' LGDBank hT

end MathFin.CVA
