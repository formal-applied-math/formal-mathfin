/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.FixedIncome.CVA

/-!
# DVA as a CVA mirror

Debt valuation adjustment is the counterparty's expected loss — equivalently, the bank's own
gain — on the bank's *own* default: structurally `CVA.cva` applied to the bank's own default
time/hazard and the exposure seen from the bank's side, `-V` (`cva`'s own convention has `V > 0`
as the counterparty owing the bank, an asset to the bank; the bank owes the counterparty exactly
when `V < 0`, which is the liability regime `-V > 0` mirrors — on the bank's own default the
counterparty does not recover that liability in full, a loss to the counterparty that is booked
as a gain to the bank, since its own liability is extinguished). This file proves that mirror as
a genuine corollary of `cva`'s own definition and of `cva_gaussian` (`dva_gaussian`), never as an
independent construction.

**What is modelled, honestly**: `cva`'s own independence hypothesis — the default time
independent of the exposure (no wrong-way risk) — carries over unchanged, now read as "the bank's
own default is independent of the exposure". This is the single-factor mirror: the bank's default
time and the counterparty's default time are not jointly modelled here, so no statement is made
about a correlated bilateral picture (bank and counterparty defaults together, wrong-way risk on
either leg). A full bilateral CVA/DVA model would need that joint law; it is out of scope.

## Main results

* `dva`: the bank's own-default mirror of `CVA.cva`.
* `dva_gaussian`: the Gaussian closed form, a corollary of `CVA.cva_gaussian` applied to the
  mirrored exposure `-(m(s) + σ(s)√s Z) = -m(s) + σ(s)√s·(-Z)`, using `gaussianReal_neg` to keep
  the driver standard normal.

## References

* J. C. Hull, *Options, Futures, and Other Derivatives* (bilateral CVA/DVA).
-/

@[expose] public section

namespace MathFin.CVA

open MeasureTheory Real ProbabilityTheory MathFin.DefaultDensity

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {ν : Measure Ω₁} {μ : Measure Ω₂}

/-- **DVA**: the bank's own-default mirror of `cva` — the bank's own default time `τBank`, applied
to the exposure `-V` seen from the bank's side; any hazard structure enters only through the CDF
hypothesis of `dva_gaussian`, exactly as in `cva_gaussian`. Inherits `cva`'s no-wrong-way-risk
(independence) assumption, now read for the bank's own default. -/
noncomputable def dva (LGDBank : ℝ) (D : ℝ → ℝ) (V : ℝ → Ω₁ → ℝ) (τBank : Ω₂ → ℝ) (T : ℝ)
    (ν : Measure Ω₁) (μ : Measure Ω₂) : ℝ :=
  cva LGDBank D (fun s ω ↦ -(V s ω)) τBank T ν μ

/-- **DVA with Gaussian exposure, no wrong-way risk**: `dva` equals `LGDBank · ∫₀..T D(s) ·
[(-m(s))·Φ((-m(s))/(σ(s)√s)) + σ(s)√s·φ((-m(s))/(σ(s)√s))] · defaultDensity h s ds` —
`cva_gaussian`'s right-hand side with `m` replaced by `-m`. Proved as a genuine corollary of
`cva_gaussian`, applied to the mirrored exposure `-(m(s) + σ(s)√s Z) = -m(s) + σ(s)√s·(-Z)`;
`gaussianReal_neg` keeps the driver `-Z` standard normal. -/
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
