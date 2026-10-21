/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.BlackScholes.GarmanNormalForm

/-!
# Basket option pricing: the moment-matching approximation

**This is an approximation, not an exact closed form.** A basket of
correlated lognormals `B_T = ∑ᵢ wᵢ Sᵢ_T` is *not* itself lognormal — the sum
of lognormals has no closed-form law. The standard market practice (the same
"replace the true law by a moment-matched lognormal" move as single-asset
Asian options, cf. Turnbull-Wakeman) is to match the first two moments of the
basket to a single lognormal and price that lognormal with the ordinary
Black-Scholes closed form.

For forwards `Fᵢ = Sᵢ₀ · e^{rT}`, weights `wᵢ`, vols `σᵢ` and correlations
`ρᵢⱼ`, the basket forward's first two (risk-neutral) moments under a joint
lognormal model are (not proved here)

  `M₁ = ∑ᵢ wᵢ Fᵢ`,
  `M₂ = ∑ᵢ ∑ⱼ wᵢ wⱼ Fᵢ Fⱼ · e^{ρᵢⱼ σᵢ σⱼ T}`,

matching the lognormal moments `𝔼[X] = m`, `𝔼[X²] = m² e^{σ_eff² T}` forces
the **effective variance** `σ_eff² = log(M₂ / M₁²) / T`. Feeding `(M₁,
σ_eff)` into the Garman normal form (`GarmanNormalForm.lean`) at `A = DF·M₁`
gives the moment-matched basket price — literally the ordinary BS closed
form, parameterised by the matched moments, in the same spirit as Kirk's
spread approximation, which is BS parameterised by its pseudo-asset.

## Results

* `basketM1`, `basketM2`: the matched first and second moments.
* `basketEffVol`: the moment-matched effective volatility
  `√(log(M₂/M₁²)/T)`.
* `basketMomentMatchPrice`: the approximate basket call price, `bsVGarman`
  at `A = DF·M₁`, the matched `σ_eff`.
* `basketEffVol_single`: **consistency check** — with a single asset
  (`n = 1`, weight `1`, self-correlation `1`; `F ≠ 0`, `T > 0`, `σ ≥ 0`), the
  matched effective vol is exactly the asset's own vol `σ`. A one-asset basket
  is lognormal, and the matching recovers its volatility; the statement is
  about `basketEffVol`, not about the price.
-/

@[expose] public section

namespace MathFin

open Real Finset

/-- **The matched first moment**: `M₁ = ∑ᵢ wᵢ Fᵢ`, the basket forward's mean. -/
noncomputable def basketM1 {n : ℕ} (w F : Fin n → ℝ) : ℝ :=
  ∑ i, w i * F i

/-- **The matched second moment**: `M₂ = ∑ᵢ∑ⱼ wᵢwⱼFᵢFⱼ · e^{ρᵢⱼσᵢσⱼT}`, from the
pairwise lognormal cross-moments `𝔼[Sᵢ_T Sⱼ_T] = Fᵢ Fⱼ e^{ρᵢⱼσᵢσⱼT}` (that `M₂` is the
second moment of the basket under a joint lognormal model is not proved here). -/
noncomputable def basketM2 {n : ℕ} (w F σ : Fin n → ℝ) (ρ : Fin n → Fin n → ℝ) (T : ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * F i * F j * Real.exp (ρ i j * σ i * σ j * T)

/-- **The moment-matched effective volatility**: solving
`M₂ = M₁² · e^{σ_eff²T}` for `σ_eff`. Meaningful when `M₂ ≥ M₁² > 0` and `T > 0`
(`M₂ ≥ M₁²` holds for a positive semidefinite correlation matrix and `T ≥ 0`, and
`M₁ > 0` for nonnegative weights and positive forwards with some weight positive;
neither is proved here). Otherwise the value comes from Mathlib's conventions for
`Real.log`, division and `Real.sqrt` and carries no meaning; it need not be `0`
(for example `M₂/M₁² < −1` with `T > 0` gives a positive value). -/
noncomputable def basketEffVol {n : ℕ} (w F σ : Fin n → ℝ) (ρ : Fin n → Fin n → ℝ) (T : ℝ) : ℝ :=
  Real.sqrt (Real.log (basketM2 w F σ ρ T / (basketM1 w F) ^ 2) / T)

/-- **The moment-matching basket call price**: the Garman-normal BS closed
form at `A = DF · M₁`, discount factor `DF`, and the matched effective
volatility. Documented as an **approximation**: the true basket law is not
lognormal, so this is not claimed to equal the discounted expected basket
payoff — only that it is literally the BS closed form at these matched
moments. -/
noncomputable def basketMomentMatchPrice {n : ℕ} (w F σ : Fin n → ℝ) (ρ : Fin n → Fin n → ℝ)
    (K DF T : ℝ) : ℝ :=
  bsVGarman (DF * basketM1 w F) K DF (basketEffVol w F σ ρ T) T

/-- **Single-asset consistency check**: a "basket" of one asset with weight
`1` and (trivial) self-correlation `1` collapses the moment-matched
effective vol to exactly that asset's own volatility `σ`, for `F ≠ 0`, `T > 0`
and `σ ≥ 0`. A one-asset basket is lognormal, and the matching recovers its
volatility; the statement is about `basketEffVol`, not about the price. -/
theorem basketEffVol_single (F σ T : ℝ) (hF : F ≠ 0) (hT : 0 < T) (hσ : 0 ≤ σ) :
    basketEffVol (n := 1) (fun _ ↦ 1) (fun _ ↦ F) (fun _ ↦ σ) (fun _ _ ↦ 1) T = σ := by
  unfold basketEffVol basketM2 basketM1
  simp only [Fin.sum_univ_one, one_mul, mul_one]
  rw [show F * F * Real.exp (σ * σ * T) / F ^ 2 = Real.exp (σ * σ * T) by
    field_simp]
  rw [Real.log_exp, show σ * σ * T / T = σ ^ 2 by field_simp]
  exact Real.sqrt_sq hσ

end MathFin
