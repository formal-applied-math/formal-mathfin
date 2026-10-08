/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.JumpDiffusionEsscher
public import MathFin.BlackScholes.JumpDiffusionIdentifiability
public import MathFin.BlackScholes.CallSpreadDigital

/-!
# Incompleteness at one date: two compensated laws, two call prices

With jumps, being compensated does not pin down the price of a call. Two standard pricing laws
are built from the same physical characteristics `(b, σ, Λ, ν)`:

* the Esscher law, the physical log-return law tilted by `e^{θy}` at an Esscher parameter `θ`,
  which is the jump-diffusion law with drift `b + θσ²`, rate `Λm(θ)` and jump law `ν_θ`
  (`jumpDiffusionIncrementLaw_tilted`) and is compensated (`compensated_tilted_iff`);
* the Merton measure, which keeps `σ`, `Λ` and `ν` and moves only the drift, to the compensated
  drift `r − σ²/2 − Λ(∫ eˣ dν − 1)`.

`exists_call_esscher_ne_merton`: if the jumps are nontrivial (`Λ ≠ 0` and `ν` not concentrated at
`0`), the jump law's moment-generating function is finite near `0` and near `θ` with finite moments
of orders `1` and `1 + θ`, and the physical drift is not already the compensated one, then the two
laws price the call differently at some strike. The physical drift being off the compensated one
makes `θ ≠ 0`. Equal call prices at every strike would make the two laws equal
(`measure_eq_of_integral_call_eq`). Equal laws have equal Lévy measures off `0`
(`jumpDiffusionIncrementLaw_eq_iff`), but the Esscher law's is `e^{θx}` times the physical one
(`smul_tilted_eq_withDensity`), and `e^{θx} ≠ 1` for `x ≠ 0`.

The statement is about laws at one date. The Esscher law is a tilt of the physical law, hence
equivalent to it (Mathlib's `tilted_absolutelyContinuous` and `absolutelyContinuous_tilted`); that
the Merton measure's law is equivalent to the physical law, and the process-level changes of measure
behind both, are not formalized here.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped NNReal ENNReal Topology

/-- **Incompleteness at one date.** Let the jumps be nontrivial (`Λ ≠ 0` and `ν {0}ᶜ ≠ 0`), let
the jump law's moment-generating function be finite near `0` and near `θ`, with finite moments of
orders `1` and `1 + θ`, and let `θ` be an Esscher parameter, `κ(θ + 1) − κ(θ) = r`. If the physical
drift `b` is not the compensated drift, then the Esscher law is compensated, and there is a strike
`K > 0` at which the discounted call price under it differs from the call price under the Merton
measure, the law with the same `σ`, `Λ`, `ν` and the compensated drift. -/
theorem exists_call_esscher_ne_merton {S r b σ : ℝ} (hS : 0 < S) {Λ : ℝ≥0} (hΛ : Λ ≠ 0)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν {0}ᶜ ≠ 0)
    (h0 : 0 ∈ interior (integrableExpSet id ν)) (h1 : Integrable rexp ν) {θ : ℝ}
    (hθν : θ ∈ interior (integrableExpSet id ν))
    (h1θ : Integrable (fun x ↦ rexp ((1 + θ) * x)) ν)
    (hθ : jumpDiffusionExponent b σ Λ ν (1 + θ) - jumpDiffusionExponent b σ Λ ν θ = r)
    (hb : b ≠ r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) {τ : ℝ≥0} (hτ : 0 < τ) :
    b + θ * σ ^ 2 = r - σ ^ 2 / 2
        - (Λ * jumpMoment ν θ : ℝ≥0) * (∫ x, rexp x ∂(ν.tilted (θ * ·)) - 1) ∧
      ∃ K, 0 < K ∧
        ∫ y, rexp (-r * τ) * max (S * rexp y - K) 0
            ∂((jumpDiffusionIncrementLaw b σ Λ ν τ).tilted (θ * ·))
          ≠ jumpDiffusionCallPrice S K r (r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) σ Λ ν τ := by
  have hθ' : Integrable (fun x ↦ rexp (θ * x)) ν := interior_subset (s := integrableExpSet id ν) hθν
  have : IsProbabilityMeasure (ν.tilted (θ * ·)) := isProbabilityMeasure_tilted hθ'
  refine ⟨(compensated_tilted_iff b σ r Λ hθ').2 hθ, ?_⟩
  -- `θ ≠ 0`: at `θ = 0` the Esscher condition says that the physical drift is compensated
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    refine hb ((compensated_iff_exponent_one b σ r Λ ν).2 ?_)
    have h00 : jumpDiffusionExponent b σ Λ ν 0 = 0 := by simp [jumpDiffusionExponent]
    simpa [h00] using hθ
  by_contra hall
  push_neg at hall
  -- equal call prices at every strike make the Esscher law the Merton measure's law
  have hE1 : Integrable rexp (ν.tilted (θ * ·)) := by
    simpa only [one_mul] using integrable_exp_mul_tilted_const_mul hθ' h1θ
  have hlaw : jumpDiffusionIncrementLaw (b + θ * σ ^ 2) σ (Λ * jumpMoment ν θ) (ν.tilted (θ * ·)) τ
      = jumpDiffusionIncrementLaw (r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) σ Λ ν τ := by
    refine measure_eq_of_integral_call_eq hS (integrable_exp_jumpDiffusionIncrementLaw _ _ _ hE1 τ)
      (integrable_exp_jumpDiffusionIncrementLaw _ _ _ h1 τ) fun K hK ↦ ?_
    have h := hall K hK
    rw [jumpDiffusionIncrementLaw_tilted b σ Λ hθν τ, jumpDiffusionCallPrice, integral_const_mul,
      integral_const_mul] at h
    exact mul_left_cancel₀ (Real.exp_pos _).ne' h
  -- so the Lévy measures agree off `0`: `e^{θx}·Λν = Λν` there
  have hLevy := ((jumpDiffusionIncrementLaw_eq_iff (zero_mem_interior_integrableExpSet_tilted hθν)
    h0 hτ).1 hlaw).2
  rw [smul_tilted_eq_withDensity Λ hθ', Measure.restrict_smul, Measure.restrict_smul,
    restrict_withDensity (measurableSet_singleton (0 : ℝ)).compl] at hLevy
  have hLevy' : (ν.restrict {0}ᶜ).withDensity (fun x ↦ ENNReal.ofReal (rexp (θ * x)))
      = (ν.restrict {0}ᶜ).withDensity 1 := by
    have h := congrArg (fun μ : Measure ℝ ↦ Λ⁻¹ • μ) hLevy
    simp only [smul_smul, inv_mul_cancel₀ hΛ, one_smul] at h
    rw [h, withDensity_one]
  have hae := (withDensity_eq_iff_of_sigmaFinite (by fun_prop) measurable_one.aemeasurable).1 hLevy'
  -- which forces `θx = 0`, that is `x = 0`, almost everywhere off `0`
  have hfalse : ∀ᵐ x ∂(ν.restrict {0}ᶜ), False := by
    filter_upwards [hae, ae_restrict_mem (measurableSet_singleton (0 : ℝ)).compl] with x hx hx0
    have hx' : ENNReal.ofReal (rexp (θ * x)) = 1 := hx
    rw [ENNReal.ofReal_eq_one, Real.exp_eq_one_iff] at hx'
    exact mem_compl_singleton_iff.1 hx0 ((mul_eq_zero.1 hx').resolve_left hθ0)
  exact hν (Measure.restrict_eq_zero.1 (ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hfalse)))

end MathFin
