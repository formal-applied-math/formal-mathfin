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
# Incompleteness at one date: two equivalent compensated laws, two call prices

With jumps, being compensated does not pin down the price of a call. Two standard pricing laws
are built from the same physical characteristics `(b, σ, Λ, ν)`:

* the Esscher law, the physical log-return law tilted by `e^{θy}` at an Esscher parameter `θ`,
  which is the jump-diffusion law with drift `b + θσ²`, rate `Λm(θ)` and jump law `ν_θ`
  (`jumpDiffusionIncrementLaw_tilted`) and is compensated (`compensated_tilted_iff`);
* the Merton measure, which keeps `σ`, `Λ` and `ν` and moves only the drift, to the compensated
  drift `r − σ²/2 − Λ(∫ eˣ dν − 1)`.

For `σ ≠ 0` both laws are equivalent to the physical law at one date. The Esscher law is a tilt of
it (Mathlib's `tilted_absolutelyContinuous` and `absolutelyContinuous_tilted`). A change of drift
is a move of the Gaussian sample of the canonical model, and the moved Gaussian `N(m, 1)` is the
Esscher tilt of `N(0, 1)` (`gaussianReal_tilted_const_mul`), equivalent to it: this is static
Girsanov on the Gaussian factor (`jumpDiffusionIncrementLaw_absolutelyContinuous`). For `σ = 0`
the Merton law need not be equivalent to the physical law: without a Gaussian part the physical
law has an atom at `bτ`, the event of no jumps, and a change of drift moves it.

`exists_call_esscher_ne_merton`: let `σ ≠ 0`, let the jumps be nontrivial (`Λ > 0` and `ν` not the
point mass at `0`), and let the jump law's moment-generating function be finite near `0` and near
`θ`, with finite exponential moments `∫ eˣ dν` and `∫ e^{(1+θ)x} dν`. If the physical drift is not
already the compensated one, the two laws are equivalent to the physical law, both have the
forward `∫ eʸ = e^{rτ}`, and they price the call differently at some strike. The physical drift
being off the compensated one makes `θ ≠ 0`. Equal call prices at every strike would make the two
laws equal (`measure_eq_of_integral_call_eq`). Equal laws have equal Lévy measures off `0`
(`jumpDiffusionIncrementLaw_eq_iff`), but the Esscher law's is `e^{θx}` times the physical one
(`smul_tilted_eq_withDensity`), and `e^{θx} ≠ 1` for `x ≠ 0`.

The statement is about laws at one date. The process-level changes of measure behind the two laws,
equivalent martingale measures for the price process, are not formalized here.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped NNReal ENNReal Topology

/-- **A change of drift gives an equivalent law** (static Girsanov on the Gaussian factor). For
`σ ≠ 0` and `τ > 0`, the log-return law with drift `b'` is absolutely continuous with respect to the
one with drift `b`; with the roles exchanged, the two laws are equivalent. The drift `b'` is the
drift `b` with the Gaussian sample moved by `m = (b' − b)√τ/σ`, and `N(m, 1)` is the Esscher tilt of
`N(0, 1)` (`gaussianReal_tilted_const_mul`), absolutely continuous with respect to it (Mathlib's
`tilted_absolutelyContinuous`). -/
lemma jumpDiffusionIncrementLaw_absolutelyContinuous (b b' : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (Λ : ℝ≥0)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionIncrementLaw b' σ Λ ν τ ≪ jumpDiffusionIncrementLaw b σ Λ ν τ := by
  have hs : σ * Real.sqrt τ ≠ 0 := mul_ne_zero hσ (Real.sqrt_pos.2 (NNReal.coe_pos.2 hτ)).ne'
  obtain ⟨m, hm⟩ : ∃ m, σ * Real.sqrt τ * m = (b' - b) * τ :=
    ⟨(b' - b) * τ / (σ * Real.sqrt τ), mul_div_cancel₀ _ hs⟩
  have hid : Measurable (@id (ℕ × (ℕ → ℝ))) := measurable_id
  -- the drift `b'` is the drift `b` with the Gaussian sample moved by `m`
  have hL : jumpDiffusionLogReturn b' σ τ
      = jumpDiffusionLogReturn b σ τ ∘ Prod.map (· + m) id := by
    funext ω
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, jumpDiffusionLogReturn]
    linear_combination -hm
  -- and moving the sample by `m` turns `N(0, 1)` into its Esscher tilt `N(m, 1)`
  have hshift : (jumpDiffusionMeasure (Λ * τ) ν).map (Prod.map (· + m) id)
      = ((gaussianReal 0 1).tilted (m * ·)).prod
          ((poissonMeasure (Λ * τ)).prod (Measure.infinitePi fun _ : ℕ ↦ ν)) := by
    rw [jumpDiffusionMeasure, ← Measure.map_prod_map _ _ (measurable_add_const m) hid,
      gaussianReal_map_add_const, Measure.map_id, gaussianReal_tilted_const_mul, NNReal.coe_one,
      mul_one]
  unfold jumpDiffusionIncrementLaw
  rw [hL, ← Measure.map_map (measurable_jumpDiffusionLogReturn b σ τ)
    ((measurable_add_const m).prodMap hid), hshift]
  unfold jumpDiffusionMeasure
  exact ((tilted_absolutelyContinuous (gaussianReal 0 1) (m * ·)).prod
    Measure.AbsolutelyContinuous.rfl).map (measurable_jumpDiffusionLogReturn b σ τ)

/-- **Incompleteness at one date.** Let `σ ≠ 0`, let the jumps be nontrivial (`Λ > 0` and `ν` not
the point mass at `0`), let the jump law's moment-generating function be finite near `0` and near
`θ`, with finite exponential moments `∫ eˣ dν` and `∫ e^{(1+θ)x} dν`, and let `θ` be an Esscher
parameter, `κ(1 + θ) − κ(θ) = r`. If the physical drift `b` is not the compensated drift `c`, then
at every date `τ > 0` the Esscher law and the Merton measure's law (the same `σ`, `Λ`, `ν` and the
drift `c`) are both equivalent to the physical law and both compensated, `∫ eʸ = e^{rτ}`, and for
every spot `S > 0` there is a strike `K > 0` at which the discounted call prices under them
differ. -/
theorem exists_call_esscher_ne_merton {S r b c σ : ℝ} (hS : 0 < S) (hσ : σ ≠ 0) {Λ : ℝ≥0}
    (hΛ : 0 < Λ) {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν0 : ν ≠ Measure.dirac 0)
    (h0 : 0 ∈ interior (integrableExpSet id ν)) (h1 : Integrable rexp ν) {θ : ℝ}
    (hθν : θ ∈ interior (integrableExpSet id ν))
    (h1θ : Integrable (fun x ↦ rexp ((1 + θ) * x)) ν)
    (hθ : jumpDiffusionExponent b σ Λ ν (1 + θ) - jumpDiffusionExponent b σ Λ ν θ = r)
    (hc : c = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) (hb : b ≠ c) {τ : ℝ≥0} (hτ : 0 < τ) :
    ((jumpDiffusionIncrementLaw b σ Λ ν τ).tilted (θ * ·) ≪ jumpDiffusionIncrementLaw b σ Λ ν τ ∧
        jumpDiffusionIncrementLaw b σ Λ ν τ ≪ (jumpDiffusionIncrementLaw b σ Λ ν τ).tilted (θ * ·) ∧
        ∫ y, rexp y ∂((jumpDiffusionIncrementLaw b σ Λ ν τ).tilted (θ * ·)) = rexp (r * τ)) ∧
      (jumpDiffusionIncrementLaw c σ Λ ν τ ≪ jumpDiffusionIncrementLaw b σ Λ ν τ ∧
        jumpDiffusionIncrementLaw b σ Λ ν τ ≪ jumpDiffusionIncrementLaw c σ Λ ν τ ∧
        ∫ y, rexp y ∂(jumpDiffusionIncrementLaw c σ Λ ν τ) = rexp (r * τ)) ∧
      ∃ K, 0 < K ∧
        ∫ y, rexp (-r * τ) * max (S * rexp y - K) 0
            ∂((jumpDiffusionIncrementLaw b σ Λ ν τ).tilted (θ * ·))
          ≠ jumpDiffusionCallPrice S K r c σ Λ ν τ := by
  have hθ' : Integrable (fun x ↦ rexp (θ * x)) ν := interior_subset (s := integrableExpSet id ν) hθν
  have : IsProbabilityMeasure (ν.tilted (θ * ·)) := isProbabilityMeasure_tilted hθ'
  have hE1 : Integrable rexp (ν.tilted (θ * ·)) := by
    simpa only [one_mul] using integrable_exp_mul_tilted_const_mul hθ' h1θ
  refine ⟨⟨tilted_absolutelyContinuous _ _, absolutelyContinuous_tilted
      (integrable_exp_mul_jumpDiffusionIncrementLaw b σ Λ hθ' τ), ?_⟩,
    ⟨jumpDiffusionIncrementLaw_absolutelyContinuous b c hσ Λ ν hτ,
      jumpDiffusionIncrementLaw_absolutelyContinuous c b hσ Λ ν hτ, ?_⟩, ?_⟩
  · -- the Esscher law is compensated: its characteristics are at their compensated drift
    rw [jumpDiffusionIncrementLaw_tilted b σ Λ hθν τ,
      integral_exp_jumpDiffusionIncrementLaw _ _ _ hE1]
    congr 1
    linear_combination (τ : ℝ) * (compensated_tilted_iff b σ r Λ hθ').2 hθ
  · -- and so is the Merton measure's law, by construction
    exact integral_exp_jumpDiffusionIncrementLaw_of_compensated h1 hc τ
  subst hc
  -- `θ ≠ 0`: at `θ = 0` the Esscher condition says that the physical drift is compensated
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    refine hb ((compensated_iff_exponent_one b σ r Λ ν).2 ?_)
    have h00 : jumpDiffusionExponent b σ Λ ν 0 = 0 := by simp [jumpDiffusionExponent]
    simpa [h00] using hθ
  -- the jumps move the price: `ν` charges `{0}ᶜ`
  have hν : ν {0}ᶜ ≠ 0 := by
    refine fun h ↦ hν0 ?_
    have hae : (id : ℝ → ℝ) =ᵐ[ν] fun _ ↦ 0 := by
      filter_upwards [compl_mem_ae_iff.2 h] with x hx
      simpa using hx
    simpa using (hasLaw_dirac_of_ae_eq hae).map_eq
  by_contra hall
  push Not at hall
  -- equal call prices at every strike make the Esscher law the Merton measure's law
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
    h0 hτ).1 hlaw).2.2
  rw [smul_tilted_eq_withDensity Λ hθ', Measure.restrict_smul, Measure.restrict_smul,
    restrict_withDensity (measurableSet_singleton (0 : ℝ)).compl] at hLevy
  have hLevy' : (ν.restrict {0}ᶜ).withDensity (fun x ↦ ENNReal.ofReal (rexp (θ * x)))
      = (ν.restrict {0}ᶜ).withDensity 1 := by
    have h := congrArg (fun μ : Measure ℝ ↦ Λ⁻¹ • μ) hLevy
    simp only [smul_smul, inv_mul_cancel₀ hΛ.ne', one_smul] at h
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
