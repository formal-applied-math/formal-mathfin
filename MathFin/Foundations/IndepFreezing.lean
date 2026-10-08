/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Freezing an independent variable

If `X` and `Y` are independent, the expectation of `g(X, Y)` can be computed by freezing `X` at
a value `x`, averaging `g(x, Y)` over `Y` alone, and then averaging the result over the law of
`X`:

  `𝔼[g(X, Y)] = ∫ x, 𝔼[g(x, Y)] d(law X)`.

This is the *freezing lemma* (Shreve's *independence lemma*, *Stochastic Calculus for Finance II*,
Lemma 2.3.4, in its unconditional form). When `X = N` is a count it is the law of total
expectation over the number of jumps, the step every Poisson-mixture computation takes: the
Merton jump-diffusion price (`BlackScholes/MertonModel.lean`) and the compound-Poisson moment
generating function (`Actuarial/CompoundPoissonMGF.lean`) both go through it. With `X` a jump part
of any law it is the mixing formula of `BlackScholes/JumpDiffusionMixing.lean`: a jump-diffusion
call is the Black–Scholes price averaged over the jumps.

The proof composes two Mathlib facts: independence makes the joint law the product of the
marginal laws (`IndepFun.map_prod_eq_prod_map_map`), and an integral against a product measure
is an iterated integral (`integral_prod`).

## Main results

* `integrable_comp_prodMk_iff_of_indepFun`: `g(X, Y)` is integrable exactly when `g` is
  integrable against the product of the laws.
* `integral_comp_prodMk_of_indepFun`: the freezing lemma.
* `integrable_prod_map_of_countable`: for a countable-valued `X`, integrability against the
  product of the laws is checked one value of `X` at a time.
* `integral_comp_prodMk_of_indepFun_of_countable`: the freezing lemma for a countable-valued `X`
  and a nonnegative `g`, with integrability checked one value of `X` at a time.
* `integral_comp_of_hasLaw_of_countable`: integrating out a countable variable. For `X` with
  a countable law `ν`, independent of `Y`, and a nonnegative `F` whose expectations
  `c a = 𝔼[F(a, Y)]` are finite and integrable against `ν`, `𝔼[F(X, Y)] = ∫ a, c a ∂ν`. With
  `ν = Poisson(Λ)` this is the Poisson-mixture step.
* `indepFun_prodMk_of_indepFun_prodMk`: if `X` is independent of `(Y, W)` and `Y` of `W`, then
  `Y` is independent of `(X, W)`. Mutual independence of three variables can be stated with any
  of them split off first.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω α β E : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} [NormedAddCommGroup E]
  {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → α} {Y : Ω → β}

/-- For independent `X` and `Y`, `g(X, Y)` is integrable exactly when `g` is integrable against
the product of the laws of `X` and `Y`. -/
theorem integrable_comp_prodMk_iff_of_indepFun (hXY : X ⟂ᵢ[P] Y) (hX : AEMeasurable X P)
    (hY : AEMeasurable Y P) {g : α × β → E}
    (hg : AEStronglyMeasurable g ((P.map X).prod (P.map Y))) :
    Integrable (fun ω ↦ g (X ω, Y ω)) P ↔ Integrable g ((P.map X).prod (P.map Y)) := by
  rw [← hXY.map_prod_eq_prod_map_map hX hY] at hg ⊢
  exact (integrable_map_measure hg (hX.prodMk hY)).symm

/-- **The freezing lemma.** For independent `X` and `Y`, and `g` integrable against the product
of their laws, `𝔼[g(X, Y)] = ∫ x, 𝔼[g(x, Y)] d(law X)`. -/
theorem integral_comp_prodMk_of_indepFun [NormedSpace ℝ E] (hXY : X ⟂ᵢ[P] Y)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) {g : α × β → E}
    (hg : Integrable g ((P.map X).prod (P.map Y))) :
    ∫ ω, g (X ω, Y ω) ∂P = ∫ x, ∫ ω, g (x, Y ω) ∂P ∂(P.map X) := by
  have hmap := hXY.map_prod_eq_prod_map_map hX hY
  have hgm : AEStronglyMeasurable g (P.map fun ω ↦ (X ω, Y ω)) := by
    rw [hmap]
    exact hg.aestronglyMeasurable
  calc ∫ ω, g (X ω, Y ω) ∂P = ∫ p, g p ∂(P.map fun ω ↦ (X ω, Y ω)) :=
        (integral_map (hX.prodMk hY) hgm).symm
    _ = ∫ x, ∫ y, g (x, y) ∂(P.map Y) ∂(P.map X) := by rw [hmap, integral_prod g hg]
    _ = ∫ x, ∫ ω, g (x, Y ω) ∂P ∂(P.map X) := integral_congr_ae <| by
        filter_upwards [hg.prod_right_ae] with x hx
        exact integral_map hY hx.aestronglyMeasurable

/-- For a countable-valued `X`, integrability of `g` against the product of the laws is checked
one value of `X` at a time: each `g(a, Y)` integrable, and `a ↦ 𝔼‖g(a, Y)‖` integrable against
the law of `X`. Measurability of the sections suffices, since `X` takes countably many values. -/
theorem integrable_prod_map_of_countable [Countable α] [MeasurableSingletonClass α]
    (hY : AEMeasurable Y P) {g : α × β → ℝ} (hgm : ∀ a, Measurable fun b ↦ g (a, b))
    (hint : ∀ a, Integrable (fun ω ↦ g (a, Y ω)) P)
    (hint' : Integrable (fun a ↦ ∫ ω, ‖g (a, Y ω)‖ ∂P) (P.map X)) :
    Integrable g ((P.map X).prod (P.map Y)) := by
  refine (integrable_prod_iff
    (measurable_from_prod_countable_right (f := g) hgm).aestronglyMeasurable).mpr
    ⟨ae_of_all _ fun a ↦ (integrable_map_measure (hgm a).aestronglyMeasurable hY).mpr (hint a),
      hint'.congr (ae_of_all _ fun a ↦ ?_)⟩
  exact (integral_map hY (hgm a).norm.aestronglyMeasurable).symm

/-- **The freezing lemma for a countable variable.** For a countable-valued `X` independent of `Y`
and a nonnegative `g`, if each `g(a, Y)` is integrable and `a ↦ 𝔼[g(a, Y)]` is integrable against
the law of `X`, then `𝔼[g(X, Y)] = ∫ a, 𝔼[g(a, Y)] d(law X)`. -/
theorem integral_comp_prodMk_of_indepFun_of_countable [Countable α]
    [MeasurableSingletonClass α] (hXY : X ⟂ᵢ[P] Y) (hX : AEMeasurable X P)
    (hY : AEMeasurable Y P) {g : α × β → ℝ} (hgm : ∀ a, Measurable fun b ↦ g (a, b))
    (hg0 : ∀ p, 0 ≤ g p) (hint : ∀ a, Integrable (fun ω ↦ g (a, Y ω)) P)
    (hint' : Integrable (fun a ↦ ∫ ω, g (a, Y ω) ∂P) (P.map X)) :
    ∫ ω, g (X ω, Y ω) ∂P = ∫ a, ∫ ω, g (a, Y ω) ∂P ∂(P.map X) :=
  integral_comp_prodMk_of_indepFun hXY hX hY <| integrable_prod_map_of_countable hY hgm hint <|
    hint'.congr <| ae_of_all _ fun a ↦ integral_congr_ae <| ae_of_all _ fun ω ↦
      (Real.norm_of_nonneg (hg0 (a, Y ω))).symm

/-- **Integrating out a countable variable.** For `X` with a countable law `ν`, independent of
`Y`, and a nonnegative `F`, if each `F(a, Y)` is integrable with expectation `c a` and `c` is
integrable against `ν`, then `𝔼[F(X, Y)] = ∫ a, c a ∂ν`. For a Poisson count this is the
Poisson-mixture step of a compound-Poisson computation. -/
theorem integral_comp_of_hasLaw_of_countable [Countable α] [MeasurableSingletonClass α]
    {ν : Measure α} (hX : HasLaw X ν P) (hY : AEMeasurable Y P) (hXY : X ⟂ᵢ[P] Y)
    {F : α → β → ℝ} (hFm : ∀ a, Measurable fun y ↦ F a y) (hF0 : ∀ a y, 0 ≤ F a y)
    {c : α → ℝ} (hint : ∀ a, Integrable (fun ω ↦ F a (Y ω)) P)
    (hc : ∀ a, ∫ ω, F a (Y ω) ∂P = c a) (hcint : Integrable c ν) :
    ∫ ω, F (X ω) (Y ω) ∂P = ∫ a, c a ∂ν := by
  have hint' : Integrable (fun a ↦ ∫ ω, F a (Y ω) ∂P) (P.map X) := by
    rw [hX.map_eq]
    exact hcint.congr (ae_of_all _ fun a ↦ (hc a).symm)
  calc ∫ ω, F (X ω) (Y ω) ∂P = ∫ a, ∫ ω, F a (Y ω) ∂P ∂(P.map X) :=
        integral_comp_prodMk_of_indepFun_of_countable (g := fun p ↦ F p.1 p.2) hXY
          hX.aemeasurable hY hFm (fun p ↦ hF0 p.1 p.2) hint hint'
    _ = ∫ a, c a ∂ν := by
        rw [hX.map_eq]
        exact integral_congr_ae (ae_of_all _ hc)

/-! ### Re-associating independence -/

/-- Moving the middle factor of a triple product measure to the front:
`(μ ⊗ (ν ⊗ ρ)).map ((a, b, c) ↦ (b, a, c)) = ν ⊗ (μ ⊗ ρ)`. -/
theorem map_prod_prod_rotate {γ : Type*} {mγ : MeasurableSpace γ} (μ : Measure α)
    (ν : Measure β) (ρ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    (μ.prod (ν.prod ρ)).map (fun p : α × β × γ ↦ (p.2.1, p.1, p.2.2)) = ν.prod (μ.prod ρ) := by
  have hrot : (fun p : α × β × γ ↦ (p.2.1, p.1, p.2.2))
      = MeasurableEquiv.prodAssoc ∘ Prod.map Prod.swap id ∘ MeasurableEquiv.prodAssoc.symm :=
    rfl
  rw [hrot, ← Measure.map_map MeasurableEquiv.prodAssoc.measurable
      ((measurable_swap.prodMap measurable_id).comp MeasurableEquiv.prodAssoc.symm.measurable),
    ← Measure.map_map (measurable_swap.prodMap measurable_id)
      MeasurableEquiv.prodAssoc.symm.measurable,
    ← Measure.prodAssoc_prod (μ := μ), MeasurableEquiv.map_symm_map,
    ← Measure.map_prod_map (μ.prod ν) ρ measurable_swap measurable_id, Measure.prod_swap,
    Measure.map_id, Measure.prodAssoc_prod]

/-- **Re-associating independence.** If `X` is independent of `(Y, W)` and `Y` of `W`, then `Y`
is independent of `(X, W)`. Either pair of hypotheses says that `X`, `Y` and `W` are mutually
independent: the joint law is the product of the three marginal laws. -/
theorem indepFun_prodMk_of_indepFun_prodMk {γ : Type*} {mγ : MeasurableSpace γ} {W : Ω → γ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (hW : AEMeasurable W P)
    (hXYW : X ⟂ᵢ[P] fun ω ↦ (Y ω, W ω)) (hYW : Y ⟂ᵢ[P] W) :
    Y ⟂ᵢ[P] fun ω ↦ (X ω, W ω) := by
  have hXW : X ⟂ᵢ[P] W := hXYW.comp measurable_id measurable_snd
  have hrot : Measurable fun p : α × β × γ ↦ (p.2.1, p.1, p.2.2) := by fun_prop
  rw [indepFun_iff_map_prod_eq_prod_map_map hY (hX.prodMk hW),
    hXW.map_prod_eq_prod_map_map hX hW,
    show (fun ω ↦ (Y ω, X ω, W ω))
      = (fun p : α × β × γ ↦ (p.2.1, p.1, p.2.2)) ∘ fun ω ↦ (X ω, Y ω, W ω) from rfl,
    ← AEMeasurable.map_map_of_aemeasurable hrot.aemeasurable (hX.prodMk (hY.prodMk hW)),
    hXYW.map_prod_eq_prod_map_map hX (hY.prodMk hW), hYW.map_prod_eq_prod_map_map hY hW]
  exact map_prod_prod_rotate _ _ _

end MathFin
