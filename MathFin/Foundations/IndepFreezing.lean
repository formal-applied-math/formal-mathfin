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
generating function (`Actuarial/CompoundPoissonMGF.lean`) both go through it.

The proof composes two Mathlib facts: independence makes the joint law the product of the
marginal laws (`IndepFun.map_prod_eq_prod_map_map`), and an integral against a product measure
is an iterated integral (`integral_prod`).

## Main results

* `integrable_comp_prodMk_iff_of_indepFun`: `g(X, Y)` is integrable exactly when `g` is
  integrable against the product of the laws.
* `integral_comp_prodMk_of_indepFun`: the freezing lemma.
* `integrable_prod_map_of_countable`: for a countable-valued `X`, integrability against the
  product of the laws is checked one value of `X` at a time.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω α β E : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
theorem integral_comp_prodMk_of_indepFun (hXY : X ⟂ᵢ[P] Y) (hX : AEMeasurable X P)
    (hY : AEMeasurable Y P) {g : α × β → E} (hg : Integrable g ((P.map X).prod (P.map Y))) :
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

end MathFin
