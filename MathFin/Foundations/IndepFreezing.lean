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
* `integral_comp_prodMk_of_indepFun_of_countable`: the freezing lemma for a countable-valued `X`
  and a nonnegative `g`, with integrability checked one value of `X` at a time.
* `integral_comp_of_hasLaw_poissonMeasure`: conditioning on a Poisson count. For
  `N ∼ Poisson(Λ)` independent of `Y`, `𝔼[F(N, Y)] = ∫ n, 𝔼[F(n, Y)] ∂Poisson(Λ)`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

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

/-- **Conditioning on a Poisson count.** For `N ∼ Poisson(Λ)` independent of `Y` and a nonnegative
`F`, if each `F(n, Y)` is integrable with expectation `c n`, and `c` is integrable against
`Poisson(Λ)`, then `𝔼[F(N, Y)] = ∫ n, c n ∂Poisson(Λ)`. -/
theorem integral_comp_of_hasLaw_poissonMeasure {Λ : ℝ≥0} {N : Ω → ℕ}
    (hN : HasLaw N (poissonMeasure Λ) P) (hY : AEMeasurable Y P) (hNY : N ⟂ᵢ[P] Y)
    {F : ℕ → β → ℝ} (hFm : ∀ n, Measurable fun y ↦ F n y) (hF0 : ∀ n y, 0 ≤ F n y)
    {c : ℕ → ℝ} (hint : ∀ n, Integrable (fun ω ↦ F n (Y ω)) P)
    (hc : ∀ n, ∫ ω, F n (Y ω) ∂P = c n) (hcint : Integrable c (poissonMeasure Λ)) :
    ∫ ω, F (N ω) (Y ω) ∂P = ∫ n, c n ∂(poissonMeasure Λ) := by
  have hint' : Integrable (fun n ↦ ∫ ω, F n (Y ω) ∂P) (P.map N) := by
    rw [hN.map_eq]
    exact hcint.congr (ae_of_all _ fun n ↦ (hc n).symm)
  calc ∫ ω, F (N ω) (Y ω) ∂P = ∫ n, ∫ ω, F n (Y ω) ∂P ∂(P.map N) :=
        integral_comp_prodMk_of_indepFun_of_countable (g := fun p ↦ F p.1 p.2) hNY
          hN.aemeasurable hY hFm (fun p ↦ hF0 p.1 p.2) hint hint'
    _ = ∫ n, c n ∂(poissonMeasure Λ) := by
        rw [hN.map_eq]
        exact integral_congr_ae (ae_of_all _ hc)

end MathFin
