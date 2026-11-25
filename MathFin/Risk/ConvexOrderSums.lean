/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Laws.ConvexOrder
public import MathFin.Risk.ExpectedShortfall
public import Mathlib.Probability.HasLaw

/-!
# Sums of risks in convex order

A loss `X` below `Y` in convex order is less risky to every risk-averse observer, and expected
shortfall sees it: `ES_α(X) ≤ ES_α(Y)` at every level. For the sum `S = X₁ + ⋯ + Xₙ` of risks with
fixed marginals and unknown dependence, a sum that is smallest in convex order among all
couplings would minimise every such risk measure at once. Such a minimum exists for two risks
(the counter-monotonic coupling) and in the jointly mixable cases, but not in general; which
marginals admit one is open (MF-OP-018). This file proves the comparison of expected shortfalls
and a small instance without a minimum: three risks on three atoms each.

## Main definitions

* `uniform3 x y z`: the uniform law on three atoms.

## Main results

* `expectedShortfall_le_of_convexOrder`: `ES_α` is monotone in convex order.
* `exists_not_convexOrder_sum`: for the marginals uniform on `{0, 0, 4}`, `{0, 2, 5}`,
  `{0, 4, 6}`, every coupling's sum fails to be below the sum of some other coupling. So no sum
  with these marginals is a convex-order minimum. The instance is smaller than the published one
  of Bernard, Jiang and Wang (atoms `{0, 3, 8}`, `{0, 6, 16}`, `{0, 7, 13}`). It does not settle
  the open question, which asks for the conditions on the marginals.

## References

* [C. Bernard, X. Jiang and R. Wang, *Risk aggregation with dependence
  uncertainty*][BernardJiangWang2014], Example 3.1
* [R. Wang, *Current open questions in complete mixability*][Wang2015CompleteMixability]
* [R. T. Rockafellar and S. Uryasev, *Conditional value-at-risk for general loss
  distributions*][RockafellarUryasev2002]

## Tags

convex order, risk aggregation, dependence uncertainty, expected shortfall, comonotonicity,
complete mixability, MSC 60E15, MSC 91G70, JEL G22, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

section ExpectedShortfall

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- **Expected shortfall respects convex order.** If the law of `X` is below the law of `Y` in
convex order, `ES_α(X) ≤ ES_α(Y)` at every level `α ∈ (0, 1)`. The Rockafellar–Uryasev objective
of `X` at `c = VaR_α(Y)` bounds `ES_α(X)`; it is below the objective of `Y` at the same `c`,
since the call struck at `c` is worth less under the smaller law; and the latter is `ES_α(Y)`. -/
theorem expectedShortfall_le_of_convexOrder {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : Integrable X P)
    (hY : Integrable Y P') (h : ConvexOrder (P.map X) (P'.map Y)) {α : ℝ} (hα : α ∈ Ioo 0 1) :
    expectedShortfall X P α ≤ expectedShortfall Y P' α := by
  set c := valueAtRisk Y P' α
  have hφ : Continuous fun x : ℝ ↦ max (x - c) 0 := by fun_prop
  have hcall : ∫ ω, max (X ω - c) 0 ∂P ≤ ∫ ω, max (Y ω - c) 0 ∂P' := by
    rw [← integral_map hX.aemeasurable hφ.aestronglyMeasurable,
      ← integral_map hY.aemeasurable hφ.aestronglyMeasurable]
    exact h.integral_call_le c
      ((integrable_map_measure hφ.aestronglyMeasurable hX.aemeasurable).2
        (hX.sub (integrable_const c)).pos_part)
      ((integrable_map_measure hφ.aestronglyMeasurable hY.aemeasurable).2
        (hY.sub (integrable_const c)).pos_part)
  calc expectedShortfall X P α ≤ rockafellarUryasev X P α c :=
        expectedShortfall_le_rockafellarUryasev hX hα c
    _ ≤ rockafellarUryasev Y P' α c := by
        have h1α : 0 ≤ (1 - α)⁻¹ := inv_nonneg.2 (sub_nonneg.2 hα.2.le)
        unfold rockafellarUryasev
        gcongr
    _ = expectedShortfall Y P' α := rockafellarUryasev_valueAtRisk hY hα

end ExpectedShortfall

section NoMinimum

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The uniform law on three atoms `x, y, z`, `(δ_x + δ_y + δ_z)/3`; a repeated atom carries its
multiplicity. -/
noncomputable def uniform3 (x y z : α) : Measure α := (3 : ℝ≥0∞)⁻¹ • (Measure.dirac x + Measure.dirac y + Measure.dirac z)

instance (x y z : α) : IsProbabilityMeasure (uniform3 x y z) :=
  ⟨by
    simp only [uniform3, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [show (1 : ℝ≥0∞) + 1 + 1 = 3 by norm_num]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

/-- The image of a uniform three-atom law is the uniform law on the images. -/
lemma map_uniform3 {f : α → β} (hf : Measurable f) (x y z : α) :
    (uniform3 x y z).map f = uniform3 (f x) (f y) (f z) := by
  simp only [uniform3, Measure.map_smul _ hf.aemeasurable, Measure.map_add _ _ hf, Measure.map_dirac' hf]

/-- A property holds almost surely under `uniform3 x y z` iff it holds at the three atoms. -/
lemma ae_uniform3_iff [MeasurableSingletonClass α] {x y z : α} {p : α → Prop} :
    (∀ᵐ w ∂uniform3 x y z, p w) ↔ p x ∧ p y ∧ p z := by
  simp [uniform3, ae_dirac_eq, and_assoc]

/-- A column `a : Fin 3 → ℝ` on the three-state space with equal weights has the uniform law on
its entries. -/
lemma hasLaw_uniform3 (a : Fin 3 → ℝ) :
    HasLaw a (uniform3 (a 0) (a 1) (a 2)) (uniform3 (0 : Fin 3) 1 2) :=
  ⟨Measurable.of_discrete.aemeasurable, map_uniform3 .of_discrete _ _ _⟩

/-- **Sums with given marginals need not have a convex-order minimum.** Take `X₁, X₂, X₃` uniform
on the atoms `{0, 0, 4}`, `{0, 2, 5}` and `{0, 4, 6}`. Whatever their dependence, some other
coupling of the same marginals, on three equally likely states, has a sum that the given sum is
not below in convex order.

Two couplings do it. In the first the sum takes the values `6, 6, 9`, in the second `8, 8, 5`. A
sum below both would live on `[6, 8]` (`ConvexOrder.ae_ge_of_ae_ge`,
`ConvexOrder.ae_le_of_ae_le`), but in every coupling, on the event `X₂ = 5` of probability `1/3`,
the sum lies in `{5, 9, 11, 13, 15}`. -/
theorem exists_not_convexOrder_sum {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X₁ X₂ X₃ : Ω → ℝ} (h₁ : HasLaw X₁ (uniform3 0 0 4) P)
    (h₂ : HasLaw X₂ (uniform3 0 2 5) P) (h₃ : HasLaw X₃ (uniform3 0 4 6) P) :
    ∃ Y₁ Y₂ Y₃ : Fin 3 → ℝ, HasLaw Y₁ (uniform3 0 0 4) (uniform3 (0 : Fin 3) 1 2) ∧
      HasLaw Y₂ (uniform3 0 2 5) (uniform3 (0 : Fin 3) 1 2) ∧
      HasLaw Y₃ (uniform3 0 4 6) (uniform3 (0 : Fin 3) 1 2) ∧
      ¬ ConvexOrder (P.map (X₁ + X₂ + X₃)) ((uniform3 (0 : Fin 3) 1 2).map (Y₁ + Y₂ + Y₃)) := by
  by_contra! hmin
  have hS : AEMeasurable (X₁ + X₂ + X₃) P :=
    (h₁.aemeasurable.add h₂.aemeasurable).add h₃.aemeasurable
  have hX : ∀ᵐ ω ∂P, (X₁ ω = 0 ∨ X₁ ω = 0 ∨ X₁ ω = 4) ∧ (X₂ ω = 0 ∨ X₂ ω = 2 ∨ X₂ ω = 5) ∧
      (X₃ ω = 0 ∨ X₃ ω = 4 ∨ X₃ ω = 6) := by
    have e₁ := ae_of_ae_map h₁.aemeasurable
      (p := fun w ↦ w = 0 ∨ w = 0 ∨ w = 4) (by rw [h₁.map_eq, ae_uniform3_iff]; simp)
    have e₂ := ae_of_ae_map h₂.aemeasurable
      (p := fun w ↦ w = 0 ∨ w = 2 ∨ w = 5) (by rw [h₂.map_eq, ae_uniform3_iff]; simp)
    have e₃ := ae_of_ae_map h₃.aemeasurable
      (p := fun w ↦ w = 0 ∨ w = 4 ∨ w = 6) (by rw [h₃.map_eq, ae_uniform3_iff]; simp)
    filter_upwards [e₁, e₂, e₃] with ω a b c using ⟨a, b, c⟩
  have hSI : ∀ᵐ x ∂P.map (X₁ + X₂ + X₃), x ∈ Icc (0 : ℝ) 15 := by
    rw [ae_map_iff hS (p := (· ∈ Icc (0 : ℝ) 15)) measurableSet_Icc]
    filter_upwards [hX] with ω ⟨a, b, c⟩
    simp only [Pi.add_apply, mem_Icc]
    rcases a with a | a | a <;> rcases b with b | b | b <;> rcases c with c | c | c <;>
      norm_num [a, b, c]
  have hcall (t : ℝ) : Continuous fun x : ℝ ↦ max (x - t) 0 := by fun_prop
  have hput (t : ℝ) : Continuous fun x : ℝ ↦ max (t - x) 0 := by fun_prop
  -- the first coupling: the sum takes the values 6, 6, 9
  have c₁ := hmin ![4, 0, 0] ![2, 0, 5] ![0, 6, 4]
    (by convert hasLaw_uniform3 ![4, 0, 0] using 1; simp only [uniform3]; norm_num; abel)
    (by convert hasLaw_uniform3 ![2, 0, 5] using 1; simp only [uniform3]; norm_num; abel)
    (by convert hasLaw_uniform3 ![0, 6, 4] using 1; simp only [uniform3]; norm_num; abel)
  -- the second coupling: the sum takes the values 8, 8, 5
  have c₂ := hmin ![4, 0, 0] ![0, 2, 5] ![4, 6, 0]
    (by convert hasLaw_uniform3 ![4, 0, 0] using 1; simp only [uniform3]; norm_num; abel)
    (by convert hasLaw_uniform3 ![0, 2, 5] using 1; simp only [uniform3]; norm_num)
    (by convert hasLaw_uniform3 ![4, 6, 0] using 1; simp only [uniform3]; norm_num; abel)
  have hν (Y : Fin 3 → ℝ) (p : ℝ → Prop) (hp : MeasurableSet {x | p x})
      (h : p (Y 0) ∧ p (Y 1) ∧ p (Y 2)) : ∀ᵐ x ∂(uniform3 (0 : Fin 3) 1 2).map Y, p x := by
    rw [map_uniform3 .of_discrete, ae_uniform3_iff]; exact h
  have hlo : ∀ᵐ x ∂P.map (X₁ + X₂ + X₃), 6 ≤ x :=
    c₁.ae_ge_of_ae_ge (integrable_of_ae_mem_Icc (hput 6) hSI)
      (integrable_of_ae_mem_Icc (hput 6) (hν _ (· ∈ Icc (0 : ℝ) 15) measurableSet_Icc (by norm_num)))
      (hν _ (6 ≤ ·) measurableSet_Ici (by norm_num))
  have hhi : ∀ᵐ x ∂P.map (X₁ + X₂ + X₃), x ≤ 8 :=
    c₂.ae_le_of_ae_le (integrable_of_ae_mem_Icc (hcall 8) hSI)
      (integrable_of_ae_mem_Icc (hcall 8) (hν _ (· ∈ Icc (0 : ℝ) 15) measurableSet_Icc (by norm_num)))
      (hν _ (· ≤ 8) measurableSet_Iic (by norm_num))
  -- where `X₂ = 5` the sum avoids `[6, 8]`, so that event is null; but it has mass `1/3`
  have h5 : ∀ᵐ ω ∂P, X₂ ω ≠ 5 := by
    filter_upwards [hX, ae_of_ae_map hS hlo, ae_of_ae_map hS hhi] with ω ⟨a, _, c⟩ hl hh h5
    have h68 := And.intro hl hh
    simp only [Pi.add_apply, h5] at h68
    rcases a with a | a | a <;> rcases c with c | c | c <;> norm_num [a, c] at h68
  have := (ae_map_iff h₂.aemeasurable (measurableSet_singleton (5 : ℝ)).compl).2 h5
  rw [h₂.map_eq, ae_uniform3_iff] at this
  exact this.2.2 rfl

end NoMinimum

end MathFin
