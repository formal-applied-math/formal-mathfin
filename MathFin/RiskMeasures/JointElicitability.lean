/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.RiskMeasures.Elicitability

/-!
# Joint elicitability of (VaR, ES): a Fissler–Ziegel score

Expected shortfall alone is not elicitable (`not_isElicitable_expectedShortfall`), but the pair
(value-at-risk, expected shortfall) is: Fissler and Ziegel (2016), *Higher order elicitability and
Osband's principle*, Ann. Statist. 44(4), Corollary 5.5. This file transcribes their scoring
function (5.5) and proves strict consistency of its simplest strictly consistent member.

## The source formula

Transcribed from the LaTeX source of arXiv:1503.08123v3, Corollary 5.5, equation (5.5). On the
action domain `{x ∈ ℝ² : x₁ ≥ x₂}`,

`S(x₁, x₂, y) = (𝟙{y ≤ x₁} − α) G₁(x₁) − 𝟙{y ≤ x₁} G₁(y)`
`             + G₂(x₂) (x₂ − x₁ + α⁻¹ 𝟙{y ≤ x₁} (x₁ − y)) − 𝒢₂(x₂) + a(y)`,

with `𝒢₂' = G₂`. It is strictly consistent for `(VaR_α, ES_α)` if `G₁` is increasing and `𝒢₂` is
strictly increasing and strictly convex; the paper remarks after Corollary 5.5 that `G₁ = 0` is
allowed. The paper uses the **profit** sign convention: `VaR_α(F) = F⁻¹(α)` is the lower
`α`-quantile and `ES_α(F) = α⁻¹ ∫₀^α VaR_u(F) du` (its (5.1)) averages the *lower* tail, so
`ES_α ≤ VaR_α`. That lower-tail functional is `lowerExpectedShortfall` here; it differs from the
loss-convention `expectedShortfall` of `RiskMeasures/ValueAtRisk.lean`, which averages the upper
tail.

## The member proved

`G₁ = 0`, `a = 0`, `𝒢₂ = G₂ = exp`. With `G₁ = 0` the monotonicity condition linking the two
coordinates disappears, so strict consistency holds on all of `ℝ²`, not only on `x₁ ≥ x₂`. The
proof reduces to the pinball loss: `α⁻¹ 𝟙{y ≤ v}(v − y) − v = α⁻¹ S_α(v, y) − y`, so the expected
score is `exp e · (e − E[Y] + α⁻¹ E[S_α(v, Y)]) − exp e`. The `v`-part is minimized only at the
quantile (`strictlyElicits_pinballLoss`), with minimum value `−ES_α`; what remains,
`exp e · (e − ES_α − 1)`, is minimized only at `e = ES_α` by `1 + t < exp t`.

## Main results

* `StrictlyJointlyElicits`, `IsJointlyElicitable`: strict consistency of a joint score for a pair.
* `StrictlyJointlyElicits.apply_mixture`: jointly elicitable pairs have convex joint level sets.
* `fisslerZieglerScore`: the scoring family (5.5), verbatim.
* `fisslerZieglerExpScore`: its member `G₁ = 0`, `𝒢₂ = exp`, `a = 0`.
* `lowerExpectedShortfall`: the lower-tail expected shortfall (5.1) of the paper.
* `strictlyJointlyElicits_fisslerZieglerExpScore`: the member strictly elicits
  `(VaR_α, ES_α)` on laws with finite mean and unique `α`-quantile.
* `isJointlyElicitable_valueAtRisk_lowerExpectedShortfall`: the pair is jointly elicitable.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {α : ℝ}

/-! ### Joint elicitability of a pair of functionals -/

/-- The joint score `S` **strictly elicits** the pair `(T₁, T₂)` on the class `C` of laws on `ℝ`:
for every `μ ∈ C` each expected score `∫ S x e y dμ(y)` is finite, and `(T₁ μ, T₂ μ)` is the unique
minimizer of `(x, e) ↦ ∫ S x e y dμ(y)`. -/
def StrictlyJointlyElicits (S : ℝ → ℝ → ℝ → ℝ) (T₁ T₂ : Measure ℝ → ℝ) (C : Set (Measure ℝ)) :
    Prop :=
  ∀ μ ∈ C, (∀ x e, Integrable (S x e) μ) ∧
    ∀ x e, (x, e) ≠ (T₁ μ, T₂ μ) → ∫ y, S (T₁ μ) (T₂ μ) y ∂μ < ∫ y, S x e y ∂μ

/-- A pair of functionals is **jointly elicitable** on `C` if some joint score strictly elicits
it. -/
def IsJointlyElicitable (T₁ T₂ : Measure ℝ → ℝ) (C : Set (Measure ℝ)) : Prop :=
  ∃ S, StrictlyJointlyElicits S T₁ T₂ C

/-- **Jointly elicitable pairs have convex joint level sets**, the pair version of
`StrictlyElicits.apply_mixture` (Osband 1985; Fissler–Ziegel 2016, Proposition 2.14): if both
components agree on `μ` and `ν`, they take the same values on every mixture in the class. -/
theorem StrictlyJointlyElicits.apply_mixture {S : ℝ → ℝ → ℝ → ℝ} {T₁ T₂ : Measure ℝ → ℝ}
    {C : Set (Measure ℝ)} (hS : StrictlyJointlyElicits S T₁ T₂ C)
    {μ ν : Measure ℝ} (hμ : μ ∈ C) (hν : ν ∈ C) {c : ℝ≥0} (hc : c ≤ 1)
    (hm : c • μ + (1 - c) • ν ∈ C) (hT₁ : T₁ μ = T₁ ν) (hT₂ : T₂ μ = T₂ ν) :
    T₁ (c • μ + (1 - c) • ν) = T₁ μ ∧ T₂ (c • μ + (1 - c) • ν) = T₂ μ := by
  by_contra hne
  obtain ⟨hμi, hμlt⟩ := hS μ hμ
  obtain ⟨hνi, hνlt⟩ := hS ν hν
  have hne' : (T₁ (c • μ + (1 - c) • ν), T₂ (c • μ + (1 - c) • ν)) ≠ (T₁ μ, T₂ μ) :=
    fun heq ↦ hne ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  have hne2 : (T₁ (c • μ + (1 - c) • ν), T₂ (c • μ + (1 - c) • ν)) ≠ (T₁ ν, T₂ ν) := by
    rw [← hT₁, ← hT₂]; exact hne'
  have h1 := (hμlt _ _ hne').le
  have h2 := (hνlt _ _ hne2).le
  have h3 := (hS _ hm).2 _ _ (Ne.symm hne')
  rw [← hT₁, ← hT₂] at h2
  rw [integral_mixture (hμi _ _) (hνi _ _) hc, integral_mixture (hμi _ _) (hνi _ _) hc] at h3
  have hc1 : (0 : ℝ) ≤ 1 - c := sub_nonneg.2 (by exact_mod_cast hc)
  nlinarith [mul_le_mul_of_nonneg_left h1 c.coe_nonneg, mul_le_mul_of_nonneg_left h2 hc1]

/-! ### The Fissler–Ziegel scoring family -/

/-- The **Fissler–Ziegel score** for `(VaR_α, ES_α)`, equation (5.5) of Fissler–Ziegel (2016),
in their profit sign convention, for a VaR forecast `x₁`, an ES forecast `x₂` and an outcome `y`:
`(𝟙{y ≤ x₁} − α) G₁(x₁) − 𝟙{y ≤ x₁} G₁(y) + G₂(x₂)(x₂ − x₁ + α⁻¹ 𝟙{y ≤ x₁}(x₁ − y))
− 𝒢₂(x₂) + a(y)`. Their Corollary 5.5 requires `𝒢₂' = G₂`. -/
noncomputable def fisslerZieglerScore (G₁ G₂ 𝒢₂ a : ℝ → ℝ) (α x₁ x₂ y : ℝ) : ℝ :=
  ((if y ≤ x₁ then 1 else 0) - α) * G₁ x₁ - (if y ≤ x₁ then 1 else 0) * G₁ y +
    G₂ x₂ * (x₂ - x₁ + α⁻¹ * (if y ≤ x₁ then 1 else 0) * (x₁ - y)) - 𝒢₂ x₂ + a y

/-- The member of the Fissler–Ziegel family with `G₁ = 0`, `𝒢₂ = G₂ = exp` and `a = 0`. -/
noncomputable def fisslerZieglerExpScore (α : ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fisslerZieglerScore 0 Real.exp Real.exp 0 α

/-- The exponential member through the pinball loss:
`S(v, e, y) = exp e · (e − y + α⁻¹ S_α(v, y)) − exp e`. -/
lemma fisslerZieglerExpScore_eq (hα : α ≠ 0) (v e y : ℝ) :
    fisslerZieglerExpScore α v e y = Real.exp e * (e - y + α⁻¹ * pinballLoss α v y) - Real.exp e
    := by
  rw [fisslerZieglerExpScore, fisslerZieglerScore, pinballLoss_eq_ite]
  simp only [Pi.zero_apply, mul_zero, sub_zero, add_zero]
  congr 2
  field_simp
  split_ifs <;> ring

/-- The **lower-tail expected shortfall** `ES_α(μ) = α⁻¹ ∫₀^α VaR_u(μ) du`, equation (5.1) of
Fissler–Ziegel (2016): the mean of the worst `α`-fraction of outcomes in the profit convention. -/
noncomputable def lowerExpectedShortfall (μ : Measure ℝ) (α : ℝ) : ℝ :=
  α⁻¹ * ∫ u in Ioc 0 α, quantile μ u

/-- The minimum of the `v`-part of the expected score is minus the lower-tail expected shortfall:
`E[Y] − α⁻¹ E[S_α(VaR_α, Y)] = ES_α`. -/
lemma integral_sub_inv_mul_integral_pinballLoss {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable id μ) (hα : α ∈ Ioo 0 1) :
    ∫ y, y ∂μ - α⁻¹ * ∫ y, pinballLoss α (quantile μ α) y ∂μ = lowerExpectedShortfall μ α := by
  have hvar : ∀ u, valueAtRisk id μ u = quantile μ u := fun u ↦ by rw [valueAtRisk, Measure.map_id]
  have h := integral_pinballLoss (P := μ) (X := id) hint hα (quantile μ α)
  simp only [id] at h
  rw [h, ← hvar, rockafellarUryasev_valueAtRisk hint hα, expectedShortfall]
  simp_rw [hvar]
  have hq := integrableOn_valueAtRisk (P := μ) hint
  simp_rw [hvar] at hq
  have hmean : ∫ y, y ∂μ = (∫ u in Ioc 0 α, quantile μ u) + ∫ u in Ioo α 1, quantile μ u := by
    rw [integral_eq_setIntegral_quantile (f := fun y : ℝ ↦ y) (by fun_prop),
      ← Ioc_union_Ioo_eq_Ioo hα.1.le hα.2, setIntegral_union
      (Ioc_disjoint_Ioi_same.mono_right Ioo_subset_Ioi_self) measurableSet_Ioo
      (hq.mono_set fun u hu ↦ ⟨hu.1, hu.2.trans_lt hα.2⟩)
      (hq.mono_set (Ioo_subset_Ioo_left hα.1.le))]
  rw [hmean, lowerExpectedShortfall]
  have h1α : 1 - α ≠ 0 := (sub_pos.2 hα.2).ne'
  have hα0 : α ≠ 0 := hα.1.ne'
  field_simp
  ring

/-- **The exponential Fissler–Ziegel score strictly elicits `(VaR_α, ES_α)`** (Fissler–Ziegel 2016,
Corollary 5.5, with `G₁ = 0` and `𝒢₂ = exp`) on the laws with finite mean whose `α`-quantile is
unique: the true pair (lower `α`-quantile, lower-tail expected shortfall) is the unique minimizer
of the expected score over all of `ℝ²`. The paper's own domain is `A₀ = {x₁ ≥ x₂}`; the extension
to all of `ℝ²` is this file's own observation (see the module docstring), not the paper's claim —
`G₁ = 0` removes the term that ties the two coordinates together. -/
theorem strictlyJointlyElicits_fisslerZieglerExpScore (hα : α ∈ Ioo 0 1) :
    StrictlyJointlyElicits (fisslerZieglerExpScore α) (fun μ ↦ quantile μ α)
      (fun μ ↦ lowerExpectedShortfall μ α)
      {μ | IsProbabilityMeasure μ ∧ Integrable id μ ∧ ∀ x, quantile μ α < x → α < cdf μ x} := by
  intro μ hμC
  obtain ⟨hpi, hplt⟩ := strictlyElicits_pinballLoss hα μ hμC
  obtain ⟨hμ, hint, -⟩ := hμC
  have hα0 : α ≠ 0 := hα.1.ne'
  have hint' : Integrable (fun y : ℝ ↦ y) μ := hint
  have hS : ∀ v e, fisslerZieglerExpScore α v e = fun y ↦
      Real.exp e * (e - y + α⁻¹ * pinballLoss α v y) - Real.exp e :=
    fun v e ↦ funext (fisslerZieglerExpScore_eq hα0 v e)
  have hA : ∀ e : ℝ, Integrable (fun y : ℝ ↦ e - y) μ := fun e ↦ (integrable_const e).sub hint'
  have hB : ∀ v, Integrable (fun y ↦ α⁻¹ * pinballLoss α v y) μ := fun v ↦ (hpi v).const_mul _
  have hi : ∀ v e, Integrable (fun y ↦ e - y + α⁻¹ * pinballLoss α v y) μ := fun v e ↦
    (hA e).add (hB v)
  -- the expected score, in terms of the expected pinball loss
  have hE : ∀ v e, ∫ y, fisslerZieglerExpScore α v e y ∂μ =
      Real.exp e * (e - ∫ y, y ∂μ + α⁻¹ * ∫ y, pinballLoss α v y ∂μ) - Real.exp e := by
    intro v e
    rw [hS, integral_sub ((hi v e).const_mul _) (integrable_const _), integral_const_mul,
      integral_add (hA e) (hB v), integral_sub (integrable_const e) hint', integral_const,
      integral_const, integral_const_mul]
    simp
  refine ⟨fun v e ↦ hS v e ▸ ((hi v e).const_mul _).sub (integrable_const _), fun v e hne ↦ ?_⟩
  have hr := integral_sub_inv_mul_integral_pinballLoss hint hα
  set q := quantile μ α
  set r := lowerExpectedShortfall μ α
  rw [hE, hE]
  -- `D ≥ 0` is the pinball excess, strictly positive off the quantile
  set D := ∫ y, pinballLoss α v y ∂μ - ∫ y, pinballLoss α q y ∂μ
  have hD : 0 ≤ D := by
    rcases eq_or_ne v q with rfl | hv
    · simp [D]
    · exact (sub_pos.2 (hplt v hv)).le
  have hαi : 0 < α⁻¹ := inv_pos.2 hα.1
  have hexp : ∀ t : ℝ, Real.exp t * (t - 1) + 1 ≥ 0 ∧ (t ≠ 0 → Real.exp t * (t - 1) + 1 > 0) := by
    intro t
    have key : ∀ t : ℝ, 1 - t ≤ Real.exp (-t) := fun t ↦ by
      linarith [Real.add_one_le_exp (-t)]
    have hm : Real.exp t * (t - 1) + 1 = Real.exp t * (Real.exp (-t) - (1 - t)) := by
      have h1 : Real.exp t * Real.exp (-t) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      linear_combination (-1 : ℝ) * h1
    refine ⟨hm ▸ mul_nonneg (Real.exp_pos t).le (sub_nonneg.2 (key t)), fun ht ↦ ?_⟩
    rw [hm]
    refine mul_pos (Real.exp_pos t) (sub_pos.2 ?_)
    linarith [Real.add_one_lt_exp (neg_ne_zero.2 ht)]
  -- rewrite both sides through `r` and `D`
  have hLHS : Real.exp r * (r - ∫ y, y ∂μ + α⁻¹ * ∫ y, pinballLoss α q y ∂μ) - Real.exp r =
      -Real.exp r := by
    linear_combination (-Real.exp r) * hr
  have hRHS : Real.exp e * (e - ∫ y, y ∂μ + α⁻¹ * ∫ y, pinballLoss α v y ∂μ) - Real.exp e =
      Real.exp e * (e - r - 1) + Real.exp e * (α⁻¹ * D) := by
    simp only [D]; linear_combination (-Real.exp e) * hr
  rw [hLHS, hRHS]
  have hsplit : Real.exp e * (e - r - 1) + Real.exp r =
      Real.exp r * (Real.exp (e - r) * (e - r - 1) + 1) := by
    rw [mul_add, ← mul_assoc, ← Real.exp_add, add_sub_cancel]; ring
  have hED : 0 ≤ Real.exp e * (α⁻¹ * D) := mul_nonneg (Real.exp_pos e).le (mul_nonneg hαi.le hD)
  rcases eq_or_ne e r with he | he
  · have hv : v ≠ q := fun hv ↦ hne (by rw [hv, he])
    have hDpos : 0 < D := sub_pos.2 (hplt v hv)
    have : 0 < Real.exp e * (α⁻¹ * D) := mul_pos (Real.exp_pos e) (mul_pos hαi hDpos)
    rw [he] at this ⊢
    linarith
  · have h1 := (hexp (e - r)).2 (sub_ne_zero.2 he)
    have h2 := mul_pos (Real.exp_pos r) h1
    linarith [hsplit]

/-- **`(VaR_α, ES_α)` is jointly elicitable** (Fissler–Ziegel 2016, Corollary 5.5) on the laws with
finite mean and unique `α`-quantile, although `ES_α` alone is not. -/
theorem isJointlyElicitable_valueAtRisk_lowerExpectedShortfall (hα : α ∈ Ioo 0 1) :
    IsJointlyElicitable (fun μ ↦ quantile μ α) (fun μ ↦ lowerExpectedShortfall μ α)
      {μ | IsProbabilityMeasure μ ∧ Integrable id μ ∧ ∀ x, quantile μ α < x → α < cdf μ x} :=
  ⟨_, strictlyJointlyElicits_fisslerZieglerExpScore hα⟩

end MathFin
