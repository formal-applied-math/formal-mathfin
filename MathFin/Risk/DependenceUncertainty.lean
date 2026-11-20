/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Risk.ValueAtRisk

/-!
# Value-at-risk of a sum under dependence uncertainty: the dual bound

The marginal laws `μ i` of losses `X i` are known, but their dependence is not. How large can
`VaR_α(X₁ + ⋯ + X_d)` be? Weak duality bounds it using the marginals alone. Let `f i ≥ 0` be
functions with `∑ f i (x i) ≥ 1` whenever `∑ x i > s`. Then `P(∑ X i > s) ≤ ∑ ∫ f i ∂μ i`. So
once that sum is at most `1 − α`, `VaR_α(∑ X i) ≤ s` under **every** joint law with these
marginals (`valueAtRisk_sum_le_of_dual`). That is the easy half of Rüschendorf's duality for
the worst-case value-at-risk.

The capped calls `x ↦ min ((x − t)⁺, c) / c` are one such family. With thresholds `t i`, they
cover the level `∑ t i + c` (`one_le_sum_capCall`). This is the dual bound of Embrechts and
Puccetti for homogeneous portfolios. Read with heterogeneous thresholds, it is the form of
Puccetti and Rüschendorf (`valueAtRisk_sum_le_of_capCall`). Each `∫ capCall` is a tail
integral of the marginal, so a rational choice of `t` and `c` gives a certificate. It is
checked by exact arithmetic for laws whose tail integrals are rational, for example the
Pareto laws with integer index.

## Main definitions

* `capCall`: the capped call `x ↦ min ((x − t)⁺, c) / c`, valued in `[0, 1]`.

## Main results

* `valueAtRisk_sum_le_of_dual`: weak duality. A family of nonnegative functions covering the
  level `s`, with total mass at most `1 − α` under the marginals, bounds the value-at-risk of
  the sum by `s`, for every dependence.
* `one_le_sum_capCall`: the capped calls with thresholds `t` cover the level `∑ t i + c`.
* `valueAtRisk_sum_le_of_capCall`: the dual bound with capped calls.

## References

* [P. Embrechts and G. Puccetti, *Bounds for functions of dependent risks*][EmbrechtsPuccetti2006],
  Theorem 4.2
* [G. Puccetti and L. Rüschendorf, *Bounds for joint portfolios of dependent
  risks*][PuccettiRuschendorf2012], §3
* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], §8.4.4

## Tags

worst-case value-at-risk, dependence uncertainty, model uncertainty, risk aggregation, dual bound,
rearrangement, Fréchet class, MSC 91G70, MSC 60E15, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [Fintype ι] {X : ι → Ω → ℝ} {μ : ι → Measure ℝ} {α s : ℝ}

/-- **Weak duality for the value-at-risk of a sum.**

Let the losses `X i` have marginal laws `μ i`. Suppose nonnegative `f i` satisfy
`∑ f i (x i) ≥ 1` whenever `∑ x i > s`, and `∑ ∫ f i ∂μ i ≤ 1 − α`. Then
`VaR_α(∑ X i) ≤ s`. Only the marginals enter the hypotheses, so the bound holds for every
dependence between the losses. -/
theorem valueAtRisk_sum_le_of_dual (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (μ i) P) (hα : α ∈ Ioo 0 1) {f : ι → ℝ → ℝ}
    (hf0 : ∀ i x, 0 ≤ f i x) (hfi : ∀ i, Integrable (f i) (μ i))
    (hcover : ∀ x : ι → ℝ, s < ∑ i, x i → 1 ≤ ∑ i, f i (x i))
    (hmass : ∑ i, ∫ x, f i x ∂μ i ≤ 1 - α) :
    valueAtRisk (fun ω ↦ ∑ i, X i ω) P α ≤ s := by
  have hS : Measurable fun ω ↦ ∑ i, X i ω := Finset.measurable_sum _ fun i _ ↦ hXm i
  have hA : MeasurableSet {ω | s < ∑ i, X i ω} := measurableSet_lt measurable_const hS
  have hint (i : ι) : Integrable (fun ω ↦ f i (X i ω)) P := (hX i).integrable_comp (hfi i)
  have htail : P.real {ω | s < ∑ i, X i ω} ≤ 1 - α :=
    calc P.real {ω | s < ∑ i, X i ω}
        = ∫ ω, {ω | s < ∑ i, X i ω}.indicator 1 ω ∂P := (integral_indicator_one hA).symm
      _ ≤ ∫ ω, ∑ i, f i (X i ω) ∂P := by
          refine integral_mono_of_nonneg
            (ae_of_all _ fun ω ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) ω)
            (integrable_finsetSum _ fun i _ ↦ hint i) (ae_of_all _ fun ω ↦ ?_)
          by_cases h : s < ∑ i, X i ω
          · simpa [indicator_of_mem (show ω ∈ {ω | s < ∑ i, X i ω} from h)] using
              hcover (fun i ↦ X i ω) h
          · simpa [indicator_of_notMem (show ω ∉ {ω | s < ∑ i, X i ω} from h)] using
              Finset.sum_nonneg fun i _ ↦ hf0 i (X i ω)
      _ = ∑ i, ∫ x, f i x ∂μ i := by
          rw [integral_finsetSum _ fun i _ ↦ hint i]
          exact Finset.sum_congr rfl fun i _ ↦ (hX i).integral_comp (hfi i).aestronglyMeasurable
      _ ≤ 1 - α := hmass
  rw [valueAtRisk_le_iff hS.aemeasurable hα]
  have hc : {ω | ∑ i, X i ω ≤ s} = {ω | s < ∑ i, X i ω}ᶜ := by ext; simp
  rw [hc, probReal_compl_eq_one_sub hA]
  linarith

/-! ### Capped calls -/

/-- The **capped call** `x ↦ min ((x − t)⁺, c) / c`. Its value is `0` below `t`, it rises
linearly to `1` at `t + c`, and stays `1` above. -/
noncomputable def capCall (t c x : ℝ) : ℝ := min (max (x - t) 0) c / c

variable {t c x : ℝ}

lemma capCall_nonneg (hc : 0 < c) : 0 ≤ capCall t c x :=
  div_nonneg (le_min (le_max_right _ _) hc.le) hc.le

lemma capCall_le_one (hc : 0 < c) : capCall t c x ≤ 1 :=
  (div_le_one hc).2 (min_le_right _ _)

lemma continuous_capCall : Continuous (capCall t c) :=
  (((continuous_id.sub continuous_const).max continuous_const).min continuous_const).div_const c

/-- The capped calls with thresholds `t i` and common cap `c` cover the level `∑ t i + c`:
a sum above it makes `∑ capCall (t i) c (x i) ≥ 1`. -/
lemma one_le_sum_capCall {t : ι → ℝ} (hc : 0 < c) {x : ι → ℝ}
    (hx : ∑ i, t i + c < ∑ i, x i) : 1 ≤ ∑ i, capCall (t i) c (x i) := by
  by_cases h : ∃ j, t j + c ≤ x j
  · obtain ⟨j, hj⟩ := h
    have hj1 : capCall (t j) c (x j) = 1 := by
      rw [capCall, min_eq_right (le_max_of_le_left (by linarith)), div_self hc.ne']
    exact hj1.symm.le.trans
      (Finset.single_le_sum (fun i _ ↦ capCall_nonneg hc) (Finset.mem_univ j))
  · push Not at h
    have key (i : ι) : x i - t i ≤ c * capCall (t i) c (x i) := by
      rw [capCall, mul_div_cancel₀ _ hc.ne',
        min_eq_left (max_le_iff.2 ⟨by linarith [h i], hc.le⟩)]
      exact le_max_left _ _
    refine ((lt_mul_iff_one_lt_right hc).1 ?_).le
    calc c < ∑ i, x i - ∑ i, t i := by linarith
      _ = ∑ i, (x i - t i) := (Finset.sum_sub_distrib ..).symm
      _ ≤ ∑ i, c * capCall (t i) c (x i) := Finset.sum_le_sum fun i _ ↦ key i
      _ = c * ∑ i, capCall (t i) c (x i) := (Finset.mul_sum ..).symm

/-- **The dual bound with capped calls** (Embrechts–Puccetti; Puccetti–Rüschendorf). Take
thresholds `t i` and a cap `c > 0`. If the mean capped calls under the marginals sum to at most
`1 − α`, then `VaR_α(∑ X i) ≤ ∑ t i + c`, for every dependence between the losses. -/
theorem valueAtRisk_sum_le_of_capCall [∀ i, IsProbabilityMeasure (μ i)]
    (hXm : ∀ i, Measurable (X i)) (hX : ∀ i, HasLaw (X i) (μ i) P) (hα : α ∈ Ioo 0 1)
    {t : ι → ℝ} (hc : 0 < c) (hmass : ∑ i, ∫ x, capCall (t i) c x ∂μ i ≤ 1 - α) :
    valueAtRisk (fun ω ↦ ∑ i, X i ω) P α ≤ ∑ i, t i + c :=
  valueAtRisk_sum_le_of_dual (f := fun i ↦ capCall (t i) c) hXm hX hα
    (fun _ _ ↦ capCall_nonneg hc)
    (fun _ ↦ (integrable_const (1 : ℝ)).mono' continuous_capCall.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ (Real.norm_of_nonneg (capCall_nonneg hc)).trans_le (capCall_le_one hc)))
    (fun _ ↦ one_le_sum_capCall hc) hmass

end MathFin
