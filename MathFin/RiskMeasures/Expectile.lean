/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Expectiles

The **`α`-expectile** of an integrable loss `Y` is the threshold `e` at which the
`α`-weighted expected excess above `e` balances the `(1 − α)`-weighted expected shortfall below
it:

  `α · E[(Y − e)⁺] = (1 − α) · E[(e − Y)⁺]`

(McNeil–Frey–Embrechts, §8.2.6; QRM Exercise Book, Exercises 8.13–8.14). Write
`expectileGap α Y e = α E[(Y − e)⁺] − (1 − α) E[(e − Y)⁺]`. Because `(y − e)⁺ − (e − y)⁺ = y − e`,
the gap equals `(2α − 1)·E[(Y − e)⁺] + (1 − α)(E[Y] − e)`. The map `e ↦ E[(Y − e)⁺]` is
`1`-Lipschitz and antitone, so the gap falls with slope at most `−min(α, 1 − α)`
(`expectileGap_sub_le`). A continuous function falling at a linear rate has exactly one root.
That root is the expectile (`existsUnique_expectileGap_eq_zero`).

Raising the level raises the gap pointwise, since `∂/∂α = E[(Y − e)⁺] + E[(e − Y)⁺] ≥ 0`, so it
moves the root to the right: **expectiles are nondecreasing in the level**
(`expectile_mono`, Exercise 8.13).

## Main results

* `expectileGap`: `α E[(Y − e)⁺] − (1 − α) E[(e − Y)⁺]`.
* `expectileGap_sub_le`: the gap falls at rate at least `min(α, 1 − α)`.
* `existsUnique_expectileGap_eq_zero`: the expectile exists and is unique.
* `expectile`: the `α`-expectile, and `expectileGap_expectile`.
* `expectile_mono`: expectiles are nondecreasing in the level.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Y : Ω → ℝ} {α : ℝ}

/-- The **expectile gap** `α E[(Y − e)⁺] − (1 − α) E[(e − Y)⁺]`, whose root is the
`α`-expectile. -/
noncomputable def expectileGap (α : ℝ) (Y : Ω → ℝ) (P : Measure Ω) (e : ℝ) : ℝ :=
  α * ∫ ω, max (Y ω - e) 0 ∂P - (1 - α) * ∫ ω, max (e - Y ω) 0 ∂P

/-- The **`α`-expectile** of `Y`: the infimum of the thresholds with a nonpositive gap, which is
the unique root of the gap for an integrable `Y` and `α ∈ (0, 1)` (`expectileGap_expectile`). -/
noncomputable def expectile (α : ℝ) (Y : Ω → ℝ) (P : Measure Ω) : ℝ :=
  sInf {e | expectileGap α Y P e ≤ 0}

private lemma integrable_max_sub (hY : Integrable Y P) (e : ℝ) :
    Integrable (fun ω ↦ max (Y ω - e) 0) P :=
  (hY.sub (integrable_const e)).pos_part

/-- The gap in terms of the upper partial moment alone:
`(2α − 1)·E[(Y − e)⁺] + (1 − α)(E[Y] − e)`, from `(e − y)⁺ = (y − e)⁺ − (y − e)`. -/
lemma expectileGap_eq (hY : Integrable Y P) (e : ℝ) :
    expectileGap α Y P e =
      (2 * α - 1) * ∫ ω, max (Y ω - e) 0 ∂P + (1 - α) * ((∫ ω, Y ω ∂P) - e) := by
  have hpt : (fun ω ↦ max (e - Y ω) 0) = fun ω ↦ max (Y ω - e) 0 - (Y ω - e) := by
    ext ω
    rcases le_total (Y ω) e with h | h
    · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h)]
      ring
    · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]
      ring
  have hYe : Integrable (fun ω ↦ Y ω - e) P := hY.sub (integrable_const e)
  rw [expectileGap, hpt, integral_sub (integrable_max_sub hY e) hYe,
    integral_sub hY (integrable_const e), integral_const, probReal_univ, one_smul]
  ring

/-- The upper partial moment `e ↦ E[(Y − e)⁺]` is antitone and falls by at most the increment. -/
private lemma upperPartialMoment_sub (hY : Integrable Y P) {e e' : ℝ} (h : e ≤ e') :
    0 ≤ (∫ ω, max (Y ω - e) 0 ∂P) - ∫ ω, max (Y ω - e') 0 ∂P ∧
      (∫ ω, max (Y ω - e) 0 ∂P) - ∫ ω, max (Y ω - e') 0 ∂P ≤ e' - e := by
  rw [← integral_sub (integrable_max_sub hY e) (integrable_max_sub hY e')]
  refine ⟨integral_nonneg fun ω ↦ sub_nonneg.2 (max_le_max (by linarith) le_rfl), ?_⟩
  calc ∫ ω, (max (Y ω - e) 0 - max (Y ω - e') 0) ∂P ≤ ∫ _, (e' - e) ∂P :=
        integral_mono ((integrable_max_sub hY e).sub (integrable_max_sub hY e'))
          (integrable_const _) fun ω ↦ sub_le_iff_le_add.2 <|
            max_le (by linarith [le_max_left (Y ω - e') 0])
              (by linarith [le_max_right (Y ω - e') 0])
    _ = e' - e := by simp

/-- **The gap falls at a linear rate**: for `e ≤ e'`,
`min(α, 1 − α)·(e' − e) ≤ gap(e) − gap(e')`. -/
theorem expectileGap_sub_le (hY : Integrable Y P) {e e' : ℝ} (h : e ≤ e') :
    min α (1 - α) * (e' - e) ≤ expectileGap α Y P e - expectileGap α Y P e' := by
  rw [expectileGap_eq hY, expectileGap_eq hY]
  obtain ⟨h0, h1⟩ := upperPartialMoment_sub hY h
  rcases le_total 0 (2 * α - 1) with hs | hs
  · nlinarith [mul_nonneg hs h0,
      mul_le_mul_of_nonneg_right (min_le_right α (1 - α)) (sub_nonneg.2 h)]
  · nlinarith [mul_le_mul_of_nonpos_left h1 hs,
      mul_le_mul_of_nonneg_right (min_le_left α (1 - α)) (sub_nonneg.2 h)]

/-- The gap is continuous: the upper partial moment is `1`-Lipschitz. -/
lemma continuous_expectileGap (hY : Integrable Y P) : Continuous (expectileGap α Y P) := by
  have hm : Continuous fun e ↦ ∫ ω, max (Y ω - e) 0 ∂P := by
    refine (LipschitzWith.of_dist_le_mul fun e e' ↦ ?_).continuous (K := 1)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rcases le_total e e' with h | h
    · obtain ⟨h0, h1⟩ := upperPartialMoment_sub hY h
      rw [abs_of_nonneg h0, abs_of_nonpos (sub_nonpos.2 h)]
      linarith
    · obtain ⟨h0, h1⟩ := upperPartialMoment_sub hY h
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (sub_nonneg.2 h)]
      linarith
  simp_rw [funext (expectileGap_eq (α := α) hY)]
  fun_prop

/-- **The expectile exists and is unique**: the gap has exactly one root. -/
theorem existsUnique_expectileGap_eq_zero (hY : Integrable Y P) (hα : α ∈ Ioo 0 1) :
    ∃! e, expectileGap α Y P e = 0 := by
  have hc : 0 < min α (1 - α) := lt_min hα.1 (sub_pos.2 hα.2)
  set G := expectileGap α Y P
  set t := |G 0| / min α (1 - α)
  have ht : min α (1 - α) * t = |G 0| := mul_div_cancel₀ _ hc.ne'
  have ht0 : 0 ≤ t := div_nonneg (abs_nonneg _) hc.le
  have hlo : 0 ≤ G (-t) := by
    have := expectileGap_sub_le (α := α) hY (show -t ≤ 0 by linarith)
    linarith [neg_abs_le (G 0)]
  have hhi : G t ≤ 0 := by
    have := expectileGap_sub_le (α := α) hY ht0
    linarith [le_abs_self (G 0)]
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc' (by linarith : -t ≤ t)
    (continuous_expectileGap hY).continuousOn ⟨hhi, hlo⟩
  refine ⟨r, hr, fun r' hr' ↦ ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · nlinarith [expectileGap_sub_le (α := α) hY h.le, mul_pos hc (sub_pos.2 h)]
  · nlinarith [expectileGap_sub_le (α := α) hY h.le, mul_pos hc (sub_pos.2 h)]

/-- **The expectile is the root of the gap**: the thresholds with a nonpositive gap are exactly
`[e_α, ∞)`, so their infimum `expectile α Y P` is the root. -/
theorem expectileGap_expectile (hY : Integrable Y P) (hα : α ∈ Ioo 0 1) :
    expectileGap α Y P (expectile α Y P) = 0 := by
  have hc : 0 < min α (1 - α) := lt_min hα.1 (sub_pos.2 hα.2)
  obtain ⟨r, hr, -⟩ := existsUnique_expectileGap_eq_zero hY hα
  have hset : {e | expectileGap α Y P e ≤ 0} = Ici r := by
    ext e
    refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
    · by_contra h
      rw [mem_Ici, not_le] at h
      have he' : expectileGap α Y P e ≤ 0 := he
      nlinarith [expectileGap_sub_le (α := α) hY h.le, mul_pos hc (sub_pos.2 h)]
    · have he' : r ≤ e := he
      show expectileGap α Y P e ≤ 0
      nlinarith [expectileGap_sub_le (α := α) hY he', mul_nonneg hc.le (sub_nonneg.2 he')]
  rw [expectile, hset, csInf_Ici, hr]

/-- **Expectiles are nondecreasing in the level** (QRM Exercise 8.13): raising the level raises
the gap at every threshold, which moves its root to the right. -/
theorem expectile_mono (hY : Integrable Y P) (hα : α ∈ Ioo 0 1) {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (hαβ : α ≤ β) : expectile α Y P ≤ expectile β Y P := by
  set e := expectile α Y P
  have hA : 0 ≤ ∫ ω, max (Y ω - e) 0 ∂P := integral_nonneg fun _ ↦ le_max_right _ _
  have hB : 0 ≤ ∫ ω, max (e - Y ω) 0 ∂P := integral_nonneg fun _ ↦ le_max_right _ _
  have hge : 0 ≤ expectileGap β Y P e := by
    have h := expectileGap_expectile hY hα
    rw [expectileGap] at h ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hαβ) hA, mul_nonneg (sub_nonneg.2 hαβ) hB]
  by_contra hlt
  rw [not_le] at hlt
  have := expectileGap_sub_le (α := β) hY hlt.le
  rw [expectileGap_expectile hY hβ] at this
  nlinarith [mul_pos (lt_min hβ.1 (sub_pos.2 hβ.2)) (sub_pos.2 hlt)]

end MathFin
