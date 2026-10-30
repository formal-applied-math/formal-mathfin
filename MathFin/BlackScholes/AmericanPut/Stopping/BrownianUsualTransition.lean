/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.BrownianTransition
public import MathFin.BlackScholes.AmericanPut.Stopping.UsualBrownianValue

/-! # Gaussian log-state transitions in the completed usual Brownian filtration

A bounded continuous terminal payoff has an explicit continuous martingale of
conditional values. Lifting that martingale through completion, null augmentation,
and right continuation proves the usual-filtration transition without any PDE.

## Result

Public entry points include `brownianTerminalValue`, `brownianTerminalValue_at_maturity`,
`brownianTerminalValue_bound`, `brownianTerminalValue_continuous`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
open MathFin.ItoLocalMartingale (nullAugmentation supermartingale_nullAugmentation)

/-- The `brownianHeatFlow` of `f` over time `(σ^2*(T-min t T)).toNNReal`, started from the log
state `brownianLogState β σ x (min t T) ω` shifted by `β*(T-min t T)`. -/
noncomputable def brownianTerminalValue (f : ℝ → ℝ) (β σ x : ℝ) (T t : ℝ≥0)
    (ω : ℝ≥0 → ℝ) : ℝ :=
  brownianHeatFlow f (σ^2*((T : ℝ)-(min t T : ℝ≥0))).toNNReal
    (brownianLogState β σ x (min t T) ω+β*((T : ℝ)-(min t T : ℝ≥0)))

theorem brownianTerminalValue_at_maturity (f : ℝ → ℝ) (β σ x : ℝ) {T t : ℝ≥0}
    (ht : T ≤ t) : brownianTerminalValue f β σ x T t = fun ω => f (brownianLogState β σ x T ω) := by
  funext ω
  simp [brownianTerminalValue,min_eq_right ht,brownianHeatFlow_zero]

theorem brownianTerminalValue_bound {f : ℝ → ℝ} {C : ℝ} (hb : ∀ y, ‖f y‖ ≤ C)
    (β σ x : ℝ) (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ‖brownianTerminalValue f β σ x T t ω‖ ≤ C :=
  brownianHeatFlow_bound hb _ _

theorem brownianTerminalValue_continuous {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ y, ‖f y‖ ≤ C) (β σ x : ℝ) (T : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    Continuous (fun t => brownianTerminalValue f β σ x T t ω) := by
  have hw : Continuous (fun t : ℝ≥0 => brownian (min t T) ω) :=
    (continuous_brownian ω).comp (continuous_id.min continuous_const)
  exact (brownianHeatFlow_continuous hf hb).comp
    ((show Continuous (fun t : ℝ≥0 => (σ^2*((T : ℝ)-(min t T : ℝ≥0))).toNNReal) by fun_prop).prodMk
      (show Continuous (fun t : ℝ≥0 => brownianLogState β σ x (min t T) ω+
        β*((T : ℝ)-(min t T : ℝ≥0))) by unfold brownianLogState; fun_prop))

theorem brownianTerminalValue_adapted {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ y, ‖f y‖ ≤ C) (β σ x : ℝ) (T : ℝ≥0) :
    Adapted brownianFiltration (brownianTerminalValue f β σ x T) := by
  intro t
  have hw := (brownian_adapted (min t T)).mono (brownianFiltration.mono (min_le_left _ _)) le_rfl
  exact (brownianHeatFlow_continuous hf hb).measurable.comp
    (measurable_const.prodMk
        ((measurable_const.add (measurable_const.mul hw)).add measurable_const))

theorem brownianTerminalValue_eq_condExp {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ y, ‖f y‖ ≤ C) (β σ x : ℝ) (T t : ℝ≥0) :
    gaussianLimit[fun ω => f (brownianLogState β σ x T ω) | brownianFiltration t] =ᵐ[gaussianLimit]
      brownianTerminalValue f β σ x T t := by
  by_cases ht : t ≤ T
  · convert! brownianLogState_condExp_transition hf hb ht β σ x using 1
    ext ω
    simp only [brownianTerminalValue,min_eq_left ht]
  · have hTt := le_of_not_ge ht
    rw [brownianTerminalValue_at_maturity f β σ x hTt]
    have hm : Measurable[brownianFiltration t] (fun ω => f (brownianLogState β σ x T ω)) :=
      hf.measurable.comp (measurable_const.add (measurable_const.mul
        ((brownian_adapted T).mono (brownianFiltration.mono hTt) le_rfl)))
    rw [condExp_of_stronglyMeasurable (brownianFiltration.le t) hm.stronglyMeasurable
      ((integrable_const C).mono' (hm.mono (brownianFiltration.le t) le_rfl).aestronglyMeasurable
        (Eventually.of_forall (fun ω => hb _)))]

theorem brownianTerminalValue_martingale {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ y, ‖f y‖ ≤ C) (β σ x : ℝ) (T : ℝ≥0) :
    Martingale (brownianTerminalValue f β σ x T) brownianFiltration gaussianLimit := by
  refine ⟨fun t => (brownianTerminalValue_adapted hf hb β σ x T t).stronglyMeasurable,?_⟩
  intro i j hij
  exact (condExp_congr_ae (brownianTerminalValue_eq_condExp hf hb β σ x T j).symm).trans
    ((condExp_condExp_of_le (brownianFiltration.mono hij) (brownianFiltration.le j)).trans
      (brownianTerminalValue_eq_condExp hf hb β σ x T i))

theorem brownianTerminalValue_usual_martingale {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ y, ‖f y‖ ≤ C) (β σ x : ℝ) (T : ℝ≥0) :
    Martingale (brownianTerminalValue f β σ x T) brownianUsualFiltration
      (completedMeasure gaussianLimit) := by
  have hM := brownianTerminalValue_martingale hf hb β σ x T
  have hbound := brownianTerminalValue_bound hb β σ x T
  have hc := brownianTerminalValue_continuous hf hb β σ x T
  have hu := bounded_supermartingale_completion gaussianLimit hM.supermartingale hbound
  have hn := bounded_supermartingale_completion gaussianLimit hM.neg.supermartingale
    (fun t ω => by simpa only [Pi.neg_apply,norm_neg] using hbound t ω)
  letI : MeasurableSpace (ℝ≥0 → ℝ) := completedMeasurableSpace gaussianLimit
  have hu' :=
      bounded_continuous_supermartingale_rightCont
      (supermartingale_nullAugmentation hu) hc hbound
  have hn' :=
      bounded_continuous_supermartingale_rightCont (supermartingale_nullAugmentation hn)
    (fun ω => (hc ω).neg) (fun t ω => by simpa only [Pi.neg_apply,norm_neg] using hbound t ω)
  apply martingale_iff.mpr
  refine ⟨hu',?_⟩
  convert! hn'.neg using 1
  simp only [neg_neg]

theorem brownianLogState_usual_condExp_transition {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ C) {i j : ℝ≥0} (hij : i ≤ j) (β σ x : ℝ) :
    (completedMeasure gaussianLimit)[fun ω =>
        f (brownianLogState β σ x j ω) | brownianUsualFiltration i]
      =ᵐ[completedMeasure gaussianLimit]
      fun ω => brownianHeatFlow f (σ^2*((j : ℝ)-(i : ℝ))).toNNReal
        (brownianLogState β σ x i ω+β*((j : ℝ)-(i : ℝ))) := by
  have he := (brownianTerminalValue_usual_martingale hf hb β σ x j).2 i j hij
  rw [brownianTerminalValue_at_maturity f β σ x le_rfl] at he
  convert! he using 1
  ext ω
  simp only [brownianTerminalValue,min_eq_left hij]

end MathFin.BlackScholes.AmericanPut.Stopping
