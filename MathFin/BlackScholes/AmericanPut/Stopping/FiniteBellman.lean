/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.Rules

/-! # Backward Bellman values on an arbitrary filtered probability space

This is conditional-expectation recursion, not a binomial transition model.
The process is frozen after its finite horizon.

## Result

Public entry points include `bellmanAux`, `finiteBellman`, `bellmanAux_measurable`,
`bellmanAux_integrable`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Backward Bellman recursion with `n` steps left from index `i`: it is `Z i` for `n = 0`, and
otherwise the pointwise maximum of `Z i` and `P[bellmanAux P 𝓕 Z n (i+1) | 𝓕 i]`. -/
noncomputable def bellmanAux (P : Measure Ω) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›)
    (Z : ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ
  | 0, i => Z i
  | n+1, i => fun ω => max (Z i ω) (P[bellmanAux P 𝓕 Z n (i+1) | 𝓕 i] ω)

/-- The Bellman value at index `i` for horizon `N`: the recursion run for the `N-i` remaining
steps from index `min i N`, so it is frozen at `Z N` past the horizon. -/
noncomputable def finiteBellman (P : Measure Ω) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›)
    (Z : ℕ → Ω → ℝ) (N i : ℕ) : Ω → ℝ :=
  bellmanAux P 𝓕 Z (N-i) (min i N)

variable {P : Measure Ω}
  {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}

theorem bellmanAux_measurable (hZ : Adapted 𝓕 Z) (n i : ℕ) :
    Measurable[𝓕 i] (bellmanAux P 𝓕 Z n i) := by
  cases n with
  | zero => exact hZ i
  | succ n => exact (hZ i).max stronglyMeasurable_condExp.measurable

theorem bellmanAux_integrable (hZ : ∀ i, Integrable (Z i) P) (n i : ℕ) :
    Integrable (bellmanAux P 𝓕 Z n i) P := by
  cases n with
  | zero => exact hZ i
  | succ n => exact (hZ i).sup integrable_condExp

theorem bellmanAux_dominates (n i : ℕ) (ω : Ω) : Z i ω ≤ bellmanAux P 𝓕 Z n i ω := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

theorem finiteBellman_after_horizon {N i : ℕ} (hNi : N ≤ i) :
    finiteBellman P 𝓕 Z N i = Z N := by
  simp only [finiteBellman,Nat.sub_eq_zero_of_le hNi,min_eq_right hNi,bellmanAux]

theorem finiteBellman_recursion {N i : ℕ} (hi : i < N) :
    finiteBellman P 𝓕 Z N i =
      fun ω => max (Z i ω) (P[finiteBellman P 𝓕 Z N (i+1) | 𝓕 i] ω) := by
  have hn : N-i = (N-(i+1))+1 := by omega
  rw [finiteBellman,min_eq_left hi.le,hn,bellmanAux]
  simp only [finiteBellman,min_eq_left (show i+1 ≤ N by omega)]

theorem finiteBellman_stronglyAdapted (hZ : Adapted 𝓕 Z) (N : ℕ) :
    StronglyAdapted 𝓕 (finiteBellman P 𝓕 Z N) := by
  intro i
  exact ((bellmanAux_measurable hZ (N-i) (min i N)).mono (𝓕.mono (min_le_left _ _))
      le_rfl).stronglyMeasurable

theorem finiteBellman_integrable (hZ : ∀ i, Integrable (Z i) P) (N i : ℕ) :
    Integrable (finiteBellman P 𝓕 Z N i) P := bellmanAux_integrable hZ _ _

theorem finiteBellman_dominates (N i : ℕ) (ω : Ω) :
    Z (min i N) ω ≤ finiteBellman P 𝓕 Z N i ω := bellmanAux_dominates _ _ ω

variable [IsProbabilityMeasure P]

theorem finiteBellman_supermartingale (ha : Adapted 𝓕 Z) (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    Supermartingale (finiteBellman P 𝓕 Z N) 𝓕 P := by
  apply supermartingale_nat (finiteBellman_stronglyAdapted ha N) (finiteBellman_integrable hi N)
  intro i
  by_cases hiN : i < N
  · rw [finiteBellman_recursion hiN]
    exact Eventually.of_forall (fun ω => le_max_right _ _)
  · have hNi : N ≤ i := le_of_not_gt hiN
    rw [finiteBellman_after_horizon hNi,
      finiteBellman_after_horizon (hNi.trans (Nat.le_succ i)),
      condExp_of_stronglyMeasurable (𝓕.le i)
        (((ha N).mono (𝓕.mono hNi) le_rfl).stronglyMeasurable) (hi N)]

omit [IsProbabilityMeasure P] in
/-- Minimality among integrable supermartingales dominating the reward. -/
theorem bellmanAux_le_supermartingale {U : ℕ → Ω → ℝ}
    (hU : Supermartingale U 𝓕 P) (hi : ∀ i, Integrable (Z i) P)
    (hdom : ∀ i, Z i ≤ᵐ[P] U i) (n i : ℕ) : bellmanAux P 𝓕 Z n i ≤ᵐ[P] U i := by
  induction n generalizing i with
  | zero => exact hdom i
  | succ n ih =>
    have hc :=
        condExp_mono (m := 𝓕 i) (bellmanAux_integrable hi n (i+1)) (hU.integrable (i+1)) (ih (i+1))
    filter_upwards [hdom i,hc,hU.2.1 i (i+1) (Nat.le_succ i)] with ω hz hc hu
    exact max_le hz (hc.trans hu)

omit [IsProbabilityMeasure P] in
theorem finiteBellman_le_supermartingale {U : ℕ → Ω → ℝ}
    (hU : Supermartingale U 𝓕 P) (hi : ∀ i, Integrable (Z i) P)
    (hdom : ∀ i, Z i ≤ᵐ[P] U i) {N i : ℕ} (hiN : i ≤ N) :
    finiteBellman P 𝓕 Z N i ≤ᵐ[P] U i := by
  simpa only [finiteBellman,min_eq_left hiN] using bellmanAux_le_supermartingale hU hi hdom (N-i) i

end MathFin.BlackScholes.AmericanPut.Stopping
