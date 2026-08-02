/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksey Salkutsan
-/
module

public import MathFin.Performance.Ratios

/-!
# Downside performance metrics

Finite-state Omega ratio, maximum drawdown of a finite price path, and the
positive-scaling invariance of the Calmar ratio.
-/

@[expose] public section

namespace MathFin

open scoped BigOperators

/-- A finite return model with nonnegative probability weights of total mass one. -/
structure FiniteReturnModel (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  outcome : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum_one : ∑ i, weight i = 1

/-- Expected return of a finite return model. -/
def finiteExpectedReturn {ι : Type*} [Fintype ι] (m : FiniteReturnModel ι) : ℝ :=
  ∑ i, m.weight i * m.outcome i

/-- Expected gain above a threshold. -/
def omegaUpside {ι : Type*} [Fintype ι] (m : FiniteReturnModel ι) (threshold : ℝ) : ℝ :=
  ∑ i, m.weight i * max (m.outcome i - threshold) 0

/-- Expected shortfall below a threshold. -/
def omegaDownside {ι : Type*} [Fintype ι]
    (m : FiniteReturnModel ι) (threshold : ℝ) : ℝ :=
  ∑ i, m.weight i * max (threshold - m.outcome i) 0

/-- Omega ratio at a threshold in a finite state space. -/
def omegaRatio {ι : Type*} [Fintype ι] (m : FiniteReturnModel ι) (threshold : ℝ) : ℝ :=
  omegaUpside m threshold / omegaDownside m threshold

private theorem positivePart_sub_negativePart (x : ℝ) :
    max x 0 - max (-x) 0 = x := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · have hx0 : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx0, max_eq_left (neg_nonneg.mpr hx0)]
    ring

/-- Expected upside minus expected downside equals mean excess return. -/
theorem omega_upside_sub_downside {ι : Type*} [Fintype ι]
    (m : FiniteReturnModel ι) (threshold : ℝ) :
    omegaUpside m threshold - omegaDownside m threshold =
      finiteExpectedReturn m - threshold := by
  unfold omegaUpside omegaDownside finiteExpectedReturn
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i, (m.weight i * max (m.outcome i - threshold) 0 -
        m.weight i * max (threshold - m.outcome i) 0)) =
        ∑ i, m.weight i * (m.outcome i - threshold) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← mul_sub]
          congr 1
          convert positivePart_sub_negativePart (m.outcome i - threshold) using 1 <;> ring
    _ = ∑ i, (m.weight i * m.outcome i - threshold * m.weight i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (∑ i, m.weight i * m.outcome i) - threshold * (∑ i, m.weight i) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (∑ i, m.weight i * m.outcome i) - threshold := by
          rw [m.weight_sum_one, mul_one]

/-- The finite-state Omega ratio is nonnegative. -/
theorem omegaRatio_nonneg {ι : Type*} [Fintype ι]
    (m : FiniteReturnModel ι) (threshold : ℝ) :
    0 ≤ omegaRatio m threshold := by
  unfold omegaRatio omegaUpside omegaDownside
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (m.weight_nonneg i) (le_max_right _ _)
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (m.weight_nonneg i) (le_max_right _ _)

/-- Threshold identity for the Omega ratio when expected downside is nonzero. -/
theorem omegaRatio_threshold_identity {ι : Type*} [Fintype ι]
    (m : FiniteReturnModel ι) (threshold : ℝ)
    (hdown : omegaDownside m threshold ≠ 0) :
    omegaRatio m threshold - 1 =
      (finiteExpectedReturn m - threshold) / omegaDownside m threshold := by
  calc
    omegaRatio m threshold - 1 =
        (omegaUpside m threshold - omegaDownside m threshold) /
          omegaDownside m threshold := by
            unfold omegaRatio
            field_simp [hdown]
    _ = (finiteExpectedReturn m - threshold) / omegaDownside m threshold := by
          rw [omega_upside_sub_downside]

/-- Maximum of a finite list, with zero as the empty-list baseline. -/
def listMaximum : List ℝ → ℝ
  | [] => 0
  | x :: xs => max x (listMaximum xs)

private theorem listMaximum_nonneg (xs : List ℝ) : 0 ≤ listMaximum xs := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact ih.trans (le_max_right _ _)

private theorem listMaximum_map_mul (c : ℝ) (hc : 0 ≤ c) (xs : List ℝ) :
    listMaximum (xs.map fun x => c * x) = c * listMaximum xs := by
  induction xs with
  | nil => simp [listMaximum]
  | cons x xs ih =>
      simp only [List.map_cons, listMaximum]
      rw [ih]
      by_cases h : x ≤ listMaximum xs
      · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h hc)]
      · have h' : listMaximum xs ≤ x := le_of_not_ge h
        rw [max_eq_left h', max_eq_left (mul_le_mul_of_nonneg_left h' hc)]

/-- All chronologically admissible peak-to-trough losses of a finite price path. -/
def drawdownCandidates {n : ℕ} (price : Fin n → ℝ) : List ℝ :=
  (((Finset.univ : Finset (Fin n)).product Finset.univ).toList).map fun ij =>
    if ij.1 ≤ ij.2 then price ij.1 - price ij.2 else 0

private theorem drawdownCandidates_scale {n : ℕ} (price : Fin n → ℝ) (c : ℝ) :
    drawdownCandidates (fun i => c * price i) =
      (drawdownCandidates price).map fun x => c * x := by
  simp [drawdownCandidates, List.map_map, mul_sub]

/-- Maximum drawdown of a finite price path. -/
def maximumDrawdown {n : ℕ} (price : Fin n → ℝ) : ℝ :=
  listMaximum (drawdownCandidates price)

/-- Maximum drawdown is nonnegative, including for an empty path. -/
theorem maximumDrawdown_nonneg {n : ℕ} (price : Fin n → ℝ) :
    0 ≤ maximumDrawdown price :=
  listMaximum_nonneg _

/-- Maximum drawdown is positively homogeneous for nonnegative scaling. -/
theorem maximumDrawdown_scale {n : ℕ} (price : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    maximumDrawdown (fun i => c * price i) = c * maximumDrawdown price := by
  unfold maximumDrawdown
  rw [drawdownCandidates_scale, listMaximum_map_mul c hc]

/-- Calmar ratio: annual return divided by maximum drawdown. -/
def calmarRatio (annualReturn maxDrawdown : ℝ) : ℝ :=
  annualReturn / maxDrawdown

/-- Calmar ratio is invariant under strictly positive common scaling. -/
theorem calmarRatio_scale_invariant (annualReturn maxDrawdown c : ℝ) (hc : 0 < c) :
    calmarRatio (c * annualReturn) (c * maxDrawdown) =
      calmarRatio annualReturn maxDrawdown := by
  simpa [calmarRatio] using
    (diff_div_scale_invariant (c := c) hc.ne' annualReturn 0 maxDrawdown)

/-- One acceptance bundle covering Omega, maximum drawdown, and Calmar. -/
theorem downsideMetrics_bundle {ι : Type*} [Fintype ι]
    (m : FiniteReturnModel ι) (threshold : ℝ)
    (hdown : omegaDownside m threshold ≠ 0)
    {n : ℕ} (price : Fin n → ℝ) (annualReturn c : ℝ) (hc : 0 < c) :
    (0 ≤ omegaRatio m threshold ∧
      omegaRatio m threshold - 1 =
        (finiteExpectedReturn m - threshold) / omegaDownside m threshold) ∧
    (0 ≤ maximumDrawdown price ∧
      maximumDrawdown (fun i => c * price i) = c * maximumDrawdown price) ∧
    calmarRatio (c * annualReturn) (c * maximumDrawdown price) =
      calmarRatio annualReturn (maximumDrawdown price) := by
  exact
    ⟨⟨omegaRatio_nonneg m threshold,
        omegaRatio_threshold_identity m threshold hdown⟩,
      ⟨maximumDrawdown_nonneg price,
        maximumDrawdown_scale price c hc.le⟩,
      calmarRatio_scale_invariant annualReturn (maximumDrawdown price) c hc⟩

end MathFin
