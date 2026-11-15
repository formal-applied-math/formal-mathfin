/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Probability.Martingales.StoppingRule
public import MathFin.Probability.Martingales.TimeChange

/-!
# Stopping on a grid

A discrete filtration `𝓖` read in continuous time along the step count `t ↦ ⌊t / h⌋₊`
(`Filtration.comp`) is the information of an observer who learns only at the dates `n h`. A
process read the same way, `t ↦ Z ⌊t / h⌋₊`, can in effect only be stopped on the grid. A rule
`θ` of the continuous-time filtration, counted in whole steps, `⌊θ / h⌋₊`, is a discrete rule; a
discrete rule `σ` read in time, `σ h`, is a continuous-time rule; and both give the same stopped
payoff. So the two stopping values agree, with no integrability or boundedness assumption: their
sets of expected stopped payoffs are equal.

This is how a discrete market read in continuous time, such as the binomial market, prices an
American claim by the discrete stopping value of its tree (`Market.americanPrice`).

## Main definitions

* `StoppingRule.floorDiv`: a rule of the filtration along `⌊t / h⌋₊`, counted in whole steps.
* `StoppingRule.mulStep`: a discrete rule, read in time as the date `σ h`.

## Main results

* `floor_div_le_iff`: `⌊x / h⌋₊ ≤ n ↔ x < (n + 1) h` for `x ≥ 0` and `h > 0`.
* `stoppingValue_comp_floorDiv`: the stopping value of `t ↦ Z ⌊t / h⌋₊` for the filtration along
  `⌊t / h⌋₊` with horizon `T` is the discrete stopping value of `Z` with horizon `⌊T / h⌋₊`.

## References

* [G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*][PeskirShiryaev2006]

## Tags

stopping time, optimal stopping, discrete grid, step count, time change, Bermudan exercise,
MSC 60G40, MSC 91G20
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MathFin

/-- Whole steps of length `h > 0` made by time `x ≥ 0`: at most `n` exactly when `x` is before the
`(n + 1)`-th date. -/
theorem floor_div_le_iff {h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x) (n : ℕ) :
    ⌊x / h⌋₊ ≤ n ↔ x < (n + 1) * h := by
  rw [← Nat.lt_succ_iff, Nat.floor_lt (div_nonneg hx hh.le), Nat.cast_succ, div_lt_iff₀ hh]

variable {Ω : Type*} [MeasurableSpace Ω] {𝓖 : Filtration ℕ ‹MeasurableSpace Ω›} {h : ℝ}
  (hφ : Monotone fun t : ℝ≥0 ↦ ⌊(t : ℝ) / h⌋₊)

namespace StoppingRule

/-- A stopping rule of the filtration along the step count `⌊t / h⌋₊`, counted in whole steps:
`⌊θ / h⌋₊` is a discrete stopping rule, with horizon `⌊T / h⌋₊`. The event `{⌊θ / h⌋₊ ≤ n}` is
`{θ < (n + 1) h}`, the union of the events `{θ ≤ s}` over dates `s` before the `(n + 1)`-th, each
known at step `⌊s / h⌋₊ ≤ n`. -/
noncomputable def floorDiv (hh : 0 < h) {T : ℝ≥0} (θ : StoppingRule (𝓖.comp hφ) T) :
    StoppingRule 𝓖 ⌊(T : ℝ) / h⌋₊ where
  time ω := ⌊(θ.time ω : ℝ) / h⌋₊
  stopping n := by
    have key (x : ℝ≥0) : ⌊(x : ℝ) / h⌋₊ ≤ n ↔ x < (n + 1) * h.toNNReal := by
      rw [floor_div_le_iff hh x.coe_nonneg, ← NNReal.coe_lt_coe]
      simp [Real.coe_toNNReal _ hh.le]
    have hc : (0 : ℝ≥0) < (n + 1) * h.toNNReal := by positivity
    obtain ⟨s, -, hs, hlim⟩ := exists_seq_strictMono_tendsto' hc
    have hset : {ω | ((⌊(θ.time ω : ℝ) / h⌋₊ : ℕ) : WithTop ℕ) ≤ n}
        = ⋃ k, {ω | ((θ.time ω : ℝ≥0) : WithTop ℝ≥0) ≤ s k} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, WithTop.coe_le_coe, Nat.cast_le, key]
      exact ⟨fun hθ ↦ ((hlim.eventually (lt_mem_nhds hθ)).exists).imp fun _ ↦ le_of_lt,
        fun ⟨k, hk⟩ ↦ hk.trans_lt (hs k).2⟩
    exact (congrArg (MeasurableSet[𝓖 n] ·) hset).mpr
      (MeasurableSet.iUnion fun k ↦ 𝓖.mono ((key (s k)).2 (hs k).2) _ (θ.stopping (s k)))
  le_horizon ω := hφ (θ.le_horizon ω)

/-- A discrete stopping rule read in time: it stops at the date `σ h`, a stopping rule of the
filtration along `⌊t / h⌋₊` with horizon `T`. -/
noncomputable def mulStep (hh : 0 < h) {T : ℝ≥0} (σ : StoppingRule 𝓖 ⌊(T : ℝ) / h⌋₊) :
    StoppingRule (𝓖.comp hφ) T where
  time ω := σ.time ω * h.toNNReal
  stopping t := by
    have hset : {ω | (((σ.time ω : ℝ≥0) * h.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ t}
        = {ω | ((σ.time ω : ℕ) : WithTop ℕ) ≤ ⌊(t : ℝ) / h⌋₊} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_mul,
        NNReal.coe_natCast, Real.coe_toNNReal _ hh.le]
      rw [Nat.cast_le, Nat.le_floor_iff (div_nonneg t.coe_nonneg hh.le), le_div_iff₀ hh]
    rw [hset]
    exact σ.stopping _
  le_horizon ω := by
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ hh.le,
      ← le_div_iff₀ hh]
    exact (Nat.cast_le.2 (σ.le_horizon ω)).trans (Nat.floor_le (div_nonneg T.coe_nonneg hh.le))

theorem floorDiv_mulStep (hh : 0 < h) {T : ℝ≥0} (σ : StoppingRule 𝓖 ⌊(T : ℝ) / h⌋₊) (ω : Ω) :
    ((σ.mulStep hφ hh).floorDiv hφ hh).time ω = σ.time ω := by
  simp [floorDiv, mulStep, Real.coe_toNNReal _ hh.le, hh.ne']

end StoppingRule

/-- **Stopping on a grid is discrete stopping.** For a step `h > 0`, the stopping value of the
process `t ↦ Z ⌊t / h⌋₊` for the filtration along `⌊t / h⌋₊`, over the rules with horizon `T`, is
the discrete stopping value of `Z` over the rules with horizon `⌊T / h⌋₊`: the two sets of expected
stopped payoffs are equal. -/
theorem stoppingValue_comp_floorDiv (hh : 0 < h) (P : Measure Ω) (Z : ℕ → Ω → ℝ) (T : ℝ≥0) :
    stoppingValue P (𝓖.comp hφ) (fun t ω ↦ Z ⌊(t : ℝ) / h⌋₊ ω) T =
      stoppingValue P 𝓖 Z ⌊(T : ℝ) / h⌋₊ := by
  unfold stoppingValue
  congr 1
  ext x
  constructor
  · rintro ⟨θ, -, rfl⟩
    exact ⟨θ.floorDiv hφ hh, mem_univ _, rfl⟩
  · rintro ⟨σ, -, rfl⟩
    refine ⟨σ.mulStep hφ hh, mem_univ _, ?_⟩
    simp only
    congr 1 with ω
    rw [← σ.floorDiv_mulStep hφ hh ω]
    rfl

end MathFin
