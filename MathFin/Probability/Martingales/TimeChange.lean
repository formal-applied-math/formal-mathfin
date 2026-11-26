/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import Mathlib.Probability.Martingale.Basic

/-!
# A martingale along a monotone time change

A filtration `𝓕` indexed by `ι` and a monotone map `φ : κ → ι` give a filtration indexed by `κ`,
`t ↦ 𝓕 (φ t)` (`Filtration.comp`). A martingale `f` for `𝓕` read along `φ`, `t ↦ f (φ t)`, is a
martingale for it (`Martingale.comp`). When `φ` has a monotone right inverse `ψ` (`φ (ψ i) = i`),
the converse holds: a process whose reading along `φ` is a martingale is one itself
(`Martingale.of_comp`).

The time change that matters here is the step count of a discrete market seen in continuous time:
`t ↦ ⌊t⌋₊` for unit steps, `t ↦ ⌊t / h⌋₊` for steps of length `h`. The discrete market and the
binomial tree become markets indexed by `ℝ≥0` this way (`Pricing/DiscreteMarket.lean`,
`Models/Binomial/Market.lean`).

## Main definitions

* `MeasureTheory.Filtration.comp`: the filtration `t ↦ 𝓕 (φ t)` along a monotone `φ`.
* `MeasureTheory.Filtration.twoStep`: trivial at date `0`, everything from date `1` on; a
  one-period market's information, which a one-date market reads along its date step.

## Main results

* `MeasureTheory.Martingale.comp`: a martingale read along a monotone time change is a martingale.
* `MeasureTheory.Martingale.of_comp`: the converse, along a time change with a monotone right
  inverse.

## References

* [Rogers and Williams][RogersWilliams]

## Tags

martingale, filtration, time change, reindexing, discrete time in continuous time, MSC 60G42,
MSC 60G44
-/

@[expose] public section

namespace MeasureTheory

variable {Ω ι κ E : Type*} {m : MeasurableSpace Ω} [Preorder ι] [Preorder κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Ω}

/-- The filtration `t ↦ 𝓕 (φ t)` along a monotone time change `φ`. -/
def Filtration.comp (𝓕 : Filtration ι m) {φ : κ → ι} (hφ : Monotone φ) : Filtration κ m where
  seq t := 𝓕 (φ t)
  mono' _ _ hst := 𝓕.mono (hφ hst)
  le' _ := 𝓕.le _

@[simp]
theorem Filtration.comp_apply (𝓕 : Filtration ι m) {φ : κ → ι} (hφ : Monotone φ) (t : κ) :
    𝓕.comp hφ t = 𝓕 (φ t) :=
  rfl

/-- **A martingale read along a monotone time change is a martingale** for the time-changed
filtration. -/
theorem Martingale.comp {𝓕 : Filtration ι m} {f : ι → Ω → E} (hf : Martingale f 𝓕 μ)
    {φ : κ → ι} (hφ : Monotone φ) : Martingale (fun t ↦ f (φ t)) (𝓕.comp hφ) μ :=
  ⟨fun t ↦ hf.1 (φ t), fun _ _ hst ↦ hf.2 _ _ (hφ hst)⟩

/-- **Conversely, a process whose reading along a time change is a martingale is a martingale**,
when the time change `φ` has a monotone right inverse `ψ`: read the martingale at the times
`ψ i`. -/
theorem Martingale.of_comp {𝓕 : Filtration ι m} {f : ι → Ω → E} {φ : κ → ι} (hφ : Monotone φ)
    {ψ : ι → κ} (hψ : Monotone ψ) (hφψ : ∀ i, φ (ψ i) = i)
    (hf : Martingale (fun t ↦ f (φ t)) (𝓕.comp hφ) μ) : Martingale f 𝓕 μ := by
  refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · have h := hf.1 (ψ i)
    beta_reduce at h
    rw [Filtration.comp_apply, hφψ] at h
    exact h
  · have h := hf.2 (ψ i) (ψ j) (hψ hij)
    beta_reduce at h
    rw [Filtration.comp_apply, hφψ, hφψ] at h
    exact h

/-- **The two-step filtration** of `ℕ`: nothing is known at date `0`, everything from date `1`
on. It is the information of a one-period market with trivial initial information. -/
def Filtration.twoStep (Ω : Type*) [mΩ : MeasurableSpace Ω] : Filtration ℕ mΩ where
  seq n := if n = 0 then ⊥ else mΩ
  mono' a b hab := by
    dsimp only
    split_ifs with ha hb hb
    · exact le_rfl
    · exact bot_le
    · exact absurd (Nat.le_zero.mp (hb ▸ hab)) ha
    · exact le_rfl
  le' n := by
    dsimp only
    split_ifs
    · exact bot_le
    · exact le_rfl

section TwoStep

variable (Ω : Type*) [mΩ : MeasurableSpace Ω]

/-- Nothing is known at date `0`. -/
theorem Filtration.twoStep_zero : Filtration.twoStep Ω 0 = ⊥ := rfl

/-- Everything is known at date `1`. -/
theorem Filtration.twoStep_one : Filtration.twoStep Ω 1 = mΩ := rfl

variable {Ω} in
/-- Everything is known from date `1` on. -/
theorem Filtration.twoStep_of_ne_zero {n : ℕ} (hn : n ≠ 0) : Filtration.twoStep Ω n = mΩ :=
  if_neg hn

end TwoStep

end MeasureTheory
