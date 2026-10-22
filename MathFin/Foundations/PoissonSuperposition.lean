/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.PoissonCounting

/-!
# Superposition of Poisson streams: the map-form increment law

The convolution identity `poissonMeasure a ∗ poissonMeasure b =
poissonMeasure (a + b)` is **Mathlib's** — `ProbabilityTheory.poissonMeasure_conv_poissonMeasure`,
landed 2026-05-26 (leanprover-community/mathlib4#34435), proved there by
characteristic functions. This file used to re-derive it from the point masses
(Cauchy product + binomial collapse); that proof was a duplicate of upstream and
has been replaced by consumption. What remains here is the piece Mathlib does
not carry in this form.

Mathlib's superposition statements are `HasLaw`-shaped
(`IndepFun.hasLaw_add_poissonMeasure`). The Poisson-process tower states its
increment laws as **pushforward equalities** `μ.map X = poissonMeasure a`, and
gets the measurability side conditions for free from a nonzero pushforward
rather than assuming them. `indepFun_map_add_poissonMeasure` is that adapter,
and it is the only mathematical content this file still owns.

## Main results

* `PoissonSuperposition.poissonMeasure_conv_poissonMeasure` — re-export of
  Mathlib's convolution identity, kept as the name the Poisson benchmark
  snippets reference.
* `PoissonSuperposition.indepFun_map_add_poissonMeasure` — if `X, Y` are
  independent with `Poisson(a)`, `Poisson(b)` laws *as pushforwards*, then
  `X + Y` has `Poisson(a+b)` law (the superposition theorem at increment level,
  Saporito Theorem 3.3.9, with no measurability hypotheses).
* `PoissonSuperposition.map_add_count_eq_poissonMeasure` — two counting processes built
  from independent families of i.i.d. `Exp(r₁)` and `Exp(r₂)` interarrival times
  (`Foundations/PoissonCounting`) merge into a count with `Poisson((r₁ + r₂)·t)` law at
  every time `t ≥ 0`. The marginal laws are derived by `map_count_eq_poissonMeasure`, and
  the independence of the two counts is derived from that of the interarrival families.
  This is the one-time marginal of the merged stream; that the merged count is a Poisson
  process (independent increments, exponential merged interarrival times) is not proved.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace PoissonSuperposition

/-- **Poisson convolution identity** — Mathlib's
`ProbabilityTheory.poissonMeasure_conv_poissonMeasure`, re-exported under the
name the Poisson benchmark snippets reference. Not proved here: upstream has it
(via characteristic functions) and a second proof would be a duplicate. -/
theorem poissonMeasure_conv_poissonMeasure (a b : ℝ≥0) :
    poissonMeasure a ∗ poissonMeasure b = poissonMeasure (a + b) :=
  _root_.ProbabilityTheory.poissonMeasure_conv_poissonMeasure a b

/-! ### Superposition at increment level -/

/-- **Superposition theorem (increment form, Saporito Theorem 3.3.9).** If
`X` and `Y` are independent `ℕ`-valued random counts with `Poisson(a)` and
`Poisson(b)` laws, their sum is `Poisson(a + b)`. No measurability hypotheses
are needed: a nonzero pushforward forces a.e.-measurability. -/
theorem indepFun_map_add_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {a b : ℝ≥0} {X Y : Ω → ℕ} (hXY : IndepFun X Y μ)
    (hX : μ.map X = poissonMeasure a) (hY : μ.map Y = poissonMeasure b) :
    μ.map (fun ω ↦ X ω + Y ω) = poissonMeasure (a + b) := by
  rw [show (fun ω ↦ X ω + Y ω) = X + Y from rfl,
    hXY.map_add_eq_map_conv_map₀', hX, hY, poissonMeasure_conv_poissonMeasure]
  · apply AEMeasurable.of_map_ne_zero
    simp [hX, NeZero.ne]
  · apply AEMeasurable.of_map_ne_zero
    simp [hY, NeZero.ne]
  · rw [hX]; infer_instance
  · rw [hY]; infer_instance

/-! ### Merging two arrival-time constructions -/

/-- A counting process read off its interarrival times is a function of the whole family of
interarrival times: `N t` is measurable for the σ-algebra that family generates. -/
lemma measurable_count_comap {Ω : Type*} {ξ : ℕ → Ω → ℝ}
    {N : ℝ → Ω → ℕ}
    (hcount : ∀ t k ω, N t ω = k ↔
      (∑ i ∈ Finset.range k, ξ i ω) ≤ t ∧ t < ∑ i ∈ Finset.range (k + 1), ξ i ω) (t : ℝ) :
    Measurable[MeasurableSpace.comap (fun ω i ↦ ξ i ω) inferInstance] (N t) := by
  refine @measurable_to_countable' ℕ Ω _ _
    (MeasurableSpace.comap (fun ω i ↦ ξ i ω) inferInstance) (N t) fun k ↦
    ⟨{x : ℕ → ℝ | (∑ i ∈ Finset.range k, x i) ≤ t ∧ t < ∑ i ∈ Finset.range (k + 1), x i},
      ?_, ?_⟩
  · exact (measurableSet_le (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i)
      measurable_const).inter
      (measurableSet_lt measurable_const (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i))
  · ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff, hcount]

/-- **Superposition of two arrival-time constructions.** Let `ξ` and `η` be families of i.i.d.
`Exp(r₁)` and `Exp(r₂)` interarrival times, independent of each other, and `N₁`, `N₂` the
counting processes they generate (`N t = k` iff the `k`-th arrival has happened by `t` but the
`(k+1)`-st has not). Then for every `t ≥ 0` the merged count `N₁ t + N₂ t` has the
`Poisson((r₁ + r₂)·t)` law.

The marginals `Poisson(r₁ t)` and `Poisson(r₂ t)` are derived from the constructions
(`PoissonCounting.map_count_eq_poissonMeasure`); the two counts are independent because each is
a function of its own interarrival family (`measurable_count_comap`); the convolution is
`indepFun_map_add_poissonMeasure`. Only the one-time marginal of the merged stream is stated. -/
theorem map_add_count_eq_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {r₁ r₂ : ℝ≥0} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) {ξ η : ℕ → Ω → ℝ}
    (hξm : ∀ i, Measurable (ξ i)) (hηm : ∀ i, Measurable (η i))
    (hξ0 : ∀ i ω, 0 ≤ ξ i ω) (hη0 : ∀ i ω, 0 ≤ η i ω)
    (hξlaw : ∀ i, μ.map (ξ i) = expMeasure r₁) (hηlaw : ∀ i, μ.map (η i) = expMeasure r₂)
    (hξind : iIndepFun ξ μ) (hηind : iIndepFun η μ)
    (hξη : IndepFun (fun ω i ↦ ξ i ω) (fun ω i ↦ η i ω) μ)
    {N₁ N₂ : ℝ → Ω → ℕ}
    (hN₁ : ∀ t k ω, N₁ t ω = k ↔
      (∑ i ∈ Finset.range k, ξ i ω) ≤ t ∧ t < ∑ i ∈ Finset.range (k + 1), ξ i ω)
    (hN₂ : ∀ t k ω, N₂ t ω = k ↔
      (∑ i ∈ Finset.range k, η i ω) ≤ t ∧ t < ∑ i ∈ Finset.range (k + 1), η i ω)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.map (fun ω ↦ N₁ t ω + N₂ t ω) = poissonMeasure ((r₁ + r₂) * ⟨t, ht⟩) := by
  have hind : IndepFun (N₁ t) (N₂ t) μ :=
    (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
      (indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).1 hξη)
        (measurable_count_comap hN₁ t).comap_le)
      (measurable_count_comap hN₂ t).comap_le)
  convert indepFun_map_add_poissonMeasure hind
    (PoissonCounting.map_count_eq_poissonMeasure hr₁ hξm hξ0 hξlaw hξind hN₁ ht)
    (PoissonCounting.map_count_eq_poissonMeasure hr₂ hηm hη0 hηlaw hηind hN₂ ht) using 2
  exact add_mul r₁ r₂ (⟨t, ht⟩ : ℝ≥0)

end PoissonSuperposition

end MathFin
