/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# The fundamental theorems of asset pricing in discrete time, one risky asset

A market trades one risky asset with discounted price `S t` at the dates `t = 0, 1, …, T` of a
filtered probability space `(Ω, 𝓕, P)`; cash is the numéraire and earns nothing. A trading
strategy holds `φ (t + 1)` units of the asset over the period `(t, t + 1]`, chosen with the
information of date `t`, and its terminal gain is the discrete stochastic integral
`∑_{t < T} φ (t + 1) * (S (t + 1) - S t)`.

`noArbitrage_iff_exists_isEMM` is the one-asset case of the Dalang–Morton–Willinger theorem
(Dalang, Morton and Willinger, *Stochastics and Stochastic Reports* 29 (1990)): on an arbitrary
filtered probability space, an adapted price admits no arbitrage up to the horizon if and only if
there is a probability measure `Q`, equivalent to `P`, under which the price stopped at the horizon
is a martingale. No integrability of `S`, no finiteness of `Ω` and no measurable-selection
hypothesis is assumed.

`isCompleteMarket_iff_existsUnique_isEMM` is the second fundamental theorem on a finite space
(Harrison and Pliska, *Stochastic Processes and their Applications* 11 (1981)): when `P` gives
every state positive mass, all events are observable at the horizon and there is no arbitrage,
every bounded claim is replicable if and only if the equivalent martingale measure is unique.

Scope, stated here so the reader need not reconstruct it:

* one risky asset only; the several-asset theorem of Dalang–Morton–Willinger is not claimed;
* arbitrage is tested with **bounded** predictable strategies (`NoArbitrage`). Every arbitrage-free
  market in this sense has an equivalent martingale measure, and the converse is proved for the
  same class; the theorem says nothing directly about unbounded strategies;
* the second theorem is stated on a finite space whose singletons are measurable and charged by
  `P`, with `𝓕 T` the whole σ-algebra, and completeness is replication of bounded claims by
  bounded strategies (on a finite space every claim and every strategy is bounded).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace DiscreteFTAP

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The **gain** up to date `n` of the strategy `φ` trading the price `S`:
`∑_{k < n} φ (k + 1) ω * (S (k + 1) ω - S k ω)`. The holding `φ (k + 1)` is carried over the
period `(k, k + 1]`. -/
noncomputable def gains (φ S : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, φ (k + 1) ω * (S (k + 1) ω - S k ω)

/-- **No arbitrage** up to the horizon `T`: every predictable (`φ (t + 1)` is `𝓕 t`-measurable
for `t < T`) and bounded strategy whose gain at `T` is `P`-almost surely nonnegative has gain
`P`-almost surely zero. -/
def NoArbitrage (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → ℝ) (T : ℕ) : Prop :=
  ∀ φ : ℕ → Ω → ℝ, (∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1))) →
    (∃ K : ℝ, ∀ n ≤ T, ∀ ω, |φ n ω| ≤ K) →
    0 ≤ᵐ[P] gains φ S T → gains φ S T =ᵐ[P] 0

/-- `Q` is an **equivalent martingale measure** for the price `S` up to the horizon `T`: a
probability measure with the same null sets as `P` under which the price stopped at the horizon,
`t ↦ S (min t T)`, is a martingale for `𝓕`. -/
structure IsEMM (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → ℝ) (T : ℕ)
    (Q : Measure Ω) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure Q
  absolutelyContinuous : Q ≪ P
  absolutelyContinuous' : P ≪ Q
  martingale : Martingale (fun t ↦ S (min t T)) 𝓕 Q

/-- The market is **complete** up to the horizon `T`: every bounded `𝓕 T`-measurable claim `H`
is, `P`-almost surely, the terminal wealth `x + gains φ S T` of some initial capital `x` and some
predictable bounded strategy `φ`. -/
def IsCompleteMarket (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → ℝ) (T : ℕ) : Prop :=
  ∀ H : Ω → ℝ, StronglyMeasurable[𝓕 T] H → (∃ C : ℝ, ∀ ω, |H ω| ≤ C) →
    ∃ (x : ℝ) (φ : ℕ → Ω → ℝ), (∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1))) ∧
      (∃ K : ℝ, ∀ n ≤ T, ∀ ω, |φ n ω| ≤ K) ∧ H =ᵐ[P] fun ω ↦ x + gains φ S T ω

variable {𝓕 : Filtration ℕ m0} {P : Measure Ω} {S : ℕ → Ω → ℝ} {T : ℕ}

/-- **The Dalang–Morton–Willinger theorem for one asset.** On any filtered probability space, a
real price adapted up to the horizon `T` admits no arbitrage up to `T` if and only if it has an
equivalent martingale measure. -/
theorem noArbitrage_iff_exists_isEMM [IsProbabilityMeasure P]
    (hS : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) :
    NoArbitrage 𝓕 P S T ↔ ∃ Q, IsEMM 𝓕 P S T Q := by
  sorry

/-- **The second fundamental theorem of asset pricing on a finite space.** On a nonempty finite
space with measurable singletons, each of positive `P`-measure, and with every event observable at
the horizon (`𝓕 T = m0`), an adapted price with no arbitrage gives a complete market if and only
if its equivalent martingale measure is unique. -/
theorem isCompleteMarket_iff_existsUnique_isEMM [Finite Ω] [Nonempty Ω]
    [MeasurableSingletonClass Ω] (hS : StronglyAdapted 𝓕 S) (hP : ∀ ω, 0 < P {ω})
    (hT : 𝓕 T = m0) (hNA : NoArbitrage 𝓕 P S T) :
    IsCompleteMarket 𝓕 P S T ↔ ∃! Q, IsEMM 𝓕 P S T Q := by
  sorry

end DiscreteFTAP
