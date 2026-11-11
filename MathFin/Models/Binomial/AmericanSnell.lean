/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.Binomial.American
public import MathFin.Models.Binomial.PathMeasure

/-!
# The binomial American price is the Snell envelope

The tree's American price `americanPrice u d ρ g N S₀` (`Models/Binomial/American.lean`) is the
Bellman recursion with exercise at every step. Under the risk-neutral coin flips
`coinFlipMeasure q`, with `q = crrUpProb u d ρ`, it is the time-`0` value of the library's Snell
envelope `snellEnvelope` (`Probability/Discrete/SnellEnvelope.lean`, Mathlib's conditional
expectation on the flip filtration) of the discounted intrinsic value `e^{−ρn} g(Sₙ)` along the
spot path, with every date an exercise date. It is the exercise-everywhere case of
`snellEnvelope_discounted_bermudanPrice` at time `0`.

Not proved here: the envelope as a supremum over stopping times, or any statement about the
price at a later time.

## Main results

* `americanPrice_eq_snellEnvelope`: almost surely under `coinFlipMeasure q`, the Snell envelope at
  time `0` of the discounted intrinsic value is `americanPrice u d ρ g N S₀`.

## References

* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  4.4

## Tags

American option, binomial tree, Snell envelope, optimal stopping, early exercise,
MSC 91G20, MSC 60G40, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory
open scoped NNReal

/-- **The binomial American price is the Snell envelope.** Under the risk-neutral coin flips
(`crrUpProb u d ρ = q`), the Snell envelope of the discounted intrinsic value `e^{−ρn} g(Sₙ)`
along the spot path, for the flip filtration, horizon `N` and exercise at every date, is at time
`0` almost surely `americanPrice u d ρ g N S₀`. -/
theorem americanPrice_eq_snellEnvelope {u d ρ : ℝ} {q : ℝ≥0} (hq : q ≤ 1)
    (hqcrr : crrUpProb u d ρ = q) (g : ℝ → ℝ) (S₀ : ℝ) (N : ℕ) :
    ∀ᵐ ω ∂coinFlipMeasure q hq,
      snellEnvelope (coinFlipMeasure q hq) flipFiltration Set.univ
        (fun n ω ↦ Real.exp (-ρ * n) * g (spotPath S₀ u d n ω)) N 0 ω
      = americanPrice u d ρ g N S₀ := by
  have h := snellEnvelope_discounted_bermudanPrice (E := Set.univ) hq u d ρ g S₀ hqcrr
    (N := N) (k := 0) (Nat.zero_le N)
  simp only [Set.mem_univ, Set.setOf_true] at h
  filter_upwards [h] with ω hω
  rw [hω]
  simp [americanPrice, spotPath]

end MathFin
