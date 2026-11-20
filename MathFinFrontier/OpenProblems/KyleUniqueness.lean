/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin

/-!
# Open problem MF-OP-008: the one-period Gaussian Kyle equilibrium is unique

Catalogue record `MF-OP-008` (`docs/research-problems/README.md`); frontier node
`thm:kyle-equilibrium-unique`; statement `MathFinFrontier.kyle_equilibrium_unique`.

Kyle (1985) found an affine equilibrium of his one-period model: the insider trades
`φ(v) = (σ/τ)(v - m)` and the market makers price the order flow at `p(y) = m + (τ/(2σ)) y`.
Whether another equilibrium exists among all Borel strategies was a long-standing open question.
Monteiro–Tourky (ANU Working Paper 708, August 2026, Theorem 1.1) report that it is unique.
Their proof has not been checked here, and the catalogue records the problem as
`resolution_reported` (`docs/research-problems/problems.json`). Proving this statement settles
it. The converse, that Kyle's pair is an equilibrium, is the frontier node
`thm:kyle-equilibrium`.

The statement follows the paper's definition of equilibrium (§1, conditions 1 and 2):
the value `V ~ N(m, τ²)` and the noise demand `U ~ N(0, σ²)` are independent; the insider's
strategy `φ` and the pricing rule `p` are Borel; profit maximisation holds for every value `v`
and every order `x`; market efficiency holds almost surely. Expected profits are Bochner
integrals. They take no junk values here: given market efficiency, `p(x + U)` is integrable for
every `x` (the paper's Lemma 2.3), so the integrals are the expected profits.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- **MF-OP-008: uniqueness of the one-period Gaussian Kyle equilibrium.** Let `V ~ N(m, τ²)`
and `U ~ N(0, σ²)` be independent. If a Borel strategy `φ` and a Borel pricing rule `p` form an
equilibrium (the insider's order `φ v` maximises `E[(v - p(x + U)) x]` over `x` for every value
`v`, and `p(φ(V) + U) = E[V | φ(V) + U]` almost surely), then `φ` is Kyle's linear strategy
`v ↦ (σ/τ)(v - m)` at every `v`, and the price is `m + (τ/(2σ))(φ(V) + U)` almost surely. -/
theorem MathFinFrontier.kyle_equilibrium_unique {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℝ) {τ σ : ℝ≥0} (hτ : 0 < τ) (hσ : 0 < σ)
    {V U : Ω → ℝ} (hV : Measurable V) (hU : Measurable U)
    (hVlaw : μ.map V = gaussianReal m (τ ^ 2)) (hUlaw : μ.map U = gaussianReal 0 (σ ^ 2))
    (hindep : IndepFun V U μ) {φ p : ℝ → ℝ} (hφ : Measurable φ) (hp : Measurable p)
    (hprofit : ∀ v x : ℝ,
      ∫ ω, (v - p (x + U ω)) * x ∂μ ≤ ∫ ω, (v - p (φ v + U ω)) * φ v ∂μ)
    (hefficient : (fun ω ↦ p (φ (V ω) + U ω)) =ᵐ[μ]
      μ[V | MeasurableSpace.comap (fun ω ↦ φ (V ω) + U ω) inferInstance]) :
    (∀ v, φ v = σ / τ * (v - m)) ∧
      (fun ω ↦ p (φ (V ω) + U ω)) =ᵐ[μ] fun ω ↦ m + τ / (2 * σ) * (φ (V ω) + U ω) := by
  sorry
