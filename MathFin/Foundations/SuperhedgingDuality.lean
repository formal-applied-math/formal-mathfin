/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.FTAPMultiState

/-!
# The fundamental superhedging bound

In a finite-state market with excess-return matrix `z : Fin M → Fin N → ℝ` (`M` assets, `N` states),
every **martingale probability vector** `q` — `q ≥ 0`, `∑ q = 1`, every asset's excess return
`q`-fair (`martingaleProbVectors z`) — prices a claim at most its super-replication cost:
`∑ qₙ Yₙ ≤ x` for any cost-`x` portfolio `θ` that dominates `Y` in every state. A martingale
probability vector may vanish on some states; the equivalent martingale measures
(`HasEMM_multi_state`, `Foundations/FTAPMultiState.lean`) are exactly its strictly positive members
(`hasEMM_multi_state_iff_exists_pos_mem`), so the bound holds for every EMM in particular.

Two consequences:

* `martingalePrice_eq_of_replicates` — the law of one price: every martingale probability vector
  prices a replicable claim at its replication cost.
* `exists_pos_price_le_superReplication` — under no arbitrage the multi-state FTAP
  (`hasEMM_multi_of_not_hasArbitrage`, by separation) supplies a strictly positive pricing vector
  whose price of each claim bounds every super-replication cost of that claim from below, so the
  superhedging price of a claim is not `−∞`.

The full superhedging *duality* (superhedging price *equals* the supremum of EMM prices) is the reverse,
separation-based direction; it requires closedness of the super-replication cone `{W | ∃ θ, W ≤ θ·z}`.
Farkas itself is *not* the blocker — Mathlib ships `ProperCone.hyperplane_separation` and
`hyperplane_separation_point` (`Analysis/Convex/Cone/Dual.lean`). What is missing at this pin is
closedness of a finitely generated cone: Mathlib has `PointedCone.DualFG` but no Minkowski–Weyl and no
`PointedCone.isClosed_span_of_finite`. That one lemma is the whole remaining cost.

## Main results
* `MathFin.martingaleProbVectors`, `MathFin.SuperReplicates`
* `MathFin.emm_le_superReplication` — the fundamental bound, over all martingale probability vectors
* `MathFin.hasEMM_multi_state_iff_exists_pos_mem` — the EMMs are the strictly positive ones
* `MathFin.martingalePrice_eq_of_replicates` — the law of one price
* `MathFin.exists_pos_price_le_superReplication` — the bound is non-vacuous under no arbitrage
-/

@[expose] public section

namespace MathFin


variable {M N : ℕ}

/-- The **martingale probability vectors** of an excess-return matrix `z`: probability vectors
`q ≥ 0`, `∑ q = 1`, under which every asset's excess return is fair (prices to zero). These are
the martingale measures on the `N` states. They need not be *equivalent* ones: `q` may vanish on a
state. The equivalent martingale measures are the strictly positive members
(`hasEMM_multi_state_iff_exists_pos_mem`). -/
def martingaleProbVectors (z : Fin M → Fin N → ℝ) : Set (Fin N → ℝ) :=
  {q | (∀ n, 0 ≤ q n) ∧ (∑ n, q n = 1) ∧ ∀ m, ∑ n, q n * z m n = 0}

/-- `(x, θ)` super-replicates the claim `Y`: cost `x` plus the portfolio `θ` dominates `Y` in every
state. -/
def SuperReplicates (z : Fin M → Fin N → ℝ) (Y : Fin N → ℝ) (x : ℝ) (θ : Fin M → ℝ) : Prop :=
  ∀ n, Y n ≤ x + ∑ m, θ m * z m n

/-- **The fundamental superhedging bound.** Every martingale probability vector — in particular
every equivalent martingale measure — prices a claim at most every super-replication cost: under
any martingale measure, the claim's expected value cannot exceed the cost of any portfolio that
dominates it. The name records the classical EMM form; the statement holds on the larger set
`martingaleProbVectors z`. -/
theorem emm_le_superReplication (z : Fin M → Fin N → ℝ) (Y : Fin N → ℝ)
    {q : Fin N → ℝ} (hq : q ∈ martingaleProbVectors z) {x : ℝ} {θ : Fin M → ℝ}
    (hsr : SuperReplicates z Y x θ) :
    ∑ n, q n * Y n ≤ x := by
  obtain ⟨hq_nn, hq_sum, hq_mart⟩ := hq
  have hcross : ∑ n, q n * (∑ m, θ m * z m n) = 0 := by
    have hswap : ∑ n, q n * (∑ m, θ m * z m n) = ∑ m, θ m * (∑ n, q n * z m n) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun n _ ↦ by ring
    rw [hswap]
    exact Finset.sum_eq_zero fun m _ ↦ by rw [hq_mart m, mul_zero]
  calc ∑ n, q n * Y n
      ≤ ∑ n, q n * (x + ∑ m, θ m * z m n) :=
        Finset.sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_left (hsr n) (hq_nn n)
    _ = x := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hq_sum, one_mul, hcross, add_zero]

/-- **The EMMs are the strictly positive martingale probability vectors.** An equivalent
martingale measure of the finite-state market (`HasEMM_multi_state`) is exactly a member of
`martingaleProbVectors z` charging every state. -/
theorem hasEMM_multi_state_iff_exists_pos_mem (z : Fin M → Fin N → ℝ) :
    HasEMM_multi_state z ↔ ∃ q ∈ martingaleProbVectors z, ∀ n, 0 < q n :=
  ⟨fun ⟨q, hpos, hsum, hfair⟩ ↦ ⟨q, ⟨fun n ↦ (hpos n).le, hsum, hfair⟩, hpos⟩,
   fun ⟨q, ⟨_, hsum, hfair⟩, hpos⟩ ↦ ⟨q, hpos, hsum, hfair⟩⟩

/-- **The law of one price.** Every martingale probability vector prices a replicable claim at its
replication cost: if `Yₙ = x + ∑ₘ θₘ zₘₙ` in every state, then `∑ qₙ Yₙ = x`. Both inequalities
are `emm_le_superReplication`: `(x, θ)` super-replicates `Y`, and `(−x, −θ)` super-replicates
`−Y`. -/
theorem martingalePrice_eq_of_replicates (z : Fin M → Fin N → ℝ) {Y : Fin N → ℝ}
    {q : Fin N → ℝ} (hq : q ∈ martingaleProbVectors z) {x : ℝ} {θ : Fin M → ℝ}
    (hrep : ∀ n, Y n = x + ∑ m, θ m * z m n) :
    ∑ n, q n * Y n = x := by
  have hneg : SuperReplicates z (-Y) (-x) (-θ) := fun n ↦ by
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hrep n, neg_add, le_refl]
  have hlow := emm_le_superReplication z (-Y) hq hneg
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff] at hlow
  exact le_antisymm (emm_le_superReplication z Y hq fun n ↦ (hrep n).le) hlow

/-- **Under no arbitrage the superhedging price is bounded below by an EMM price.** The
multi-state FTAP (`hasEMM_multi_of_not_hasArbitrage`) supplies an equivalent martingale measure
`q`, strictly positive and in `martingaleProbVectors z`; by `emm_le_superReplication` its price
`∑ qₙ Yₙ` of any claim `Y` is at most every super-replication cost of `Y`. So no claim can be
super-replicated arbitrarily cheaply. -/
theorem exists_pos_price_le_superReplication [NeZero N] (z : Fin M → Fin N → ℝ)
    (hNA : ¬ HasArbitrage_multi_state z) :
    ∃ q ∈ martingaleProbVectors z, (∀ n, 0 < q n) ∧
      ∀ (Y : Fin N → ℝ) (x : ℝ) (θ : Fin M → ℝ), SuperReplicates z Y x θ →
        ∑ n, q n * Y n ≤ x := by
  obtain ⟨q, hq, hpos⟩ :=
    (hasEMM_multi_state_iff_exists_pos_mem z).mp (hasEMM_multi_of_not_hasArbitrage z hNA)
  exact ⟨q, hq, hpos, fun Y _ _ hsr ↦ emm_le_superReplication z Y hq hsr⟩

end MathFin
