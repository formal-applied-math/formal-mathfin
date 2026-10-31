/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.MartingaleTransform

/-!
# Binomial martingale representation (completeness of the binomial market)

On the binomial tree — coin-flip paths `ω : ℕ → Bool`, with the **risk-neutral one-step
condition** `q·X_{n+1}(…,U) + (1 − q)·X_{n+1}(…,D) = X_n` (the explicit form of the conditional
expectation w.r.t. the binomial filtration) — every martingale `M` is the discrete stochastic
integral of a **predictable** strategy `H` against the discounted asset `S`:

  `M_N = M_0 + (A · S)_N` (`binomial_martingale_representation`),

where `(A · S)_N(ω) = ∑_{k<N} A_{k+1}(ω)·(S_{k+1}(ω) − S_k(ω))` is the library's
`martingaleTransform` and `A_{k+1}` is the holding over `(k, k+1]`, fixed by the first `k` flips.

This is the **martingale representation theorem** in discrete time — the second pillar of the
fundamental theorem of asset pricing (completeness: every contingent claim is replicable). The
hedge ratio is the node-wise *delta* `H_n = ΔM_{n+1} / ΔS_{n+1}` (the change in `M` over the
change in `S` across the two children of a node); it is predictable because it is fixed *before*
the `(n+1)`-th flip is revealed.

The argument is purely algebraic and pathwise — no measure theory. The one-step identity
(`repr_one_step`) is the node-wise delta hedge, and the multi-period form telescopes. It is the
converse of `martingaleTransform_isMartingale` (`Foundations/MartingaleTransform.lean`): there a
predictable bounded `A` turns a martingale into a martingale; here every martingale of the tree is
such a transform of the discounted spot.
-/

@[expose] public section

namespace MathFin

/-- A real function of an infinite coin-flip path is **`n`-adapted** when it depends only on the
first `n` flips `ω 0, …, ω (n−1)`. -/
def PathAdaptedAt (n : ℕ) (X : (ℕ → Bool) → ℝ) : Prop :=
  ∀ ω ω' : ℕ → Bool, (∀ i, i < n → ω i = ω' i) → X ω = X ω'

/-- Fixing the `n`-th flip of a function of the first `n + 1` flips leaves a function of the
first `n`. -/
lemma PathAdaptedAt.fixFlip {n : ℕ} {f : (ℕ → Bool) → ℝ} (hf : PathAdaptedAt (n + 1) f)
    (b : Bool) :
    PathAdaptedAt n fun ω ↦ f (Function.update ω n b) := fun ω ω' h ↦
  hf _ _ fun i hi ↦ by
    rcases eq_or_ne i n with rfl | hin
    · simp
    · rw [Function.update_of_ne hin, Function.update_of_ne hin]
      exact h i (by omega)

variable {q : ℝ} {M S : ℕ → (ℕ → Bool) → ℝ}

/-- The **node-wise hedge ratio** (discrete delta): the change in `M` over the change in `S`
across the up/down children of the level-`n` node carrying path `ω`. -/
noncomputable def hedgeRatio (M S : ℕ → (ℕ → Bool) → ℝ) (n : ℕ) (ω : ℕ → Bool) : ℝ :=
  (M (n + 1) (Function.update ω n true) - M (n + 1) (Function.update ω n false)) /
    (S (n + 1) (Function.update ω n true) - S (n + 1) (Function.update ω n false))

/-- **One-step representation (the node-wise delta hedge).** Under the risk-neutral one-step
condition for `M` and `S` and non-degeneracy of `S`'s branching, the one-period change in `M`
equals the hedge ratio times the one-period change in `S`, on every path. -/
theorem repr_one_step
    (hM_mart : ∀ n ω, q * M (n + 1) (Function.update ω n true)
        + (1 - q) * M (n + 1) (Function.update ω n false) = M n ω)
    (hS_mart : ∀ n ω, q * S (n + 1) (Function.update ω n true)
        + (1 - q) * S (n + 1) (Function.update ω n false) = S n ω)
    (hS_nondeg : ∀ n ω, S (n + 1) (Function.update ω n true)
        ≠ S (n + 1) (Function.update ω n false))
    (n : ℕ) (ω : ℕ → Bool) :
    M (n + 1) ω - M n ω = hedgeRatio M S n ω * (S (n + 1) ω - S n ω) := by
  have hne : S (n + 1) (Function.update ω n true) - S (n + 1) (Function.update ω n false) ≠ 0 :=
    sub_ne_zero.mpr (hS_nondeg n ω)
  rw [hedgeRatio, ← hM_mart n ω, ← hS_mart n ω]
  by_cases hb : ω n = true
  · have hωeq : Function.update ω n true = ω := by
      conv_rhs => rw [← Function.update_eq_self n ω]
      rw [hb]
    rw [hωeq] at hne ⊢
    field_simp
    ring
  · have hbf : ω n = false := by simpa using hb
    have hωeq : Function.update ω n false = ω := by
      conv_rhs => rw [← Function.update_eq_self n ω]
      rw [hbf]
    rw [hωeq] at hne ⊢
    field_simp
    ring

/-- **Binomial martingale representation theorem.** Under the risk-neutral one-step condition,
every martingale `M` is its initial value plus the `martingaleTransform` of a predictable hedge `A`
against the discounted asset `S`: `M_N = M_0 + ∑_{k<N} A_{k+1}·(S_{k+1} − S_k)`. The holding
`A_{k+1}` over `(k, k+1]` depends only on the first `k` flips; it is the node-wise delta
`hedgeRatio M S k`. The binomial market is complete: every claim is replicable by a self-financing
strategy. -/
theorem binomial_martingale_representation
    (hM_adapt : ∀ n, PathAdaptedAt n (M n)) (hS_adapt : ∀ n, PathAdaptedAt n (S n))
    (hM_mart : ∀ n ω, q * M (n + 1) (Function.update ω n true)
        + (1 - q) * M (n + 1) (Function.update ω n false) = M n ω)
    (hS_mart : ∀ n ω, q * S (n + 1) (Function.update ω n true)
        + (1 - q) * S (n + 1) (Function.update ω n false) = S n ω)
    (hS_nondeg : ∀ n ω, S (n + 1) (Function.update ω n true)
        ≠ S (n + 1) (Function.update ω n false)) :
    ∃ A : ℕ → (ℕ → Bool) → ℝ, (∀ n, PathAdaptedAt n (A (n + 1))) ∧
      ∀ N ω, M N ω = M 0 ω + martingaleTransform A S N ω := by
  refine ⟨fun n ↦ hedgeRatio M S (n - 1), ?_, ?_⟩
  · -- predictability: the hedge ratio depends only on the first `n` flips
    intro n ω ω' hω
    have key (b : Bool) :
        M (n + 1) (Function.update ω n b) = M (n + 1) (Function.update ω' n b) ∧
        S (n + 1) (Function.update ω n b) = S (n + 1) (Function.update ω' n b) :=
      ⟨(hM_adapt (n + 1)).fixFlip b ω ω' hω, (hS_adapt (n + 1)).fixFlip b ω ω' hω⟩
    simp only [hedgeRatio, Nat.add_sub_cancel]
    rw [(key true).1, (key true).2, (key false).1, (key false).2]
  · -- the representation telescopes from the one-step identity
    intro N ω
    induction N with
    | zero => simp
    | succ N ih =>
      rw [martingaleTransform_real] at ih ⊢
      rw [Finset.sum_range_succ, ← add_assoc, ← ih, Nat.add_sub_cancel,
          ← repr_one_step hM_mart hS_mart hS_nondeg N ω]
      ring

end MathFin
