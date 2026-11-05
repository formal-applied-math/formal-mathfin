/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# The product of two standard simplices

`Convexity.StdSimplex R X` is the finitely supported probability distributions on `X`. Mathlib has
the monad structure (`StdSimplex.map`, `StdSimplex.join`) and no product of independent
distributions. `StdSimplex.prod p q` is the monadic bind of `p` against `x ↦ q.map (x, ·)`, so its
weights are nonnegative and sum to one by the monad's own proofs, and its weight at `(x, y)` is the
product `p x * q y` (`StdSimplex.weights_prod`).
-/

@[expose] public section

namespace Convexity.StdSimplex

variable {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {X Y : Type*}

/-- The **product distribution** of independent `p` on `X` and `q` on `Y`. -/
noncomputable def prod (p : StdSimplex R X) (q : StdSimplex R Y) : StdSimplex R (X × Y) :=
  (p.map fun x ↦ q.map (x, ·)).join

/-- The weight of the product distribution at `(x, y)` is `p x * q y`. -/
@[simp] theorem weights_prod (p : StdSimplex R X) (q : StdSimplex R Y) (x : X) (y : Y) :
    (p.prod q).weights (x, y) = p.weights x * q.weights y := by
  classical
  have key : ((p.weights.mapDomain fun x ↦ q.map (x, ·)).sum fun d r ↦ r • d.weights) =
      p.weights.sum fun x r ↦ r • (q.map (x, ·)).weights :=
    Finsupp.sum_mapDomain_index (fun _ ↦ zero_smul _ _) fun _ _ _ ↦ add_smul _ _ _
  rw [prod, weights_join, weights_map, key, Finsupp.sum_apply, Finsupp.sum_eq_single x]
  · simp [Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective x)]
  · intro x' _ hx'
    have hn : ((x, y) : X × Y) ∉ Set.range fun y' ↦ (x', y') := by
      rintro ⟨y', hy'⟩
      exact hx' (congrArg Prod.fst hy')
    simp [Finsupp.mapDomain_of_notMem_range _ _ hn]
  · intro _
    simp

end Convexity.StdSimplex
