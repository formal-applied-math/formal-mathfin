/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

/-!
# Mixtures of standard simplices

The library's probability vector on a finite type `ι` is Mathlib's `Convexity.StdSimplex ℝ ι`:
nonnegative weights summing to one. This file adds the one operation on it that the finance
developments reach for, the **mixture** `mix α p q = α p + (1 - α) q` of two probability vectors
at a weight `α ∈ [0, 1]`, and its algebra. `mix` is Mathlib's binary convex combination
`Convexity.convexCombPair` for the convex space structure `ConvexSpace ℝ (StdSimplex ℝ ι)`
(`StdSimplex.join`), with the weights `α` and `1 - α` fixed, so a mixture of probability vectors
is a probability vector by construction and nothing has to be checked.

The weight carries its two bounds as arguments, as in `convexCombPair`; the identities
(`mix_compound`, `mix_mix_right`, `mix_mix_mix`) state the resulting weight by an equation, so
that no rewrite has to go through a term that a proof depends on.

## Main definitions

* `Convexity.StdSimplex.mix`: the mixture `α p + (1 - α) q` of two probability vectors.

## Main results

* `Convexity.StdSimplex.weights_mix_apply`: the weights of `mix α p q` are
  `α * p.weights i + (1 - α) * q.weights i`.
* `Convexity.StdSimplex.mix_one`, `mix_zero`, `mix_self`, `mix_comm`, `mix_compound`: the algebra
  of mixtures, including the reduction of compound lotteries.
* `Convexity.StdSimplex.mem_of_mix_closed`: a set of probability vectors on a finite type that
  contains the point masses and is closed under mixtures is everything (the simplex is the convex
  hull of its vertices).
* `Convexity.StdSimplex.exists_weights_eq_iff`: a function on a finite type is the weight
  function of a probability vector exactly when it is nonnegative and sums to one, the bridge to
  the predicate form `(∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1`.

## Tags

standard simplex, probability vector, mixture, convex combination, compound lottery,
finitely supported probability, MSC 60E05
-/

@[expose] public section

namespace Convexity.StdSimplex

variable {ι : Type*}

/-- The **mixture** `α p + (1 - α) q` of two probability vectors at a weight `α ∈ [0, 1]`: with
probability `α` you face `p`, otherwise `q`. It is `convexCombPair` for the convex space
`StdSimplex ℝ ι`. -/
noncomputable def mix (α : ℝ) (h₀ : 0 ≤ α) (h₁ : α ≤ 1) (p q : StdSimplex ℝ ι) :
    StdSimplex ℝ ι :=
  convexCombPair α (1 - α) h₀ (sub_nonneg.2 h₁) (by ring) p q

/-- The weight of a mixture at `i` is the mixture of the weights. -/
@[simp] theorem weights_mix_apply (α : ℝ) (h₀ : 0 ≤ α) (h₁ : α ≤ 1) (p q : StdSimplex ℝ ι)
    (i : ι) :
    (mix α h₀ h₁ p q).weights i = α * p.weights i + (1 - α) * q.weights i := by
  simp [mix]

/-- The weight function of a mixture, as a function on `ι`. -/
theorem coe_weights_mix (α : ℝ) (h₀ : 0 ≤ α) (h₁ : α ≤ 1) (p q : StdSimplex ℝ ι) :
    ⇑(mix α h₀ h₁ p q).weights = α • ⇑p.weights + (1 - α) • ⇑q.weights := by
  funext i
  simp

/-- Mixing with certainty on the first vector returns it. -/
theorem mix_one {h₀ : (0 : ℝ) ≤ 1} {h₁ : (1 : ℝ) ≤ 1} (p q : StdSimplex ℝ ι) :
    mix 1 h₀ h₁ p q = p := by
  ext i
  simp only [weights_mix_apply]
  ring

/-- Mixing with certainty on the second vector returns it. -/
theorem mix_zero {h₀ : (0 : ℝ) ≤ 0} {h₁ : (0 : ℝ) ≤ 1} (p q : StdSimplex ℝ ι) :
    mix 0 h₀ h₁ p q = q := by
  ext i
  simp only [weights_mix_apply]
  ring

/-- Mixing a vector with itself is a no-op, at any weight. -/
theorem mix_self {α : ℝ} {h₀ : 0 ≤ α} {h₁ : α ≤ 1} (p : StdSimplex ℝ ι) :
    mix α h₀ h₁ p p = p := by
  ext i
  simp only [weights_mix_apply]
  ring

/-- Swapping the two vectors complements the weight. -/
theorem mix_comm {α : ℝ} (h₀ : 0 ≤ α) (h₁ : α ≤ 1) (p q : StdSimplex ℝ ι) :
    mix α h₀ h₁ p q = mix (1 - α) (sub_nonneg.2 h₁) (sub_le_self 1 h₀) q p := by
  ext i
  simp only [weights_mix_apply]
  ring

/-- **Reduction of compound lotteries**: mixing `q` into a mixture of `p` and `q` just rescales
the weight on `p`, `α β = γ`. The formal content of the "only the resulting distribution matters"
assumption. -/
theorem mix_compound {α β γ : ℝ} {hα₀ : 0 ≤ α} {hα₁ : α ≤ 1} {hβ₀ : 0 ≤ β} {hβ₁ : β ≤ 1}
    (hγ : α * β = γ) (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) {p q : StdSimplex ℝ ι} :
    mix α hα₀ hα₁ (mix β hβ₀ hβ₁ p q) q = mix γ hγ₀ hγ₁ p q := by
  subst hγ
  ext i
  simp only [weights_mix_apply]
  ring

/-- Mixing `b` into a mixture of `b` and `w` is a mixture of `b` and `w`, at the weight
`c = β + (1 - β) a`. -/
theorem mix_mix_right {β a c : ℝ} {hβ₀ : 0 ≤ β} {hβ₁ : β ≤ 1} {ha₀ : 0 ≤ a} {ha₁ : a ≤ 1}
    (hc : β + (1 - β) * a = c) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {b w : StdSimplex ℝ ι} :
    mix β hβ₀ hβ₁ b (mix a ha₀ ha₁ b w) = mix c hc₀ hc₁ b w := by
  subst hc
  ext i
  simp only [weights_mix_apply]
  ring

/-- A mixture of two mixtures of `b` and `w` is a mixture of `b` and `w`, at the weight
`d = γ a + (1 - γ) c`. -/
theorem mix_mix_mix {γ a c d : ℝ} {hγ₀ : 0 ≤ γ} {hγ₁ : γ ≤ 1} {ha₀ : 0 ≤ a} {ha₁ : a ≤ 1}
    {hc₀ : 0 ≤ c} {hc₁ : c ≤ 1} (hd : γ * a + (1 - γ) * c = d) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1)
    {b w : StdSimplex ℝ ι} :
    mix γ hγ₀ hγ₁ (mix a ha₀ ha₁ b w) (mix c hc₀ hc₁ b w) = mix d hd₀ hd₁ b w := by
  subst hd
  ext i
  simp only [weights_mix_apply]
  ring

/-- **The simplex is generated by its vertices under mixing**: a set of probability vectors on a
finite type that contains every point mass and is closed under mixtures contains every
probability vector. -/
theorem mem_of_mix_closed [Fintype ι] {S : Set (StdSimplex ℝ ι)}
    (hS : ∀ p ∈ S, ∀ q ∈ S, ∀ (α : ℝ) (h₀ : 0 ≤ α) (h₁ : α ≤ 1), mix α h₀ h₁ p q ∈ S)
    (hδ : ∀ o, single o ∈ S) (p : StdSimplex ℝ ι) : p ∈ S := by
  classical
  have hconv : Convex ℝ ((fun p : StdSimplex ℝ ι ↦ ⇑p.weights) '' S) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
    obtain rfl : b = 1 - a := by linarith
    refine ⟨mix a ha (by linarith) x y, hS x hx y hy a ha (by linarith), ?_⟩
    funext i
    simp
  obtain ⟨q, hq, hqp⟩ := hconv.sum_mem (t := Finset.univ) (w := ⇑p.weights)
    (z := fun i ↦ ⇑(single i : StdSimplex ℝ ι).weights) (fun i _ ↦ p.weights_nonneg i)
    p.total_of_fintype (fun i _ ↦ ⟨single i, hδ i, rfl⟩)
  have hqp' : q = p := by
    ext j
    have := congrFun hqp j
    simpa [Finset.sum_apply, Finsupp.single_apply] using this
  rwa [← hqp']

/-- **Probability vectors are the nonnegative functions summing to one**: a function `q` on a finite
type is the weight function of a point of the standard simplex exactly when it is nonnegative and
sums to one. -/
theorem exists_weights_eq_iff [Fintype ι] {q : ι → ℝ} :
    (∃ p : StdSimplex ℝ ι, ⇑p.weights = q) ↔ (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 := by
  have h := Set.ext_iff.1 (range_toFun_comp_weights (R := ℝ) (X := ι)) q
  simpa [Set.mem_iInter] using h

end Convexity.StdSimplex
