/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The arbitrage pricing theory decomposition, exact factor model

PLACEHOLDER-DOCSTRING
-/

@[expose] public section

namespace MathFin

variable {ι κ : Type*}

/-- The **exact-factor no-arbitrage condition** on assets `i ∈ s` with prices `p`, payoffs `a`
and factor loadings `β` over factors `k ∈ t`: every portfolio `w` that costs nothing
(`∑ i ∈ s, w i * p i = 0`) and carries no factor exposure (`∑ i ∈ s, w i * β i k = 0` for every
`k ∈ t`) has zero expected payoff (`∑ i ∈ s, w i * a i = 0`). At unit prices `p = fun _ => 1`
this is the condition of Ross's arbitrage pricing theory: a portfolio orthogonal to the price
vector and to every loading column is orthogonal to the payoffs. -/
def ExactFactorNoArbitrage (s : Finset ι) (t : Finset κ) (p a : ι → ℝ) (β : ι → κ → ℝ) :
    Prop :=
  ∀ w : ι → ℝ, (∑ i ∈ s, w i * p i = 0) → (∀ k ∈ t, ∑ i ∈ s, w i * β i k = 0) →
    ∑ i ∈ s, w i * a i = 0

/-- The payoffs of the exact-factor model lie in the span of the price vector and the loading
columns: the finite-dimensional duality step of the arbitrage pricing theory. The hypothesis is
`ExactFactorNoArbitrage`: a portfolio orthogonal (in the pairing `∑ w i * f i` over `s`) to the
price vector and to every loading column is orthogonal to the payoffs, so the payoffs lie in the
double orthogonal of that span, which for the finite-dimensional space of portfolios on `s` is
the span itself. -/
private lemma exists_coeffs_of_exactFactorNoArbitrage {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {s : Finset ι} {t : Finset κ} {p a : ι → ℝ} {β : ι → κ → ℝ}
    (h : ExactFactorNoArbitrage s t p a β) :
    ∃ lam₀ : ℝ, ∃ lam : κ → ℝ, ∀ i ∈ s, a i = p i * lam₀ + ∑ k ∈ t, lam k * β i k := by
  classical
  -- the price vector and the loading columns, restricted to the assets in `s`
  set v : Option ↥t → EuclideanSpace ℝ ↥s := fun b =>
    Option.elim b (WithLp.toLp 2 fun i : ↥s => p ↑i) fun k =>
      WithLp.toLp 2 fun i : ↥s => β ↑i ↑k with hv
  set U : Submodule ℝ (EuclideanSpace ℝ ↥s) := Submodule.span ℝ (Set.range v) with hU
  have key : WithLp.toLp 2 (fun i : ↥s => a ↑i) ∈ U := by
    rw [← Submodule.orthogonal_orthogonal U]
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    have hinner : ∀ g : ι → ℝ,
        inner ℝ w (WithLp.toLp 2 fun i : ↥s => g ↑i) = ∑ i : ↥s, w.ofLp i * g ↑i := fun g => by
      simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    have hinner' : ∀ g : ι → ℝ,
        inner ℝ (WithLp.toLp 2 fun i : ↥s => g ↑i) w = ∑ i : ↥s, w.ofLp i * g ↑i := fun g => by
      simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    rw [hinner a]
    -- the generators of `U` give the zero-cost and zero-exposure conditions
    have hgen : ∀ b : Option ↥t, inner ℝ (v b) w = 0 := fun b =>
      hw (v b) (Submodule.subset_span (Set.mem_range_self b))
    -- extend `w` by zero outside `s`
    set w' : ι → ℝ := fun j => if hj : j ∈ s then w.ofLp ⟨j, hj⟩ else 0 with hw'
    have coeSum : ∀ f : ι → ℝ, ∑ i ∈ s, f i = ∑ i : ↥s, f ↑i := fun f =>
      (Finset.sum_coe_sort s f).symm
    have w'coe : ∀ i : ↥s, w' ↑i = w.ofLp i := fun i => by simp [hw', i.2]
    have hcost : ∑ i ∈ s, w' i * p i = 0 := by
      rw [coeSum (fun i => w' i * p i),
        Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset ↥s)) => by rw [w'coe i],
        ← hinner' p]
      exact hgen none
    have hexpo : ∀ k ∈ t, ∑ i ∈ s, w' i * β i k = 0 := by
      intro k hk
      rw [coeSum (fun i => w' i * β i k),
        Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset ↥s)) => by rw [w'coe i],
        ← hinner' (fun j => β j k)]
      exact hgen (some ⟨k, hk⟩)
    have hna := h w' hcost hexpo
    rw [coeSum (fun i => w' i * a i),
      Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset ↥s)) => by rw [w'coe i]] at hna
    exact hna
  rw [Submodule.mem_span_range_iff_exists_fun ℝ] at key
  obtain ⟨c, hc⟩ := key
  set lam : κ → ℝ := fun k => if hk : k ∈ t then c (some ⟨k, hk⟩) else 0 with hlam
  refine ⟨c none, lam, fun i hi => ?_⟩
  have hcoord : (∑ b, c b • v b).ofLp ⟨i, hi⟩ = a ↑i := by
    rw [hc]
  have hcoord' : (∑ b, c b • v b).ofLp ⟨i, hi⟩
      = c none * p ↑i + ∑ k : ↥t, c (some k) * β ↑i ↑k := by
    simp [hv]
  have hlamcoe : ∀ k : ↥t, lam ↑k = c (some k) := fun k => by simp [hlam, k.2]
  have coeSumT : ∀ g : κ → ℝ, ∑ k ∈ t, g k = ∑ k : ↥t, g ↑k := fun g =>
    (Finset.sum_coe_sort t g).symm
  rw [← hcoord, hcoord', mul_comm (p ↑i) (c none), coeSumT (fun k => lam k * β ↑i k),
    Finset.sum_congr rfl fun k (_ : k ∈ (Finset.univ : Finset ↥t)) => by rw [← hlamcoe k]]

end MathFin
