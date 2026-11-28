/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Convex order

A law `μ` on `ℝ` is below `ν` in **convex order**, `μ ≤cx ν`, when `∫ φ dμ ≤ ∫ φ dν` for every
convex `φ`. Spreading mass out (a mean-preserving spread) moves a law up. The order compares
risk at a fixed mean: the identity and its negative are convex, so ordered laws with a first
moment have the same mean. Martingale couplings, peacocks and the best-case aggregation of risks
are stated in it.

The definition quantifies over the convex `φ` integrable under both laws. The results below use
three families of convex functions: the identity, the calls `(x − K)⁺` and the puts `(K − x)⁺`.
A call with price zero under `ν` pins `ν` below its strike, so convex order passes bounds on the
support down: when the calls and puts at the bounds are integrable under both laws, `μ ≤cx ν`
lives inside every interval `ν` lives in.

## Main definitions

* `ConvexOrder μ ν`: `∫ φ dμ ≤ ∫ φ dν` for every convex `φ` integrable under both.

## Main results

* `ConvexOrder.refl`: every law is below itself.
* `ConvexOrder.dirac_integral_le`: the point mass at the mean is below the law (Jensen's
  inequality). It is the smallest law with that mean.
* `ConvexOrder.integral_id_eq`: ordered laws with a first moment have the same mean.
* `ConvexOrder.integral_call_le`, `ConvexOrder.integral_put_le`: ordered laws have ordered call
  and put prices at every strike.
* `ConvexOrder.ae_le_of_ae_le`, `ConvexOrder.ae_ge_of_ae_ge`: if `ν` lives below (above) `t`, so
  does every `μ ≤cx ν`.
* `convexOn_call_payoff_spot`, `convexOn_call_payoff`: the call payoff `max(S − K, 0)` is convex
  in the spot and in the strike; the second, read in the spot, is the put payoff.
* `integrable_of_ae_mem_Icc`: a continuous function is integrable against a finite law on a
  compact interval, which supplies the integrability hypotheses for laws of bounded support.

## References

* [M. Shaked and J. G. Shanthikumar, *Stochastic Orders*][ShakedShanthikumar2007], Ch. 3
* [C. Bernard, X. Jiang and R. Wang, *Risk aggregation with dependence
  uncertainty*][BernardJiangWang2014]

## Tags

convex order, stochastic order, mean-preserving spread, stop-loss order, call prices, risk
aggregation, MSC 60E15, MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory Set

/-- **Convex order**: `μ ≤cx ν` when `∫ φ dμ ≤ ∫ φ dν` for every convex `φ : ℝ → ℝ`
integrable under both laws. -/
def ConvexOrder (μ ν : Measure ℝ) : Prop :=
  ∀ ⦃φ : ℝ → ℝ⦄, ConvexOn ℝ univ φ → Integrable φ μ → Integrable φ ν →
    ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂ν

/-- A continuous function is integrable against a finite law that lives on `[a, b]`. -/
lemma integrable_of_ae_mem_Icc {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Continuous f) {a b : ℝ} (h : ∀ᵐ x ∂μ, x ∈ Icc a b) : Integrable f μ := by
  have := hf.integrableOn_Icc (μ := μ) (a := a) (b := b)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem h] at this

/-- **Call payoff is convex in the spot**: `S ↦ max(S − K, 0)` is the positive part of an affine
function. -/
lemma convexOn_call_payoff_spot (K : ℝ) : ConvexOn ℝ univ fun S : ℝ ↦ max (S - K) 0 :=
  ((convexOn_id convex_univ).sub (concaveOn_const K convex_univ)).sup
    (convexOn_const 0 convex_univ)

/-- **Call payoff is convex in the strike**: `K ↦ max(S − K, 0)` is convex. Read in the spot, it
is the put payoff `x ↦ (S − x)⁺`.

This is the structural spine of static option-price no-arbitrage relations. Butterfly
non-negativity and Breeden–Litzenberger PDF positivity are discrete and infinitesimal
consequences (respectively) of this single fact, after passing through risk-neutral
expectation. -/
lemma convexOn_call_payoff (S : ℝ) : ConvexOn ℝ univ fun K : ℝ ↦ max (S - K) 0 :=
  ((convexOn_const S convex_univ).sub (concaveOn_id convex_univ)).sup
    (convexOn_const 0 convex_univ)

variable {μ ν : Measure ℝ}

namespace ConvexOrder

lemma refl (μ : Measure ℝ) : ConvexOrder μ μ := fun _ _ _ _ ↦ le_rfl

/-- **Jensen's inequality, in convex order**: the point mass at the mean of a law is below the
law. A convex function is continuous on `ℝ`, so `ConvexOn.map_integral_le` applies. -/
lemma dirac_integral_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : Integrable id ν) :
    ConvexOrder (Measure.dirac (∫ x, x ∂ν)) ν := by
  intro φ hφ _ hφν
  rw [integral_dirac]
  exact hφ.map_integral_le (by simpa using hφ.continuousOn_interior) isClosed_univ
    (ae_of_all _ fun _ ↦ mem_univ _) hν hφν

/-- **Ordered laws have equal means.** The identity and its negative are both convex. -/
lemma integral_id_eq (h : ConvexOrder μ ν) (hμ : Integrable id μ) (hν : Integrable id ν) :
    ∫ x, x ∂μ = ∫ x, x ∂ν := by
  refine le_antisymm (h (convexOn_id convex_univ) hμ hν) ?_
  have := h (concaveOn_id convex_univ).neg hμ.neg hν.neg
  simp only [Pi.neg_apply, id_eq] at this
  rw [integral_neg, integral_neg, neg_le_neg_iff] at this
  exact this

/-- **Ordered laws have ordered call prices**: `∫ (x − K)⁺ dμ ≤ ∫ (x − K)⁺ dν`. -/
lemma integral_call_le (h : ConvexOrder μ ν) (K : ℝ)
    (hμ : Integrable (fun x ↦ max (x - K) 0) μ) (hν : Integrable (fun x ↦ max (x - K) 0) ν) :
    ∫ x, max (x - K) 0 ∂μ ≤ ∫ x, max (x - K) 0 ∂ν :=
  h (convexOn_call_payoff_spot K) hμ hν

/-- **Ordered laws have ordered put prices**: `∫ (K − x)⁺ dμ ≤ ∫ (K − x)⁺ dν`. -/
lemma integral_put_le (h : ConvexOrder μ ν) (K : ℝ)
    (hμ : Integrable (fun x ↦ max (K - x) 0) μ) (hν : Integrable (fun x ↦ max (K - x) 0) ν) :
    ∫ x, max (K - x) 0 ∂μ ≤ ∫ x, max (K - x) 0 ∂ν :=
  h (convexOn_call_payoff K) hμ hν

/-- **Convex order passes an upper bound of the support down.** If `ν` lives on `(-∞, t]`, the
call struck at `t` is worth nothing under `ν`, hence under `μ ≤cx ν`, so `μ` lives there too. -/
lemma ae_le_of_ae_le (h : ConvexOrder μ ν) {t : ℝ}
    (hμ : Integrable (fun x ↦ max (x - t) 0) μ) (hν : Integrable (fun x ↦ max (x - t) 0) ν)
    (ht : ∀ᵐ x ∂ν, x ≤ t) : ∀ᵐ x ∂μ, x ≤ t := by
  have h0 : ∫ x, max (x - t) 0 ∂ν = 0 :=
    integral_eq_zero_of_ae (ht.mono fun x hx ↦ max_eq_right (sub_nonpos.2 hx))
  have hμ0 : ∫ x, max (x - t) 0 ∂μ = 0 :=
    le_antisymm ((h.integral_call_le t hμ hν).trans_eq h0)
      (integral_nonneg fun _ ↦ le_max_right _ _)
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _ ↦ le_max_right _ _) hμ).1 hμ0]
    with x hx
  exact sub_nonpos.1 (max_eq_right_iff.1 hx)

/-- **Convex order passes a lower bound of the support down**, through the put struck at `t`. -/
lemma ae_ge_of_ae_ge (h : ConvexOrder μ ν) {t : ℝ}
    (hμ : Integrable (fun x ↦ max (t - x) 0) μ) (hν : Integrable (fun x ↦ max (t - x) 0) ν)
    (ht : ∀ᵐ x ∂ν, t ≤ x) : ∀ᵐ x ∂μ, t ≤ x := by
  have h0 : ∫ x, max (t - x) 0 ∂ν = 0 :=
    integral_eq_zero_of_ae (ht.mono fun x hx ↦ max_eq_right (sub_nonpos.2 hx))
  have hμ0 : ∫ x, max (t - x) 0 ∂μ = 0 :=
    le_antisymm ((h.integral_put_le t hμ hν).trans_eq h0)
      (integral_nonneg fun _ ↦ le_max_right _ _)
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _ ↦ le_max_right _ _) hμ).1 hμ0]
    with x hx
  exact sub_nonpos.1 (max_eq_right_iff.1 hx)

end ConvexOrder

end MathFin
