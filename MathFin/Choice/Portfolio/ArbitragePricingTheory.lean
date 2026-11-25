/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Init
public import MathFin.Pricing.Market
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The arbitrage pricing theory decomposition, exact factor model

PLACEHOLDER-DOCSTRING
-/

@[expose] public section

namespace MathFin

open MeasureTheory
open scoped NNReal

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

/-- **The arbitrage pricing theory decomposition** (Ross 1976, exact factor model). If every
portfolio on the assets `s` that costs nothing (the assets are priced at one) and carries no
factor exposure has zero expected payoff, the expected payoffs are affine in the loadings:
there are a premium `lam₀` and factor premia `lam k` with `a i = lam₀ + ∑ k ∈ t, lam k * β i k`
for every asset `i ∈ s`. The hypothesis is the exact-factor no-arbitrage condition
(`ExactFactorNoArbitrage`) at unit prices: a portfolio orthogonal to the price vector and to
every loading column is orthogonal to the payoffs. The premia are not unique unless the
columns are independent; when an asset `i₀ ∈ s` has zero loadings, `lam₀` is its payoff,
the risk-free return of the market (`lam0_eq_of_zeroLoadingAsset`). -/
theorem exists_premia_of_exactFactorNoArbitrage {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {s : Finset ι} {t : Finset κ} {a : ι → ℝ} {β : ι → κ → ℝ}
    (h : ExactFactorNoArbitrage s t (fun _ => 1) a β) :
    ∃ lam₀ : ℝ, ∃ lam : κ → ℝ, ∀ i ∈ s, a i = lam₀ + ∑ k ∈ t, lam k * β i k := by
  obtain ⟨lam₀, lam, hlam⟩ := exists_coeffs_of_exactFactorNoArbitrage h
  exact ⟨lam₀, lam, fun i hi => by rw [hlam i hi, one_mul]⟩

/-- **A pricing measure delivers the exact-factor no-arbitrage condition.** In a market whose
assets `i ∈ s` pay `a i + ∑ k ∈ t, β i k * F k` at `T`, with a deterministic numéraire and a
pricing measure `Q` up to `T`, every portfolio that costs nothing at the prices
`M.price Q (.pay T (.obs i T))` and carries no factor exposure has zero expected
payoff: the cost is the discounted expected payoff by the martingale property, the factor
terms cancel by the zero-exposure condition, and the deflator is the positive constant
`f 0 / f T`. This is the no-arbitrage step of the arbitrage pricing theory in the library's
pricing vocabulary: a pricing measure certifies the condition that
`exists_premia_of_isPricingMeasure` consumes. -/
theorem exactFactorNoArbitrage_of_pricingMeasure
    {ι κ Ω : Type*} [DecidableEq ι] [DecidableEq κ] [MeasurableSpace Ω] [Nonempty Ω]
    {M : MathFin.Market ι Ω} {T : ℝ≥0} {Q : Measure Ω} (hQ : M.IsPricingMeasure T Q)
    (f : ℝ≥0 → ℝ) (hN : ∀ τ ω, M.numeraire τ ω = f τ)
    {s : Finset ι} {t : Finset κ} {a : ι → ℝ} {β : ι → κ → ℝ} {F : κ → Ω → ℝ}
    (hR : ∀ i ∈ s, ∀ ω, M.asset i T ω = a i + ∑ k ∈ t, β i k * F k ω) :
    ExactFactorNoArbitrage s t (fun i => M.price Q (.pay T (.obs i T))) a β := by
  have hD : ∀ τ ω, M.deflator τ ω = f 0 / f τ := fun τ ω => Market.deflator_of_numeraire hN τ ω
  have hfpos : ∀ τ, 0 < f τ := fun τ => by
    simpa [hN τ] using M.numeraire_pos τ (Classical.arbitrary Ω)
  -- the deflated payoff `D T * R i` is integrable for every asset
  have hint : ∀ i ∈ s, Integrable (fun ω => M.deflator T ω * M.asset i T ω) Q := by
    intro i _
    have hd := (hQ.martingale i).integrable T
    have hd' : Integrable (fun ω => M.deflated i T ω) Q := by
      refine hd.congr ?_
      exact MeasureTheory.ae_of_all _ fun ω => by rw [min_eq_left (le_refl T)]
    have hdet : (fun ω => M.deflator T ω * M.asset i T ω)
        = fun ω => f 0 * M.deflated i T ω := by
      funext ω
      rw [hD T ω, Market.deflated, hN T ω]
      field_simp
    rw [hdet]
    simpa only [smul_eq_mul] using Integrable.const_mul hd' (f 0)
  intro w hw_cost hw_expo
  -- the price of each claim is the integral of the deflated payoff
  have hprice : ∀ i ∈ s, M.price Q (.pay T (.obs i T))
      = ∫ ω, M.deflator T ω * M.asset i T ω ∂Q := fun i _ =>
    Contracts.Contract.value_pay Q M.deflator M.asset T (.obs i T)
  -- the factor terms cancel by the zero-exposure condition
  have hfactor : ∀ ω, ∑ i ∈ s, w i * M.asset i T ω = ∑ i ∈ s, w i * a i := by
    intro ω
    have h1 : ∑ i ∈ s, w i * M.asset i T ω
        = ∑ i ∈ s, (w i * a i + w i * ∑ k ∈ t, β i k * F k ω) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hR i hi ω, mul_add]
    rw [h1, Finset.sum_add_distrib]
    have h2 : ∑ i ∈ s, w i * ∑ k ∈ t, β i k * F k ω
        = ∑ i ∈ s, ∑ k ∈ t, w i * (β i k * F k ω) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    have h3 : ∑ i ∈ s, ∑ k ∈ t, w i * (β i k * F k ω)
        = ∑ k ∈ t, ∑ i ∈ s, w i * (β i k * F k ω) := by
      rw [Finset.sum_comm]
    have h4 : ∑ k ∈ t, ∑ i ∈ s, w i * (β i k * F k ω) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hsw : ∑ i ∈ s, w i * (β i k * F k ω) = F k ω * ∑ i ∈ s, w i * β i k := by
        refine Eq.symm ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsw, hw_expo k hk, mul_zero]
    rw [h2, h3, h4, add_zero]
  have hpoint : ∀ ω : Ω, ∑ i ∈ s, w i * (M.deflator T ω * M.asset i T ω)
      = M.deflator T ω * ∑ i ∈ s, w i * M.asset i T ω := by
    intro ω
    refine Eq.symm ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hfs : ∀ i ∈ s, Integrable (fun ω => w i * (M.deflator T ω * M.asset i T ω)) Q := by
    intro i hi
    simpa only [smul_eq_mul] using (hint i hi).const_mul (w i)
  have hsplit : ∫ (a : Ω), ∑ i ∈ s, w i * (M.deflator T a * M.asset i T a) ∂Q
      = ∑ i ∈ s, ∫ (a : Ω), w i * (M.deflator T a * M.asset i T a) ∂Q :=
    MeasureTheory.integral_finsetSum s hfs
  have hterms : ∀ i ∈ s, ∫ (a : Ω), w i * (M.deflator T a * M.asset i T a) ∂Q
      = w i * M.price Q (.pay T (.obs i T)) := by
    intro i hi
    rw [hprice i hi, ← integral_const_mul (w i) (fun a => M.deflator T a * M.asset i T a)]
  have hinteg : ∫ ω, M.deflator T ω * (∑ i ∈ s, w i * M.asset i T ω) ∂Q = 0 := by
    rw [← integral_congr_ae (MeasureTheory.ae_of_all _ hpoint), hsplit,
      Finset.sum_congr rfl hterms]
    exact hw_cost
  have : IsProbabilityMeasure Q := hQ.isProb
  have hval : ∫ ω, M.deflator T ω * (∑ i ∈ s, w i * M.asset i T ω) ∂Q
      = f 0 / f T * ∑ i ∈ s, w i * a i := by
    rw [integral_congr_ae (MeasureTheory.ae_of_all Q fun ω => by rw [hfactor ω]),
      integral_mul_const,
      integral_congr_ae (MeasureTheory.ae_of_all Q fun ω => by rw [hD T ω]),
      integral_const, smul_eq_mul, probReal_univ, one_mul]
  have hfne : f 0 / f T ≠ 0 := div_ne_zero (hfpos 0).ne' (hfpos T).ne'
  exact (mul_eq_zero.mp (by rw [← hval]; exact hinteg)).resolve_left hfne

end MathFin
