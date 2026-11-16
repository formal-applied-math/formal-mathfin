/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.Binomial.Market
public import MathFin.Models.Binomial.BarrierReflection
public import MathFin.Contracts.Instruments.Options

/-!
# The binomial market prices the up-and-in knock-in by reflection

`Models/Binomial/BarrierReflection.lean` prices an up-and-in claim on the symmetric ±1 walk by
André's reflection: `E[g(Sₙ); max ≥ a] = E[g(Sₙ); Sₙ ≥ a] + E[g(2a − Sₙ); Sₙ > a]`. This file
reads that walk as the log-spot of the binomial market (`Models/Binomial/Market.lean`) with
`d = u⁻¹`, where the spot after `k` steps is `S₀ u^{Wₖ}` (`spotPath_inv_eq_zpow`), and the claim as
a contract of the payoff language, the discretely monitored knock-in `upAndIn` with barrier
`S₀ uᵃ` watched at every step. Its market price under the symmetric coin flips is the reflection
formula, and when the risk-neutral up-probability `crrUpProb u u⁻¹ ρ` is `1/2` the symmetric coin
flips are a pricing measure of the market.

## Main results

* `spotPath_inv_eq_zpow`: with `d = u⁻¹` the spot after `k ≤ n` steps is `S₀ u^{Wₖ}`, `W` the ±1
  walk of the first `n` flips.
* `exists_le_spotPath_iff`: the spot reaches `S₀ uᵃ` at a step `k ≤ n` exactly when the walk hits
  `a`.
* `price_upAndIn_market`: for `u > 1`, `S₀ > 0`, a step `h > 0`, a barrier `S₀ uᵃ` with `a > 0`
  watched at the `n + 1` grid dates, and a payoff `f` that reads the spot only at `T = nh`, the
  symmetric coin flips are a pricing measure when `crrUpProb u u⁻¹ ρ = 1/2`, and the market price
  of `upAndIn` is `e^{−ρn}(E[g(Wₙ); Wₙ ≥ a] + E[g(2a − Wₙ); Wₙ > a])`, `g j` the payoff at the
  spot `S₀ uʲ`.

## References

* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]
* [André (1887)][Andre1887]

## Tags

barrier option, up-and-in, knock-in, reflection principle, binomial market, running maximum,
MSC 91G20, MSC 60G50, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts.Binomial

variable {n : ℕ} {u ρ h S₀ : ℝ}

/-- **The spot of the recombining tree with `d = u⁻¹` is `S₀ u^{Wₖ}`**, `W` the ±1 walk of the
first `n` flips, at every step `k ≤ n`. -/
theorem spotPath_inv_eq_zpow (S₀ : ℝ) (hu : u ≠ 0) (ω : ℕ → Bool) {k : ℕ} (hk : k ≤ n) :
    spotPath S₀ u u⁻¹ k ω = S₀ * u ^ walkPos (flips n ω) k := by
  induction k with
  | zero => simp [spotPath, walkPos_zero]
  | succ k ih =>
    have hkn : k < n := by omega
    have hsucc : spotPath S₀ u u⁻¹ (k + 1) ω = spotPath S₀ u u⁻¹ k ω * (if ω k then u else u⁻¹) :=
      by simp only [spotPath, Finset.prod_range_succ, mul_assoc]
    have hstep : (if ω k then u else u⁻¹) = u ^ walkStep (flips n ω ⟨k, hkn⟩) := by
      rcases Bool.eq_false_or_eq_true (ω k) with hb | hb <;> simp [flips, walkStep, hb]
    rw [hsucc, ih hkn.le, walkPos_succ _ hkn, zpow_add₀ hu, hstep, mul_assoc]

/-- **The spot reaches the barrier `S₀ uᵃ` exactly when the walk hits `a`.** For `u > 1`,
`S₀ > 0` and `a ≥ 0`, the spot is at or above `S₀ uᵃ` at some step `k ≤ n` if and only if the ±1
walk of the first `n` flips hits `a`. -/
theorem exists_le_spotPath_iff (hS : 0 < S₀) (hu : 1 < u) {a : ℤ} (ha : 0 ≤ a) (ω : ℕ → Bool) :
    (∃ k ≤ n, S₀ * u ^ a ≤ spotPath S₀ u u⁻¹ k ω) ↔ HitsLevel a (flips n ω) := by
  have hu0 : u ≠ 0 := (zero_lt_one.trans hu).ne'
  constructor
  · rintro ⟨k, hk, hle⟩
    rw [spotPath_inv_eq_zpow S₀ hu0 ω hk] at hle
    exact HitsLevel_of_le_walkPos _ a ha hk
      ((zpow_le_zpow_iff_right₀ hu).1 (le_of_mul_le_mul_left hle hS))
  · rintro ⟨k, hk⟩
    rw [hittingSet, Finset.mem_filter, Finset.mem_range] at hk
    have hkn : k ≤ n := Nat.lt_succ_iff.1 hk.1
    exact ⟨k, hkn, le_of_eq (by rw [spotPath_inv_eq_zpow S₀ hu0 ω hkn, hk.2])⟩

/-- On the grid of step `h > 0`, the `k`-th date is at step `k`. -/
theorem floor_gridDate_div (hh : 0 < h) (k : ℕ) :
    ⌊(((k : ℝ≥0) * h.toNNReal : ℝ≥0) : ℝ) / h⌋₊ = k := by
  rw [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ hh.le, mul_div_assoc,
    div_self hh.ne', mul_one, Nat.floor_natCast]

/-- **The binomial market prices the up-and-in knock-in by reflection.** Take `u > 1`, `d = u⁻¹`,
`S₀ > 0`, a step `h > 0`, the horizon `T = nh`, and a payoff `f` that reads the spot only at `T`;
let `g j` be its value at the spot `S₀ uʲ` and `W` the ±1 walk of the first `n` flips. When the
risk-neutral up-probability `crrUpProb u u⁻¹ ρ` is `1/2`, the symmetric coin flips are a pricing
measure of the market (for a physical law of i.i.d. flips with up-probability `0 < p < 1`); and,
watched at the grid dates `0, h, …, nh`, the knock-in `upAndIn` with barrier `S₀ uᵃ`, `a > 0`, is
priced under them at `e^{−ρn}(E[g(Wₙ); Wₙ ≥ a] + E[g(2a − Wₙ); Wₙ > a])`. -/
theorem price_upAndIn_market (hu : 1 < u) (hS : 0 < S₀) (hh : 0 < h)
    (hq : (1 / 2 : ℝ≥0) ≤ 1) (hna : BinomialNoArb u u⁻¹ ρ)
    (hqcrr : crrUpProb u u⁻¹ ρ = (1 / 2 : ℝ≥0)) {p : ℝ≥0} (hp0 : 0 < p) (hp : p < 1)
    {a : ℤ} (ha : 0 < a) (f : Payoff Unit)
    (hf : ∀ o ∈ f.obsList, o.2 = (n : ℝ≥0) * h.toNNReal) :
    (market (coinFlipMeasure p hp.le) S₀ u u⁻¹ ρ hh.le).IsPricingMeasure
        ((n : ℝ≥0) * h.toNNReal) (coinFlipMeasure (1 / 2) hq) ∧
      (market (coinFlipMeasure p hp.le) S₀ u u⁻¹ ρ hh.le).price (coinFlipMeasure (1 / 2) hq)
          (upAndIn (S₀ * u ^ a) f () ((n : ℝ≥0) * h.toNNReal)
            ((List.range n).map fun k : ℕ ↦ (k : ℝ≥0) * h.toNNReal)) =
        Real.exp (-(ρ * n)) *
          ((∫ ω, (if a ≤ walkPos (flips n ω) n
              then f.eval (fun _ _ ↦ S₀ * u ^ walkPos (flips n ω) n) else 0)
              ∂coinFlipMeasure (1 / 2) hq) +
            ∫ ω, (if a < walkPos (flips n ω) n
              then f.eval (fun _ _ ↦ S₀ * u ^ (2 * a - walkPos (flips n ω) n)) else 0)
              ∂coinFlipMeasure (1 / 2) hq) := by
  refine ⟨isPricingMeasure_coinFlipMeasure hq hna hqcrr S₀ hh.le hp0 hp _, ?_⟩
  have hu0 : u ≠ 0 := (zero_lt_one.trans hu).ne'
  have hspot (k : ℕ) (ω : ℕ → Bool) :
      assets S₀ u u⁻¹ h () ((k : ℝ≥0) * h.toNNReal) ω = spotPath S₀ u u⁻¹ k ω := by
    simp only [assets]
    rw [floor_gridDate_div hh]
  have hmon (ω : ℕ → Bool) :
      (∃ τ ∈ ((n : ℝ≥0) * h.toNNReal) ::
          (List.range n).map (fun k : ℕ ↦ (k : ℝ≥0) * h.toNNReal),
          S₀ * u ^ a ≤ assets S₀ u u⁻¹ h () τ ω) ↔ HitsLevel a (flips n ω) := by
    rw [← exists_le_spotPath_iff hS hu ha.le ω]
    constructor
    · rintro ⟨τ, hτ, hB⟩
      rcases List.mem_cons.1 hτ with rfl | hτ
      · exact ⟨n, le_rfl, hspot n ω ▸ hB⟩
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hτ
        exact ⟨k, (List.mem_range.1 hk).le, hspot k ω ▸ hB⟩
    · rintro ⟨k, hk, hB⟩
      rcases hk.lt_or_eq with hk | hk
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩),
          (hspot k ω).symm ▸ hB⟩
      · exact ⟨_, List.mem_cons_self, by rw [hk] at hB; rwa [hspot n ω]⟩
  have hpay (ω : ℕ → Bool) :
      f.eval (scenarioAt (assets S₀ u u⁻¹ h) ω)
        = f.eval (fun _ _ ↦ S₀ * u ^ walkPos (flips n ω) n) :=
    f.eval_congr fun o ho ↦ by
      change assets S₀ u u⁻¹ h o.1 o.2 ω = S₀ * u ^ walkPos (flips n ω) n
      rw [hf o ho, hspot n ω, spotPath_inv_eq_zpow S₀ hu0 ω le_rfl]
  have hdefl (ω : ℕ → Bool) :
      (market (coinFlipMeasure p hp.le) S₀ u u⁻¹ ρ hh.le).deflator
        ((n : ℝ≥0) * h.toNNReal) ω = Real.exp (-(ρ * n)) := by
    simp only [Market.deflator, market]
    rw [floor_gridDate_div hh, NNReal.coe_zero, zero_div, Nat.floor_zero, Nat.cast_zero, mul_zero,
      Real.exp_zero, one_div, Real.exp_neg]
  have hrefl := binomial_upAndIn_reflection (n := n) hq a ha
    (fun j ↦ f.eval (fun _ _ ↦ S₀ * u ^ j))
  rw [Market.price, upAndIn, Contract.value_pay]
  refine (integral_congr_ae (.of_forall fun ω ↦ ?_)).trans
    ((integral_const_mul (Real.exp (-(ρ * n))) _).trans (congrArg _ hrefl))
  rw [hdefl ω, eval_upAndInPayoff]
  exact congrArg _ (if_congr (hmon ω) (hpay ω) rfl)

end MathFin.Contracts.Binomial
