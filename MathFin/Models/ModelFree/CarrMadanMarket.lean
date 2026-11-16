/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.ModelFree.CarrMadan
public import MathFin.Pricing.Market
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Carr–Madan replication in a market

The spanning identity `carrMadan_spanning` writes a payoff `f(S)` as cash, a forward and a strip of
out-of-the-money options, for each spot `S ∈ [L, U]`. Taking the expectation under a pricing
measure turns it into a statement about a market's prices: in a market with unit numéraire,

  `𝔼_Q[f(S_T)] = f(κ) + f'(κ)(𝔼_Q[S_T] − κ) + ∫_L^κ f''(K) P(K) dK + ∫_κ^U f''(K) C(K) dK`,

where `P(K)` and `C(K)` are the market's prices of the put and the call at strike `K` and
maturity `T` (`Market.IsPricingMeasure.integral_eq_carrMadan`). The step from the identity to the
prices is Fubini: an option payoff is dominated by `|S| + |K|`, integrable against `Q` times
Lebesgue measure on a bounded strike range.

The strikes run over a bounded range `[L, U]` holding `S_T` almost surely; the unbounded strip
needs integrability conditions at `0` and `∞` and is not treated.

## Main results

* `Market.IsPricingMeasure.integral_eq_carrMadan`: the Carr–Madan decomposition of
  `𝔼_Q[f(S_T)]` into cash, the forward and the market's put and call prices.

## References

* [Carr and Madan (2001)][CarrMadan2001]
* [Breeden and Litzenberger, *Prices of state-contingent claims implicit in option
  prices*][BreedenLitzenberger1978]

## Tags

static replication, Carr–Madan formula, strip of options, pricing measure, Fubini,
JEL G13, MSC 91G20
-/

@[expose] public section

open MeasureTheory Set MathFin.Contracts
open scoped NNReal

namespace MathFin

namespace Market

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {M : Market Unit Ω} {T : ℝ≥0} {Q : Measure Ω}

/-- **Carr–Madan replication in a market.** In a market with unit numéraire, let `Q` be a pricing
measure up to `T` under which `S_T ∈ [L, U]` almost surely. For a payoff `f` twice differentiable on
`[L, U]` with continuous `f''`, and `κ ∈ [L, U]`,

`𝔼_Q[f(S_T)] = f(κ) + f'(κ)(𝔼_Q[S_T] − κ) + ∫_L^κ f''(K) P(K) dK + ∫_κ^U f''(K) C(K) dK`,

with `P(K)`, `C(K)` the market's prices of the European put and call at strike `K` and
maturity `T`. -/
theorem IsPricingMeasure.integral_eq_carrMadan (hQ : M.IsPricingMeasure T Q)
    (hN : ∀ t x, M.numeraire t x = 1) {f f' f'' : ℝ → ℝ} {L U κ : ℝ} (hLκ : L ≤ κ)
    (hκU : κ ≤ U) (hS : ∀ᵐ x ∂Q, M.asset () T x ∈ Icc L U)
    (hf : ∀ t ∈ Icc L U, HasDerivAt f (f' t) t) (hf' : ∀ t ∈ Icc L U, HasDerivAt f' (f'' t) t)
    (hf'' : ContinuousOn f'' (Icc L U)) :
    ∫ x, f (M.asset () T x) ∂Q = f κ + f' κ * (∫ x, M.asset () T x ∂Q - κ)
      + (∫ K in L..κ, f'' K * M.price Q (europeanPut K T))
      + ∫ K in κ..U, f'' K * M.price Q (europeanCall K T) := by
  have := hQ.isProb
  have hY : Integrable (M.asset () T) Q := hQ.integrable_asset hN
  -- Fubini for a strip of options: a payoff `φ(y, K)` with `|φ(y, K)| ≤ |y| + |K|`, weighted by
  -- `g`, is integrable against `Q` times the strike measure `ν`
  have strip {ν : Measure ℝ} [SFinite ν] {g : ℝ → ℝ} (hg : Integrable g ν)
      (hgK : Integrable (fun K ↦ g K * K) ν) {φ : ℝ → ℝ → ℝ}
      (hφ : Continuous (Function.uncurry φ)) (hφb : ∀ y K, |φ y K| ≤ |y| + |K|) :
      Integrable (Function.uncurry fun x K ↦ g K * φ (M.asset () T x) K) (Q.prod ν) := by
    have hdom : Integrable (fun p : Ω × ℝ ↦ |M.asset () T p.1| * |g p.2| + 1 * |g p.2 * p.2|)
        (Q.prod ν) :=
      (hY.abs.mul_prod hg.abs).add ((integrable_const (1 : ℝ)).mul_prod hgK.abs)
    refine hdom.mono' ?_ (.of_forall fun p ↦ ?_)
    · have h1 : AEStronglyMeasurable (fun p : Ω × ℝ ↦ M.asset () T p.1) (Q.prod ν) :=
        hY.aestronglyMeasurable.comp_fst
      have h2 : AEStronglyMeasurable (fun p : Ω × ℝ ↦ p.2) (Q.prod ν) :=
        measurable_snd.aestronglyMeasurable
      exact hg.aestronglyMeasurable.comp_snd.mul (hφ.comp_aestronglyMeasurable (h1.prodMk h2))
    · obtain ⟨x, K⟩ := p
      have := hφb (M.asset () T x) K
      simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, one_mul, abs_mul]
      nlinarith [abs_nonneg (g K), abs_nonneg (φ (M.asset () T x) K)]
  have hput : Integrable (Function.uncurry fun x K ↦ f'' K * max (K - M.asset () T x) 0)
      (Q.prod (volume.restrict (Ioc L κ))) :=
    strip ((hf''.mono (Icc_subset_Icc_right hκU)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (((hf''.mono (Icc_subset_Icc_right hκU)).mul continuousOn_id).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self)
      (φ := fun y K ↦ max (K - y) 0)
      (show Continuous fun p : ℝ × ℝ ↦ max (p.2 - p.1) 0 from
        (continuous_snd.sub continuous_fst).max continuous_const)
      fun y K ↦ by
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [le_abs_self K, neg_le_abs y]) (by positivity)
  have hcall : Integrable (Function.uncurry fun x K ↦ f'' K * max (M.asset () T x - K) 0)
      (Q.prod (volume.restrict (Ioc κ U))) :=
    strip ((hf''.mono (Icc_subset_Icc_left hLκ)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (((hf''.mono (Icc_subset_Icc_left hLκ)).mul continuousOn_id).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self)
      (φ := fun y K ↦ max (y - K) 0)
      (show Continuous fun p : ℝ × ℝ ↦ max (p.1 - p.2) 0 from
        (continuous_fst.sub continuous_snd).max continuous_const)
      fun y K ↦ by
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [le_abs_self y, neg_le_abs K]) (by positivity)
  have hputi : Integrable (fun x ↦ ∫ K in Ioc L κ, f'' K * max (K - M.asset () T x) 0) Q :=
    hput.integral_prod_left
  have hcalli : Integrable (fun x ↦ ∫ K in Ioc κ U, f'' K * max (M.asset () T x - K) 0) Q :=
    hcall.integral_prod_left
  have hputp : ∫ x, (∫ K in Ioc L κ, f'' K * max (K - M.asset () T x) 0) ∂Q
      = ∫ K in Ioc L κ, f'' K * M.price Q (europeanPut K T) := by
    rw [integral_integral_swap hput]
    exact integral_congr_ae (.of_forall fun K ↦ by
      simp only [price_europeanPut_of_numeraire_eq_one hN, integral_const_mul])
  have hcallp : ∫ x, (∫ K in Ioc κ U, f'' K * max (M.asset () T x - K) 0) ∂Q
      = ∫ K in Ioc κ U, f'' K * M.price Q (europeanCall K T) := by
    rw [integral_integral_swap hcall]
    exact integral_congr_ae (.of_forall fun K ↦ by
      simp only [price_europeanCall_of_numeraire_eq_one hN, integral_const_mul])
  -- the spanning identity at each spot, integrated
  have hpt : ∀ᵐ x ∂Q, f (M.asset () T x) = (f κ + f' κ * (M.asset () T x - κ))
      + (∫ K in Ioc L κ, f'' K * max (K - M.asset () T x) 0)
      + ∫ K in Ioc κ U, f'' K * max (M.asset () T x - K) 0 :=
    hS.mono fun x hx ↦ by
      simpa only [intervalIntegral.integral_of_le hLκ, intervalIntegral.integral_of_le hκU] using
        carrMadan_spanning hLκ hκU hx hf hf' hf''
  have hlin : Integrable (fun x ↦ f' κ * (M.asset () T x - κ)) Q :=
    (hY.sub (integrable_const κ)).const_mul _
  have hcash : Integrable (fun x ↦ f κ + f' κ * (M.asset () T x - κ)) Q :=
    (integrable_const (f κ)).add hlin
  have hcashput : Integrable (fun x ↦ f κ + f' κ * (M.asset () T x - κ)
      + ∫ K in Ioc L κ, f'' K * max (K - M.asset () T x) 0) Q := hcash.add hputi
  rw [integral_congr_ae hpt, integral_add hcashput hcalli, integral_add hcash hputi,
    integral_add (integrable_const (f κ)) hlin, hputp, hcallp,
    intervalIntegral.integral_of_le hLκ, intervalIntegral.integral_of_le hκU, integral_const_mul,
    integral_sub hY (integrable_const κ)]
  simp

end Market

end MathFin
