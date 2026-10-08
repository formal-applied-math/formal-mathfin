/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.Spreads

/-!
# Call spreads tend to the digital, so call prices determine the law

A bull-call spread long `1/h` calls struck at `K` and short `1/h` calls struck at `K + h` pays
`((X − K)⁺ − (X − K − h)⁺)/h`. The payoff lies in `[0, 1]`: it is nonnegative because the call
payoff is antitone in the strike (`bull_call_spread_payoff_le`), and at most `1` because the call
payoff is `1`-Lipschitz in the strike. As `h ↓ 0` it tends to the digital payoff `1_{X > K}`. So in
any model, minus the right strike derivative of the call price is the price of the event `X > K`,
and the call prices at every strike determine the law of the underlying. This is the first-order
form of Breeden and Litzenberger (1978), for any law with a finite mean, not only the lognormal
one.

* `tendsto_call_spread`: `(C(K) − C(K + h))/h → μ {X > K}` as `h ↓ 0`, where
  `C(k) = ∫ (X − k)⁺ dμ`, for an integrable `X` under a finite measure `μ` (dominated
  convergence).
* `measure_eq_of_integral_call_eq`: two probability laws of a log-return, each with `∫ eʸ < ∞`,
  that give the same undiscounted call price `∫ (Seʸ − K)⁺` at every strike `K > 0` (for one
  `S > 0`) are equal. The digital at the strike `Seᵃ` is the tail `P(Y > a)`.

In Black–Scholes the right strike derivative is `−e^{−rτ}Φ(d₂)` (`hasDerivAt_bsV_K`) and the
cash-or-nothing price is `e^{−rτ}Φ(d₂)` (`bs_cash_or_nothing_formula`). Both are proved from the
closed forms, not from this file. The second-order form, the lognormal density as the second
strike derivative of `bsV`, is in `BlackScholes/BreedenLitzenberger.lean`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory Filter Set
open scoped Topology

/-- **A digital is a limit of call spreads.** For an integrable `X` under a finite measure `μ`,
the bull-call spread `(C(K) − C(K + h))/h`, where `C(k) = ∫ (X − k)⁺ dμ`, tends to `μ {X > K}` as
`h ↓ 0`: minus the right strike derivative of the undiscounted call price is the price of the
event `X > K`. The spread payoff lies in `[0, 1]` and tends to `1_{X > K}` pointwise, so dominated
convergence applies. -/
theorem tendsto_call_spread {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hXm : Measurable X) (hX : Integrable X μ) (K : ℝ) :
    Tendsto (fun h ↦ (∫ ω, max (X ω - K) 0 ∂μ - ∫ ω, max (X ω - (K + h)) 0 ∂μ) / h) (𝓝[>] 0)
      (𝓝 (μ.real {ω | K < X ω})) := by
  have hcall (k : ℝ) : Integrable (fun ω ↦ max (X ω - k) 0) μ :=
    (hX.sub (integrable_const k)).pos_part
  have hspread : (fun h ↦ (∫ ω, max (X ω - K) 0 ∂μ - ∫ ω, max (X ω - (K + h)) 0 ∂μ) / h)
      = fun h ↦ ∫ ω, (max (X ω - K) 0 - max (X ω - (K + h)) 0) / h ∂μ := by
    funext h
    rw [integral_div, integral_sub (hcall K) (hcall (K + h))]
  rw [hspread, ← integral_indicator_one (measurableSet_lt measurable_const hXm)]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1)
    (Eventually.of_forall fun h ↦ ?_) ?_ (integrable_const 1) (ae_of_all _ fun ω ↦ ?_)
  · exact (by fun_prop : Measurable fun ω ↦
      (max (X ω - K) 0 - max (X ω - (K + h)) 0) / h).aestronglyMeasurable
  · -- the spread payoff lies in `[0, 1]`
    filter_upwards [self_mem_nhdsWithin] with h hh
    refine ae_of_all _ fun ω ↦ ?_
    have hh : 0 < h := hh
    have hlo := bull_call_spread_payoff_le (X ω) K (K + h) (by linarith)
    have hhi : max (X ω - K) 0 ≤ max (X ω - (K + h)) 0 + h :=
      max_le (by linarith [le_max_left (X ω - (K + h)) 0])
        (by linarith [le_max_right (X ω - (K + h)) 0])
    show ‖(max (X ω - K) 0 - max (X ω - (K + h)) 0) / h‖ ≤ 1
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sub_nonneg.2 hlo), abs_of_pos hh,
      div_le_one hh]
    linarith
  · -- and tends to the digital payoff `1_{X > K}`
    by_cases hω : K < X ω
    · rw [indicator_of_mem (show ω ∈ {ω | K < X ω} from hω), Pi.one_apply]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hω)] with h hh
      rw [max_eq_left (by linarith [hh.1, hh.2]), max_eq_left (by linarith [hh.1, hh.2]),
        show X ω - K - (X ω - (K + h)) = h by ring, div_self hh.1.ne']
    · rw [indicator_of_notMem (show ω ∉ {ω | K < X ω} from hω)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh : 0 < h := hh
      rw [max_eq_right (by linarith [not_lt.1 hω]), max_eq_right (by linarith [not_lt.1 hω]),
        sub_self, zero_div]

/-- **Call prices at every strike determine the law** (Breeden–Litzenberger, first order). Two
probability laws of a log-return, each with `∫ eʸ < ∞`, that give the same undiscounted call
price `∫ (Seʸ − K)⁺` at every strike `K > 0` (for one `S > 0`) are equal. The call spreads at the
strike `Seᵃ` tend to the tail `P(Y > a)` under each law (`tendsto_call_spread`), so the tails
agree, and the tails fix the law (Mathlib's `Measure.ext_of_Iic`). -/
theorem measure_eq_of_integral_call_eq {μ μ' : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {S : ℝ} (hS : 0 < S) (hμ : Integrable Real.exp μ)
    (hμ' : Integrable Real.exp μ')
    (h : ∀ K, 0 < K →
      ∫ y, max (S * Real.exp y - K) 0 ∂μ = ∫ y, max (S * Real.exp y - K) 0 ∂μ') :
    μ = μ' := by
  have hX : Measurable fun y ↦ S * Real.exp y := by fun_prop
  have htail (a : ℝ) : μ (Ioi a) = μ' (Ioi a) := by
    have hset : {y | S * Real.exp a < S * Real.exp y} = Ioi a := by
      ext y
      rw [mem_setOf_eq, mem_Ioi, mul_lt_mul_iff_right₀ hS, Real.exp_lt_exp]
    have hlim := tendsto_call_spread hX (hμ.const_mul S) (S * Real.exp a)
    have hlim' := tendsto_call_spread hX (hμ'.const_mul S) (S * Real.exp a)
    rw [hset] at hlim hlim'
    have hK : 0 < S * Real.exp a := mul_pos hS (Real.exp_pos a)
    refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ' _)).1
      (tendsto_nhds_unique hlim (hlim'.congr' ?_))
    filter_upwards [self_mem_nhdsWithin] with k hk
    rw [h _ hK, h _ (add_pos hK hk)]
  refine Measure.ext_of_Iic μ μ' fun a ↦ ?_
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
    prob_compl_eq_one_sub measurableSet_Ioi, htail]

end MathFin
