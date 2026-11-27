/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import MathFin.Contracts.StaticHedge
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Carr–Madan static replication (spanning formula)

Any twice-differentiable European payoff `f` decomposes, around a reference level
`κ`, as cash + a forward + a static portfolio of out-of-the-money options:

  `f S = f κ + f' κ · (S − κ) + ∫_L^κ f''(K)·(K − S)⁺ dK + ∫_κ^U f''(K)·(S − K)⁺ dK`,

the **Carr–Madan spanning formula** (`carrMadan_spanning`). The puts (strikes `K < κ`)
and calls (strikes `K > κ`) are weighted by the payoff convexity `f''`. We prove the
honest **compact strike-range** version on `[L, U]` (no improper integrals); the textbook
unbounded form is the `L = 0`, `U → ∞` limit, which needs separate integrability-at-`∞`
hypotheses.

The proof is one integration by parts — the second-order Taylor remainder
`∫_κ^S (S − t) f''(t) dt = f S − f κ − f' κ (S − κ)`
(`secondOrder_remainder_eq_integral`) — followed by a case split on `S` vs `κ`: in each
case one option leg vanishes (its positive part is `0` over its strike range) and the other
reproduces the remainder.

The finite exact case is the static-hedge compiler of `Contracts/StaticHedge.lean`: a continuous
piecewise-linear payoff is `a + b S + ∑ⱼ wⱼ (S − Kⱼ)⁺`, the same decomposition with the measure
`f'' dK` replaced by the point masses `wⱼ δ_{Kⱼ}`. The bridge is
`StaticHedge.jump_eval_of_mem_normalize`:
in the normal form of a portfolio the weight of the call at `K` is the jump of the one-sided slopes
of the value function at `K`, `f'(K+) − f'(K−)`, the second derivative of `f` in the sense of
distributions; and the forward amount is the right slope at `0` when every strike is positive
(`StaticHedge.derivWithin_Ioi_zero`).

## Main results

* `carrMadan_spanning`: for `f` twice differentiable on `[L, U]` with `f''` continuous there, and
  `L ≤ κ ≤ U`, `S ∈ [L, U]`,
  `f S = f κ + f' κ · (S − κ) + ∫_L^κ f''(K)·(K − S)⁺ dK + ∫_κ^U f''(K)·(S − K)⁺ dK`.
  This is the compact strike-range form; no improper integral appears.
* `StaticHedge.jump_eval_of_mem_normalize`: the weight of a call of a normalised static hedge is the
  jump of the right and left slopes of its value function at the strike.
* `StaticHedge.derivWithin_Ioi_zero`: the forward amount is the right slope at `0`, when the strikes
  are positive.
* `carrMadan_log_spanning`: the case `f = log` with `0 < L`, where the option weights are
  `−1/K²`.

## References

* [Carr and Madan (2001)][CarrMadan2001]
* [Demeterfi et al., *More than you ever wanted to know about volatility
  swaps*][DemeterfiDermanKamalZou1999]

## Tags

static replication, spanning formula, Carr–Madan formula, variance swap replication,
Taylor remainder, strip of options, JEL G13, MSC 91G20
-/

@[expose] public section

namespace MathFin

/-- **Second-order Taylor remainder as an integral against `f''`.** For `f` twice
differentiable on `[[κ, S]]` with continuous `f''`,
`∫_κ^S (S − t) · f''(t) dt = f S − f κ − f' κ · (S − κ)`. One integration by parts
(`u = S − ·`, `v = f'`) plus the fundamental theorem of calculus.

This is the `n = 1` case of Mathlib's `taylor_integral_remainder` (stated there via
`ContDiffOn` + `iteratedDerivWithin`); we keep this explicit-`HasDerivAt` form because the
spanning proof consumes `f'`, `f''` as named functions and the `iteratedDerivWithin` bridge
would be longer than the IBP proof itself. -/
theorem secondOrder_remainder_eq_integral {f f' f'' : ℝ → ℝ} {κ S : ℝ}
    (hf : ∀ t ∈ Set.uIcc κ S, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.uIcc κ S, HasDerivAt f' (f'' t) t)
    (hf'' : ContinuousOn f'' (Set.uIcc κ S)) :
    ∫ t in κ..S, (S - t) * f'' t = f S - f κ - f' κ * (S - κ) := by
  have hu : ∀ t ∈ Set.uIcc κ S, HasDerivAt (fun s ↦ S - s) (-1 : ℝ) t :=
    fun t _ ↦ by simpa using (hasDerivAt_id t).const_sub S
  have hf'_cont : ContinuousOn f' (Set.uIcc κ S) :=
    fun t ht ↦ (hf' t ht).continuousAt.continuousWithinAt
  have hf'_int : IntervalIntegrable f' MeasureTheory.volume κ S := hf'_cont.intervalIntegrable
  have hf''_int : IntervalIntegrable f'' MeasureTheory.volume κ S := hf''.intervalIntegrable
  have hconst_int : IntervalIntegrable (fun _ ↦ (-1 : ℝ)) MeasureTheory.volume κ S :=
    intervalIntegrable_const
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hf' hconst_int hf''_int
  have hftc : ∫ t in κ..S, f' t = f S - f κ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hf hf'_int
  calc ∫ t in κ..S, (S - t) * f'' t
      = (S - S) * f' S - (S - κ) * f' κ - ∫ t in κ..S, (-1 : ℝ) * f' t := hibp
    _ = (S - S) * f' S - (S - κ) * f' κ + ∫ t in κ..S, f' t := by
          rw [intervalIntegral.integral_const_mul]; ring
    _ = f S - f κ - f' κ * (S - κ) := by rw [hftc]; ring

/-- **Carr–Madan static replication / spanning formula (compact strike range).** For a
twice-differentiable payoff `f` on `[L, U]` (pointwise derivatives `f'`, `f''`, with `f''`
continuous) and reference level `κ ∈ [L, U]`, every spot `S ∈ [L, U]` satisfies

  `f S = f κ + f' κ · (S − κ) + ∫_L^κ f''(K)·(K − S)⁺ dK + ∫_κ^U f''(K)·(S − K)⁺ dK`,

i.e. the payoff is cash `f κ`, a forward position `f' κ` in `(S − κ)`, plus a static book of
puts (strikes `K ∈ [L, κ]`) and calls (strikes `K ∈ [κ, U]`) held in density `f''(K) dK`.
This is the honest compact-strike-range Carr–Madan formula; the textbook unbounded form is
the `L = 0`, `U → ∞` limit, needing separate integrability-at-`∞` hypotheses. -/
theorem carrMadan_spanning {f f' f'' : ℝ → ℝ} {L U κ S : ℝ}
    (hLκ : L ≤ κ) (hκU : κ ≤ U) (hS : S ∈ Set.Icc L U)
    (hf : ∀ t ∈ Set.Icc L U, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc L U, HasDerivAt f' (f'' t) t)
    (hf'' : ContinuousOn f'' (Set.Icc L U)) :
    f S = f κ + f' κ * (S - κ)
      + (∫ K in L..κ, f'' K * max (K - S) 0)
      + (∫ K in κ..U, f'' K * max (S - K) 0) := by
  have hκ : κ ∈ Set.Icc L U := ⟨hLκ, hκU⟩
  have hL : L ∈ Set.Icc L U := ⟨le_rfl, hLκ.trans hκU⟩
  have hU : U ∈ Set.Icc L U := ⟨hLκ.trans hκU, le_rfl⟩
  have hsub : Set.uIcc κ S ⊆ Set.Icc L U := Set.uIcc_subset_Icc hκ hS
  have hcore : ∫ t in κ..S, (S - t) * f'' t = f S - f κ - f' κ * (S - κ) :=
    secondOrder_remainder_eq_integral (fun t ht ↦ hf t (hsub ht))
      (fun t ht ↦ hf' t (hsub ht)) (hf''.mono hsub)
  have hcont_put : ContinuousOn (fun K ↦ f'' K * max (K - S) 0) (Set.Icc L U) :=
    hf''.mul (((continuous_id.sub continuous_const).max continuous_const).continuousOn)
  have hcont_call : ContinuousOn (fun K ↦ f'' K * max (S - K) 0) (Set.Icc L U) :=
    hf''.mul (((continuous_const.sub continuous_id).max continuous_const).continuousOn)
  rcases le_total κ S with h | h
  · -- `κ ≤ S`: the put leg vanishes; the call leg is the remainder.
    have hput0 : (∫ K in L..κ, f'' K * max (K - S) 0) = 0 := by
      have h0 : Set.EqOn (fun K ↦ f'' K * max (K - S) 0) (fun _ ↦ (0 : ℝ)) (Set.uIcc L κ) := by
        intro K hK
        rw [Set.uIcc_of_le hLκ] at hK
        simp only [max_eq_right (show K - S ≤ 0 by linarith [hK.2]), mul_zero]
      rw [intervalIntegral.integral_congr h0]; simp
    have hcall : (∫ K in κ..U, f'' K * max (S - K) 0) = f S - f κ - f' κ * (S - κ) := by
      have hsplit : (∫ K in κ..U, f'' K * max (S - K) 0)
          = (∫ K in κ..S, f'' K * max (S - K) 0) + (∫ K in S..U, f'' K * max (S - K) 0) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont_call.mono (Set.uIcc_subset_Icc hκ hS)).intervalIntegrable
          (hcont_call.mono (Set.uIcc_subset_Icc hS hU)).intervalIntegrable).symm
      have hupper : (∫ K in S..U, f'' K * max (S - K) 0) = 0 := by
        have h0 : Set.EqOn (fun K ↦ f'' K * max (S - K) 0) (fun _ ↦ (0 : ℝ)) (Set.uIcc S U) := by
          intro K hK
          rw [Set.uIcc_of_le hS.2] at hK
          simp only [max_eq_right (show S - K ≤ 0 by linarith [hK.1]), mul_zero]
        rw [intervalIntegral.integral_congr h0]; simp
      have hlower : (∫ K in κ..S, f'' K * max (S - K) 0) = ∫ K in κ..S, (S - K) * f'' K := by
        refine intervalIntegral.integral_congr fun K hK ↦ ?_
        rw [Set.uIcc_of_le h] at hK
        rw [max_eq_left (show (0 : ℝ) ≤ S - K by linarith [hK.2])]; ring
      rw [hsplit, hupper, hlower, add_zero, hcore]
    rw [hput0, hcall]; ring
  · -- `S ≤ κ`: the call leg vanishes; the put leg is the remainder.
    have hcall0 : (∫ K in κ..U, f'' K * max (S - K) 0) = 0 := by
      have h0 : Set.EqOn (fun K ↦ f'' K * max (S - K) 0) (fun _ ↦ (0 : ℝ)) (Set.uIcc κ U) := by
        intro K hK
        rw [Set.uIcc_of_le hκU] at hK
        simp only [max_eq_right (show S - K ≤ 0 by linarith [hK.1]), mul_zero]
      rw [intervalIntegral.integral_congr h0]; simp
    have hput : (∫ K in L..κ, f'' K * max (K - S) 0) = f S - f κ - f' κ * (S - κ) := by
      have hsplit : (∫ K in L..κ, f'' K * max (K - S) 0)
          = (∫ K in L..S, f'' K * max (K - S) 0) + (∫ K in S..κ, f'' K * max (K - S) 0) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont_put.mono (Set.uIcc_subset_Icc hL hS)).intervalIntegrable
          (hcont_put.mono (Set.uIcc_subset_Icc hS hκ)).intervalIntegrable).symm
      have hlowZero : (∫ K in L..S, f'' K * max (K - S) 0) = 0 := by
        have h0 : Set.EqOn (fun K ↦ f'' K * max (K - S) 0) (fun _ ↦ (0 : ℝ)) (Set.uIcc L S) := by
          intro K hK
          rw [Set.uIcc_of_le hS.1] at hK
          simp only [max_eq_right (show K - S ≤ 0 by linarith [hK.2]), mul_zero]
        rw [intervalIntegral.integral_congr h0]; simp
      have hhigh : (∫ K in S..κ, f'' K * max (K - S) 0) = ∫ K in S..κ, (K - S) * f'' K := by
        refine intervalIntegral.integral_congr fun K hK ↦ ?_
        rw [Set.uIcc_of_le h] at hK
        rw [max_eq_left (show (0 : ℝ) ≤ K - S by linarith [hK.1])]; ring
      rw [hsplit, hlowZero, hhigh, zero_add, ← hcore,
          intervalIntegral.integral_symm S κ, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun K _ ↦ ?_
      ring
    rw [hcall0, hput]; ring

/-- **Carr–Madan log-contract replication** — the variance-swap building block. On a positive
strike range `0 < L ≤ κ ≤ U`, the log payoff replicates as a forward position `κ⁻¹·(S − κ)` in
the underlying plus a static strip of out-of-the-money options weighted by `1/K²`:

  `log S = log κ + κ⁻¹·(S − κ) + ∫_L^κ −(K²)⁻¹·(K − S)⁺ dK + ∫_κ^U −(K²)⁻¹·(S − K)⁺ dK`.

The `−1/K²` weight (the log payoff's convexity `f''`) is exactly the density of OTM puts and
calls a variance swap holds. Specialises `carrMadan_spanning` to `f = Real.log`. -/
theorem carrMadan_log_spanning {L U κ S : ℝ} (hL : 0 < L)
    (hLκ : L ≤ κ) (hκU : κ ≤ U) (hS : S ∈ Set.Icc L U) :
    Real.log S = Real.log κ + κ⁻¹ * (S - κ)
      + (∫ K in L..κ, -(K ^ 2)⁻¹ * max (K - S) 0)
      + (∫ K in κ..U, -(K ^ 2)⁻¹ * max (S - K) 0) := by
  have hpos : ∀ t ∈ Set.Icc L U, t ≠ 0 := fun t ht ↦ (lt_of_lt_of_le hL ht.1).ne'
  exact carrMadan_spanning (f := Real.log) (f' := fun t ↦ t⁻¹) (f'' := fun K ↦ -(K ^ 2)⁻¹)
    hLκ hκU hS (fun t ht ↦ Real.hasDerivAt_log (hpos t ht))
    (fun t ht ↦ by simpa using hasDerivAt_inv (hpos t ht))
    (((continuousOn_id.pow 2).inv₀ (fun K hK ↦ pow_ne_zero 2 (hpos K hK))).neg)

end MathFin

namespace MathFin.Contracts

open Set Filter Topology

/-- A call `w (S − K)⁺` has the right derivative `w` at `x` if `K ≤ x`, and `0` if `x < K`. -/
theorem hasDerivWithinAt_call_Ioi (K w x : ℝ) :
    HasDerivWithinAt (fun y : ℝ ↦ w * max (y - K) 0) (if K ≤ x then w else 0) (Ioi x) x := by
  by_cases hK : K ≤ x
  · rw [if_pos hK]
    have h : HasDerivWithinAt (fun y : ℝ ↦ w * (y - K)) w (Ioi x) x :=
      (((hasDerivAt_id' x).sub (hasDerivAt_const x K)).const_mul w).hasDerivWithinAt.congr_deriv
        (by ring)
    refine h.congr (fun y hy ↦ ?_) ?_
    · rw [max_eq_left (by linarith [mem_Ioi.1 hy])]
    · rw [max_eq_left (by linarith)]
  · rw [if_neg hK]
    have hxK : x < K := not_le.1 hK
    have hev : (fun y : ℝ ↦ w * max (y - K) 0) =ᶠ[𝓝[Ioi x] x] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhdsGT hxK] with y hy
      rw [max_eq_right (by linarith [hy.2]), mul_zero]
    exact (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq hev
      (by rw [max_eq_right (by linarith), mul_zero])

/-- A call `w (S − K)⁺` has the left derivative `w` at `x` if `K < x`, and `0` if `x ≤ K`. -/
theorem hasDerivWithinAt_call_Iio (K w x : ℝ) :
    HasDerivWithinAt (fun y : ℝ ↦ w * max (y - K) 0) (if K < x then w else 0) (Iio x) x := by
  by_cases hK : K < x
  · rw [if_pos hK]
    have h : HasDerivWithinAt (fun y : ℝ ↦ w * (y - K)) w (Iio x) x :=
      (((hasDerivAt_id' x).sub (hasDerivAt_const x K)).const_mul w).hasDerivWithinAt.congr_deriv
        (by ring)
    have hev : (fun y : ℝ ↦ w * max (y - K) 0) =ᶠ[𝓝[Iio x] x] fun y ↦ w * (y - K) := by
      filter_upwards [Ioo_mem_nhdsLT hK] with y hy
      rw [max_eq_left (by linarith [hy.1])]
    exact h.congr_of_eventuallyEq hev (by rw [max_eq_left (by linarith)])
  · rw [if_neg hK]
    have hxK : x ≤ K := not_lt.1 hK
    refine (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
    · rw [max_eq_right (by linarith [mem_Iio.1 hy]), mul_zero]
    · rw [max_eq_right (by linarith), mul_zero]

/-- A call sum has the right derivative the sum of the weights of the calls
struck at or below `x`. -/
theorem hasDerivWithinAt_callSum_Ioi (L : List (ℝ × ℝ)) (x : ℝ) :
    HasDerivWithinAt (callSum L) (L.map fun p ↦ if p.1 ≤ x then p.2 else 0).sum (Ioi x) x := by
  induction L with
  | nil =>
    have h := (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt (s := Ioi x)
    simpa using h.congr (fun y _ ↦ callSum_nil y) (callSum_nil x)
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons]
    exact ((hasDerivWithinAt_call_Ioi p.1 p.2 x).add ih).congr (fun y _ ↦ callSum_cons p L y)
      (callSum_cons p L x)

/-- A call sum has the left derivative the sum of the weights of the calls struck below `x`. -/
theorem hasDerivWithinAt_callSum_Iio (L : List (ℝ × ℝ)) (x : ℝ) :
    HasDerivWithinAt (callSum L) (L.map fun p ↦ if p.1 < x then p.2 else 0).sum (Iio x) x := by
  induction L with
  | nil =>
    have h := (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt (s := Iio x)
    simpa using h.congr (fun y _ ↦ callSum_nil y) (callSum_nil x)
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons]
    exact ((hasDerivWithinAt_call_Iio p.1 p.2 x).add ih).congr (fun y _ ↦ callSum_cons p L y)
      (callSum_cons p L x)

namespace StaticHedge

/-- The affine part `a + b S` of a portfolio has the derivative `b`, on any side. -/
theorem hasDerivWithinAt_affine (a b x : ℝ) (s : Set ℝ) :
    HasDerivWithinAt (fun y : ℝ ↦ a + b * y) b s x :=
  ((hasDerivAt_const x a).add ((hasDerivAt_id' x).const_mul b)).hasDerivWithinAt.congr_deriv
    (by ring)

/-- **The right slope of a static hedge**: its value function has the right derivative `b` plus the
weights of the calls struck at or below `x`. -/
theorem hasDerivWithinAt_eval_Ioi (H : StaticHedge) (x : ℝ) :
    HasDerivWithinAt H.eval
      (H.forwardAmount + (H.calls.map fun p ↦ if p.1 ≤ x then p.2 else 0).sum) (Ioi x) x :=
  (hasDerivWithinAt_affine H.bondAmount H.forwardAmount x _).add
    (hasDerivWithinAt_callSum_Ioi H.calls x)

/-- **The left slope of a static hedge**: its value function has the left derivative `b` plus the
weights of the calls struck below `x`. -/
theorem hasDerivWithinAt_eval_Iio (H : StaticHedge) (x : ℝ) :
    HasDerivWithinAt H.eval
      (H.forwardAmount + (H.calls.map fun p ↦ if p.1 < x then p.2 else 0).sum) (Iio x) x :=
  (hasDerivWithinAt_affine H.bondAmount H.forwardAmount x _).add
    (hasDerivWithinAt_callSum_Iio H.calls x)

/-- The weights of the calls struck at or below `x`, less those struck below `x`, are the weights of
the calls struck at `x`. -/
theorem sum_ite_le_sub_sum_ite_lt (L : List (ℝ × ℝ)) (x : ℝ) :
    (L.map fun p ↦ if p.1 ≤ x then p.2 else 0).sum - (L.map fun p ↦ if p.1 < x then p.2 else 0).sum
      = (L.map fun p ↦ if p.1 = x then p.2 else 0).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases lt_trichotomy p.1 x with h | h | h
    · simp only [if_pos h, if_pos h.le, if_neg h.ne]
      linarith
    · simp only [if_pos h.le, if_neg (not_lt.2 h.ge), if_pos h]
      linarith
    · simp only [if_neg (not_le.2 h), if_neg (not_lt.2 h.le), if_neg h.ne']
      linarith

/-- **The jump of the slope of a static hedge** at `x`, `f'(x+) − f'(x−)` for `f = H.eval`, is the
total weight of the calls struck at `x`. -/
theorem derivWithin_Ioi_sub_derivWithin_Iio (H : StaticHedge) (x : ℝ) :
    derivWithin H.eval (Ioi x) x - derivWithin H.eval (Iio x) x
      = (H.calls.map fun p ↦ if p.1 = x then p.2 else 0).sum := by
  rw [(hasDerivWithinAt_eval_Ioi H x).derivWithin (uniqueDiffWithinAt_Ioi x),
    (hasDerivWithinAt_eval_Iio H x).derivWithin (uniqueDiffWithinAt_Iio x),
    ← sum_ite_le_sub_sum_ite_lt H.calls x]
  ring

/-- In a list with strictly increasing strikes, the weights of the calls struck at `K` sum to the
weight `w` of a call `(K, w)` of the list. -/
theorem sum_ite_eq_of_mem {K w : ℝ} :
    ∀ L : List (ℝ × ℝ), L.Pairwise (fun a b ↦ a.1 < b.1) → (K, w) ∈ L →
      (L.map fun p ↦ if p.1 = K then p.2 else 0).sum = w
  | [], _, h => absurd h List.not_mem_nil
  | r :: L, hL, h => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hL
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · have h0 : (L.map fun p ↦ if p.1 = K then p.2 else 0).sum = 0 :=
        List.sum_eq_zero fun a ha ↦ by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
          exact if_neg (h1 q hq).ne'
      rw [h0, if_pos rfl, add_zero]
    · rw [if_neg (h1 _ h).ne, zero_add]
      exact sum_ite_eq_of_mem L h2 h

/-- **The slope bridge to the Carr–Madan formula.** In the normal form of a portfolio, the weight
of the call at a strike `K` is the jump of the one-sided slopes of the value function there:
`w = f'(K+) − f'(K−)` for `f = H.eval`. The calls of a static hedge are the second derivative of the
payoff, as a measure; `carrMadan_spanning` is the same decomposition for a payoff with a density
`f''`. -/
theorem jump_eval_of_mem_normalize (H : StaticHedge) {K w : ℝ} (h : (K, w) ∈ H.normalize.calls) :
    derivWithin H.eval (Ioi K) K - derivWithin H.eval (Iio K) K = w := by
  have hf : H.normalize.eval = H.eval := funext (eval_normalize H)
  rw [← hf, derivWithin_Ioi_sub_derivWithin_Iio]
  exact sum_ite_eq_of_mem _ (pairwise_normalize_calls H) h

/-- **The forward amount is the right slope at `0`**, when every call is struck above `0`: the
value function of the portfolio is then `a + b S` just right of `0`. -/
theorem derivWithin_Ioi_zero (H : StaticHedge) (h : ∀ q ∈ H.calls, 0 < q.1) :
    derivWithin H.eval (Ioi 0) 0 = H.forwardAmount := by
  rw [(hasDerivWithinAt_eval_Ioi H 0).derivWithin (uniqueDiffWithinAt_Ioi 0)]
  have : (H.calls.map fun p ↦ if p.1 ≤ 0 then p.2 else 0).sum = 0 :=
    List.sum_eq_zero fun a ha ↦ by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
      exact if_neg (not_le.2 (h q hq))
  rw [this, add_zero]

end StaticHedge

end MathFin.Contracts
