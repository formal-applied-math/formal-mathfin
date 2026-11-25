/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.Rates.DurationSensitivity
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Key-rate partials sum to the parallel-shift derivative

`MacaulayModified` prices a bond off a single flat yield, `P(y) = Σ cᵢ / (1 + y)^{tᵢ}`
(`bondPriceDisc`), and `DurationSensitivity` differentiates it: `P'(y) = -ModNum(y)`
(`hasDerivAt_bondPriceDisc`).
Key-rate analysis refines the flat yield to a curve: cashflow `i` is discounted at its own rate
`kᵢ` (one node per cashflow, not a tenor-indexed curve),

  `P(k) = Σ cᵢ / (1 + kᵢ)^{tᵢ}`     (`bondPriceKeyRate`).

The key-rate sensitivity to node `j` is the partial derivative `∂P/∂kⱼ`, the derivative of `P`
along the curve that moves `kⱼ` alone (`Function.update k j`). The key-rate duration is
`KRDⱼ = -(1/P)·∂P/∂kⱼ`. For the per-cash-flow nodes the results are stated for the partials; the
durations are defined on a tenor grid (`TenorGrid`), where the nodes are a few tenors, the rate at
every other tenor is interpolated from them, and the bump of a node is its hat function.

The identity that makes key rates a decomposition of duration: the partials sum to the
derivative under a parallel shift `k ↦ k + ε·1`. On a flat curve `k ≡ y` the parallel shift is
a move of the flat yield, so the sum is `dP/dy`, the derivative `hasDerivAt_bondPriceDisc`
computes.

## Main definitions

* `bondPriceKeyRate`: the bond price with cashflow `i` discounted at its own rate `k i`, with
  annual compounding.

* `TenorGrid`: the hat functions of the nodes, summing to `1`; `TenorGrid.rate` the interpolated
  rate and `TenorGrid.price` the price at it.
* `TenorGrid.piecewiseLinear`: linear interpolation between adjacent nodes, flat beyond the ends,
  with the hats built from clamped ramps (`TenorGrid.ramp`); `piecewiseLinear_rate_node` says the
  curve passes through the node rates.
* `TenorGrid.keyRateDuration`, `TenorGrid.effectiveDuration`: `-(1/P) ∂P/∂kⱼ` along the bump of node
  `j`, and `-(1/P) dP/dε` along the parallel shift of the nodes.

## Main results

* `bondPriceKeyRate_update_eq`: moving the spot rate of node `j ∈ s` to `x` leaves every other
  cashflow's term unchanged (used to prove both results below).
* `hasDerivAt_bondPriceKeyRate_update`: for `1 + kⱼ ≠ 0`, `∂P/∂kⱼ = -tⱼ·cⱼ / (1 + kⱼ)^{tⱼ+1}`,
  as a `HasDerivAt`.
* `hasDerivAt_bondPriceKeyRate_parallel`: on any curve, the parallel-shift derivative is
  `Σⱼ ∂P/∂kⱼ`, for any choice of witnesses `∂P/∂kⱼ`.
* `sum_keyRate_partials_eq_deriv_bondPriceDisc`, `sum_deriv_keyRate_eq_deriv_bondPriceDisc`:
  on a flat curve `k ≡ y` (`1 + y ≠ 0`), `Σⱼ ∂P/∂kⱼ = dP/dy` (`deriv (bondPriceDisc s t c) y`),
  for given partial-derivative witnesses and for the `deriv`s themselves.
* `TenorGrid.hasDerivAt_price_update`, `TenorGrid.hasDerivAt_price_parallel`: the node partials
  of the grid price and its parallel-shift derivative, in closed form.
* `TenorGrid.sum_keyRateDuration_eq_effectiveDuration`: the key-rate durations of the nodes sum to
  the effective duration of the parallel shift.

## References

* [Ho, *Key rate durations: measures of interest rate risks*][Ho1992]

## Tags

key rate duration, partial duration, parallel shift, yield curve sensitivity, bond risk,
spot rate node, MSC 91G30, JEL G12
-/

@[expose] public section

namespace MathFin

variable {ι : Type*}

/-- Bond price with cashflow `i` discounted at its own rate `k i` (one node per cashflow),
annual compounding. On a flat curve it is `bondPriceDisc`. -/
noncomputable def bondPriceKeyRate (s : Finset ι) (t : ι → ℕ) (c k : ι → ℝ) : ℝ :=
  ∑ i ∈ s, c i / (1 + k i) ^ t i

/-- On a flat curve the key-rate price is the flat-yield price `bondPriceDisc`. -/
theorem bondPriceKeyRate_const (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) :
    bondPriceKeyRate s t c (fun _ ↦ y) = bondPriceDisc s t c y := rfl

/-- Moving the spot rate of node `j ∈ s` to `x` changes only cashflow `j`'s discount term; the
rest of the curve's contribution is unchanged. -/
theorem bondPriceKeyRate_update_eq [DecidableEq ι] (s : Finset ι) (t : ι → ℕ) (c k : ι → ℝ)
    {j : ι} (hj : j ∈ s) (x : ℝ) :
    bondPriceKeyRate s t c (Function.update k j x) =
      c j / (1 + x) ^ t j + ∑ i ∈ s.erase j, c i / (1 + k i) ^ t i := by
  rw [bondPriceKeyRate, ← Finset.add_sum_erase s _ hj, Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- **Key-rate partial derivative.** Moving the spot rate of node `j ∈ s` alone moves only
cashflow `j`'s discount term, so, for `1 + kⱼ ≠ 0`, `∂P/∂kⱼ = -tⱼ·cⱼ / (1 + kⱼ)^{tⱼ+1}`: the
per-cashflow derivative `hasDerivAt_coupon_term` that `hasDerivAt_bondPriceDisc` sums. -/
theorem hasDerivAt_bondPriceKeyRate_update [DecidableEq ι] (s : Finset ι) (t : ι → ℕ)
    (c k : ι → ℝ) {j : ι} (hj : j ∈ s) (hk : 1 + k j ≠ 0) :
    HasDerivAt (fun x ↦ bondPriceKeyRate s t c (Function.update k j x))
      (-((t j : ℝ) * c j / (1 + k j) ^ (t j + 1))) (k j) := by
  simpa only [bondPriceKeyRate_update_eq s t c k hj] using
    (hasDerivAt_coupon_term (c j) (t j) hk).add_const _

/-- **Key-rate partials sum to the parallel-shift derivative.** On any curve `k`, if `D j` is
the partial derivative `∂P/∂kⱼ` for every node `j ∈ s`, then the price along the parallel shift
`ε ↦ P(k + ε·1)` has derivative `Σⱼ D j` at `ε = 0`. The partials are taken as hypotheses, so
the statement holds for whatever `∂P/∂kⱼ` is — `hasDerivAt_bondPriceKeyRate_update` computes one
such witness in closed form. -/
theorem hasDerivAt_bondPriceKeyRate_parallel [DecidableEq ι] (s : Finset ι) (t : ι → ℕ)
    (c k : ι → ℝ) {D : ι → ℝ}
    (hD : ∀ j ∈ s,
      HasDerivAt (fun x ↦ bondPriceKeyRate s t c (Function.update k j x)) (D j) (k j)) :
    HasDerivAt (fun ε ↦ bondPriceKeyRate s t c (fun i ↦ k i + ε)) (∑ j ∈ s, D j) 0 := by
  unfold bondPriceKeyRate
  refine HasDerivAt.fun_sum fun j hj ↦ ?_
  have h0 : HasDerivAt (fun x ↦ bondPriceKeyRate s t c (Function.update k j x)) (D j)
      (k j + 0) := by simpa using hD j hj
  simpa only [bondPriceKeyRate_update_eq s t c k hj, add_sub_cancel_right] using
    (h0.comp_const_add (k j) 0).sub_const (∑ i ∈ s.erase j, c i / (1 + k i) ^ t i)

/-- **`Σⱼ ∂P/∂kⱼ = dP/dy`.** On a flat curve `k ≡ y` (with `1 + y ≠ 0`), the key-rate partials
`D j = ∂P/∂kⱼ` sum to the derivative of the flat-yield price `bondPriceDisc` at `y`: a
parallel shift of a flat curve is a move of the yield, so `hasDerivAt_bondPriceKeyRate_parallel`
and `hasDerivAt_bondPriceDisc` compute the same derivative. -/
theorem sum_keyRate_partials_eq_deriv_bondPriceDisc [DecidableEq ι] (s : Finset ι) (t : ι → ℕ)
    (c : ι → ℝ) {y : ℝ} (hy : 1 + y ≠ 0) {D : ι → ℝ}
    (hD : ∀ j ∈ s, HasDerivAt
      (fun x ↦ bondPriceKeyRate s t c (Function.update (fun _ ↦ y) j x)) (D j) y) :
    ∑ j ∈ s, D j = deriv (bondPriceDisc s t c) y := by
  have hpar := hasDerivAt_bondPriceKeyRate_parallel s t c (fun _ ↦ y) hD
  have hflat : HasDerivAt (fun ε ↦ bondPriceKeyRate s t c (fun _ ↦ y + ε))
      (-modifiedNumerator s t c y) 0 := by
    have := (hasDerivAt_bondPriceDisc s t c (y := y + 0) (by simpa using hy)).comp_const_add y 0
    rwa [add_zero] at this
  rw [hpar.unique hflat, (hasDerivAt_bondPriceDisc s t c hy).deriv]

/-- **`Σⱼ ∂P/∂kⱼ = dP/dy`, with the partials as `deriv`s.** On a flat curve `k ≡ y`
(`1 + y ≠ 0`), the key-rate partial derivatives sum to the derivative of the flat-yield price
`bondPriceDisc` at `y`. Each partial exists by `hasDerivAt_bondPriceKeyRate_update`. -/
theorem sum_deriv_keyRate_eq_deriv_bondPriceDisc [DecidableEq ι] (s : Finset ι) (t : ι → ℕ)
    (c : ι → ℝ) {y : ℝ} (hy : 1 + y ≠ 0) :
    ∑ j ∈ s, deriv (fun x ↦ bondPriceKeyRate s t c (Function.update (fun _ ↦ y) j x)) y =
      deriv (bondPriceDisc s t c) y :=
  sum_keyRate_partials_eq_deriv_bondPriceDisc s t c hy fun _ hj ↦
    (hasDerivAt_bondPriceKeyRate_update s t c _ hj hy).differentiableAt.hasDerivAt

/-! ### Key-rate durations on a tenor grid

The nodes above are one per cash flow. A desk quotes the curve at a few tenors instead, and the
rate at every other tenor is interpolated from them. A **tenor grid** is the interpolation, the
hat function `hat j` of each node `j`, the weight of node `j`'s rate in the rate at tenor `u`.
The weights sum to `1`, so a parallel shift of the node rates is the same shift of the whole curve,
and the bump of one node is the bump of its hat function. -/

section TenorGrid

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A **tenor grid**: the hat function `hat j u` of each node `j`, the weight of node `j`'s rate in
the interpolated rate at tenor `u`, with the weights summing to `1` at every tenor. Piecewise-linear
interpolation with flat ends is one such grid, the hats of linear interpolation between adjacent
nodes. -/
structure TenorGrid (κ : Type*) [Fintype κ] where
  /-- The hat function of node `j`. -/
  hat : κ → ℝ → ℝ
  /-- The hat functions sum to `1`: the bumps of all nodes together are the constant `1`. -/
  sum_hat : ∀ u, ∑ j, hat j u = 1

namespace TenorGrid

variable (G : TenorGrid κ)

/-- The **interpolated zero rate** at tenor `u` from the node rates `k`: `∑ⱼ kⱼ · hat j u`. -/
noncomputable def rate (k : κ → ℝ) (u : ℝ) : ℝ := ∑ j, k j * G.hat j u

/-- The **price of the cash flows `c i` at the integer tenors `t i`** on the grid curve with node
rates `k`: the key-rate price (`bondPriceKeyRate`) at the interpolated rates. -/
noncomputable def price (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (k : κ → ℝ) : ℝ :=
  bondPriceKeyRate s t c fun i ↦ G.rate k (t i)

/-- A parallel shift of the node rates is the same shift of the interpolated curve. -/
theorem rate_add_const (k : κ → ℝ) (ε u : ℝ) : G.rate (fun j ↦ k j + ε) u = G.rate k u + ε := by
  simp only [rate, add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, G.sum_hat, mul_one]

/-- Moving the rate of node `j` alone to `x` moves the interpolated rate at tenor `u` by
`(x - kⱼ) · hat j u`. -/
theorem rate_update (k : κ → ℝ) (j : κ) (x u : ℝ) :
    G.rate (Function.update k j x) u = G.rate k u + (x - k j) * G.hat j u := by
  have h1 := Finset.add_sum_erase Finset.univ (fun i ↦ Function.update k j x i * G.hat i u)
    (Finset.mem_univ j)
  have h2 := Finset.add_sum_erase Finset.univ (fun i ↦ k i * G.hat i u) (Finset.mem_univ j)
  have e : ∑ i ∈ Finset.univ.erase j, Function.update k j x i * G.hat i u
      = ∑ i ∈ Finset.univ.erase j, k i * G.hat i u :=
    Finset.sum_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [rate]
  rw [← h1, ← h2, e, Function.update_self]
  ring

variable {G}

/-- **Key-rate partial derivative on a grid.** Bumping the rate of node `j` bumps the curve by its
hat function, so, when every interpolated rate has `1 + r ≠ 0`, `∂P/∂kⱼ = -∑ᵢ tᵢ cᵢ hat j tᵢ /
(1 + rᵢ)^{tᵢ+1}`, the per-cash-flow derivatives weighted by the hat. -/
theorem hasDerivAt_price_update (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (k : κ → ℝ) (j : κ)
    (hk : ∀ i ∈ s, 1 + G.rate k (t i) ≠ 0) :
    HasDerivAt (fun x ↦ G.price s t c (Function.update k j x))
      (∑ i ∈ s, -((t i : ℝ) * c i / (1 + G.rate k (t i)) ^ (t i + 1)) * G.hat j (t i)) (k j) := by
  unfold price bondPriceKeyRate
  refine HasDerivAt.fun_sum fun i hi ↦ ?_
  have e : (fun x ↦ c i / (1 + G.rate (Function.update k j x) (t i)) ^ t i)
      = fun x ↦ c i / (1 + (G.rate k (t i) + (x - k j) * G.hat j (t i))) ^ t i :=
    funext fun x ↦ by rw [G.rate_update]
  have hin : HasDerivAt (fun x ↦ G.rate k (t i) + (x - k j) * G.hat j (t i)) (G.hat j (t i))
      (k j) := by
    simpa using (((hasDerivAt_id (k j)).sub_const (k j)).mul_const (G.hat j (t i))).const_add
      (G.rate k (t i))
  have hc := (hasDerivAt_coupon_term (c i) (t i)
    (y := G.rate k (t i) + (k j - k j) * G.hat j (t i)) (by simpa using hk i hi)).comp (k j) hin
  change HasDerivAt (fun x ↦ c i / (1 + G.rate (Function.update k j x) (t i)) ^ t i) _ _
  rw [e]
  exact hc.congr_deriv (by ring)

/-- **The parallel-shift derivative on a grid.** On the grid curve with node rates `k`, the price
along `ε ↦ P(k + ε·1)` has derivative `-∑ᵢ tᵢ cᵢ / (1 + rᵢ)^{tᵢ+1}` at `0`, since a parallel shift
of the nodes shifts every interpolated rate by `ε` (`rate_add_const`). -/
theorem hasDerivAt_price_parallel (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (k : κ → ℝ)
    (hk : ∀ i ∈ s, 1 + G.rate k (t i) ≠ 0) :
    HasDerivAt (fun ε ↦ G.price s t c fun j ↦ k j + ε)
      (∑ i ∈ s, -((t i : ℝ) * c i / (1 + G.rate k (t i)) ^ (t i + 1))) 0 := by
  unfold price bondPriceKeyRate
  refine HasDerivAt.fun_sum fun i hi ↦ ?_
  have e : (fun ε ↦ c i / (1 + G.rate (fun j ↦ k j + ε) (t i)) ^ t i)
      = fun ε ↦ c i / (1 + (G.rate k (t i) + ε)) ^ t i :=
    funext fun ε ↦ by rw [G.rate_add_const]
  have hc := (hasDerivAt_coupon_term (c i) (t i) (y := G.rate k (t i) + 0)
    (by simpa using hk i hi)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_add (G.rate k (t i)))
  change HasDerivAt (fun ε ↦ c i / (1 + G.rate (fun j ↦ k j + ε) (t i)) ^ t i) _ _
  rw [e]
  exact hc

variable (G)

/-- The **key-rate duration** of node `j`: `KRDⱼ = -(1/P) ∂P/∂kⱼ`, the partial derivative of the
price along the bump of node `j` (`Function.update`), relative to the price. -/
noncomputable def keyRateDuration (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (k : κ → ℝ) (j : κ) :
    ℝ :=
  -deriv (fun x ↦ G.price s t c (Function.update k j x)) (k j) / G.price s t c k

/-- The **effective duration** of the grid curve: `-(1/P) dP/dε` along the parallel shift
`k ↦ k + ε·1` of the node rates, at `ε = 0`. -/
noncomputable def effectiveDuration (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (k : κ → ℝ) : ℝ :=
  -deriv (fun ε ↦ G.price s t c fun j ↦ k j + ε) 0 / G.price s t c k

/-- **The key-rate durations sum to the effective duration.** On any grid curve with `1 + rᵢ ≠ 0`
at the cash-flow tenors, the key-rate durations of the nodes sum to the effective duration of the
parallel shift: the bumps of the nodes sum to the constant `1` (`sum_hat`), so the node partials
sum to the parallel-shift derivative. -/
theorem sum_keyRateDuration_eq_effectiveDuration (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ)
    (k : κ → ℝ) (hk : ∀ i ∈ s, 1 + G.rate k (t i) ≠ 0) :
    ∑ j, G.keyRateDuration s t c k j = G.effectiveDuration s t c k := by
  have hsum : ∑ j, deriv (fun x ↦ G.price s t c (Function.update k j x)) (k j)
      = deriv (fun ε ↦ G.price s t c fun j ↦ k j + ε) 0 := by
    have h1 (j : κ) : deriv (fun x ↦ G.price s t c (Function.update k j x)) (k j)
        = ∑ i ∈ s, -((t i : ℝ) * c i / (1 + G.rate k (t i)) ^ (t i + 1)) * G.hat j (t i) :=
      (hasDerivAt_price_update s t c k j hk).deriv
    simp only [h1]
    rw [(hasDerivAt_price_parallel s t c k hk).deriv, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.mul_sum, G.sum_hat, mul_one]
  simp only [keyRateDuration, effectiveDuration, ← Finset.sum_div, Finset.sum_neg_distrib, hsum]

/-! #### Piecewise-linear interpolation

Between adjacent nodes the rate is interpolated linearly, and beyond the first and last nodes it is
held flat. The hat functions are built from **ramps**: `ramp τ m` climbs linearly from `0` at the
node `τ m` to `1` at the node `τ (m + 1)` and is clamped outside. The node `j` has weight
`1` below its left neighbour's ramp and `0` above its right neighbour's, `hat j = cum j − cum (j+1)`
with `cum j` the ramp from node `j − 1` to node `j` (`1` before the first node, `0` after the
last), so the hats telescope to `1`. -/

/-- The **ramp** from node `m` to node `m + 1`: `0` up to `τ m`, linear to `1` at `τ (m + 1)`, and
`1` after. -/
noncomputable def ramp (τ : ℕ → ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  max 0 (min 1 ((u - τ m) / (τ (m + 1) - τ m)))

/-- The ramp up to node `j` among the nodes `0, …, n`: the constant `1` for `j = 0`, the ramp from
node `j − 1` for `1 ≤ j ≤ n`, and the constant `0` beyond the last node. -/
noncomputable def cumRamp (τ : ℕ → ℝ) (n j : ℕ) (u : ℝ) : ℝ :=
  if j = 0 then 1 else if j ≤ n then ramp τ (j - 1) u else 0

/-- At the nodes of a strictly increasing grid the ramp from `m` is `1` past `m`, `0` up to it. -/
theorem ramp_node {τ : ℕ → ℝ} (hτ : StrictMono τ) (m i : ℕ) :
    ramp τ m (τ i) = if m < i then 1 else 0 := by
  have hd : 0 < τ (m + 1) - τ m := sub_pos.2 (hτ (Nat.lt_succ_self m))
  unfold ramp
  split_ifs with h
  · have h1 : 1 ≤ (τ i - τ m) / (τ (m + 1) - τ m) := by
      rw [le_div_iff₀ hd]
      linarith [hτ.monotone (show m + 1 ≤ i from h)]
    rw [min_eq_left h1, max_eq_right zero_le_one]
  · have h1 : (τ i - τ m) / (τ (m + 1) - τ m) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [hτ.monotone (not_lt.1 h)]) hd.le
    rw [min_eq_right (h1.trans zero_le_one), max_eq_left h1]

/-- At the node `τ i`, `i ≤ n`, the ramp up to node `j` is `1` for `j ≤ i` and `0` after. -/
theorem cumRamp_node {τ : ℕ → ℝ} (hτ : StrictMono τ) {n i : ℕ} (hi : i ≤ n) (j : ℕ) :
    cumRamp τ n j (τ i) = if j ≤ i then 1 else 0 := by
  unfold cumRamp
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · rw [if_neg hj.ne']
    by_cases hjn : j ≤ n
    · rw [if_pos hjn, ramp_node hτ]
      by_cases hji : j ≤ i
      · rw [if_pos (show j - 1 < i by omega), if_pos hji]
      · rw [if_neg (show ¬ j - 1 < i by omega), if_neg hji]
    · rw [if_neg hjn, if_neg (show ¬ j ≤ i by omega)]

/-- **The piecewise-linear tenor grid** on the nodes `τ 0, …, τ n`: the hat of node `j` is
`cum j − cum (j + 1)` (`cumRamp`), so the hats telescope to `1`. -/
noncomputable def piecewiseLinear (τ : ℕ → ℝ) (n : ℕ) : TenorGrid (Fin (n + 1)) where
  hat j u := cumRamp τ n j u - cumRamp τ n ((j : ℕ) + 1) u
  sum_hat u := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ cumRamp τ n j u - cumRamp τ n (j + 1) u) (n + 1),
      Finset.sum_range_sub' (fun j ↦ cumRamp τ n j u) (n + 1)]
    simp [cumRamp]

/-- **The hat of node `j` is `1` at its own tenor and `0` at the other nodes.** -/
theorem piecewiseLinear_hat_node {τ : ℕ → ℝ} (hτ : StrictMono τ) (n : ℕ) (i j : Fin (n + 1)) :
    (piecewiseLinear τ n).hat j (τ i) = if i = j then 1 else 0 := by
  have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.2
  show cumRamp τ n j (τ i) - cumRamp τ n ((j : ℕ) + 1) (τ i) = _
  rw [cumRamp_node hτ hi, cumRamp_node hτ hi]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h]
    rcases lt_or_gt_of_ne (fun e : (j : ℕ) = i ↦ h (Fin.ext e.symm)) with h1 | h1
    · have a : (j : ℕ) ≤ i := h1.le
      have b : (j : ℕ) + 1 ≤ i := h1
      simp [a, b]
    · have a : ¬ (j : ℕ) ≤ i := not_le.2 h1
      have b : ¬ (j : ℕ) + 1 ≤ i := by omega
      simp [a, b]

/-- **The interpolated curve passes through the node rates**: at the tenor `τ i` of node `i` the
rate is `k i`. -/
theorem piecewiseLinear_rate_node {τ : ℕ → ℝ} (hτ : StrictMono τ) (n : ℕ) (k : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : (piecewiseLinear τ n).rate k (τ i) = k i := by
  simp [rate, piecewiseLinear_hat_node hτ]

end TenorGrid

end TenorGrid

end MathFin
