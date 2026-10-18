/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Aave v2: kinked interest-rate model, health factor, liquidity index

Adapted from the Aave v2 whitepaper (Aave, "Aave Protocol V2", 2020,
<https://github.com/aave/protocol-v2/blob/master/aave-v2-whitepaper.pdf>),
§3.2 ("Interest rate model") and §4 ("Health factor").

## Results

* `kinkedRate`: the piecewise-linear borrow-rate curve.
* `kinkedRate_apply_optimal`: the rate at the kink, `R₀ + slope1` — the
  common value both branches take at `U = U_opt` (this does not by itself
  establish `ContinuousAt`, which would additionally need `Uopt ≠ 1`).
* `kinkedRate_monotone`: the curve is monotone nondecreasing on `[0, 1]`
  when both slopes are nonnegative.
* `healthFactorV1`, `healthFactorV2`: the single-asset and multi-asset
  (summed) health-factor definitions.
* `liquidityIndexStep`, `liquidityIndex_closedForm`: the linear recurrence
  `LI_t = (R_t·U_t·ΔT/T_year + 1)·LI_{t-1}`
  and its closed-form (product) solution. **Scope disclosure**: the
  whitepaper's per-period factor is `LiquidityRate_t·ΔT/T_year + 1`, where
  `LiquidityRate = BorrowRate·U·(1 − reserveFactor)`; `R` here stands for
  `BorrowRate` and the recurrence omits `(1 − reserveFactor)` (equivalently,
  the `reserveFactor = 0` simplification).
* `stableRateUpdate`: the weighted-average new stable rate, shown (when the
  new borrower's rate is at least the pool's prior average) to lie between
  the two (a weighted average is a convex combination).
-/

@[expose] public section

namespace MathFin

namespace DeFi

namespace Aave

/-- **Aave v2 kinked borrow-rate model** (whitepaper §3.2): below the optimal
utilization `U_opt`, the rate rises linearly from `R₀` with slope `slope1/U_opt`;
above it, it rises linearly from `R₀ + slope1` with slope `slope2/(1-U_opt)`.
`U_opt ∈ (0,1)` is the kink location. -/
noncomputable def kinkedRate (R₀ slope1 slope2 Uopt U : ℝ) : ℝ :=
  if U ≤ Uopt then R₀ + U / Uopt * slope1
  else R₀ + slope1 + (U - Uopt) / (1 - Uopt) * slope2

/-- **The rate at the kink** is `R₀ + slope1` — the value the `U ≤ Uopt`
branch takes at `U = Uopt`, which is also what the `else` branch would give
there (it is excluded from this `if`, but both expressions agree, which is
what makes the curve a genuine piecewise-linear function with no jump).
This lemma states the kink value only; it is not a `ContinuousAt` claim. -/
theorem kinkedRate_apply_optimal (R₀ slope1 slope2 Uopt : ℝ) (hU : Uopt ≠ 0) :
    kinkedRate R₀ slope1 slope2 Uopt Uopt = R₀ + slope1 := by
  unfold kinkedRate
  rw [if_pos le_rfl, div_self hU, one_mul]

/-- **Monotonicity on `[0,1]`**: if both slopes are nonnegative, the kinked
rate is monotone nondecreasing in utilization `U`. -/
theorem kinkedRate_monotone {R₀ slope1 slope2 Uopt : ℝ}
    (hUopt0 : 0 < Uopt) (hUopt1 : Uopt < 1)
    (hs1 : 0 ≤ slope1) (hs2 : 0 ≤ slope2) :
    MonotoneOn (kinkedRate R₀ slope1 slope2 Uopt) (Set.Icc 0 1) := by
  intro U hU V hV hUV
  simp only [Set.mem_Icc] at hU hV
  unfold kinkedRate
  have h1mUopt : 0 < 1 - Uopt := by linarith
  by_cases hUle : U ≤ Uopt <;> by_cases hVle : V ≤ Uopt
  · rw [if_pos hUle, if_pos hVle]
    gcongr
  · rw [if_pos hUle, if_neg hVle]
    have h1 : U / Uopt * slope1 ≤ slope1 :=
      mul_le_of_le_one_left hs1 ((div_le_one hUopt0).mpr hUle)
    have h2 : 0 ≤ (V - Uopt) / (1 - Uopt) * slope2 :=
      mul_nonneg (div_nonneg (by linarith [not_le.mp hVle]) h1mUopt.le) hs2
    linarith
  · exact absurd ((not_le.mp hUle).trans_le (hUV.trans hVle)) (lt_irrefl _)
  · rw [if_neg hUle, if_neg hVle]
    have : (U - Uopt) / (1 - Uopt) ≤ (V - Uopt) / (1 - Uopt) :=
      (div_le_div_iff_of_pos_right h1mUopt).mpr (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right this hs2]

/-- **Aave v1/v2 single-asset health factor**: collateral weighted by its
liquidation threshold, over total debt (borrows plus accrued fees). Values
`> 1` indicate a safe position. -/
noncomputable def healthFactorV1 (collateral liquidationThreshold borrows fees : ℝ) : ℝ :=
  collateral * liquidationThreshold / (borrows + fees)

/-- **Health factor safety criterion**: `Hf > 1 ↔ collateral·LT > debt`, when
total debt is positive. -/
theorem healthFactorV1_gt_one_iff
    {collateral liquidationThreshold borrows fees : ℝ} (hdebt : 0 < borrows + fees) :
    1 < healthFactorV1 collateral liquidationThreshold borrows fees ↔
      borrows + fees < collateral * liquidationThreshold := by
  unfold healthFactorV1
  rw [lt_div_iff₀ hdebt, one_mul]

/-- **Aave v2 multi-asset health factor**: summed over the borrower's
assets `i ∈ s`, collateral weighted by each asset's liquidation threshold
over total borrows across assets. -/
noncomputable def healthFactorV2 {ι : Type*} (s : Finset ι)
    (collateral liquidationThreshold borrows : ι → ℝ) : ℝ :=
  (∑ i ∈ s, collateral i * liquidationThreshold i) / ∑ i ∈ s, borrows i

/-- **Multi-asset health factor safety criterion**, the `healthFactorV2`
analogue of `healthFactorV1_gt_one_iff`. -/
theorem healthFactorV2_gt_one_iff {ι : Type*} {s : Finset ι}
    {collateral liquidationThreshold borrows : ι → ℝ}
    (hdebt : 0 < ∑ i ∈ s, borrows i) :
    1 < healthFactorV2 s collateral liquidationThreshold borrows ↔
      ∑ i ∈ s, borrows i < ∑ i ∈ s, collateral i * liquidationThreshold i := by
  unfold healthFactorV2
  rw [lt_div_iff₀ hdebt, one_mul]

/-- **Aave v2 liquidity-index recurrence** (whitepaper §3.3): the index
accrues each period by the per-period yield `R · U · ΔT / T_year`, where `R`
stands for the borrow rate. **Scope disclosure**: the whitepaper's per-period
factor is `LiquidityRate·ΔT/T_year + 1` with
`LiquidityRate = BorrowRate·U·(1 − reserveFactor)`; this definition omits the
`(1 − reserveFactor)` factor (the `reserveFactor = 0` simplification). -/
noncomputable def liquidityIndexStep (R U ΔT Tyear : ℝ) : ℝ :=
  R * U * ΔT / Tyear + 1

/-- **Closed form of the liquidity-index recurrence**: given a sequence
`LI` satisfying `LI (n+1) = liquidityIndexStep (R (n+1)) (U (n+1)) ΔT Tyear * LI n`
for every step, the index after `n` steps equals the initial index times the
product of all per-step growth factors. Proved by induction on `n`. -/
theorem liquidityIndex_closedForm
    (LI R U : ℕ → ℝ) (ΔT Tyear : ℝ)
    (hrec : ∀ n, LI (n + 1) = liquidityIndexStep (R (n + 1)) (U (n + 1)) ΔT Tyear * LI n) :
    ∀ n, LI n = (∏ t ∈ Finset.range n, liquidityIndexStep (R (t + 1)) (U (t + 1)) ΔT Tyear) * LI 0
  | 0 => by simp
  | (n + 1) => by
      rw [hrec n, liquidityIndex_closedForm LI R U ΔT Tyear hrec n,
        Finset.prod_range_succ]
      ring

/-- **Aave v2 stable-rate weighted average** (whitepaper §3.4): when a new
stable-rate borrow of size `SBnew` at rate `SRnew` joins an existing stable
debt pool `SDprev` at average rate `SRprev`, the new pool average is the
debt-weighted mean of the two rates. -/
noncomputable def stableRateUpdate (SRprev SDprev SRnew SBnew : ℝ) : ℝ :=
  (SRprev * SDprev + SRnew * SBnew) / (SDprev + SBnew)

/-- **The updated stable rate is a convex combination** of the previous
average and the new borrower's rate, hence lies between them **when the new
borrower's rate is at least the prior average** (`hle : SRprev ≤ SRnew`). A
weighted average with nonnegative weights and positive total weight cannot
exceed (resp. fall below) the larger (resp. smaller) of the two inputs. -/
theorem stableRateUpdate_mem_interval
    {SRprev SDprev SRnew SBnew : ℝ}
    (hSDprev : 0 ≤ SDprev) (hSBnew : 0 < SBnew) (hle : SRprev ≤ SRnew) :
    SRprev ≤ stableRateUpdate SRprev SDprev SRnew SBnew ∧
      stableRateUpdate SRprev SDprev SRnew SBnew ≤ SRnew := by
  unfold stableRateUpdate
  have hden : 0 < SDprev + SBnew := by linarith
  constructor
  · rw [le_div_iff₀ hden]; nlinarith
  · rw [div_le_iff₀ hden]; nlinarith

end Aave

end DeFi

end MathFin
