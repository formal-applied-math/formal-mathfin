/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Instruments.FixedIncome

/-!
# The autocallable note, as a contract

An autocallable note observes an underlying `S` at the dates `t₀ < ⋯ < t_{n-1}`. At the first
observation `tₖ` with `S_{tₖ} ≥ B` (the autocall barrier) it redeems the notional together with
the coupons accrued, `1 + (k+1) c` per unit of notional, and terminates. If no observation
reaches `B`, it redeems at the maturity `T`: the notional if `S_T ≥ P` (the protection barrier),
and the fraction `S_T / S₀` of it otherwise, a down-and-in put on the capital.

**The existing constructors suffice.** The contract language's spec
(`docs/specs/2026-08-16-contracts-tower-design.md` §2.3) expected the first autocall to force a
branching constructor and a lifecycle layer. It does not: "the first date at which" is a product of
indicators that the earlier observations were below `B` (`survivalPayoff`), so the note is a
`payFlows` schedule whose `k`-th payoff is that survival indicator times the redemption times the
indicator that `S_{tₖ} ≥ B`, plus one `pay` at `T`. `autocallUnit` is that contract, at fixed
dates, so every model-free theorem of `Pricing/Value.lean` applies to it.

What is *not* in this encoding, and a reader should know: termination is a fact about each
scenario (`cashflows_autocallUnit_of_firstAbove`), not a structural one: the contract lists a
payment at every date, and all but one amount are `0` along every path. There is no calendar, no
business-day convention, no issuer credit risk, no discrete-coupon memory beyond the
`(k+1) c` accrual, and the observations are discrete; the underlying is one asset.

## Main definitions

* `Scenario.FirstAbove` — the `k`-th observation is the first at or above the barrier; by
  `Scenario.firstAbove_iff_hittingAfter` it is Mathlib's discrete `hittingAfter` of the sampled
  process, the grid case of the language's `Scenario.hitTime`.
* `survivalPayoff` — the indicator that the first `k` observations are all below the barrier.
* `redemptionPayoff`, `maturityPayoff` — the early redemption at date `k`, and the maturity
  redemption with its protection barrier.
* `autocallUnit` — the note per unit of notional; `autocall` — the note on a notional `N`.

## Main results

* `eval_redemptionPayoff` — the `k`-th payoff is the redemption on the scenarios where `k` is the
  first autocall date and `0` otherwise.
* `cashflows_autocallUnit_of_firstAbove` — if the barrier is reached, the cash flows are a single
  redemption at the first autocall date: every other amount is `0`.
* `cashflows_autocallUnit_of_forall_lt` — if it is not, every early amount is `0` and the
  maturity amount is the protected redemption.
* `pathPV_autocallUnit_of_firstAbove`, `pathPV_autocallUnit_of_forall_lt` — the same for the
  present value under any discount function.
* `pathPV_autocallUnit_mono_coupon` — with nonnegative discount factors at observation dates,
  the present value is nondecreasing in the coupon.
* `pathPV_autocallUnit_le` bounds the value by `1 + n c` discounted at the first observation.
  It assumes at least one observation, a nonnegative coupon, a positive initial fixing, a
  protection barrier at most that fixing, and nonincreasing discount factors nonnegative through
  maturity. Every observation falls between the first observation and maturity.
* `autocallUnit_fixedDated` — the note pays at fixed dates.

## Source

The layered separation of contract semantics from pricing semantics, and the
framing "the contract is not the model", are due to Paul Bilokon,
*The Contract Is Not the Model: Proof-Carrying Exotic Derivatives and the
Economics of Model Risk* (working paper, 9 August 2026; Mathematical
Finance, Imperial College London), with code at
<https://github.com/thalesians/lean_contracts> (Apache-2.0). That paper in
turn builds on the compositional contract-DSL of
Peyton Jones, Eber and Seward (2000) and the certified-contract work of Bahr,
Berthold and Elsman (2015) and Annenkov (2018).

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [M. Bouzoubaa and A. Osseiran, *Exotic Options and Hybrids*][BouzoubaaOsseiran2010], ch. 12

## Tags

autocallable, autocall, structured product, barrier, protection barrier, knock-in put,
first-passage decomposition, MSC 91G20, JEL G13
-/

@[expose] public section

open scoped NNReal Classical

namespace MathFin.Contracts

variable {ι : Type*}

/-- The `k`-th observation of underlying `i` at the dates `t` is the **first** at or above the
barrier `B`: it reaches `B`, and every earlier observation is below. -/
def Scenario.FirstAbove (s : Scenario ι) (i : ι) (t : ℕ → ℝ≥0) (B : ℝ) (k : ℕ) : Prop :=
  B ≤ s i (t k) ∧ ∀ j < k, s i (t j) < B

/-- The first autocall date is unique. -/
theorem Scenario.FirstAbove.unique {s : Scenario ι} {i : ι} {t : ℕ → ℝ≥0} {B : ℝ} {k j : ℕ}
    (hk : s.FirstAbove i t B k) (hj : s.FirstAbove i t B j) : k = j := by
  rcases lt_trichotomy k j with h | h | h
  · exact absurd hk.1 (not_le.2 (hj.2 k h))
  · exact h
  · exact absurd hj.1 (not_le.2 (hk.2 j h))

/-- **`FirstAbove` is Mathlib's discrete hitting time.** The `k`-th observation of underlying `i` at
the dates `t` is the first at or above `B` exactly when `hittingAfter` (from time `0`) of the
sampled process `k ↦ s i (t k)` at the set `[B, ∞)` is `k`. So the autocall's first date is the
one object of the language's `Scenario.hitTime`, `hittingAfter` of `u ↦ s i u`, read on the grid of
observation dates: the `FirstAbove` predicate is the explicit form of the discrete case. -/
theorem Scenario.firstAbove_iff_hittingAfter (s : Scenario ι) (i : ι) (t : ℕ → ℝ≥0) (B : ℝ)
    (k : ℕ) :
    s.FirstAbove i t B k ↔
      MeasureTheory.hittingAfter (fun (j : ℕ) (s : Scenario ι) ↦ s i (t j)) (Set.Ici B) 0 s
        = (k : WithTop ℕ) := by
  have hle (m : ℕ) :
      MeasureTheory.hittingAfter (fun (j : ℕ) (s : Scenario ι) ↦ s i (t j)) (Set.Ici B) 0 s
        ≤ (m : WithTop ℕ) ↔ ∃ j ∈ Set.Icc 0 m, B ≤ s i (t j) :=
    MeasureTheory.hittingAfter_le_iff
  have hlt (m : ℕ) :
      MeasureTheory.hittingAfter (fun (j : ℕ) (s : Scenario ι) ↦ s i (t j)) (Set.Ici B) 0 s
        < (m : WithTop ℕ) ↔ ∃ j ∈ Set.Ico 0 m, B ≤ s i (t j) :=
    MeasureTheory.hittingAfter_lt_iff
  constructor
  · rintro ⟨hk, hbelow⟩
    refine le_antisymm ((hle k).2 ⟨k, ⟨Nat.zero_le _, le_rfl⟩, hk⟩) (not_lt.1 fun h ↦ ?_)
    obtain ⟨j, hj, hjB⟩ := (hlt k).1 h
    exact absurd hjB (not_le.2 (hbelow j hj.2))
  · intro h
    have h1 := (hle k).1 h.le
    have h2 : ¬ ∃ j ∈ Set.Ico 0 k, B ≤ s i (t j) := fun h' ↦ ((hlt k).2 h').ne h
    have h3 : ∀ j < k, s i (t j) < B := fun j hj ↦
      not_le.1 fun hB ↦ h2 ⟨j, ⟨Nat.zero_le _, hj⟩, hB⟩
    obtain ⟨j, hj, hjB⟩ := h1
    have hjk : j = k := by
      by_contra hne
      exact absurd hjB (not_le.2 (h3 j (lt_of_le_of_ne hj.2 hne)))
    subst hjk
    exact ⟨hjB, h3⟩

/-- If some observation among the first `n` reaches the barrier, there is a first one. -/
theorem Scenario.exists_firstAbove {s : Scenario ι} {i : ι} {t : ℕ → ℝ≥0} {B : ℝ} {n : ℕ}
    (h : ∃ k < n, B ≤ s i (t k)) : ∃ k < n, s.FirstAbove i t B k := by
  have h' : ∃ k, k < n ∧ B ≤ s i (t k) := h
  refine ⟨Nat.find h', (Nat.find_spec h').1, (Nat.find_spec h').2, fun j hj ↦ ?_⟩
  by_contra hcon
  exact Nat.find_min h' hj ⟨hj.trans (Nat.find_spec h').1, not_lt.1 hcon⟩

/-- The indicator that the first `k` observations of underlying `i` at the dates `t` are all
below the barrier `B`: the product of the indicators `1{S_{tⱼ} < B}`, `j < k`. -/
noncomputable def survivalPayoff (i : ι) (t : ℕ → ℝ≥0) (B : ℝ) : ℕ → Payoff ι
  | 0 => .const 1
  | k + 1 => .mul (survivalPayoff i t B k) (.indicatorLt (.obs i (t k)) (.const B))

/-- The survival indicator is `1` exactly when the first `k` observations are all below `B`. -/
theorem eval_survivalPayoff (s : Scenario ι) (i : ι) (t : ℕ → ℝ≥0) (B : ℝ) (k : ℕ) :
    (survivalPayoff i t B k).eval s = if ∀ j < k, s i (t j) < B then 1 else 0 := by
  induction k with
  | zero => simp [survivalPayoff, Payoff.eval]
  | succ k ih =>
    have key : (∀ j < k + 1, s i (t j) < B) ↔ (∀ j < k, s i (t j) < B) ∧ s i (t k) < B :=
      ⟨fun h ↦ ⟨fun j hj ↦ h j (by omega), h k (by omega)⟩, fun ⟨h1, h2⟩ j hj ↦ by
        rcases Nat.lt_or_ge j k with h | h
        · exact h1 j h
        · obtain rfl : j = k := by omega
          exact h2⟩
    change (survivalPayoff i t B k).eval s * (if s i (t k) < B then 1 else 0) = _
    rw [ih]
    by_cases h1 : ∀ j < k, s i (t j) < B <;> by_cases h2 : s i (t k) < B
    · rw [if_pos h1, if_pos h2, if_pos (key.2 ⟨h1, h2⟩)] <;> ring
    · rw [if_pos h1, if_neg h2, if_neg (fun h ↦ h2 (key.1 h).2)] <;> ring
    · rw [if_neg h1, if_pos h2, if_neg (fun h ↦ h1 (key.1 h).1)] <;> ring
    · rw [if_neg h1, if_neg h2, if_neg (fun h ↦ h1 (key.1 h).1)] <;> ring

/-- The early redemption at the `k`-th date: the survival indicator, times `1 + (k+1) c` (the
notional and the `k+1` coupons accrued), times the indicator `1{S_{tₖ} ≥ B}`. -/
noncomputable def redemptionPayoff (i : ι) (t : ℕ → ℝ≥0) (B c : ℝ) (k : ℕ) : Payoff ι :=
  .mul (survivalPayoff i t B k) (.mul (.const (1 + ((k : ℝ) + 1) * c))
    (.sub (.const 1) (.indicatorLt (.obs i (t k)) (.const B))))

/-- The `k`-th payoff is the redemption `1 + (k+1) c` on the scenarios where `k` is the first
autocall date, and `0` otherwise. -/
theorem eval_redemptionPayoff (s : Scenario ι) (i : ι) (t : ℕ → ℝ≥0) (B c : ℝ) (k : ℕ) :
    (redemptionPayoff i t B c k).eval s
      = if s.FirstAbove i t B k then 1 + ((k : ℝ) + 1) * c else 0 := by
  change (survivalPayoff i t B k).eval s *
    ((1 + ((k : ℝ) + 1) * c) * (1 - if s i (t k) < B then 1 else 0)) = _
  rw [eval_survivalPayoff]
  by_cases h1 : ∀ j < k, s i (t j) < B
  · by_cases h2 : s i (t k) < B
    · have h3 : ¬ s.FirstAbove i t B k := fun h ↦ absurd h.1 (not_le.2 h2)
      rw [if_pos h1, if_pos h2, if_neg h3] <;> ring
    · have h3 : s.FirstAbove i t B k := ⟨not_lt.1 h2, h1⟩
      rw [if_pos h1, if_neg h2, if_pos h3] <;> ring
  · have h3 : ¬ s.FirstAbove i t B k := fun h ↦ h1 h.2
    rw [if_neg h1, if_neg h3] <;> ring

/-- The maturity redemption with its protection barrier `P` and initial fixing `S₀`: the notional
if `S_T ≥ P`, and the fraction `S_T / S₀` of it otherwise. For `P ≤ S₀` the shortfall
`1 − S_T / S₀` below `P` is what a down-and-in put struck at `S₀` pays per unit of notional. -/
noncomputable def maturityPayoff (i : ι) (P S₀ : ℝ) (T : ℝ≥0) : Payoff ι :=
  .add (.sub (.const 1) (.indicatorLt (.obs i T) (.const P)))
    (.mul (.indicatorLt (.obs i T) (.const P)) (.mul (.const S₀⁻¹) (.obs i T)))

/-- The maturity redemption is `1` at or above the protection barrier and `S_T / S₀` below. -/
theorem eval_maturityPayoff (s : Scenario ι) (i : ι) (P S₀ : ℝ) (T : ℝ≥0) :
    (maturityPayoff i P S₀ T).eval s = if P ≤ s i T then 1 else S₀⁻¹ * s i T := by
  change (1 - if s i T < P then 1 else 0) +
    (if s i T < P then 1 else 0) * (S₀⁻¹ * s i T) = _
  by_cases h : s i T < P
  · rw [if_pos h, if_neg (not_le.2 h)] <;> ring
  · rw [if_neg h, if_pos (not_lt.1 h)] <;> ring

/-- **The autocallable note per unit of notional**, observing underlying `i` at the dates `t k`,
`k < n`, with autocall barrier `B`, coupon `c` per period, initial fixing `S₀`, protection barrier
`P` and maturity `T`. At the `k`-th date it pays `1 + (k+1) c` if that is the first date at or
above `B` (`redemptionPayoff`); at `T` it pays the protected redemption (`maturityPayoff`) if no
date was. `eval_redemptionPayoff` and `cashflows_autocallUnit_of_firstAbove` show it does what
this says. -/
noncomputable def autocallUnit (i : ι) (t : ℕ → ℝ≥0) (n : ℕ) (B c S₀ P : ℝ) (T : ℝ≥0) :
    Contract ι :=
  .both (payFlows t (redemptionPayoff i t B c) n)
    (.pay T (.mul (survivalPayoff i t B n) (maturityPayoff i P S₀ T)))

/-- The autocallable note on the notional `N`. -/
noncomputable def autocall (N : ℝ) (i : ι) (t : ℕ → ℝ≥0) (n : ℕ) (B c S₀ P : ℝ) (T : ℝ≥0) :
    Contract ι :=
  .scale N (autocallUnit i t n B c S₀ P T)

/-- The note pays at fixed dates, so its value depends on a model only through the observations
at the `t k` and `T` (`Contract.value_eq_of_map_observation_eq`). -/
theorem autocallUnit_fixedDated (i : ι) (t : ℕ → ℝ≥0) (n : ℕ) (B c S₀ P : ℝ) (T : ℝ≥0) :
    (autocallUnit i t n B c S₀ P T).FixedDated := by
  simp [autocallUnit, Contract.FixedDated, payFlows_fixedDated]

/-- The note on a notional `N` pays at fixed dates. -/
theorem autocall_fixedDated (N : ℝ) (i : ι) (t : ℕ → ℝ≥0) (n : ℕ) (B c S₀ P : ℝ) (T : ℝ≥0) :
    (autocall N i t n B c S₀ P T).FixedDated :=
  autocallUnit_fixedDated i t n B c S₀ P T

/-- **What the note is worth along a scenario**, under any discount function `D`: the redemption
`D(tⱼ) (1 + (j+1) c)` at each date `j` that is the first at or above `B` (at most one), plus the
discounted protected redemption at `T` if every date was below `B`. -/
theorem pathPV_autocallUnit (D : ℝ≥0 → ℝ) (s : Scenario ι) (i : ι) (t : ℕ → ℝ≥0) (n : ℕ)
    (B c S₀ P : ℝ) (T : ℝ≥0) :
    (autocallUnit i t n B c S₀ P T).pathPV D s
      = ∑ j ∈ Finset.range n,
          D (t j) * (if s.FirstAbove i t B j then 1 + ((j : ℝ) + 1) * c else 0)
        + D T * (if ∀ j < n, s i (t j) < B
            then (if P ≤ s i T then 1 else S₀⁻¹ * s i T) else 0) := by
  have hpay : (Contract.pay T (.mul (survivalPayoff i t B n) (maturityPayoff i P S₀ T))).pathPV D s
      = D T * ((survivalPayoff i t B n).eval s * (maturityPayoff i P S₀ T).eval s) := by
    simp [Contract.pathPV, Contract.cashflows, Payoff.eval]
  rw [autocallUnit, Contract.pathPV_both, pathPV_payFlows, hpay, eval_survivalPayoff,
    eval_maturityPayoff]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ ↦ by rw [eval_redemptionPayoff]) ?_
  by_cases h : ∀ j < n, s i (t j) < B
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]

/-- **The note terminates at the first autocall date.** If the `k`-th observation, `k < n`, is the
first at or above the barrier, the cash flows of the note are its `n` early payments and the
maturity payment, and every amount is `0` except the redemption `1 + (k+1) c` at `t k`. -/
theorem cashflows_autocallUnit_of_firstAbove {s : Scenario ι} {i : ι} {t : ℕ → ℝ≥0} {n k : ℕ}
    {B c S₀ P : ℝ} {T : ℝ≥0} (hk : s.FirstAbove i t B k) (hkn : k < n) :
    (autocallUnit i t n B c S₀ P T).cashflows s
      = (List.range n).map (fun j ↦ (t j, if j = k then 1 + ((k : ℝ) + 1) * c else 0))
        ++ [(T, 0)] := by
  have hnone : ¬ ∀ j < n, s i (t j) < B := fun h ↦ absurd (h k hkn) (not_lt.2 hk.1)
  have h0 : (Payoff.mul (survivalPayoff i t B n) (maturityPayoff i P S₀ T)).eval s = 0 := by
    simp only [Payoff.eval, eval_survivalPayoff, if_neg hnone, zero_mul]
  simp only [autocallUnit, Contract.cashflows, cashflows_payFlows, h0]
  congr 1
  refine List.map_congr_left fun j _ ↦ Prod.ext rfl ?_
  dsimp only
  rw [eval_redemptionPayoff]
  by_cases hj : j = k
  · subst hj
    rw [if_pos hk, if_pos rfl]
  · have h3 : ¬ s.FirstAbove i t B j := fun h ↦ hj (h.unique hk)
    rw [if_neg h3, if_neg hj]

/-- **If the barrier is never reached, the note pays once, at maturity.** If every one of the first
`n` observations is below `B`, every early amount is `0` and the maturity amount is the protected
redemption: `1` if `S_T ≥ P`, `S_T / S₀` otherwise. -/
theorem cashflows_autocallUnit_of_forall_lt {s : Scenario ι} {i : ι} {t : ℕ → ℝ≥0} {n : ℕ}
    {B c S₀ P : ℝ} {T : ℝ≥0} (h : ∀ j < n, s i (t j) < B) :
    (autocallUnit i t n B c S₀ P T).cashflows s
      = (List.range n).map (fun j ↦ (t j, (0 : ℝ)))
        ++ [(T, if P ≤ s i T then 1 else S₀⁻¹ * s i T)] := by
  have hm : (Payoff.mul (survivalPayoff i t B n) (maturityPayoff i P S₀ T)).eval s
      = if P ≤ s i T then 1 else S₀⁻¹ * s i T := by
    simp only [Payoff.eval, eval_survivalPayoff, if_pos h, one_mul, eval_maturityPayoff]
  simp only [autocallUnit, Contract.cashflows, cashflows_payFlows, hm]
  congr 1
  refine List.map_congr_left fun j hj ↦ Prod.ext rfl ?_
  dsimp only
  have h3 : ¬ s.FirstAbove i t B j := fun hf ↦ absurd hf.1 (not_le.2 (h j (List.mem_range.1 hj)))
  rw [eval_redemptionPayoff, if_neg h3]

/-- **The coupon only helps**: with a nonnegative discount factor at the observation dates, the
present value of the note along every scenario is nondecreasing in the coupon `c`. -/
theorem pathPV_autocallUnit_mono_coupon {D : ℝ≥0 → ℝ} (s : Scenario ι) (i : ι) (t : ℕ → ℝ≥0)
    (n : ℕ) {B c c' : ℝ} (S₀ P : ℝ) (T : ℝ≥0) (hc : c ≤ c') (hD : ∀ j < n, 0 ≤ D (t j)) :
    (autocallUnit i t n B c S₀ P T).pathPV D s ≤ (autocallUnit i t n B c' S₀ P T).pathPV D s := by
  rw [pathPV_autocallUnit, pathPV_autocallUnit]
  refine add_le_add (Finset.sum_le_sum fun j hj ↦ ?_) le_rfl
  by_cases h : s.FirstAbove i t B j
  · rw [if_pos h, if_pos h]
    exact mul_le_mul_of_nonneg_left (by gcongr) (hD j (Finset.mem_range.1 hj))
  · simp only [if_neg h, le_refl]

/-- **The present value of a terminated note** is the discounted redemption at the first autocall
date, whatever happens to the underlying afterwards. -/
theorem pathPV_autocallUnit_of_firstAbove (D : ℝ≥0 → ℝ) {s : Scenario ι} {i : ι} {t : ℕ → ℝ≥0}
    {n k : ℕ} {B c S₀ P : ℝ} {T : ℝ≥0} (hk : s.FirstAbove i t B k) (hkn : k < n) :
    (autocallUnit i t n B c S₀ P T).pathPV D s = D (t k) * (1 + ((k : ℝ) + 1) * c) := by
  have hnone : ¬ ∀ j < n, s i (t j) < B := fun h ↦ absurd (h k hkn) (not_lt.2 hk.1)
  have h₀ : ∀ j ∈ Finset.range n, j ≠ k →
      D (t j) * (if s.FirstAbove i t B j then 1 + ((j : ℝ) + 1) * c else 0) = 0 :=
    fun j _ hj ↦ by
      have h3 : ¬ s.FirstAbove i t B j := fun h ↦ hj (h.unique hk)
      rw [if_neg h3, mul_zero]
  rw [pathPV_autocallUnit, if_neg hnone, mul_zero, add_zero,
    Finset.sum_eq_single k h₀ (fun h ↦ absurd (Finset.mem_range.2 hkn) h), if_pos hk]

/-- **The present value of a note whose barrier is never reached** is the discounted protected
redemption at maturity. -/
theorem pathPV_autocallUnit_of_forall_lt (D : ℝ≥0 → ℝ) {s : Scenario ι} {i : ι} {t : ℕ → ℝ≥0}
    {n : ℕ} {B c S₀ P : ℝ} {T : ℝ≥0} (h : ∀ j < n, s i (t j) < B) :
    (autocallUnit i t n B c S₀ P T).pathPV D s
      = D T * (if P ≤ s i T then 1 else S₀⁻¹ * s i T) := by
  rw [pathPV_autocallUnit, Finset.sum_eq_zero, zero_add, if_pos h]
  intro j hj
  have h3 : ¬ s.FirstAbove i t B j := fun hf ↦ absurd hf.1 (not_le.2 (h j (Finset.mem_range.1 hj)))
  rw [if_neg h3, mul_zero]

/-- **A bond at the first date dominates the note.** Under a nonincreasing nonnegative discount
function, with a nonnegative coupon and a protection barrier below the initial fixing, the note's
present value along every scenario is at most that of `1 + n c` paid at the first observation
date `t 0`: the notional and all `n` coupons. (Every payment is at most `1 + n c`, and it is made
no earlier than `t 0`, where discounting is smallest.) -/
theorem pathPV_autocallUnit_le {D : ℝ≥0 → ℝ} (s : Scenario ι) (i : ι) (t : ℕ → ℝ≥0) {n : ℕ}
    {B c S₀ P : ℝ} {T : ℝ≥0} (hn : 0 < n) (hc : 0 ≤ c) (hS : 0 < S₀) (hP : P ≤ S₀)
    (hD : Antitone D) (hDT : 0 ≤ D T) (ht : ∀ k < n, t 0 ≤ t k ∧ t k ≤ T) :
    (autocallUnit i t n B c S₀ P T).pathPV D s ≤ D (t 0) * (1 + (n : ℝ) * c) := by
  have h0 : 0 ≤ D (t 0) := hDT.trans (hD (ht 0 hn).2)
  by_cases hex : ∃ k < n, B ≤ s i (t k)
  · obtain ⟨k, hkn, hk⟩ := Scenario.exists_firstAbove hex
    rw [pathPV_autocallUnit_of_firstAbove D hk hkn]
    have hk1 : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hkn
    exact mul_le_mul (hD (ht k hkn).1)
      (by nlinarith [mul_le_mul_of_nonneg_right hk1 hc])
      (add_nonneg zero_le_one (mul_nonneg (by positivity) hc)) h0
  · have hlt : ∀ j < n, s i (t j) < B := fun j hj ↦ not_le.1 fun h ↦ hex ⟨j, hj, h⟩
    rw [pathPV_autocallUnit_of_forall_lt D hlt]
    have hm : (if P ≤ s i T then (1 : ℝ) else S₀⁻¹ * s i T) ≤ 1 := by
      split_ifs with h
      · exact le_rfl
      · rw [inv_mul_eq_div, div_le_one hS]
        exact (not_le.1 h).le.trans hP
    calc D T * (if P ≤ s i T then 1 else S₀⁻¹ * s i T) ≤ D T * 1 :=
          mul_le_mul_of_nonneg_left hm hDT
      _ ≤ D (t 0) * 1 := by rw [mul_one, mul_one]; exact hD (ht 0 hn).2
      _ ≤ D (t 0) * (1 + (n : ℝ) * c) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hc)) h0

end MathFin.Contracts
