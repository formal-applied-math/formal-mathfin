/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun, Raphael Coelho
-/
module

public import MathFin.Pricing.DiscreteMarket

/-!
# The chain ladder and Mack's model

A run-off triangle records the cumulative claims `C i j` of accident year `i` after `j`
development years; at calendar date `n` the cells with `i + j ≤ n` are known. The **chain
ladder** selects a development factor per column, `f̂_j = ∑ᵢ C i (j + 1) / ∑ᵢ C i j` over the
rows observed in both columns (`chainFactor`), and completes each row forward by these factors
(`chainComplete`). On an unobserved cell the completion is the last observed value times the
product of the selected factors (`chainComplete_unobserved`), the prediction
`(∏_{k ∈ [m, N)} f k) · c m` of a row `c` at its date `m` (`chainPrediction`).

**Mack's model** is the probability behind the method. A row is a process `C` adapted to the
filtration of its development with `E[C (j + 1) | 𝓕 j] = f j · C j` (`IsMackRow`). Under it the
prediction of the ultimate `C N` is its conditional expectation (`IsMackRow.condExp_eq`), and
the predictions revised as the years come in form a martingale: the reference measure is an
equivalent martingale measure of the prediction process up to the ultimate date
(`IsMackRow.isEMM_chainPrediction`), so it is a pricing measure of the discrete market whose
asset is the prediction (`IsMackRow.isPricingMeasure_toMarket`). The revision from one date to
the next, the claims development result, has conditional mean zero
(`IsMackRow.condExp_chainPrediction_succ_sub`).

The chain-ladder completion is Mack's prediction with the selected factors in place of the
model's (`chainComplete_eq_chainPrediction`). On rational data the completion is computed
exactly, and the computation certifies the real value
(`chainComplete_eq_of_chainCompleteRat?_eq_some`). That the selected factors estimate the
model's without bias, and the standard error of the reserve, are not proved here.

## Main definitions

* `chainFactor`: the selected development factor `f̂_j` of a triangle with `n` development
  periods.
* `chainComplete`: the chain-ladder completion; it keeps observed cells and multiplies forward by
  the selected factors.
* `chainPrediction f c N m`: the prediction `(∏_{k ∈ [m, N)} f k) · c m` of the value of the row
  `c` at `N` from its value at `m`.
* `IsMackRow P 𝓕 C f`: Mack's conditional-mean assumption for one accident year.
* `chainFactorRat?`, `chainCompleteRat?`: the factor and the completion of a rational triangle,
  computed exactly; `none` where a factor's denominator vanishes.

## Main results

* `chainComplete_unobserved`, `chainComplete_eq_chainPrediction`: on unobserved cells the
  completion is the last observed cell times the product of the selected factors.
* `chainComplete_eq_of_chainCompleteRat?_eq_some`,
  `chainPrediction_eq_of_chainCompleteRat?_eq_some`: a value the exact evaluator returns is the
  real completion of the cast triangle and, on unobserved cells, the prediction by the selected
  factors.
* `cast_chainCompleteRat?_some`, `chainCompleteRat?_none_of_denom_eq_zero`: the evaluator returns
  a value within the horizon when the denominators are nonzero, and `none` past a zero one.
* `le_chainComplete`: with nonnegative rows, monotone on observed cells, and positive
  denominators, the completed ultimate is at least the last observed value.
* `IsMackRow.condExp_eq`: `E[C N | 𝓕 m] = (∏_{k ∈ [m, N)} f k) · C m` for `m ≤ N`.
* `IsMackRow.isEMM_chainPrediction`, `IsMackRow.isPricingMeasure_toMarket`: the prediction
  process, frozen at the ultimate date, is a martingale under the reference measure.
* `IsMackRow.condExp_chainPrediction_succ_sub`: the claims development result has conditional
  mean zero.

## References

* [T. Mack, *Distribution-free Calculation of the Standard Error of Chain Ladder Reserve
  Estimates*][Mack1993] (the model's conditional-mean assumption and the chain-ladder estimator)
* [M. Merz and M. V. Wüthrich, *Modelling the Claims Development Result for Solvency
  Purposes*][MerzWuthrich2008] (the claims development result)

## Tags

chain ladder, loss reserving, run-off triangle, development factor, Mack model, claims
development result, best estimate, martingale, MSC 91G05, JEL G22
-/

@[expose] public section

namespace MathFin

open MeasureTheory Finset

/-! ### The chain-ladder completion of a triangle -/

/-- The **chain-ladder development factor** `f̂_j` of a cumulative triangle `C` with `n`
development periods: the ratio of the column-`j+1` sum to the column-`j` sum over the
rows `i < n - j` observed in both columns. -/
noncomputable def chainFactor (n : ℕ) (C : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  (∑ i ∈ range (n - j), C i (j + 1)) / ∑ i ∈ range (n - j), C i j

/-- The **chain-ladder completion** of `C`: observed cells (`i + j ≤ n`) keep `C i j`;
each unobserved cell multiplies the previous cell in its row by the selected factor
`chainFactor n C j`. -/
noncomputable def chainComplete : ℕ → (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ
  | _, C, i, 0 => C i 0
  | n, C, i, j + 1 =>
      if i + (j + 1) ≤ n then C i (j + 1)
      else chainComplete n C i j * chainFactor n C j

/-- The **prediction** of the value of the row `c` at `N` from its value at `m`, by the factors
`f`: `(∏_{k ∈ [m, N)} f k) · c m`. -/
noncomputable def chainPrediction (f : ℕ → ℝ) (c : ℕ → ℝ) (N m : ℕ) : ℝ :=
  (∏ k ∈ Ico m N, f k) * c m

@[simp]
theorem chainPrediction_self (f c : ℕ → ℝ) (N : ℕ) : chainPrediction f c N N = c N := by
  simp [chainPrediction]

/-- Observed cells are preserved by the completion. -/
theorem chainComplete_eq (n : ℕ) (C : ℕ → ℕ → ℝ) (i j : ℕ) (h : i + j ≤ n) :
    chainComplete n C i j = C i j := by
  cases j with
  | zero => rfl
  | succ j => simp [chainComplete, h]

/-- **Product-of-selected-factors formula**: on unobserved cells (`n < i + j`) the
completion equals the last observed cell `C i (n - i)` times the product of the
selected factors over `[n - i, j)`. -/
theorem chainComplete_unobserved (n : ℕ) (C : ℕ → ℕ → ℝ) (i j : ℕ) (hij : n < i + j) :
    chainComplete n C i j = C i (n - i) * ∏ k ∈ Ico (n - i) j, chainFactor n C k := by
  induction j with
  | zero => simp [chainComplete, show n - i = 0 by omega]
  | succ j ih =>
    simp only [chainComplete, show ¬i + (j + 1) ≤ n by omega, ↓reduceIte]
    rw [prod_Ico_succ_top (by omega), ← mul_assoc]
    by_cases hobs : i + j ≤ n
    · rw [chainComplete_eq n C i j hobs, show j = n - i by omega, Ico_self, prod_empty, mul_one]
    · rw [ih (by omega)]

/-- **The chain-ladder completion is the prediction by the selected factors**: on unobserved
cells, `chainComplete n C i j` is `chainPrediction (chainFactor n C) (C i) j (n - i)`, the
prediction of the row's value at `j` from its last observed value. -/
theorem chainComplete_eq_chainPrediction (n : ℕ) (C : ℕ → ℕ → ℝ) (i j : ℕ) (hij : n < i + j) :
    chainComplete n C i j = chainPrediction (chainFactor n C) (C i) j (n - i) := by
  rw [chainComplete_unobserved n C i j hij, chainPrediction, mul_comm]

/-- **Chain-ladder monotonicity**: with monotone cumulative rows (`hmono`), positive
selected-factor denominators (`hdenom`) and nonnegative cumulative values (`hC`), the
completed ultimate `chainComplete n C i n` is at least the last observed diagonal value
`C i (n - i)`, so the predicted outstanding claims are nonnegative: each selected factor is at
least one. -/
theorem le_chainComplete (n : ℕ) (C : ℕ → ℕ → ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hmono : ∀ i j, i + (j + 1) ≤ n → C i j ≤ C i (j + 1))
    (hdenom : ∀ j < n, 0 < ∑ i ∈ range (n - j), C i j) (i : ℕ) :
    C i (n - i) ≤ chainComplete n C i n := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [chainComplete_eq n C 0 n (by omega), Nat.sub_zero]
  rw [chainComplete_unobserved n C i n (by omega)]
  refine le_mul_of_one_le_right (hC i (n - i)) (one_le_prod₀ fun k hk ↦ ?_)
  have hk := (mem_Ico.1 hk).2
  rw [chainFactor, one_le_div (hdenom k hk)]
  exact sum_le_sum fun i' hi' ↦ hmono i' k (by have := mem_range.1 hi'; omega)

/-! ### Exact evaluation over `ℚ`

The completion of a triangle of rational data can be computed exactly, and the computation
certifies the real completion: whatever value the evaluator returns is `chainComplete` of the
cast triangle (`chainComplete_eq_of_chainCompleteRat?_eq_some`), and on an unobserved cell it is
the prediction by the selected factors (`chainPrediction_eq_of_chainCompleteRat?_eq_some`). The
evaluator returns `none` exactly where the real factor would divide by zero. -/

/-- The **rational chain-ladder development factor** over `ℚ`: the same ratio of
successive column sums as `chainFactor`, returning `none` when the denominator sum
is zero instead of totalizing division by zero. -/
def chainFactorRat? (n : ℕ) (C : ℕ → ℕ → ℚ) (j : ℕ) : Option ℚ :=
  if (∑ i ∈ range (n - j), C i j) = 0 then none
  else some ((∑ i ∈ range (n - j), C i (j + 1)) / ∑ i ∈ range (n - j), C i j)

/-- The **rational chain-ladder completion** over `ℚ`: observed cells (`i + j ≤ n`) keep
`C i j`; each unobserved cell multiplies the previous cell by the rational selected
factor, propagating `none` from any rejected factor. -/
def chainCompleteRat? : ℕ → (ℕ → ℕ → ℚ) → ℕ → ℕ → Option ℚ
  | _, C, i, 0 => some (C i 0)
  | n, C, i, j + 1 =>
      if i + (j + 1) ≤ n then some (C i (j + 1))
      else (chainCompleteRat? n C i j).bind fun q =>
        (chainFactorRat? n C j).map fun f => q * f

/-- **The exact evaluator is sound**: a value it returns is the real chain-ladder completion of
the cast triangle. No hypothesis is needed: a returned value means every factor it used had a
nonzero denominator. -/
theorem chainComplete_eq_of_chainCompleteRat?_eq_some {n : ℕ} {C : ℕ → ℕ → ℚ} {i j : ℕ}
    {q : ℚ} (h : chainCompleteRat? n C i j = some q) :
    chainComplete n (fun a b ↦ (C a b : ℝ)) i j = q := by
  induction j generalizing q with
  | zero =>
    simp only [chainCompleteRat?, Option.some.injEq] at h
    simp [chainComplete, h]
  | succ j ih =>
    by_cases hle : i + (j + 1) ≤ n
    · simp only [chainCompleteRat?, hle, ↓reduceIte, Option.some.injEq] at h
      rw [chainComplete_eq _ _ _ _ hle, h]
    · simp only [chainCompleteRat?, hle, ↓reduceIte, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at h
      obtain ⟨p, hp, f, hf, rfl⟩ := h
      simp only [chainFactorRat?] at hf
      split_ifs at hf with h0
      obtain rfl := Option.some.inj hf
      simp only [chainComplete, hle, ↓reduceIte, ih hp, chainFactor]
      push_cast
      rfl

/-- **The exact evaluator computes Mack's prediction**: on an unobserved cell, a value the
evaluator returns is the prediction `chainPrediction` of the row's value from its last observed
cell, by the selected factors of the cast triangle. -/
theorem chainPrediction_eq_of_chainCompleteRat?_eq_some {n : ℕ} {C : ℕ → ℕ → ℚ} {i j : ℕ}
    {q : ℚ} (hij : n < i + j) (h : chainCompleteRat? n C i j = some q) :
    chainPrediction (chainFactor n fun a b ↦ (C a b : ℝ)) (fun b ↦ (C i b : ℝ)) j (n - i) = q :=
  (chainComplete_eq_chainPrediction _ _ i j hij).symm.trans
    (chainComplete_eq_of_chainCompleteRat?_eq_some h)

/-- **The exact evaluator succeeds**: when every in-horizon denominator sum is nonzero, the
rational completion returns a value at every cell within the horizon, and its cast is the real
completion `chainComplete` of the cast triangle. -/
theorem cast_chainCompleteRat?_some (n : ℕ) (C : ℕ → ℕ → ℚ)
    (hdenom : ∀ j, j < n → (∑ i ∈ range (n - j), C i j) ≠ 0)
    (i j : ℕ) (hj : j ≤ n) :
    ∃ q : ℚ, chainCompleteRat? n C i j = some q
      ∧ (q : ℝ) = chainComplete n (fun a b ↦ (C a b : ℝ)) i j := by
  suffices h : ∃ q : ℚ, chainCompleteRat? n C i j = some q by
    obtain ⟨q, hq⟩ := h
    exact ⟨q, hq, (chainComplete_eq_of_chainCompleteRat?_eq_some hq).symm⟩
  induction j with
  | zero => exact ⟨C i 0, rfl⟩
  | succ j ih =>
    obtain ⟨q, hq⟩ := ih (by omega)
    by_cases h : i + (j + 1) ≤ n
    · exact ⟨C i (j + 1), by simp [chainCompleteRat?, h]⟩
    · exact ⟨q * ((∑ a ∈ range (n - j), C a (j + 1)) / ∑ a ∈ range (n - j), C a j),
        by simp [chainCompleteRat?, h, hq, chainFactorRat?, hdenom j (by omega)]⟩

/-- **Denominator failure propagates**: a zero denominator sum at a factor the cell needs makes
the rational completion `none`. -/
theorem chainCompleteRat?_none_of_denom_eq_zero (n : ℕ) (C : ℕ → ℕ → ℚ)
    (i j j' : ℕ) (hj1 : n - i ≤ j') (hj2 : j' < j)
    (h0 : (∑ a ∈ range (n - j'), C a j') = 0) :
    chainCompleteRat? n C i j = none := by
  induction j with
  | zero => omega
  | succ j ih =>
    have h : ¬i + (j + 1) ≤ n := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj2 with hlt | rfl
    · simp [chainCompleteRat?, h, ih hlt]
    · simp only [chainCompleteRat?, h, ↓reduceIte]
      cases chainCompleteRat? n C i j' <;> simp [chainFactorRat?, h0]

/-! ### Mack's model -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℕ mΩ}
  {C : ℕ → Ω → ℝ} {f : ℕ → ℝ}

/-- **Mack's model for one accident year**: the cumulative claims `C j` after `j` development
years are adapted to `𝓕` and integrable, and `E[C (j + 1) | 𝓕 j] = f j · C j`. -/
structure IsMackRow (P : Measure Ω) (𝓕 : Filtration ℕ mΩ) (C : ℕ → Ω → ℝ) (f : ℕ → ℝ) :
    Prop where
  adapted : StronglyAdapted 𝓕 C
  integrable (j : ℕ) : Integrable (C j) P
  condExp_succ (j : ℕ) : P[C (j + 1) | 𝓕 j] =ᵐ[P] fun ω ↦ f j * C j ω

namespace IsMackRow

/-- **The revised predictions of the ultimate are a martingale**: under Mack's model the
prediction `m ↦ (∏_{k ∈ [m, N)} f k) · C m` of the ultimate `C N`, frozen at `N`, is a
`P`-martingale. One step is the model's assumption; past `N` the process is constant. -/
theorem martingale_chainPrediction [IsFiniteMeasure P] (h : IsMackRow P 𝓕 C f) (N : ℕ) :
    Martingale (fun m ω ↦ chainPrediction f (C · ω) N (min m N)) 𝓕 P := by
  have hsm (m : ℕ) : StronglyMeasurable[𝓕 m] fun ω ↦ chainPrediction f (C · ω) N (min m N) :=
    ((h.adapted (min m N)).mono (𝓕.mono (min_le_left m N))).const_mul _
  refine martingale_nat hsm (fun m ↦ (h.integrable _).const_mul _) fun m ↦ ?_
  rcases lt_or_ge m N with hm | hm
  · simp only [min_eq_left hm.le, min_eq_left (Nat.succ_le_of_lt hm), chainPrediction]
    refine ((condExp_smul (∏ k ∈ Ico (m + 1) N, f k) (C (m + 1)) (𝓕 m)).trans
      ((h.condExp_succ m).mono fun ω hω ↦ ?_)).symm
    rw [Pi.smul_apply, hω, smul_eq_mul, prod_eq_prod_Ico_succ_bot hm]
    ring
  · rw [min_eq_right hm, min_eq_right (hm.trans m.le_succ)]
    exact .of_eq (condExp_of_stronglyMeasurable (𝓕.le m)
      (by simpa [min_eq_right hm] using hsm m) ((h.integrable N).const_mul _)).symm

/-- **The prediction is the conditional expectation of the ultimate**: under Mack's model,
`E[C N | 𝓕 m] = (∏_{k ∈ [m, N)} f k) · C m` for `m ≤ N`. -/
theorem condExp_eq [IsFiniteMeasure P] (h : IsMackRow P 𝓕 C f) {m N : ℕ} (hmN : m ≤ N) :
    P[C N | 𝓕 m] =ᵐ[P] fun ω ↦ chainPrediction f (C · ω) N m := by
  simpa [min_eq_left hmN] using (h.martingale_chainPrediction N).condExp_ae_eq hmN

/-- **The reference measure is an equivalent martingale measure of the prediction**: under
Mack's model, `P` is an EMM, up to the ultimate date `N`, of the process
`m ↦ (∏_{k ∈ [m, N)} f k) · C m`. -/
theorem isEMM_chainPrediction [IsProbabilityMeasure P] (h : IsMackRow P 𝓕 C f) (N : ℕ) :
    IsEMM 𝓕 P (fun m ω ↦ chainPrediction f (C · ω) N m) N P :=
  ⟨⟨inferInstance, .rfl, .rfl⟩, h.martingale_chainPrediction N⟩

/-- **The best estimate of the ultimate is priced by the reference measure**: under Mack's
model, `P` is a pricing measure, up to the ultimate date `N`, of the discrete market with unit
numéraire whose asset is the prediction of the ultimate. -/
theorem isPricingMeasure_toMarket [IsProbabilityMeasure P] (h : IsMackRow P 𝓕 C f) (N : ℕ) :
    (Contracts.DiscreteMarket.toMarket P 𝓕 (fun m ω ↦ chainPrediction f (C · ω) N m) N
      fun m _ ↦ (h.adapted m).const_mul _).IsPricingMeasure N P :=
  Contracts.DiscreteMarket.isPricingMeasure_toMarket_of_isEMM (h.isEMM_chainPrediction N)

/-- **The claims development result has conditional mean zero** (Merz–Wüthrich): under Mack's
model, the revision of the prediction of the ultimate from date `m` to date `m + 1 ≤ N` has
conditional mean zero given `𝓕 m`. -/
theorem condExp_chainPrediction_succ_sub [IsProbabilityMeasure P] (h : IsMackRow P 𝓕 C f)
    {m N : ℕ} (hm : m < N) :
    P[fun ω ↦ chainPrediction f (C · ω) N (m + 1) - chainPrediction f (C · ω) N m | 𝓕 m]
      =ᵐ[P] 0 := by
  have hE := h.isEMM_chainPrediction N
  have h2 := condExp_of_stronglyMeasurable (𝓕.le m) (hE.adapted hm.le) (hE.integrable hm.le)
  refine (condExp_sub (hE.integrable hm) (hE.integrable hm.le) _).trans ?_
  filter_upwards [hE.condExp_eq m.le_succ hm] with ω h3
  simp only [Pi.sub_apply, Pi.zero_apply, h3, h2, sub_self]

end IsMackRow

end MathFin
