/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Models.ShortRate
public import MathFin.FixedIncome.ForwardMeasure
public import MathFin.Futures.Black76

/-!
# Caplets and caps, on the bond prices of a stochastic discount factor

`bondPrice Q 𝓕 D t T = 𝔼_Q[D T | 𝓕 t] / D t` is the zero-coupon bond price `P(t, T)` at time
`t`, for any stochastic discount factor `D`: the bond prices that floating payoffs need. A
model `X` carries them as observed processes. `BondModel` says the underlying `b` is
`P(T₀, T₁)` at `T₀` (a.e.) and `ℓ` is the simple forward rate it implies,
`L = (1/P − 1)/δ` (`fraForwardRate 1 P δ`), adapted to the information at `T₀`.

* A **caplet** pays `δ (L(T₀, T₁) − K)⁺` at `T₁` (`caplet`, a one-cash-flow `Contract`). In
  every `BondModel` it is worth `(1 + δK)` puts on `P(T₀, T₁)`, struck at `1/(1 + δK)` and
  expiring at `T₀` (`valueDisc_caplet_eq_bondPut`): the tower property turns the discount factor
  `D T₁` into `D T₀ · P(T₀, T₁)`, and `P · δ (L − K)⁺ = (1 − (1 + δK) P)⁺`.
* A **cap** is its schedule of caplets (`cap`), worth their sum (`valueDisc_cap`), hence
  `(1 + δK)` times a strip of bond puts (`valueDisc_cap_eq_bondPuts`).
* **Black-76.** If `L(T₀, T₁)` is lognormal under the `T₁`-forward measure
  (`forwardMeasure`), the caplet is worth `P(0, T₁) · blackCaplet F K σ T δ`
  (`valueDisc_caplet_black76`), consuming `black_futures_formula` and the change of numéraire
  `forwardMeasure_price`; with a `BondModel`, `F` is the forward rate of the zero curve
  (`BondModel.integral_libor_forward`, `valueDisc_caplet_black76_forwardRate`).

## What is not here

Lognormality of `L` under the forward measure is a hypothesis. The Vasicek bond prices
`P(t, T)` at `t > 0` are in the library (`bondPrice_vasicek`,
`Contracts/Models/VasicekBond.lean`), but the lognormality is not derived from them; Hull–White
and the two-piece GSR are not covered. CMS rates are not covered: a CMS payoff observes a swap
rate, a ratio of bond-price sums, which `Payoff` cannot express.

## Main definitions

* `bondPrice`, `BondModel`, `capletPayoff`, `caplet`, `bondPut`, `cap`.

## Main results

* `BondModel.integral_discount_mul`, `valueDisc_caplet_eq_bondPut`, `valueDisc_cap`,
  `valueDisc_cap_eq_bondPuts`, `valueDisc_caplet_black76`, `BondModel.integral_libor_forward`,
  `valueDisc_caplet_black76_forwardRate`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The bond price at time `t`, and the caplet as a contract -/

/-- The **zero-coupon bond price at time `t`** under the stochastic discount factor `D`:
`P(t, T) = 𝔼_Q[D T | 𝓕 t] / D t`, the value at `t` of one unit paid at `T`. At `t = 0` with
`D 0 = 1` and a trivial `𝓕 0` it is the zero curve `zeroCurve Q D T`. -/
noncomputable def bondPrice (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (t T : ℝ≥0) : Ω → ℝ :=
  fun ω ↦ (Q[D T | 𝓕 t]) ω / D t ω

/-- The payoff of a **caplet**: `δ (L − K)⁺`, where the underlying `ℓ` carries the
simply-compounded forward rate `L(T₀, T₁)`, observed at its reset date `T₀`. -/
noncomputable def capletPayoff (ℓ : ι) (T₀ : ℝ≥0) (δ K : ℝ) : Payoff ι :=
  .mul (.const δ) (.max (.sub (.obs ℓ T₀) (.const K)) (.const 0))

/-- A **caplet**: pays `δ (L(T₀, T₁) − K)⁺` at `T₁`, with accrual `δ` and rate `L` observed at
`T₀`. -/
noncomputable def caplet (ℓ : ι) (T₀ T₁ : ℝ≥0) (δ K : ℝ) : Contract ι :=
  .pay T₁ (capletPayoff ℓ T₀ δ K)

/-- A **put on a zero-coupon bond**: pays `(k − P(T, ·))⁺` at its expiry `T`, where the
underlying `b` carries the bond price observed at `T`. -/
noncomputable def bondPut (b : ι) (T : ℝ≥0) (k : ℝ) : Contract ι :=
  .pay T (.max (.sub (.const k) (.obs b T)) (.const 0))

/-- A **cap**: the schedule of caplets with reset dates `T 0, …, T (n − 1)`, caplet `i` paying
`δ (Lᵢ − K)⁺` at `T (i + 1)`, where `ℓ i` carries the rate `L(T i, T (i + 1))`. -/
noncomputable def cap (ℓ : ℕ → ι) (T : ℕ → ℝ≥0) (δ K : ℝ) (n : ℕ) : Contract ι :=
  payFlows (fun i ↦ T (i + 1)) (fun i ↦ capletPayoff (ℓ i) (T i) δ K) n

/-- **A model with bond prices.** The underlying `b` carries the bond price `P(T₀, T₁)` at `T₀`
and `ℓ` the simply-compounded forward rate `L(T₀, T₁) = (1/P(T₀, T₁) − 1)/δ` it implies, both
as processes of the model `X`; `𝓕` is the information at `T₀`, and `P(T₀, T₁)` is the
conditional expectation `bondPrice` of the stochastic discount factor `D`. -/
structure BondModel (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (b ℓ : ι) (T₀ T₁ : ℝ≥0) (δ : ℝ) : Prop where
  δ_pos : 0 < δ
  D_pos : ∀ ω, 0 < D T₀ ω
  integrable_D : Integrable (D T₁) Q
  bond_eq : X b T₀ =ᵐ[Q] bondPrice Q 𝓕 D T₀ T₁
  bond_pos : ∀ᵐ ω ∂Q, 0 < X b T₀ ω
  libor_eq : X ℓ T₀ =ᵐ[Q] fun ω ↦ fraForwardRate 1 (X b T₀ ω) δ
  libor_meas : StronglyMeasurable[𝓕 T₀] (X ℓ T₀)

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ} {D : ℝ≥0 → Ω → ℝ}
  {X : ι → ℝ≥0 → Ω → ℝ} {b ℓ : ι} {T₀ T₁ : ℝ≥0} {δ : ℝ}

/-- **The bond price turns `D T₁` into `D T₀`**: for an `𝓕 T₀`-measurable `Y`,
`𝔼[D T₁ · Y] = 𝔼[D T₀ · P(T₀, T₁) · Y]`. -/
theorem BondModel.integral_discount_mul (h : BondModel Q 𝓕 D X b ℓ T₀ T₁ δ) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[𝓕 T₀] Y) (hDY : Integrable (fun ω ↦ D T₁ ω * Y ω) Q) :
    ∫ ω, D T₁ ω * Y ω ∂Q = ∫ ω, D T₀ ω * X b T₀ ω * Y ω ∂Q := by
  have hcond : Q[fun ω ↦ Y ω * D T₁ ω | 𝓕 T₀] =ᵐ[Q] fun ω ↦ Y ω * (Q[D T₁ | 𝓕 T₀]) ω :=
    condExp_mul_of_stronglyMeasurable_left hY
      (hDY.congr (ae_of_all _ fun ω ↦ mul_comm _ _)) h.integrable_D
  have hP : ∀ᵐ ω ∂Q, D T₀ ω * X b T₀ ω = (Q[D T₁ | 𝓕 T₀]) ω := by
    filter_upwards [h.bond_eq] with ω hω
    rw [hω, bondPrice]
    field_simp [(h.D_pos ω).ne']
  calc ∫ ω, D T₁ ω * Y ω ∂Q = ∫ ω, Y ω * D T₁ ω ∂Q := by simp_rw [mul_comm]
    _ = ∫ ω, (Q[fun ω ↦ Y ω * D T₁ ω | 𝓕 T₀]) ω ∂Q := (integral_condExp (𝓕.le T₀)).symm
    _ = ∫ ω, Y ω * (Q[D T₁ | 𝓕 T₀]) ω ∂Q := integral_congr_ae hcond
    _ = ∫ ω, D T₀ ω * X b T₀ ω * Y ω ∂Q := integral_congr_ae <| by
        filter_upwards [hP] with ω hω
        rw [← hω]; ring

/-- **A caplet is a multiple of a put on the bond** (the caplet–bond-put identity). In a model with
bond prices, the caplet paying `δ (L(T₀, T₁) − K)⁺` at `T₁` is worth `(1 + δK)` puts on
`P(T₀, T₁)` struck at `1/(1 + δK)` and expiring at `T₀`: pay `P(T₀, T₁) · δ (L − K)⁺` at `T₀`,
which is `(1 − (1 + δK) P)⁺`, since `δ L = 1/P − 1`. The bond price `P(T₀, T₁)` is the
conditional expectation `bondPrice` of the discount factor, not a deterministic curve. -/
theorem valueDisc_caplet_eq_bondPut (h : BondModel Q 𝓕 D X b ℓ T₀ T₁ δ) {K : ℝ}
    (hK : 0 < 1 + δ * K)
    (hint : Integrable (fun ω ↦ D T₁ ω * (δ * max (X ℓ T₀ ω - K) 0)) Q) :
    (caplet ℓ T₀ T₁ δ K).valueDisc Q D X
      = (1 + δ * K) * (bondPut b T₀ (1 / (1 + δ * K))).valueDisc Q D X := by
  have hY : StronglyMeasurable[𝓕 T₀] fun ω ↦ δ * max (X ℓ T₀ ω - K) 0 :=
    (show Continuous fun x : ℝ ↦ δ * max (x - K) 0 by fun_prop).comp_stronglyMeasurable
      h.libor_meas
  simp only [caplet, bondPut, Contract.valueDisc_pay, capletPayoff, Payoff.eval, scenarioAt]
  rw [h.integral_discount_mul hY hint, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [h.libor_eq, h.bond_pos] with ω hL hP
  have hδ := h.δ_pos
  rw [hL, fraForwardRate]
  have hc : (1 + δ * K) * (1 / (1 + δ * K) - X b T₀ ω)
      = X b T₀ ω * (δ * ((1 / X b T₀ ω - 1) / δ - K)) := by
    field_simp [hP.ne', hδ.ne', hK.ne']
    ring
  have e : X b T₀ ω * (δ * max ((1 / X b T₀ ω - 1) / δ - K) 0)
      = (1 + δ * K) * max (1 / (1 + δ * K) - X b T₀ ω) 0 := by
    rw [mul_max_of_nonneg _ _ hδ.le, mul_max_of_nonneg _ _ hP.le,
      mul_max_of_nonneg _ _ hK.le]
    simp only [mul_zero]
    rw [hc]
  calc D T₀ ω * X b T₀ ω * (δ * max ((1 / X b T₀ ω - 1) / δ - K) 0)
      = D T₀ ω * (X b T₀ ω * (δ * max ((1 / X b T₀ ω - 1) / δ - K) 0)) := by ring
    _ = _ := by rw [e]; ring

/-! ### Caps, and the Black-76 caplet -/

omit [IsProbabilityMeasure Q] in
/-- **A cap is the sum of its caplets**, in every model in which each caplet's discounted payoff
is integrable. -/
theorem valueDisc_cap (ℓ : ℕ → ι) (T : ℕ → ℝ≥0) (δ K : ℝ) (n : ℕ)
    (hint : ∀ i < n, Integrable
      (fun ω ↦ D (T (i + 1)) ω * (δ * max (X (ℓ i) (T i) ω - K) 0)) Q) :
    (cap ℓ T δ K n).valueDisc Q D X
      = ∑ i ∈ Finset.range n, (caplet (ℓ i) (T i) (T (i + 1)) δ K).valueDisc Q D X :=
  Contract.valueDisc_payFlows Q D X _ _ n fun i hi ↦ by
    simpa [capletPayoff, Payoff.eval, scenarioAt] using hint i hi

/-- **A cap is `(1 + δK)` times a strip of bond puts.** In a model with bond prices at each
reset date, the cap with accrual `δ` and strike `K` is worth `(1 + δK)` times the sum of the
puts on `P(Tᵢ, Tᵢ₊₁)` struck at `1/(1 + δK)` and expiring at `Tᵢ`. -/
theorem valueDisc_cap_eq_bondPuts (b ℓ : ℕ → ι) (T : ℕ → ℝ≥0) {δ K : ℝ} (n : ℕ)
    (h : ∀ i < n, BondModel Q 𝓕 D X (b i) (ℓ i) (T i) (T (i + 1)) δ) (hK : 0 < 1 + δ * K)
    (hint : ∀ i < n, Integrable
      (fun ω ↦ D (T (i + 1)) ω * (δ * max (X (ℓ i) (T i) ω - K) 0)) Q) :
    (cap ℓ T δ K n).valueDisc Q D X
      = (1 + δ * K) * ∑ i ∈ Finset.range n,
          (bondPut (b i) (T i) (1 / (1 + δ * K))).valueDisc Q D X := by
  rw [valueDisc_cap ℓ T δ K n hint, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi ↦
    valueDisc_caplet_eq_bondPut (h i (Finset.mem_range.1 hi)) hK (hint i (Finset.mem_range.1 hi))

/-- **The caplet is `P(0, T₁)` times a Black-76 call on the forward rate**, under the
`T₁`-forward measure `Q'` (`forwardMeasure` for the bank account `1/D T₁`). If the simple rate
`L(T₀, T₁)` is lognormal there, `L = bsTerminal F 0 σ T Z` with `Z` standard normal, then the
caplet is worth `P(0, T₁) · δ · [F Φ(d₁) − K Φ(d₂)]`, which is `blackCaplet`
(`Futures/Black76.lean`). The lognormality of `L` under `Q'` is a hypothesis, not derived from a
short-rate model, and `F` is the mean of `L` under `Q'`. -/
theorem valueDisc_caplet_black76 {Q' : Measure Ω} [IsProbabilityMeasure Q']
    (hQ' : Q' = forwardMeasure Q fun ω ↦ 1 / D T₁ ω) (hD : ∀ ω, 0 < D T₁ ω)
    (hDm : Measurable (D T₁)) (hDi : Integrable (D T₁) Q) {F K σ T : ℝ} {Z : Ω → ℝ}
    (hZ : BSCallHyp Q' F K 0 σ T Z)
    (hL : X ℓ T₀ =ᵐ[Q'] fun ω ↦ bsTerminal F 0 σ T (Z ω)) :
    (caplet ℓ T₀ T₁ δ K).valueDisc Q D X = zeroCurve Q D T₁ * blackCaplet F K σ T δ := by
  subst hQ'
  have hB : ∀ ω, 0 < 1 / D T₁ ω := fun ω ↦ one_div_pos.2 (hD ω)
  have hP0 := integral_one_div_pos (Q := Q) hB (by simpa using hDi)
  have key := forwardMeasure_price (Q := Q) (B := fun ω ↦ 1 / D T₁ ω)
    (fun ω ↦ δ * max (X ℓ T₀ ω - K) 0) (measurable_const.div hDm) hB hP0
  have e1 : ∫ ω, 1 / (1 / D T₁ ω) ∂Q = zeroCurve Q D T₁ := by simp [zeroCurve]
  have e2 : ∫ ω, δ * max (X ℓ T₀ ω - K) 0 / (1 / D T₁ ω) ∂Q
      = ∫ ω, D T₁ ω * (δ * max (X ℓ T₀ ω - K) 0) ∂Q :=
    integral_congr_ae <| ae_of_all _ fun ω ↦ by field_simp [(hD ω).ne']
  have e3 : ∫ ω, δ * max (X ℓ T₀ ω - K) 0 ∂forwardMeasure Q (fun ω ↦ 1 / D T₁ ω)
      = δ * (F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T)) := by
    rw [← show ∫ ω, max (bsTerminal F 0 σ T (Z ω) - K) 0 ∂forwardMeasure Q (fun ω ↦ 1 / D T₁ ω)
        = F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T) by
      simpa using black_futures_formula hZ 0, ← integral_const_mul]
    exact integral_congr_ae (hL.mono fun ω hω ↦ by simp only [hω])
  simp only [caplet, Contract.valueDisc_pay, capletPayoff, Payoff.eval, scenarioAt, blackCaplet]
  rw [← e2, ← key, e1, e3]

/-- **The forward rate has the forward rate of the zero curve as its mean at its own forward
measure**: `𝔼^{T₁}[L(T₀, T₁)] = (P(0, T₀)/P(0, T₁) − 1)/δ` (`fraForwardRate`). -/
theorem BondModel.integral_libor_forward (h : BondModel Q 𝓕 D X b ℓ T₀ T₁ δ)
    {Q' : Measure Ω} (hQ' : Q' = forwardMeasure Q fun ω ↦ 1 / D T₁ ω) (hD : ∀ ω, 0 < D T₁ ω)
    (hDm : Measurable (D T₁)) (hD0 : Integrable (D T₀) Q)
    (hint : Integrable (fun ω ↦ D T₁ ω * X ℓ T₀ ω) Q) :
    ∫ ω, X ℓ T₀ ω ∂Q' = fraForwardRate (zeroCurve Q D T₀) (zeroCurve Q D T₁) δ := by
  subst hQ'
  have hδ := h.δ_pos
  have hB : ∀ ω, 0 < 1 / D T₁ ω := fun ω ↦ one_div_pos.2 (hD ω)
  have hP0 := integral_one_div_pos (Q := Q) hB (by simpa using h.integrable_D)
  have e1 : ∫ ω, 1 / (1 / D T₁ ω) ∂Q = zeroCurve Q D T₁ := by simp [zeroCurve]
  rw [e1] at hP0
  have key := forwardMeasure_price (Q := Q) (B := fun ω ↦ 1 / D T₁ ω) (X ℓ T₀)
    (measurable_const.div hDm) hB (by simpa [zeroCurve] using hP0)
  have e2 : ∫ ω, X ℓ T₀ ω / (1 / D T₁ ω) ∂Q = ∫ ω, D T₁ ω * X ℓ T₀ ω ∂Q :=
    integral_congr_ae <| ae_of_all _ fun ω ↦ by field_simp [(hD ω).ne']
  have hDP : Integrable (fun ω ↦ D T₀ ω * X b T₀ ω) Q := by
    refine (integrable_condExp (m := 𝓕 T₀) (f := D T₁)).congr ?_
    filter_upwards [h.bond_eq] with ω hω
    rw [hω, bondPrice]
    field_simp [(h.D_pos ω).ne']
  have e3 : ∫ ω, D T₁ ω * X ℓ T₀ ω ∂Q = (zeroCurve Q D T₀ - zeroCurve Q D T₁) / δ := by
    rw [h.integral_discount_mul h.libor_meas hint]
    have e5 : ∫ ω, D T₁ ω ∂Q = ∫ ω, D T₀ ω * X b T₀ ω ∂Q := by
      simpa using h.integral_discount_mul (Y := fun _ ↦ 1) stronglyMeasurable_const
        (by simpa using h.integrable_D)
    rw [zeroCurve, zeroCurve, e5, ← integral_sub hD0 hDP, ← integral_div]
    refine integral_congr_ae ?_
    filter_upwards [h.libor_eq, h.bond_pos] with ω hL hP
    rw [hL, fraForwardRate]
    field_simp [hP.ne', hδ.ne']
  rw [e1, e2, e3] at key
  rw [fraForwardRate]
  field_simp [hP0.ne', hδ.ne'] at key ⊢
  linear_combination key

/-- **The Black-76 caplet formula, at the forward rate of the zero curve.** Under the hypotheses
of `valueDisc_caplet_black76` and a model with bond prices, the caplet is worth
`P(0, T₁) · blackCaplet F K σ T δ` with `F = (P(0, T₀)/P(0, T₁) − 1)/δ`, the forward rate of the
zero curve. -/
theorem valueDisc_caplet_black76_forwardRate (h : BondModel Q 𝓕 D X b ℓ T₀ T₁ δ)
    {Q' : Measure Ω} [IsProbabilityMeasure Q']
    (hQ' : Q' = forwardMeasure Q fun ω ↦ 1 / D T₁ ω) (hD : ∀ ω, 0 < D T₁ ω)
    (hDm : Measurable (D T₁)) (hD0 : Integrable (D T₀) Q)
    (hint : Integrable (fun ω ↦ D T₁ ω * X ℓ T₀ ω) Q) {K σ T : ℝ} {Z : Ω → ℝ}
    {F : ℝ} (hZ : BSCallHyp Q' F K 0 σ T Z)
    (hL : X ℓ T₀ =ᵐ[Q'] fun ω ↦ bsTerminal F 0 σ T (Z ω)) :
    (caplet ℓ T₀ T₁ δ K).valueDisc Q D X
      = zeroCurve Q D T₁ * blackCaplet
          (fraForwardRate (zeroCurve Q D T₀) (zeroCurve Q D T₁) δ) K σ T δ := by
  have hF : F = fraForwardRate (zeroCurve Q D T₀) (zeroCurve Q D T₁) δ := by
    rw [← h.integral_libor_forward hQ' hD hDm hD0 hint, integral_congr_ae hL]
    simpa using (discounted_terminal_eq_S0 hZ).symm
  rw [← hF]
  exact valueDisc_caplet_black76 hQ' hD hDm h.integrable_D hZ hL

end MathFin.Contracts
