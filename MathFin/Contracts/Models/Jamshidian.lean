/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Models.HullWhiteBond
public import MathFin.Contracts.Models.VasicekBond
public import MathFin.BlackScholes.Put
public import MathFin.FixedIncome.TimingAdjustment

/-!
# Jamshidian: the zero-coupon bond put and the caplet in the Gaussian short-rate models

A put on `P(T₀, T₁)` struck at `k` expiring at `T₀` is worth `P(0, T₀)` times the put's
expectation under the `T₀`-forward measure (`forwardMeasure`, the change of numéraire
`forwardMeasure_price`). In a Gaussian short-rate model the bond is
`P(T₀, T₁) = a·exp(−β r_{T₀})` (`bondPrice_hullWhite`), and `r_{T₀}` stays Gaussian under the
`T₀`-forward measure, its mean shifted by `−Cov(r_{T₀}, ∫₀^{T₀} r)`
(`HullWhite.shortRate_hasLaw_forwardMeasure`). So the bond is lognormal there, and the put is
a Black put (`bs_put_formula`) on it:

  `put = k·P(0, T₀)·Φ(−d₂) − P(0, T₁)·Φ(−d₁)`,   `d₁ = (ln(F/k) + s²/2)/s`,   `d₂ = d₁ − s`,

with forward price `F = P(0, T₁)/P(0, T₀)` and `s = B(T₁ − T₀)·sd(r_{T₀})`, the standard
deviation of `ln P(T₀, T₁)`. The forward price needs no computation with the affine coefficients:
it is the mean of the lognormal under `Q^{T₀}` (`discounted_terminal_eq_S0`) and, by the tower
property (`HasBondPrice.integral_discount_mul`), `𝔼^{T₀}[P(T₀, T₁)] = P(0, T₁)/P(0, T₀)`.

* `HasBondPrice.integral_bond_forward` — the forward price of the bond.
* `HasBondPrice.valueDisc_bondPut_gaussian` — the put, for a bond that is an exponential of a
  Gaussian under the `T₀`-forward measure.
* `valueDisc_bondPut_hullWhite`, `valueDisc_bondPut_vasicek` — the Hull–White put, with
  `s = B(T₁ − T₀)·sd(r_{T₀})`, and the Vasicek put as the constant forcing (`bondRate_const`).
* `valueDisc_caplet_hullWhite`, `valueDisc_caplet_vasicek` — the caplet of
  `valueDisc_caplet_eq_bondPut`, `(1 + δK)` such puts at strike `1/(1 + δK)`.

## What this is, and is not

The measure `μ` is read as the pricing measure and the Wiener representation of the short rate is
the model (as in `bondPrice_vasicek`). The caplet is *not* a Black-76 caplet in these models: the
forward LIBOR `L = (1/P − 1)/δ` is a shifted lognormal, and `valueDisc_caplet_black76` is not
applied; the caplet is `(1 + δK)` bond puts, which are Black puts on the lognormal bond.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

section Abstract

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ} {D : ℝ≥0 → Ω → ℝ}
  {X : ι → ℝ≥0 → Ω → ℝ} {b : ι} {T₀ T₁ : ℝ≥0}

/-- **Pricing at the forward measure.** For a positive integrable discount factor `D₀`, its
expectation is positive, and `𝔼[D₀ · Y] = 𝔼[D₀]·𝔼^{Q^{D₀}}[Y]` for the forward measure
`forwardMeasure Q (1/D₀)`: the change of numéraire `forwardMeasure_price`, written for the
discount factor instead of the bank account. -/
theorem integral_discount_mul_eq_forward {D₀ : Ω → ℝ} (hD : ∀ ω, 0 < D₀ ω)
    (hDm : Measurable D₀) (hDi : Integrable D₀ Q) (Y : Ω → ℝ) :
    0 < ∫ ω, D₀ ω ∂Q ∧ (∫ ω, D₀ ω ∂Q) * ∫ ω, Y ω ∂(forwardMeasure Q fun ω ↦ 1 / D₀ ω)
      = ∫ ω, D₀ ω * Y ω ∂Q := by
  have hB : ∀ ω, 0 < 1 / D₀ ω := fun ω ↦ one_div_pos.2 (hD ω)
  have e1 : ∫ ω, 1 / (1 / D₀ ω) ∂Q = ∫ ω, D₀ ω ∂Q := by simp
  have hP0 := integral_one_div_pos (Q := Q) hB (by simpa using hDi)
  rw [e1] at hP0
  have key := forwardMeasure_price (Q := Q) (B := fun ω ↦ 1 / D₀ ω) Y
    (measurable_const.div hDm) hB (by simpa using hP0)
  rw [e1] at key
  refine ⟨hP0, key.trans (integral_congr_ae <| ae_of_all _ fun ω ↦ ?_)⟩
  field_simp [(hD ω).ne']

/-- **The forward price of the bond**: under the `T₀`-forward measure (`forwardMeasure` of the bank
account `1/D T₀`), `𝔼^{T₀}[P(T₀, T₁)] = P(0, T₁)/P(0, T₀)`. The tower property turns `D T₁` into
`D T₀ · P(T₀, T₁)`, and the change of numéraire divides by `P(0, T₀)`. -/
theorem HasBondPrice.integral_bond_forward (h : HasBondPrice Q 𝓕 D X b T₀ T₁)
    (hDm : Measurable (D T₀)) (hD0 : Integrable (D T₀) Q) :
    ∫ ω, X b T₀ ω ∂(forwardMeasure Q fun ω ↦ 1 / D T₀ ω)
      = zeroCurve Q D T₁ / zeroCurve Q D T₀ := by
  obtain ⟨hpos, key⟩ := integral_discount_mul_eq_forward h.D_pos hDm hD0 (X b T₀)
  have e3 : ∫ ω, D T₀ ω * X b T₀ ω ∂Q = zeroCurve Q D T₁ := by
    simpa [zeroCurve] using (h.integral_discount_mul (Y := fun _ ↦ 1) stronglyMeasurable_const
      (by simpa using h.integrable_D)).symm
  rw [e3] at key
  have hz : zeroCurve Q D T₀ = ∫ ω, D T₀ ω ∂Q := rfl
  rw [hz, eq_div_iff hpos.ne', mul_comm]
  exact key

/-- **A put on the bond is a Black put, when the bond is lognormal at the forward measure.** Let
`Q'` be the `T₀`-forward measure and suppose, under it, `r` is Gaussian `N(m, v)` and the bond
price is `P(T₀, T₁) = a·exp(−β r)` with `β > 0`: a lognormal with log-standard-deviation
`s = β√v`. Then the put paying `(k − P(T₀, T₁))⁺` at `T₀` is worth

  `P(0, T₀)·k·Φ(−d₂) − P(0, T₁)·Φ(−d₁)`,   `d₁ = bsd1 F k 0 s 1`,   `d₂ = bsd2 F k 0 s 1`,

with `F = P(0, T₁)/P(0, T₀)` the forward price of the bond. The mean of the lognormal is `F`
(`HasBondPrice.integral_bond_forward`), so the constants `a`, `m` enter only through `s`. -/
theorem HasBondPrice.valueDisc_bondPut_gaussian (h : HasBondPrice Q 𝓕 D X b T₀ T₁)
    {Q' : Measure Ω} [IsProbabilityMeasure Q'] (hQ' : Q' = forwardMeasure Q fun ω ↦ 1 / D T₀ ω)
    (hDm : Measurable (D T₀)) (hD0 : Integrable (D T₀) Q) {r : Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hv : 0 < v) (hr : HasLaw r (gaussianReal m v) Q') {a β k : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hk : 0 < k) (hP : X b T₀ =ᵐ[Q'] fun ω ↦ a * Real.exp (-(β * r ω))) :
    (bondPut b T₀ k).valueDisc Q D X
      = zeroCurve Q D T₀ * k * Phi (-bsd2 (zeroCurve Q D T₁ / zeroCurve Q D T₀) k 0
            (β * Real.sqrt v) 1)
        - zeroCurve Q D T₁ * Phi (-bsd1 (zeroCurve Q D T₁ / zeroCurve Q D T₀) k 0
            (β * Real.sqrt v) 1) := by
  subst hQ'
  set sd : ℝ := Real.sqrt v with hsd_def
  have hsd : 0 < sd := Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hsd2 : sd ^ 2 = v := Real.sq_sqrt v.coe_nonneg
  set F₀ : ℝ := a * Real.exp (-(β * m) + β ^ 2 * v / 2) with hF₀
  set Z : Ω → ℝ := fun ω ↦ (-1 * r ω - (-1 * m)) / sd with hZdef
  have hZ : HasLaw Z (gaussianReal 0 1) (forwardMeasure Q fun ω ↦ 1 / D T₀ ω) :=
    hasLaw_sub_div_of_gaussianReal (gaussianReal_const_mul hr (-1)) hsd
      (by rw [NNReal.coe_mul, NNReal.coe_mk, hsd2]; ring)
  have hZmain : BSCallHyp (forwardMeasure Q fun ω ↦ 1 / D T₀ ω) F₀ k 0 (β * sd) 1 Z :=
    ⟨mul_pos ha (Real.exp_pos _), hk, mul_pos hβ hsd, one_pos, hZ⟩
  have hL : X b T₀ =ᵐ[forwardMeasure Q fun ω ↦ 1 / D T₀ ω]
      fun ω ↦ bsTerminal F₀ 0 (β * sd) 1 (Z ω) := hP.mono fun ω hω ↦ by
    have hsZ : β * sd * 1 * Z ω = β * (m - r ω) := by
      simp only [hZdef]; field_simp; ring
    have hs2 : (0 - (β * sd) ^ 2 / 2) * 1 = -(β ^ 2 * v / 2) := by rw [mul_pow, hsd2]; ring
    beta_reduce at hω ⊢
    rw [hω]
    unfold bsTerminal
    rw [Real.sqrt_one, hsZ, hs2, hF₀, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  obtain ⟨hpos, key⟩ := integral_discount_mul_eq_forward h.D_pos hDm hD0
    (fun ω ↦ max (k - X b T₀ ω) 0)
  have hF : F₀ = zeroCurve Q D T₁ / zeroCurve Q D T₀ := by
    rw [← h.integral_bond_forward hDm hD0, integral_congr_ae hL]
    simpa using (discounted_terminal_eq_S0 hZmain).symm
  have hput : ∫ ω, max (k - X b T₀ ω) 0 ∂(forwardMeasure Q fun ω ↦ 1 / D T₀ ω)
      = k * Phi (-bsd2 F₀ k 0 (β * sd) 1) - F₀ * Phi (-bsd1 F₀ k 0 (β * sd) 1) := by
    rw [integral_congr_ae (g := fun ω ↦ max (k - bsTerminal F₀ 0 (β * sd) 1 (Z ω)) 0)
      (hL.mono fun ω hω ↦ by simp only [hω])]
    simpa using bs_put_formula hZmain
  simp only [bondPut, Contract.valueDisc_pay, Payoff.eval, scenarioAt]
  rw [← key, hput, ← hF]
  have hpos' : 0 < zeroCurve Q D T₀ := hpos
  have h1 : zeroCurve Q D T₁ = zeroCurve Q D T₀ * F₀ := by
    rw [hF]; field_simp [hpos'.ne']
  rw [h1]
  simp only [zeroCurve]
  ring

end Abstract

/-! ### The Gaussian short-rate models -/

section GaussianShortRate

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {X : ι → ℝ≥0 → Ω → ℝ} {b : ι}
  {T₀ T₁ : ℝ≥0}

/-- **The zero-coupon bond put in the Hull–White model** (Jamshidian). For continuous forcing `θ`,
`σ ≠ 0` and `0 < T₀ < T₁`, a put struck at `k` expiring at `T₀` on the bond `P(T₀, T₁)` (an
underlying `b` that is a.e. the conditional expectation `bondPrice` of the discount factor) is worth

  `P(0, T₀)·k·Φ(−d₂) − P(0, T₁)·Φ(−d₁)`,   `d₁ = bsd1 F k 0 s 1`,   `d₂ = bsd2 F k 0 s 1`,

with `P(0, T) = zeroCurve` the bond prices of the model (`HullWhite.bondPrice_affine`),
`F = P(0, T₁)/P(0, T₀)` and `s = B(T₁ − T₀)·sd(r_{T₀})`, the standard deviation of
`ln P(T₀, T₁)`: the bond is `a·exp(−B(T₁ − T₀) r_{T₀})` (`bondPrice_hullWhite`) and `r_{T₀}` is
Gaussian under the `T₀`-forward measure with the variance of `HullWhite.integratedRate`
(`HullWhite.shortRate_hasLaw_forwardMeasure`), so `HasBondPrice.valueDisc_bondPut_gaussian`
prices the put as a Black put. The measure is read as the pricing measure. -/
theorem valueDisc_bondPut_hullWhite (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    {θ : ℝ → ℝ} (hθ : Continuous θ) (κ σ r₀ : ℝ) (hκ : 0 < κ) (h0 : 0 < T₀) (hT : T₀ < T₁)
    (hσ : σ ≠ 0)
    (hb : X b T₀ =ᵐ[μ] bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀ T₁) {k : ℝ} (hk : 0 < k) :
    (bondPut b T₀ k).valueDisc μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) X
      = zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀ * k
          * Phi (-bsd2 (zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀) k 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ)
              * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)
        - zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
          * Phi (-bsd1 (zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀) k 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ)
              * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1) := by
  set D := shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ) with hD
  have hDm (T : ℝ≥0) : Measurable (D T) := by
    unfold D shortRateDiscount HullWhite.bondRate
    exact (((Lp.stronglyMeasurable _).measurable.const_mul σ).const_add _).neg.exp
  have hDi (T : ℝ≥0) : Integrable (D T) μ :=
    (HullWhite.integrable_one_div_exp_bondRate hB θ κ σ r₀ hκ T).congr <| ae_of_all _ fun ω ↦ by
      simp [D, shortRateDiscount, Real.exp_neg]
  have hbp : HasBondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable) D X b T₀ T₁ :=
    ⟨fun ω ↦ Real.exp_pos _, hDi T₁, hb⟩
  have hfm : (forwardMeasure μ fun ω ↦ 1 / D T₀ ω)
      = forwardMeasure μ fun ω ↦ Real.exp (HullWhite.bondRate hB θ κ σ r₀ hκ T₀ ω) := by
    congr 1
    funext ω
    simp [D, shortRateDiscount, Real.exp_neg]
  haveI : IsProbabilityMeasure (forwardMeasure μ fun ω ↦ 1 / D T₀ ω) := by
    rw [hfm]
    exact forwardMeasure_isProbabilityMeasure (fun ω ↦ Real.exp_pos _)
      (HullWhite.integrable_one_div_exp_bondRate hB θ κ σ r₀ hκ T₀)
  have hr := HullWhite.shortRate_hasLaw_forwardMeasure hB θ κ σ r₀ hκ T₀
  rw [← hfm] at hr
  have hvar := vasicekSDE_variance_pos σ κ T₀ hκ (by exact_mod_cast h0) hσ
  have hτ : 0 < ((T₁ - T₀ : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_sub hT.le]; exact sub_pos.2 (by exact_mod_cast hT)
  have hβ : 0 < vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ) := by
    unfold vasicekBondB
    have : Real.exp (-(κ * ((T₁ - T₀ : ℝ≥0) : ℝ))) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith)
    exact div_pos (by linarith) hκ
  have hac : (forwardMeasure μ fun ω ↦ 1 / D T₀ ω) ≪ μ := withDensity_absolutelyContinuous _ _
  have hP := hac.ae_le (hb.trans (bondPrice_hullWhite hB hBm hθ κ σ r₀ hκ hT.le))
  have := hbp.valueDisc_bondPut_gaussian rfl (hDm T₀) (hDi T₀) (Real.toNNReal_pos.2 hvar) hr
    (Real.exp_pos _) hβ hk hP
  rwa [Real.coe_toNNReal _ hvar.le] at this

/-- **The caplet in the Hull–White model.** In a `BondModel` for the Hull–White discount factor,
the caplet paying `δ (L(T₀, T₁) − K)⁺` at `T₁` is worth `(1 + δK)` bond puts struck at
`1/(1 + δK)` (`valueDisc_caplet_eq_bondPut`), each priced by `valueDisc_bondPut_hullWhite`. The
forward LIBOR is a shifted lognormal here, not a lognormal: this is not
`valueDisc_caplet_black76`. -/
theorem valueDisc_caplet_hullWhite (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    {θ : ℝ → ℝ} (hθ : Continuous θ) (κ σ r₀ : ℝ) (hκ : 0 < κ) (h0 : 0 < T₀) (hT : T₀ < T₁)
    (hσ : σ ≠ 0) {ℓ : ι} {δ K : ℝ}
    (h : BondModel μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) X b ℓ T₀ T₁ δ)
    (hK : 0 < 1 + δ * K)
    (hint : Integrable (fun ω ↦ shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ) T₁ ω
      * (δ * max (X ℓ T₀ ω - K) 0)) μ) :
    (caplet ℓ T₀ T₁ δ K).valueDisc μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) X
      = (1 + δ * K) *
        (zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀
            * (1 / (1 + δ * K))
          * Phi (-bsd2 (zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀)
            (1 / (1 + δ * K)) 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ) * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)
          - zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
            * Phi (-bsd1 (zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀)
            (1 / (1 + δ * K)) 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ) * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)) := by
  rw [valueDisc_caplet_eq_bondPut h hK hint]
  exact congrArg _ (valueDisc_bondPut_hullWhite hB hBm hθ κ σ r₀ hκ h0 hT hσ h.bond_eq
    (one_div_pos.2 hK))

/-- **The zero-coupon bond put in the Vasicek model**: the Hull–White put at the constant forcing
`θ ≡ κθ_v` (`HullWhite.bondRate_const`), for the Vasicek integrated rate. -/
theorem valueDisc_bondPut_vasicek (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (h0 : 0 < T₀) (hT : T₀ < T₁) (hσ : σ ≠ 0)
    (hb : X b T₀ =ᵐ[μ] bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀ T₁) {k : ℝ} (hk : 0 < k) :
    (bondPut b T₀ k).valueDisc μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) X
      = zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀ * k
          * Phi (-bsd2 (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀) k 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ)
              * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)
        - zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
          * Phi (-bsd1 (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀) k 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ)
              * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1) := by
  have hD : shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)
      = shortRateDiscount (HullWhite.bondRate hB (fun _ ↦ κ * θ) κ σ r₀ hκ) := by
    funext T ω
    simp only [shortRateDiscount, HullWhite.bondRate_const]
  rw [hD] at hb ⊢
  exact valueDisc_bondPut_hullWhite hB hBm continuous_const κ σ r₀ hκ h0 hT hσ hb hk

/-- **The caplet in the Vasicek model**: `(1 + δK)` bond puts at strike `1/(1 + δK)`
(`valueDisc_caplet_eq_bondPut`), each `valueDisc_bondPut_vasicek`. Not a Black-76 caplet: the
forward LIBOR is a shifted lognormal. -/
theorem valueDisc_caplet_vasicek (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (h0 : 0 < T₀) (hT : T₀ < T₁) (hσ : σ ≠ 0) {ℓ : ι}
    {δ K : ℝ}
    (h : BondModel μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) X b ℓ T₀ T₁ δ)
    (hK : 0 < 1 + δ * K)
    (hint : Integrable (fun ω ↦ shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ) T₁ ω
      * (δ * max (X ℓ T₀ ω - K) 0)) μ) :
    (caplet ℓ T₀ T₁ δ K).valueDisc μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) X
      = (1 + δ * K) *
        (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀
            * (1 / (1 + δ * K))
          * Phi (-bsd2 (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀)
            (1 / (1 + δ * K)) 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ) * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)
          - zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
            * Phi (-bsd1 (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀)
            (1 / (1 + δ * K)) 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ) * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)) := by
  rw [valueDisc_caplet_eq_bondPut h hK hint]
  exact congrArg _ (valueDisc_bondPut_vasicek hB hBm r₀ θ σ hκ h0 hT hσ h.bond_eq
    (one_div_pos.2 hK))

end GaussianShortRate

end MathFin.Contracts
