/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.Market
public import MathFin.Models.BlackScholes.PDE
public import MathFin.Probability.Gaussian.StandardNormal
public import MathFin.Probability.Martingales.CondExpCallJensen

/-!
# Discrete arithmetic average-strike Asian option: a conditioning lower bound

The payoff `(S_T − A)⁺` with `A = (1/N) ∑ᵢ S_{tᵢ}` has no exact closed form under geometric
Brownian motion. The two-moment lognormal (Margrabe-type) approximation of `(S_T, A)` is biased
low, so this file proves the pieces of a different device, a lower bound obtained by conditioning
in the manner of Rogers and Shi (1995): for a Gaussian variable `Z`, Jensen's inequality gives

  `E[(S_T − A)⁺] ≥ E[(E[S_T − A | Z])⁺]`.

Given `Z = z` every `S_{tₖ}` is lognormal, so `g(z) = E[S_T − A | Z = z]` is a signed sum of
exponentials `∑ₖ aₖ e^{dₖ + cₖ z}`, and `E[g(Z)⁺]` is a sum of normal-cdf terms at the single
sign change of `g`. The conditioning idea is after Rogers and Shi (1995), as presented for the
continuous floating-strike case in G. W. P. Thompson, *Fast narrow bounds on the value of Asian
options* (Judge Institute of Management working paper wp0209, §3); the discrete-fixing form is
derived here. Rogers and Shi's paper itself was not read.

## Main definitions

* `expSum`: the exponential sum `z ↦ ∑ₖ aₖ exp(dₖ + cₖ z)`.
* `condBoundCall`: the closed form `D · ∑ₖ aₖ exp(dₖ + cₖ²/2) · Φ(cₖ − z*)`.
* `condRate`: the rate `cₖ` of the conditional mean of `ln Sₖ` given `Z`, junk `0` at zero variance.
* `condShift`: the log-shift `dₖ = ln Fₖ − cₖ²/2`, junk for `Fₖ ≤ 0`.

## Main results

* `expSum_pos_iff_of_root`: **single crossing.** If `aₖ(cₖ − p) ≥ 0` for all `k`, strictly for
  one, and `z*` is a root, then `expSum z > 0 ↔ z > z*`. (`expSum` itself need not be monotone;
  `expSum z · e^{−pz}` is.)
* `integral_max_expSum_hasLaw`: for `Z ~ N(0,1)` and a single crossing at `z*`,
  `E[(expSum Z)⁺] = ∑ₖ aₖ exp(dₖ + cₖ²/2) Φ(cₖ − z*)`.
* `condBoundCall_le_integral_max`: the conditioning bound, given the defining property of the
  conditional mean `g(Z)` as a hypothesis (`hcond`; it is not derived from the Brownian model
  here).
* `condBoundCall_sub_mean_le_integral_max_neg`: the put form, via parity.
* `condBoundCall_one_fixing`: with one fixing `t < T` the bound is `S₀ · bsV 1 r σ 1 (T − t)`,
  the forward-start call struck at the fixing; `condBoundCall_one_fixing_eq_marketPrice` states
  it as `S` times the Black–Scholes market's price of the unit-strike call.

## Scope

The exact first and second moments of the fixings `S_{tᵢ}` (hence of `A` and `S_T − A`) follow
from `integral_basket_eq_basketM1` and `integral_basket_sq_eq_basketM2` in
`MathFin.Models.BlackScholes.BasketMomentMatching`; they are not restated here.

The closeness of the bound to the price is *not* a theorem here. On the grid tested numerically
(`S = 97`, `r = 5%`, `q = 2%`, `T = 1`, fixings `1, 4, 10, 52`, volatility `20%, 40%, 80%`, two
million antithetic paths) the bound for calls and puts agrees with Monte Carlo to within 0.12%
(1.3 standard errors) up to 40% volatility, and to within 0.26% (3.0 standard errors, the worst
cell: the 80%-volatility put with four fixings) at 80%. The bound is below the truth by Jensen.
The identification of `E[S_T − A | Z]` with `g(Z)` from the Brownian model, and the monotone sign
pattern of `g` for general fixing dates, are hypotheses of the general statements.

## References

* [G. W. P. Thompson, *Fast narrow bounds on the value of Asian options*][ThompsonAsianBounds]
* [L. C. G. Rogers and Z. Shi, *The value of an Asian option*][RogersShi1995]

## Tags

Asian option, arithmetic average, average strike, floating strike, conditioning, Jensen,
lower bound, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal

/-! ### Exponential sums and their single crossing -/

/-- The exponential sum `z ↦ ∑ₖ aₖ exp(dₖ + cₖ z)`. With `aₖ` the signed weights of `S_{tₖ}` in
`S_T − A`, it is the conditional mean of `S_T − A` given the Gaussian variable `Z = z`. -/
noncomputable def expSum {n : ℕ} (a d c : Fin n → ℝ) (z : ℝ) : ℝ :=
  ∑ k, a k * Real.exp (d k + c k * z)

lemma continuous_expSum {n : ℕ} (a d c : Fin n → ℝ) : Continuous (expSum a d c) := by
  unfold expSum; fun_prop

/-- Rescaling by `e^{−pz}` shifts every rate `cₖ` to `cₖ − p`. -/
lemma expSum_mul_exp_neg {n : ℕ} (a d c : Fin n → ℝ) (p z : ℝ) :
    expSum a d c z * Real.exp (-(p * z)) = ∑ k, a k * Real.exp (d k + (c k - p) * z) := by
  unfold expSum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Single crossing.** Suppose `aₖ(cₖ − p) ≥ 0` for every `k` (negative weights sit at rates
`≤ p`, positive weights at rates `≥ p`), strictly for some `k`. Then `z ↦ expSum z · e^{−pz}`
is strictly increasing, so for any root `z*` the sum is positive exactly to the right of `z*`.
`expSum` itself need not be monotone. -/
theorem expSum_pos_iff_of_root {n : ℕ} {a d c : Fin n → ℝ} {p zs : ℝ}
    (hsign : ∀ k, 0 ≤ a k * (c k - p)) (hstrict : ∃ k, 0 < a k * (c k - p))
    (hroot : expSum a d c zs = 0) (z : ℝ) : 0 < expSum a d c z ↔ zs < z := by
  set h : ℝ → ℝ := fun z ↦ ∑ k, a k * Real.exp (d k + (c k - p) * z) with hh
  have hder : ∀ x, HasDerivAt h (∑ k, a k * (c k - p) * Real.exp (d k + (c k - p) * x)) x := by
    intro x
    refine HasDerivAt.fun_sum fun k _ ↦ ?_
    have h1 : HasDerivAt (fun y : ℝ ↦ d k + (c k - p) * y) (c k - p) x := by
      simpa using ((hasDerivAt_id x).const_mul (c k - p)).const_add (d k)
    have := (h1.exp).const_mul (a k)
    convert this using 1
    ring
  have hmono : StrictMono h := by
    refine strictMono_of_deriv_pos fun x ↦ ?_
    rw [(hder x).deriv]
    refine Finset.sum_pos' (fun k _ ↦ ?_) ?_
    · exact mul_nonneg (hsign k) (Real.exp_pos _).le
    · obtain ⟨k, hk⟩ := hstrict
      exact ⟨k, Finset.mem_univ k, mul_pos hk (Real.exp_pos _)⟩
  have hexp : ∀ x, expSum a d c x = h x * Real.exp (p * x) := fun x ↦ by
    have : expSum a d c x * Real.exp (-(p * x)) = h x := expSum_mul_exp_neg a d c p x
    rw [← this, mul_assoc, ← Real.exp_add]; simp
  have hzs : h zs = 0 := by
    have := hexp zs
    rw [hroot] at this
    exact (mul_eq_zero.mp this.symm).resolve_right (Real.exp_pos _).ne'
  rw [hexp z, mul_pos_iff_of_pos_right (Real.exp_pos _), ← hzs]
  exact hmono.lt_iff_lt

/-! ### The Gaussian closed form -/

lemma integrable_exp_mul_gaussianPDFReal (c : ℝ) :
    Integrable (fun z ↦ Real.exp (c * z) * gaussianPDFReal 0 1 z) := by
  simp_rw [exp_mul_gaussianPDFReal_zero_one]
  exact (integrable_gaussianPDFReal c 1).const_mul _

/-- The closed form: `E[(expSum Z)⁺]` for a standard normal density, when the sum is positive
exactly to the right of `zs`. -/
theorem integral_max_expSum_mul_gaussianPDFReal {n : ℕ} (a d c : Fin n → ℝ) (zs : ℝ)
    (hpos : ∀ z, 0 < expSum a d c z ↔ zs < z) :
    ∫ z, max (expSum a d c z) 0 * gaussianPDFReal 0 1 z
      = ∑ k, a k * Real.exp (d k + c k ^ 2 / 2) * Phi (c k - zs) := by
  have h_eq : (fun z ↦ max (expSum a d c z) 0 * gaussianPDFReal 0 1 z)
      = Set.indicator (Set.Ioi zs)
          (fun z ↦ ∑ k, a k * Real.exp (d k) * (Real.exp (c k * z) * gaussianPDFReal 0 1 z)) := by
    funext z
    by_cases hz : z ∈ Set.Ioi zs
    · rw [Set.indicator_of_mem hz, max_eq_left ((hpos z).2 hz).le]
      unfold expSum
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Real.exp_add]; ring
    · have : expSum a d c z ≤ 0 := not_lt.1 fun h ↦ hz ((hpos z).1 h)
      rw [Set.indicator_of_notMem hz, max_eq_right this, zero_mul]
  rw [h_eq, integral_indicator measurableSet_Ioi,
    integral_finsetSum _ fun k _ ↦
      (((integrable_exp_mul_gaussianPDFReal (c k)).const_mul _).integrableOn)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_const_mul, integral_exp_mul_gaussianPDFReal_Ioi, Real.exp_add]
  ring

/-- **`E[(expSum Z)⁺]` for `Z ~ N(0,1)`**, when the sum is positive exactly to the right of `zs`:
`∑ₖ aₖ exp(dₖ + cₖ²/2) Φ(cₖ − zs)`. -/
theorem integral_max_expSum_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P) {n : ℕ} (a d c : Fin n → ℝ) (zs : ℝ)
    (hpos : ∀ z, 0 < expSum a d c z ↔ zs < z) :
    ∫ ω, max (expSum a d c (Z ω)) 0 ∂P
      = ∑ k, a k * Real.exp (d k + c k ^ 2 / 2) * Phi (c k - zs) := by
  have hmeas : Measurable fun z ↦ max (expSum a d c z) 0 :=
    ((continuous_expSum a d c).max continuous_const).measurable
  have hc := hZ.integral_comp hmeas.aestronglyMeasurable
  simp only [Function.comp_def] at hc
  rw [hc, integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  simp_rw [smul_eq_mul, mul_comm (gaussianPDFReal 0 1 _)]
  exact integral_max_expSum_mul_gaussianPDFReal a d c zs hpos

/-- The conditioning-bound closed form `D · ∑ₖ aₖ exp(dₖ + cₖ²/2) Φ(cₖ − z*)`, `D` the
discount factor and `z*` the crossing of `expSum a d c`. -/
noncomputable def condBoundCall {n : ℕ} (D : ℝ) (a d c : Fin n → ℝ) (zs : ℝ) : ℝ :=
  D * ∑ k, a k * Real.exp (d k + c k ^ 2 / 2) * Phi (c k - zs)

/-- **The conditioning bound.** Let `G` be continuous and `G(Z)` have the defining property of the
conditional mean of `X` given `Z` (`hcond`: equal integrals over every `σ(Z)`-measurable set).
Then `E[G(Z)⁺] ≤ E[X⁺]`. -/
theorem integral_max_comp_le_of_condMean {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) {X : Ω → ℝ} (hX : Integrable X P)
    {G : ℝ → ℝ} (hG : Continuous G) (hGint : Integrable (fun ω ↦ G (Z ω)) P)
    (hcond : ∀ s, MeasurableSet[MeasurableSpace.comap Z inferInstance] s →
      ∫ ω in s, G (Z ω) ∂P = ∫ ω in s, X ω ∂P) :
    ∫ ω, max (G (Z ω)) 0 ∂P ≤ ∫ ω, max (X ω) 0 ∂P := by
  have hm : MeasurableSpace.comap Z inferInstance ≤ m0 := hZ.comap_le
  have hae : (fun ω ↦ G (Z ω)) =ᵐ[P] P[X | MeasurableSpace.comap Z inferInstance] :=
    ae_eq_condExp_of_forall_setIntegral_eq hm hX (fun _ _ _ ↦ hGint.integrableOn)
      (fun s hs _ ↦ hcond s hs)
      (hG.measurable.comp (comap_measurable Z)).aestronglyMeasurable
  calc ∫ ω, max (G (Z ω)) 0 ∂P
      = ∫ ω, max ((P[X | MeasurableSpace.comap Z inferInstance]) ω) 0 ∂P :=
        integral_congr_ae (by filter_upwards [hae] with ω h using by rw [h])
    _ ≤ ∫ ω, max (X ω) 0 ∂P := by
        simpa [posPart_def] using integral_posPart_sub_condExp_le hm hX 0

/-- **Lower bound for the call.** For `Z ~ N(0,1)` and `X` integrable, if `expSum a d c (Z)` is
the conditional mean of `X` given `Z` and is positive exactly to the right of `zs`, then for a
discount factor `D ≥ 0`, `condBoundCall D a d c zs ≤ D · E[X⁺]`. -/
theorem condBoundCall_le_integral_max {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ : HasLaw Z (gaussianReal 0 1) P)
    {X : Ω → ℝ} (hX : Integrable X P) {n : ℕ} (a d c : Fin n → ℝ) (zs D : ℝ) (hD : 0 ≤ D)
    (hpos : ∀ z, 0 < expSum a d c z ↔ zs < z)
    (hcond : ∀ s, MeasurableSet[MeasurableSpace.comap Z inferInstance] s →
      ∫ ω in s, expSum a d c (Z ω) ∂P = ∫ ω in s, X ω ∂P) :
    condBoundCall D a d c zs ≤ D * ∫ ω, max (X ω) 0 ∂P := by
  have hGint : Integrable (fun ω ↦ expSum a d c (Z ω)) P := by
    have h : Integrable (expSum a d c) (gaussianReal 0 1) := by
      unfold expSum
      refine integrable_finsetSum _ fun k _ ↦ ?_
      simp_rw [Real.exp_add, ← mul_assoc]
      exact (integrable_exp_mul_gaussianReal (c k)).const_mul _
    rw [← hZ.map_eq] at h
    exact h.comp_aemeasurable hZ.aemeasurable
  unfold condBoundCall
  rw [← integral_max_expSum_hasLaw hZ a d c zs hpos]
  exact mul_le_mul_of_nonneg_left
    (integral_max_comp_le_of_condMean hZm hX
      (continuous_expSum a d c) hGint hcond) hD

/-- **Lower bound for the put, through parity.** Under the hypotheses of
`condBoundCall_le_integral_max`, `condBoundCall D a d c zs − D · E[X] ≤ D · E[(−X)⁺]`; for
`X = S_T − A` the put payoff is `(−X)⁺` and `E[X] = F_T − E[A]` under the pricing measure. -/
theorem condBoundCall_sub_mean_le_integral_max_neg {Ω : Type*} {m0 : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZm : Measurable Z)
    (hZ : HasLaw Z (gaussianReal 0 1) P)
    {X : Ω → ℝ} (hX : Integrable X P) {n : ℕ} (a d c : Fin n → ℝ) (zs D : ℝ) (hD : 0 ≤ D)
    (hpos : ∀ z, 0 < expSum a d c z ↔ zs < z)
    (hcond : ∀ s, MeasurableSet[MeasurableSpace.comap Z inferInstance] s →
      ∫ ω in s, expSum a d c (Z ω) ∂P = ∫ ω in s, X ω ∂P) :
    condBoundCall D a d c zs - D * ∫ ω, X ω ∂P ≤ D * ∫ ω, max (-X ω) 0 ∂P := by
  have hparity : ∫ ω, max (-X ω) 0 ∂P = ∫ ω, max (X ω) 0 ∂P - ∫ ω, X ω ∂P := by
    rw [← integral_sub hX.pos_part hX]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    beta_reduce
    rcases le_total (X ω) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
  have := condBoundCall_le_integral_max hZm hZ hX a d c zs D hD hpos hcond
  rw [hparity]
  linarith

/-! ### The model data and the one-fixing case -/

/-- The rate `cₖ = (Cu)ₖ/√(uᵀCu)` of the conditional mean, for log-covariance
`Cⱼₖ = σ² min(tⱼ, tₖ)` and weights `u` (here `u = (−1/N, …, −1/N, 1)` over the fixings and `T`).
It is the covariance of `ln Sₖ` with `Z = ∑ uₖ ln Sₖ`, over the standard deviation of `Z`.
Junk value `0` when the variance `uᵀCu` is not positive (division by `√0`); meaningful only for a
positive variance, which callers must supply. -/
noncomputable def condRate {m : ℕ} (σ : ℝ) (ts u : Fin m → ℝ) (k : Fin m) : ℝ :=
  (∑ j, u j * (σ ^ 2 * min (ts j) (ts k))) /
    Real.sqrt (∑ i, ∑ j, u i * u j * (σ ^ 2 * min (ts i) (ts j)))

/-- The log-shift `dₖ = ln Fₖ − cₖ²/2`, so that `exp(dₖ + cₖ²/2) = Fₖ`.
Meaningful only for `Fₖ > 0`; `Real.log` is junk otherwise. -/
noncomputable def condShift {m : ℕ} (F c : Fin m → ℝ) (k : Fin m) : ℝ :=
  Real.log (F k) - c k ^ 2 / 2

/-- With `dₖ = ln Fₖ − cₖ²/2` the closed form reads `D · ∑ₖ aₖ Fₖ Φ(cₖ − z*)`. -/
theorem condBoundCall_eq_forward {m : ℕ} (D : ℝ) (a F c : Fin m → ℝ) (hF : ∀ k, 0 < F k)
    (zs : ℝ) :
    condBoundCall D a (condShift F c) c zs = D * ∑ k, a k * F k * Phi (c k - zs) := by
  unfold condBoundCall condShift
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [show Real.log (F k) - c k ^ 2 / 2 + c k ^ 2 / 2 = Real.log (F k) by ring,
    Real.exp_log (hF k)]

/-- **One fixing at `t < T`.** The data are `u = (−1, 1)` at dates
`(t, T)` and forwards `(S e^{rt}, S e^{rT})`. Then `expSum` is positive exactly to the right of
`z* = s/2 − rτ/s` (`τ = T − t`, `s = σ√τ`), and the conditioning bound with discount `e^{−rT}`
equals `S · bsV 1 r σ 1 (T − t)`: the forward-start call `(S_T − S_t)⁺`, priced by the
Black–Scholes formula at unit spot and strike. The identity uses only `τ = T − t > 0`; for
`0 ≤ t` it is the forward-start price, and no past fixings enter. -/
theorem condBoundCall_one_fixing (S r σ t T : ℝ) (hS : 0 < S) (hσ : 0 < σ)
    (htT : t < T) :
    let ts : Fin 2 → ℝ := ![t, T]
    let u : Fin 2 → ℝ := ![-1, 1]
    let F : Fin 2 → ℝ := ![S * Real.exp (r * t), S * Real.exp (r * T)]
    let c := condRate σ ts u
    let d := condShift F c
    let zs := σ * Real.sqrt (T - t) / 2 - r * (T - t) / (σ * Real.sqrt (T - t))
    (∀ z, 0 < expSum u d c z ↔ zs < z) ∧
      condBoundCall (Real.exp (-(r * T))) u d c zs = S * bsV 1 r σ 1 (T - t) := by
  intro ts u F c d zs
  have hτ : 0 < T - t := sub_pos.2 htT
  have hsq : 0 < Real.sqrt (T - t) := Real.sqrt_pos.2 hτ
  set s : ℝ := σ * Real.sqrt (T - t) with hs
  have hs0 : 0 < s := mul_pos hσ hsq
  have hs2 : s ^ 2 = σ ^ 2 * (T - t) := by rw [hs, mul_pow, Real.sq_sqrt hτ.le]
  have hmin : min t T = t := min_eq_left htT.le
  have hmin' : min T t = t := min_eq_right htT.le
  have hc0 : c 0 = 0 := by
    simp only [c, condRate, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, mul_neg, mul_one,
      neg_mul, min_self, one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one, hmin', hmin,
      neg_add_cancel, zero_div, ts, u]
  have hc1 : c 1 = s := by
    have hV : ∑ i, ∑ j, u i * u j * (σ ^ 2 * min (ts i) (ts j)) = s ^ 2 := by
      simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, mul_neg, mul_one, neg_mul,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, min_self, one_mul, neg_neg, hmin,
        add_neg_cancel, hmin', zero_add, u, ts]; rw [hs2]; ring
    have hnum : ∑ j, u j * (σ ^ 2 * min (ts j) (ts 1)) = s ^ 2 := by
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.sum_univ_two,
        Matrix.cons_val_zero, hmin, neg_mul, one_mul, min_self, u, ts]; rw [hs2]; ring
    simp only [c, condRate, hV, hnum, Real.sqrt_sq hs0.le]
    field_simp
  have hF : ∀ k, 0 < F k := by
    intro k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, F]; positivity
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, F]
      positivity
  have hzs : zs = s / 2 - r * (T - t) / s := rfl
  have hsz : s * zs = s ^ 2 / 2 - r * (T - t) := by rw [hzs]; field_simp
  have hF0 : F 0 = S * Real.exp (r * t) := rfl
  have hF1 : F 1 = S * Real.exp (r * T) := rfl
  have hform : ∀ z, expSum u d c z = -F 0 + F 1 * Real.exp (-(s ^ 2 / 2) + s * z) := by
    intro z
    have e0 : Real.exp (d 0 + c 0 * z) = F 0 := by
      simp only [d, condShift, hc0]
      rw [show Real.log (F 0) - 0 ^ 2 / 2 + 0 * z = Real.log (F 0) by ring,
        Real.exp_log (hF 0)]
    have e1 : Real.exp (d 1 + c 1 * z) = F 1 * Real.exp (-(s ^ 2 / 2) + s * z) := by
      simp only [d, condShift, hc1]
      rw [show Real.log (F 1) - s ^ 2 / 2 + s * z
          = Real.log (F 1) + (-(s ^ 2 / 2) + s * z) by ring, Real.exp_add,
        Real.exp_log (hF 1)]
    simp only [expSum, Fin.sum_univ_two, e0, e1]
    simp [u]
  have hroot : expSum u d c zs = 0 := by
    rw [hform, show -(s ^ 2 / 2) + s * zs = -(r * (T - t)) by rw [hsz]; ring, hF1,
      mul_assoc, ← Real.exp_add, hF0]
    rw [show r * T + -(r * (T - t)) = r * t by ring]
    ring
  have hpos : ∀ z, 0 < expSum u d c z ↔ zs < z := by
    refine expSum_pos_iff_of_root (p := 0) (fun k ↦ ?_) ⟨1, ?_⟩ hroot
    · fin_cases k <;> simp [u, hc0, hc1, hs0.le]
    · simp [u, hc1, hs0]
  refine ⟨hpos, ?_⟩
  rw [condBoundCall_eq_forward _ u F c hF zs, Fin.sum_univ_two, hc0, hc1]
  have hd1 : bsd1 1 1 r σ (T - t) = s - zs := by
    unfold bsd1
    rw [div_one, Real.log_one, zero_add]
    change (r + σ ^ 2 / 2) * (T - t) / s = s - zs
    rw [div_eq_iff hs0.ne']
    linear_combination hsz + (-1 / 2 : ℝ) * hs2
  have hd2 : bsd2 1 1 r σ (T - t) = -zs := by
    unfold bsd2
    rw [hd1]; ring
  rw [bsV, hd1, hd2]
  simp only [u, hF0, hF1]
  simp only [Fin.isValue, Matrix.cons_val_zero, neg_mul, one_mul, zero_sub, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have h1 : Real.exp (-(r * T)) * Real.exp (r * t) = Real.exp (-(r * (T - t))) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-(r * T)) * Real.exp (r * T) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (-(S * Phi (-zs))) * h1 + S * Phi (s - zs) * h2

/-- **The one-fixing bound is `S` times the market price of the unit-strike call.** In the
Black–Scholes market of spot `1`, drift and rate `r`, the pricing measure's price of
`europeanCall 1 τ` (`τ = T − t > 0`, horizon `H ≥ τ`) is `bsV 1 r σ 1 τ`
(`price_europeanCall_constGirsanovMeasure`), so the one-fixing conditioning bound of
`condBoundCall_one_fixing` is `S` times it: the forward-start call, grounded in the pricing
functional. Only `τ > 0` is used; for `0 ≤ t` this is the forward-start price. -/
theorem condBoundCall_one_fixing_eq_marketPrice {Ω : Type*} [MeasurableSpace Ω]
    {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] (hW : IsPreBrownianReal W μ)
    (hWmeas : ∀ s, Measurable (W s)) (S r σ t T : ℝ) {τ H : ℝ≥0} (hS : 0 < S) (hσ : 0 < σ)
    (htT : t < T) (hτ : (τ : ℝ) = T - t) (hτH : τ ≤ H) :
    let ts : Fin 2 → ℝ := ![t, T]
    let u : Fin 2 → ℝ := ![-1, 1]
    let F : Fin 2 → ℝ := ![S * Real.exp (r * t), S * Real.exp (r * T)]
    let c := condRate σ ts u
    let d := condShift F c
    let zs := σ * Real.sqrt (T - t) / 2 - r * (T - t) / (σ * Real.sqrt (T - t))
    condBoundCall (Real.exp (-(r * T))) u d c zs
      = S * (Contracts.BlackScholes.market μ hWmeas 1 r r σ).price
          (Contracts.BlackScholes.constGirsanovMeasure hW hWmeas 0 H)
          (Contracts.europeanCall 1 τ) := by
  intro ts u F c d zs
  have hτpos : 0 < (τ : ℝ) := hτ ▸ sub_pos.2 htT
  have key := Contracts.BlackScholes.price_europeanCall_constGirsanovMeasure
    (S_0 := 1) (m := r) (r := r) (σ := σ) (K := 1) hW hWmeas hτH one_pos one_pos hσ hτpos
  rw [sub_self, zero_div] at key
  rw [key, (condBoundCall_one_fixing S r σ t T hS hσ htT).2, bsV, hτ]
  simp only [one_mul, neg_mul]

end MathFin
