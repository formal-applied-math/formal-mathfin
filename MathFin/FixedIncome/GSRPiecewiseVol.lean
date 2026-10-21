/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.BrownianMotion
public import MathFin.Foundations.WienerIntegralGaussian
public import MathFin.Foundations.BrownianMartingale
public import MathFin.FixedIncome.VasicekBondPrice

/-!
# GSR (Gaussian short rate) with two-piece piecewise-constant volatility

The **GSR model** (QuantLib's `GsrProcess`/one-factor `Gsr` model) generalizes Vasicek/
Hull-White by letting the diffusion coefficient be **piecewise constant in calendar
time** rather than a single scalar — the feature actually exercised in cap/swaption
calibration, where a term structure of volatility is bootstrapped bucket by bucket.
Mean reversion is kept constant here, matching common GSR calibration practice
(reversion is held fixed while volatility is bucketed); `θ` is likewise constant
(the time-varying-drift generalization is `Foundations/HullWhiteCalibration.lean`'s
separate contribution and composes with this one in principle, but is not combined
here).

**Scope note**: this file proves
the **two-piece** case — volatility `σ₁` on `(0, T*]`, `σ₂` on `(T*, T]`, for a fixed
breakpoint `T* ∈ [0, T]` — not the general finitely-many-pieces GSR. The obstruction to
full generality is not conceptual (the argument below is already piece-count-agnostic
in spirit: split, apply FTC on each piece, sum variances) but mechanical: each
additional piece needs its own disjoint-union / interval-additivity bookkeeping, which
is better done once as an induction over a list of breakpoints than hand-duplicated.
Two pieces is the smallest case that is genuinely new (distinct from the
constant-`σ` Vasicek bond price `vasicekBondPrice_eq`) and already demonstrates the
mechanism in full.

## Why this is still "the same Gaussian-moment substrate"

Even with `σ` piecewise constant, the integrated short rate's diffusion part
`∫₀ᵀ σ(u)·g(u) dB_u` (`g` the Vasicek integrated kernel of `VasicekBondPrice.lean`) is
still the Wiener integral of a single **deterministic** `L²` integrand `u ↦ σ(u)·g(u)` —
piecewise-constant `σ` times a bounded kernel is still bounded, hence `L²` on the
finite-measure window. No new stochastic-integral machinery is needed: only a new
(elementary) variance integral, computed by splitting the integration domain at `T*` and
evaluating the antiderivative `vasicekIntegratedKernelSqAntideriv` of `g²` at the three
points `0, T*, T` (`integral_vasicekIntegratedKernel_sq_eq_sub`).

As in `VasicekBondPrice`, the integrated short rate is *defined* by its Wiener
representation `M(T) + ∫₀ᵀ σ(u)·g(u) dB_u` (`gsrIntegratedRate`): that it is the integral
of the solution of the GSR short-rate SDE (the SDE solution plus the time-order swap) is the
modelling bridge, cited, not derived here. Everything downstream of the representation is
derived.

## Main results

* `gsrSigma`, `gsrKernel` — the two-piece volatility and the σ-weighted kernel.
* `gsrBondV` — the closed-form variance `σ₁²·V(0,T*) + σ₂²·V(T*,T)`.
* `gsrKernel_integral_sq_eq` — the core calculus fact: the kernel's `L²` norm over
  `(0,T]` equals `gsrBondV`.
* `gsrIntegratedRate_hasLaw_gaussian` — the integrated short rate is Gaussian with
  this variance.
* `gsrBondPrice_eq` — the exponential-Gaussian zero-coupon bond price.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### Two-piece piecewise-constant volatility -/

/-- **Two-piece piecewise-constant volatility**: `σ₁` on `(-∞, T*]`, `σ₂` on `(T*, ∞)`. -/
noncomputable def gsrSigma (σ1 σ2 Tstar u : ℝ) : ℝ := if u ≤ Tstar then σ1 else σ2

/-- `gsrSigma` is measurable: it is an `ite` on the measurable set `{u | u ≤ Tstar}` with
constant branches. -/
private lemma gsrSigma_measurable (σ1 σ2 Tstar : ℝ) : Measurable (gsrSigma σ1 σ2 Tstar) := by
  unfold gsrSigma
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- The **GSR kernel**: the Vasicek integrated kernel `g` weighted by the piecewise
volatility — the deterministic integrand of the diffusion part `∫₀ᵀ σ(u)g(u) dB_u`. -/
noncomputable def gsrKernel (σ1 σ2 Tstar κ T : ℝ) : ℝ → ℝ :=
  fun u ↦ gsrSigma σ1 σ2 Tstar u * vasicekIntegratedKernel κ T u

/-! ### The GSR kernel is an `L²` integrand -/

/-- The GSR kernel is in `L²((0, T])`: `|σ(u)| ≤ max |σ₁| |σ₂|` and `0 ≤ g(u) ≤ 1/κ`
(for `κ > 0`), so the product is bounded by `max |σ₁| |σ₂| / κ`. -/
lemma gsrKernel_memLp {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 Tstar : ℝ) (T : ℝ≥0) :
    MemLp (gsrKernel σ1 σ2 Tstar κ (T : ℝ)) 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
  have hg_meas : Measurable (vasicekIntegratedKernel κ (T : ℝ)) := by
    unfold vasicekIntegratedKernel; fun_prop
  refine (memLp_top_of_bound
    (by unfold gsrKernel
        exact ((gsrSigma_measurable σ1 σ2 Tstar).mul hg_meas).aestronglyMeasurable)
    (max |σ1| |σ2| / κ) ?_).mono_exponent le_top
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ ?_)
  intro u hu
  rw [gsrKernel, Real.norm_eq_abs, abs_mul]
  have hexp_pos : 0 < Real.exp (-(κ * ((T : ℝ) - u))) := Real.exp_pos _
  have hTu : 0 ≤ (T : ℝ) - u := by linarith [hu.2]
  have hexp_le : Real.exp (-(κ * ((T : ℝ) - u))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hκ.le hTu])
  have hg_nonneg : 0 ≤ vasicekIntegratedKernel κ (T : ℝ) u := by
    rw [vasicekIntegratedKernel]; exact div_nonneg (by linarith) hκ.le
  have hg_le : vasicekIntegratedKernel κ (T : ℝ) u ≤ 1 / κ := by
    rw [vasicekIntegratedKernel]
    exact (div_le_div_iff_of_pos_right hκ).mpr (by linarith)
  have hσ_le : |gsrSigma σ1 σ2 Tstar u| ≤ max |σ1| |σ2| := by
    unfold gsrSigma; split
    · exact le_max_left _ _
    · exact le_max_right _ _
  calc |gsrSigma σ1 σ2 Tstar u| * |vasicekIntegratedKernel κ (T : ℝ) u|
      ≤ max |σ1| |σ2| * (1 / κ) :=
        mul_le_mul hσ_le (by rw [abs_of_nonneg hg_nonneg]; exact hg_le) (abs_nonneg _)
          (le_trans (abs_nonneg _) hσ_le)
    _ = max |σ1| |σ2| / κ := by ring

/-- The GSR kernel as an element of `L²((0, T])`. -/
noncomputable def gsrKernelLp {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 Tstar : ℝ) (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  (gsrKernel_memLp hκ σ1 σ2 Tstar T).toLp _

/-! ### The variance integral, by splitting at `T*` -/

/-- **The GSR closed-form variance**: `σ₁²·(F(T*) - F(0)) + σ₂²·(F(T) - F(T*))`,
`F = vasicekIntegratedKernelSqAntideriv κ T` (the antiderivative of `g²`). -/
noncomputable def gsrBondV (κ σ1 σ2 Tstar T : ℝ) : ℝ :=
  σ1 ^ 2 * (vasicekIntegratedKernelSqAntideriv κ T Tstar
      - vasicekIntegratedKernelSqAntideriv κ T 0)
    + σ2 ^ 2 * (vasicekIntegratedKernelSqAntideriv κ T T
      - vasicekIntegratedKernelSqAntideriv κ T Tstar)

/-- **The core calculus fact**: the `(0,T]`-window `L²` norm of the GSR kernel is the
closed-form `gsrBondV`, by splitting the window at `T*` (`gsrKernel` restricted to
`(0,T*]` is exactly `σ₁ · g`, and restricted to `(T*,T]` is exactly `σ₂ · g` — no
approximation, a genuine case split on `gsrSigma`'s own definition) and applying
`integral_vasicekIntegratedKernel_sq_eq_sub` on each piece. -/
theorem gsrKernel_integral_sq_eq {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 Tstar T : ℝ)
    (hTstar0 : 0 ≤ Tstar) (hTstarT : Tstar ≤ T) :
    ∫ u in Set.Ioc (0 : ℝ) T, (gsrKernel σ1 σ2 Tstar κ T u) ^ 2 ∂volume
      = gsrBondV κ σ1 σ2 Tstar T := by
  have heq1 : Set.EqOn (fun u ↦ (gsrKernel σ1 σ2 Tstar κ T u) ^ 2)
      (fun u ↦ σ1 ^ 2 * vasicekIntegratedKernel κ T u ^ 2) (Set.Ioc (0 : ℝ) Tstar) := by
    intro u hu
    simp only [gsrKernel, gsrSigma, if_pos hu.2]
    ring
  have heq2 : Set.EqOn (fun u ↦ (gsrKernel σ1 σ2 Tstar κ T u) ^ 2)
      (fun u ↦ σ2 ^ 2 * vasicekIntegratedKernel κ T u ^ 2) (Set.Ioc Tstar T) := by
    intro u hu
    simp only [gsrKernel, gsrSigma, if_neg (not_le.mpr hu.1)]
    ring
  have hcont1 : IntegrableOn (fun u ↦ σ1 ^ 2 * vasicekIntegratedKernel κ T u ^ 2)
      (Set.Ioc (0 : ℝ) Tstar) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hTstar0).mp
      (by apply Continuous.intervalIntegrable; unfold vasicekIntegratedKernel; fun_prop)
  have hcont2 : IntegrableOn (fun u ↦ σ2 ^ 2 * vasicekIntegratedKernel κ T u ^ 2)
      (Set.Ioc Tstar T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hTstarT).mp
      (by apply Continuous.intervalIntegrable; unfold vasicekIntegratedKernel; fun_prop)
  have hmeas1 : IntegrableOn (fun u ↦ (gsrKernel σ1 σ2 Tstar κ T u) ^ 2)
      (Set.Ioc (0 : ℝ) Tstar) volume := hcont1.congr_fun heq1.symm measurableSet_Ioc
  have hmeas2 : IntegrableOn (fun u ↦ (gsrKernel σ1 σ2 Tstar κ T u) ^ 2)
      (Set.Ioc Tstar T) volume := hcont2.congr_fun heq2.symm measurableSet_Ioc
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) Tstar) (Set.Ioc Tstar T) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 ↦ absurd hx2.1 (not_lt.mpr hx1.2))
  have hstep1 : ∫ u in Set.Ioc (0 : ℝ) T, (gsrKernel σ1 σ2 Tstar κ T u) ^ 2 ∂volume
      = (∫ u in Set.Ioc (0 : ℝ) Tstar, (gsrKernel σ1 σ2 Tstar κ T u) ^ 2 ∂volume)
        + ∫ u in Set.Ioc Tstar T, (gsrKernel σ1 σ2 Tstar κ T u) ^ 2 ∂volume := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc hTstar0 hTstarT,
      setIntegral_union hdisj measurableSet_Ioc hmeas1 hmeas2]
  have hstep2 : ∫ u in Set.Ioc (0 : ℝ) Tstar, (gsrKernel σ1 σ2 Tstar κ T u) ^ 2 ∂volume
      = σ1 ^ 2 * (vasicekIntegratedKernelSqAntideriv κ T Tstar
          - vasicekIntegratedKernelSqAntideriv κ T 0) := by
    rw [setIntegral_congr_fun measurableSet_Ioc heq1, integral_const_mul,
      ← intervalIntegral.integral_of_le hTstar0,
      integral_vasicekIntegratedKernel_sq_eq_sub κ T 0 Tstar hκ.ne']
  have hstep3 : ∫ u in Set.Ioc Tstar T, (gsrKernel σ1 σ2 Tstar κ T u) ^ 2 ∂volume
      = σ2 ^ 2 * (vasicekIntegratedKernelSqAntideriv κ T T
          - vasicekIntegratedKernelSqAntideriv κ T Tstar) := by
    rw [setIntegral_congr_fun measurableSet_Ioc heq2, integral_const_mul,
      ← intervalIntegral.integral_of_le hTstarT,
      integral_vasicekIntegratedKernel_sq_eq_sub κ T Tstar T hκ.ne']
  rw [hstep1, hstep2, hstep3, gsrBondV]

/-! ### The GSR short rate and the bond price -/

/-- `gsrBondV ≥ 0` (an integral of a square). -/
private lemma gsrBondV_nonneg {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 Tstar T : ℝ)
    (hTstar0 : 0 ≤ Tstar) (hTstarT : Tstar ≤ T) :
    (0 : ℝ) ≤ gsrBondV κ σ1 σ2 Tstar T := by
  rw [← gsrKernel_integral_sq_eq hκ σ1 σ2 Tstar T hTstar0 hTstarT]
  exact integral_nonneg fun u ↦ sq_nonneg _

/-- `∫₀ᵀ (gsrKernelLp)² = gsrBondV` for the `L²`-representative (a.e. equal to the
honest kernel). -/
private lemma gsrKernelLp_integral_sq {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 : ℝ) (Tstar T : ℝ≥0)
    (hTstarT : (Tstar : ℝ) ≤ (T : ℝ)) :
    (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T u) ^ 2 ∂volume)
      = gsrBondV κ σ1 σ2 (Tstar : ℝ) (T : ℝ) := by
  rw [show (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T u) ^ 2 ∂volume)
        = ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (gsrKernel σ1 σ2 (Tstar : ℝ) κ (T : ℝ) u) ^ 2 ∂volume by
      refine integral_congr_ae ?_
      filter_upwards [(gsrKernel_memLp hκ σ1 σ2 (Tstar : ℝ) T).coeFn_toLp] with u hu
      rw [gsrKernelLp, hu]]
  exact gsrKernel_integral_sq_eq hκ σ1 σ2 (Tstar : ℝ) (T : ℝ) Tstar.2 hTstarT

/-- The centred diffusion law for the GSR kernel: `∫₀ᵀ σ(u)g(u) dB_u` is centred
Gaussian with variance `gsrBondV κ σ₁ σ₂ T* T`. -/
private lemma gsrWienerLaw (hB : IsPreBrownianReal B μ) {κ : ℝ} (hκ : 0 < κ)
    (σ1 σ2 : ℝ) (Tstar T : ℝ≥0) (hTstarT : (Tstar : ℝ) ≤ (T : ℝ)) :
    HasLaw (fun ω ↦ wienerIntegralLp B hB T (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T) ω)
      (gaussianReal 0 (gsrBondV κ σ1 σ2 (Tstar : ℝ) (T : ℝ)).toNNReal) μ := by
  have h0 := wienerIntegralLp_hasLaw_gaussian hB T (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T)
  rwa [gsrKernelLp_integral_sq hκ σ1 σ2 Tstar T hTstarT] at h0

/-- **The GSR integrated short rate**, *defined* by its Wiener representation: deterministic
mean (the Vasicek mean, unchanged — only the volatility axis is piecewise here) plus the
Wiener integral of the piecewise-weighted kernel. That this is `∫₀ᵀ r_s ds` for the solution
of the GSR short-rate SDE is the modelling bridge (the SDE solution and the time-order swap),
cited, not derived, as for `vasicekIntegratedRate`. -/
noncomputable def gsrIntegratedRate (hB : IsPreBrownianReal B μ) (r₀ θ σ1 σ2 : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (Tstar T : ℝ≥0) (ω : Ω) : ℝ :=
  vasicekIntegratedMean r₀ θ κ (T : ℝ)
    + wienerIntegralLp B hB T (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T) ω

/-- **The GSR integrated short rate is Gaussian**: `N(M(T), gsrBondV κ σ₁ σ₂ T* T)`,
`M` the (unchanged) Vasicek mean. -/
theorem gsrIntegratedRate_hasLaw_gaussian (hB : IsPreBrownianReal B μ) (r₀ θ σ1 σ2 : ℝ)
    {κ : ℝ} (hκ : 0 < κ) (Tstar T : ℝ≥0) (hTstarT : (Tstar : ℝ) ≤ (T : ℝ)) :
    HasLaw (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar T)
      (gaussianReal (vasicekIntegratedMean r₀ θ κ (T : ℝ))
        (gsrBondV κ σ1 σ2 (Tstar : ℝ) (T : ℝ)).toNNReal) μ := by
  have hW := gsrWienerLaw hB hκ σ1 σ2 Tstar T hTstarT
  have hShift := gaussianReal_const_add hW (vasicekIntegratedMean r₀ θ κ (T : ℝ))
  convert hShift using 2 <;> first | rfl | ring

/-- **The GSR zero-coupon bond price**: the exponential-Gaussian moment
`P(0,T) = exp(−M(T) + gsrBondV κ σ₁ σ₂ T* T / 2)`, the exact two-piece-volatility
analogue of `vasicekBondPrice_eq`. -/
theorem gsrBondPrice_eq (hB : IsPreBrownianReal B μ) (r₀ θ σ1 σ2 : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (Tstar T : ℝ≥0) (hTstarT : (Tstar : ℝ) ≤ (T : ℝ)) :
    ∫ ω, Real.exp (-(gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar T ω)) ∂μ
      = Real.exp (-(vasicekIntegratedMean r₀ θ κ (T : ℝ))
          + gsrBondV κ σ1 σ2 (Tstar : ℝ) (T : ℝ) / 2) := by
  set M : ℝ := vasicekIntegratedMean r₀ θ κ (T : ℝ) with hM
  set V : ℝ := gsrBondV κ σ1 σ2 (Tstar : ℝ) (T : ℝ) with hV
  have hV_nonneg : (0 : ℝ) ≤ V := hV ▸ gsrBondV_nonneg hκ σ1 σ2 (Tstar : ℝ) (T : ℝ) Tstar.2 hTstarT
  have hW : HasLaw (fun ω ↦ wienerIntegralLp B hB T (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T) ω)
      (gaussianReal 0 V.toNNReal) μ := hV ▸ gsrWienerLaw hB hκ σ1 σ2 Tstar T hTstarT
  have hfactor : ∀ ω, Real.exp (-(gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar T ω))
      = Real.exp (-M) * Real.exp ((-(1 : ℝ)) *
          (wienerIntegralLp B hB T (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T) ω)) := by
    intro ω
    rw [gsrIntegratedRate, ← hM, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hfactor]
  rw [integral_const_mul,
    show (fun ω ↦ Real.exp ((-(1 : ℝ)) * (wienerIntegralLp B hB T (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T) ω)))
        = (fun x ↦ Real.exp ((-(1 : ℝ)) * x))
          ∘ (fun ω ↦ wienerIntegralLp B hB T (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T) ω) from rfl,
    hW.integral_comp (by fun_prop : AEStronglyMeasurable (fun x ↦ Real.exp ((-(1 : ℝ)) * x))
      (gaussianReal 0 V.toNNReal)),
    integral_exp_mul_gaussianReal_zero (-(1 : ℝ)) V.toNNReal,
    Real.coe_toNNReal _ hV_nonneg, ← Real.exp_add]
  congr 1
  ring

end MathFin
