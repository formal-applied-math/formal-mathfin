/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
import MathFin.BlackScholes.PutGreeks
import MathFin.BlackScholes.StrikeGreeks

/-!
# The forward smile: Dupire's ratio on a linear smile surface (eq 10.8)

Setting: zero rates, one maturity axis `T`, log-moneyness `k = log(K/F)`, a fixed
forward `F > 0`. The smile surface of eq 10.7 is tilted by a parameter `ε` so that
first-order-in-ε readings extract the skew slope:

  `σ_BS(ε, k, T) = σ + ε·ψ₁·k/√(T+T₀)`   (`smileSurface`; `σ > 0`, `T+T₀ > 0`)

and the call prices on it are the `bsV` composites (`bsCallSmile`). Dupire's
zero-rates ratio

  `R(ε, k, T) = 2·∂_T C / (K²·∂²_K C)`  (in `k`-form: `K²·∂²_K C = C_kk − C_k`)

enters **as a definition** (`dupireRatio`) — the derivation of the ratio itself
from a local-vol model is not developed here. The headline results:

* `dupireRatio_k_slope` — eq 10.8: the ATM k-slope of `R` has ε-slope
  `2σψ₁·((3/2)T + 2T₀)/(T+T₀)^{3/2}` (with `(T+T₀)^{3/2}` rendered as
  `(T+T₀)·√(T+T₀)`). **Typography note:** the chapter's printed numerator is
  `(3/2)T + 2T₀` — a common text-extraction of the stacked fraction renders it
  as `T + 2T₀`, which contradicts the chapter's own rule-of-two limit; the
  image-verified form is built here. The T=0 value
  recovers the rule of two exactly (`ruleOfTwo`).
* `dupireRatio_sqrt_slope` — the σ_loc reading: the same slope for `√R` is
  `ψ₁·((3/2)T + 2T₀)/(T+T₀)^{3/2}` — the local-vol ATM skew implied by the
  surface; `2×` the implied skew at `T = 0`, `(3/2)ψ₁/√T` asymptotically
  (`localSkew_tendsto`).
* `forwardSkew_eq_half` / `forwardSkew_tendsto` — eq 10.9 as chapter math
  anchored on the proved slope (the rule-of-two-in-reverse half-step), with the
  chapter's numeric readings at σ = 20%, ψ₁ = −0.10, T₀ = 1/12
  (`skewRatio_one/four/ten`: a fifth, an eighth, under a tenth).

Method (no probability, no integration, no ODEs): everything is a one-variable
`HasDerivAt` chain rule through the Black form `Φ(d₊) − e^k·Φ(d₋)` in the
coordinates `(k, w)` with total variance `w = σ̃²T`. The key exact identity is
`dupireRatio_eq`: in these coordinates Dupire's ratio is the rational function
`w_T/(1 + δ)` with `δ = −k·w_k/w + w_k²·(k²−w−w²/4)/(4w²) + w_kk/2` — the
Gatheral form of the ratio specialized to this surface — after which the
ε/k-extraction is elementary calculus on explicit functions. The `bsV` greek
layer (`MathFin.BlackScholes.PDE`: `bsV`, `bsd1`, `bsd2`,
`hasDerivAt_bsV_*`; `MathFin.BlackScholes.StrikeGreeks`: `hasDerivAt_bsV_K`,
`hasDerivAt_bsV_KK`) is the substrate: `bsV` is the price definition consumed,
`bsd1`/`bsd2` are unfolded to the `(k,w)` form (`bsCallSmile_eq`), and the
packaged strike greek `hasDerivAt_bsV_K` anchors the flat case
(`hasDerivAt_bsCallSmile_flat_k`). The
time-homogeneity side of the same chapter (§10.5.3's "no function of t" in the
Heston generator) is related but not consumed here.

Housekeeping: deriv-form chains are rebuilt from `HasDerivAt.deriv` +
`HasDerivAt.congr_of_eventuallyEq` / `congr_deriv` because the pinned MathFin
predates `Foundations.DerivOfDeriv`.
-/

namespace MathFin.ForwardSmile

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-! ## The surface, the price, the ratio -/

/-- **Eq 10.7, ε-tilted**: the smile surface `σ_BS(ε,k,T) = σ + ε·ψ₁·k/√(T+T₀)`
in log-moneyness `k = log(K/F)` at zero rates, with the tilt parameter `ε`
inserted so first-order-in-ε readings extract the skew slope. At `ε = 0` (and at
`k = 0` for every `ε`) it is the ATM vol `σ`. -/
noncomputable def smileSurface (σ ψ₁ T₀ ε k T : ℝ) : ℝ := σ + ε * ψ₁ * k / Real.sqrt (T + T₀)

/-- The smile surface is positive whenever the tilt is smaller than the base:
`|ε·ψ₁·k| < σ·√(T+T₀)` (positivity cannot hold for arbitrary tilts — the surface
dips below zero for large `|ε·ψ₁·k|`). -/
theorem smileSurface_pos {σ ψ₁ T₀ ε k T : ℝ} (hS : 0 < T + T₀)
    (hb : |ε * ψ₁ * k| < σ * Real.sqrt (T + T₀)) :
    0 < smileSurface σ ψ₁ T₀ ε k T := by
  have hs : 0 < Real.sqrt (T + T₀) := Real.sqrt_pos.mpr hS
  rw [abs_lt] at hb
  have hdiv : -σ < ε * ψ₁ * k / Real.sqrt (T + T₀) := by
    rw [lt_div_iff₀ hs]
    linarith [hb.1]
  unfold smileSurface
  linarith [hdiv]

/-- At the money the tilt vanishes: the surface sits at the base vol `σ` for
every `ε`. -/
theorem smileSurface_atm (σ ψ₁ T₀ ε T : ℝ) : smileSurface σ ψ₁ T₀ ε 0 T = σ := by
  unfold smileSurface; norm_num

/-- Total implied variance along the surface: `w = σ_BS²·T`. -/
noncomputable def totalVar (σ ψ₁ T₀ ε k T : ℝ) : ℝ := smileSurface σ ψ₁ T₀ ε k T ^ 2 * T

/-- The upper standardized normal argument in `(k, w)` coordinates:
`d₊ = (−k + w/2)/√w` (this is `bsd1 F (F·e^k) 0 σ̃ T` at `w = σ̃²T`). -/
noncomputable def dpl (k w : ℝ) : ℝ := (-k + w / 2) / Real.sqrt w

/-- The lower standardized normal argument: `d₋ = (−k − w/2)/√w`. -/
noncomputable def dmi (k w : ℝ) : ℝ := (-k - w / 2) / Real.sqrt w

/-- The Black-76 call normalized by the forward: `c(k,w) = Φ(d₊) − e^k·Φ(d₋)`,
the zero-rates `bsV` in `(k, w)` coordinates. -/
noncomputable def blackForm (k w : ℝ) : ℝ := Phi (dpl k w) - Real.exp k * Phi (dmi k w)

/-- **The call price on the tilted surface**: the zero-rates
`bsV` at strike `K = F·e^k`, spot `S = F`, vol `σ_BS(ε,k,T)`, maturity `T`. -/
noncomputable def bsCallSmile (F σ ψ₁ T₀ ε k T : ℝ) : ℝ :=
  bsV (F * Real.exp k) 0 (smileSurface σ ψ₁ T₀ ε k T) F T

/-- **Dupire's zero-rates ratio in k-form** (the ratio as a
definition — its derivation from a local-vol model is not developed here):
`R = 2·C_T/(C_kk − C_k)`, using `K²·∂²_K C = C_kk − C_k` for
`K = F·e^k`. -/
noncomputable def dupireRatio (F σ ψ₁ T₀ ε k T : ℝ) : ℝ :=
  2 * deriv (fun t => bsCallSmile F σ ψ₁ T₀ ε k t) T
    / (deriv (fun x => deriv (fun x => bsCallSmile F σ ψ₁ T₀ ε x T) x) k
        - deriv (fun x => bsCallSmile F σ ψ₁ T₀ ε x T) k)

/-! ## The `(k, w)` unfolding and the variance chains -/

/-- **The r=0, K=F·e^k magic identity**: `e^k·ϕ(d₋) = ϕ(d₊)` in `(k,w)`
coordinates — the k-form of the `bs_identity` at zero rates. It is
what makes every density term in the Dupire ratio collapse. -/
theorem exp_mul_pdf_dmi {k w : ℝ} (hw : 0 < w) :
    Real.exp k * gaussianPDFReal 0 1 (dmi k w) = gaussianPDFReal 0 1 (dpl k w) := by
  have hsq : dpl k w ^ 2 - dmi k w ^ 2 = -(2 * k) := by
    have hnum : (-k + w / 2) ^ 2 - (-k - w / 2) ^ 2 = -(2 * k) * w := by ring
    have h1 : dpl k w ^ 2 = (-k + w / 2) ^ 2 / w := by
      unfold dpl
      rw [show ((-k + w / 2) / Real.sqrt w) ^ 2 = (-k + w / 2) ^ 2 / Real.sqrt w ^ 2 from by
          ring, Real.sq_sqrt hw.le]
    have h2 : dmi k w ^ 2 = (-k - w / 2) ^ 2 / w := by
      unfold dmi
      rw [show ((-k - w / 2) / Real.sqrt w) ^ 2 = (-k - w / 2) ^ 2 / Real.sqrt w ^ 2 from by
          ring, Real.sq_sqrt hw.le]
    rw [h1, h2, ← sub_div, hnum]
    field_simp [hw.ne']
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [← mul_assoc, mul_comm (Real.exp k) (Real.sqrt (2 * π))⁻¹, mul_assoc,
    ← Real.exp_add,
    show k + -(dmi k w) ^ 2 / 2 = -(dpl k w) ^ 2 / 2 from by linarith [hsq]]

/-- **The `(k, w)` unfolding**: at zero rates with `K = F·e^k`, the `bsV`
composite on the tilted surface is the forward-normalized Black form at the
total variance `w = σ_BS²·T`. -/
theorem bsCallSmile_eq {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T)
    (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    bsCallSmile F σ ψ₁ T₀ ε k T = F * blackForm k (totalVar σ ψ₁ T₀ ε k T) := by
  have hlog : Real.log (F / (F * Real.exp k)) = -k := by
    rw [show F / (F * Real.exp k) = (Real.exp k)⁻¹ by field_simp, Real.log_inv, Real.log_exp]
  have hne : smileSurface σ ψ₁ T₀ ε k T * Real.sqrt T ≠ 0 :=
    mul_ne_zero hst.ne' (Real.sqrt_pos.mpr hT).ne'
  have hsplit : Real.sqrt (smileSurface σ ψ₁ T₀ ε k T ^ 2 * T)
      = smileSurface σ ψ₁ T₀ ε k T * Real.sqrt T := by
    rw [Real.sqrt_mul (sq_nonneg _) T, Real.sqrt_sq hst.le]
  have hbsd1 : bsd1 F (F * Real.exp k) 0 (smileSurface σ ψ₁ T₀ ε k T) T
      = dpl k (totalVar σ ψ₁ T₀ ε k T) := by
    unfold bsd1 dpl totalVar
    rw [hlog, hsplit]
    field_simp [hne]
    ring
  have hbsd2 : bsd2 F (F * Real.exp k) 0 (smileSurface σ ψ₁ T₀ ε k T) T
      = dmi k (totalVar σ ψ₁ T₀ ε k T) := by
    unfold bsd2
    rw [hbsd1]
    unfold dmi dpl totalVar
    rw [hsplit]
    field_simp [hne]
    rw [Real.sq_sqrt hT.le]
    ring
  unfold bsCallSmile bsV blackForm
  rw [hbsd1, hbsd2]
  norm_num [Real.exp_neg, Real.exp_zero]
  ring

/-- `∂_k σ_BS = ε·ψ₁/√(T+T₀)` — the surface is affine in `k`. -/
private theorem hasDerivAt_smileSurface_k {σ ψ₁ T₀ ε T x : ℝ} (hS : 0 < T + T₀) :
    HasDerivAt (fun y => smileSurface σ ψ₁ T₀ ε y T) (ε * ψ₁ / Real.sqrt (T + T₀)) x := by
  have h0 : HasDerivAt (fun y : ℝ => σ + (ε * ψ₁ / Real.sqrt (T + T₀)) * y)
      (ε * ψ₁ / Real.sqrt (T + T₀)) x := by
    simpa using ((hasDerivAt_id x).const_mul (ε * ψ₁ / Real.sqrt (T + T₀))).add_const σ
  refine h0.congr_of_eventuallyEq ?_
  filter_upwards with y
  unfold smileSurface
  field_simp
  try ring

/-- `∂_k w = 2·σ̃·(ε·ψ₁/√(T+T₀))·T` — the `k`-chain of the total variance. -/
private theorem hasDerivAt_totalVar_k {σ ψ₁ T₀ ε T x : ℝ} (hS : 0 < T + T₀) :
    HasDerivAt (fun y => totalVar σ ψ₁ T₀ ε y T)
      (2 * smileSurface σ ψ₁ T₀ ε x T * (ε * ψ₁ / Real.sqrt (T + T₀)) * T) x := by
  have hu := hasDerivAt_smileSurface_k (σ := σ) (ψ₁ := ψ₁) (T₀ := T₀) (ε := ε) (T := T) (x := x) hS
  have h2 : HasDerivAt (fun y => smileSurface σ ψ₁ T₀ ε y T ^ 2)
      (2 * smileSurface σ ψ₁ T₀ ε x T * (ε * ψ₁ / Real.sqrt (T + T₀))) x := by
    have hcp := (hasDerivAt_pow 2 (smileSurface σ ψ₁ T₀ ε x T)).comp x hu
    refine hcp.congr_deriv ?_
    ring
  exact h2.mul_const T

/-- `∂_T w = σ̃² − σ̃·(ε·ψ₁·k)·T/(T+T₀)^{3/2}` — the `T`-chain of the total
variance (both `T`-channels of `w = σ̃²T` move: `σ̃` carries `√(T+T₀)` in the
denominator). `(T+T₀)^{3/2}` is rendered `(T+T₀)·√(T+T₀)`. -/
private theorem hasDerivAt_totalVar_t {σ ψ₁ T₀ ε k T : ℝ} (_hT : 0 < T) (hS : 0 < T + T₀) :
    HasDerivAt (fun t => totalVar σ ψ₁ T₀ ε k t)
      (smileSurface σ ψ₁ T₀ ε k T ^ 2
        - smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ * k) * T / ((T + T₀) * Real.sqrt (T + T₀))) T := by
  have hs : Real.sqrt (T + T₀) ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  have hT₀ne : T + T₀ ≠ 0 := by linarith
  have hssq : Real.sqrt (T + T₀) ^ 2 = T + T₀ := Real.sq_sqrt hS.le
  have h1 : HasDerivAt (fun t : ℝ => t + T₀) 1 T := by
    simpa using (hasDerivAt_id T).add_const T₀
  have h2 : HasDerivAt (fun t : ℝ => Real.sqrt (t + T₀)) (1 / (2 * Real.sqrt (T + T₀))) T := by
    have hc := (Real.hasDerivAt_sqrt hT₀ne).comp T h1
    rw [Function.comp_def] at hc
    simpa only [mul_one] using hc
  have hinv : HasDerivAt (fun t : ℝ => (Real.sqrt (t + T₀))⁻¹)
      (-(Real.sqrt (T + T₀))⁻¹ ^ 2 * (1 / (2 * Real.sqrt (T + T₀)))) T := by
    have h0 := h2.inv hs
    refine h0.congr_deriv ?_
    field_simp [hssq]
  have hsigt : HasDerivAt (fun t : ℝ => σ + ε * ψ₁ * k * (Real.sqrt (t + T₀))⁻¹)
      (ε * ψ₁ * k * (-(Real.sqrt (T + T₀))⁻¹ ^ 2 * (1 / (2 * Real.sqrt (T + T₀))))) T := by
    have h0 := (hinv.const_mul (ε * ψ₁ * k)).add_const σ
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards with t
    ring
  have hsq : HasDerivAt (fun t : ℝ => (σ + ε * ψ₁ * k * (Real.sqrt (t + T₀))⁻¹) ^ 2)
      (2 * (σ + ε * ψ₁ * k * (Real.sqrt (T + T₀))⁻¹)
        * (ε * ψ₁ * k * (-(Real.sqrt (T + T₀))⁻¹ ^ 2 * (1 / (2 * Real.sqrt (T + T₀)))))) T := by
    have hc := (hasDerivAt_pow 2 _).comp T hsigt
    refine hc.congr_deriv ?_
    ring
  have hid : HasDerivAt (fun t : ℝ => t) 1 T := hasDerivAt_id T
  have hmul := hsq.mul hid
  have hfun : (fun t : ℝ => (σ + ε * ψ₁ * k * (Real.sqrt (t + T₀))⁻¹) ^ 2 * t)
      = fun t => totalVar σ ψ₁ T₀ ε k t := by
    funext t
    unfold totalVar smileSurface
    field_simp
    try ring
  have hfin := hmul.congr_of_eventuallyEq (Filter.Eventually.of_forall (congrFun hfun))
  refine hfin.congr_deriv ?_
  have hne : (T + T₀) * Real.sqrt (T + T₀) ≠ 0 := mul_ne_zero hT₀ne hs
  have hp3 : Real.sqrt (T + T₀) ^ 3 = (T + T₀) * Real.sqrt (T + T₀) := by
    rw [show Real.sqrt (T + T₀) ^ 3 = Real.sqrt (T + T₀) * Real.sqrt (T + T₀) ^ 2 from by ring,
      hssq]
    try ring
  have hp4 : Real.sqrt (T + T₀) ^ 4 = (T + T₀) ^ 2 := by
    rw [show Real.sqrt (T + T₀) ^ 4 = (Real.sqrt (T + T₀) ^ 2) ^ 2 from by ring, hssq]
    try ring
  unfold smileSurface
  field_simp [hne, hs]
  simp only [hssq]
  ring

/-! ## The composite chains in `(k, w)`: an abstract inner function `u` -/

/-- The `k`-chain of `d₊` through a moving inner function `u` (the total
variance composite): `∂_k d₊(k, u(k)) = ∂_k d₊ + ∂_w d₊·u'` at `x`, with
`∂_k d₊ = −1/√w` and `∂_w d₊ = (k + w/2)/(2w^{3/2})`. -/
private theorem hasDerivAt_dpl_comp {u : ℝ → ℝ} {x ub : ℝ} (hu : HasDerivAt u ub x)
    (hpos : 0 < u x) :
    HasDerivAt (fun y => dpl y (u y))
      (-(1 / Real.sqrt (u x)) + (x + u x / 2) / (2 * u x * Real.sqrt (u x)) * ub) x := by
  have hne : Real.sqrt (u x) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq : Real.sqrt (u x) ^ 2 = u x := Real.sq_sqrt hpos.le
  have hnum : HasDerivAt (fun y : ℝ => -y + u y / 2) (-1 + ub / 2) x :=
    (hasDerivAt_id x).neg.add (hu.div_const 2)
  have hden : HasDerivAt (fun y : ℝ => Real.sqrt (u y)) (ub / (2 * Real.sqrt (u x))) x := by
    have hc := (Real.hasDerivAt_sqrt hpos.ne').comp x hu
    rw [Function.comp_def] at hc
    exact hc.congr_deriv (by field_simp)
  have hq := hnum.div hden hne
  unfold dpl
  refine hq.congr_deriv ?_
  field_simp [hsq]
  simp only [hsq]
  ring

/-- The `k`-chain of `d₋` through a moving `u` (mirror of `hasDerivAt_dpl_comp`:
`∂_w d₋ = (k − w/2)/(2w^{3/2})`). -/
private theorem hasDerivAt_dmi_comp {u : ℝ → ℝ} {x ub : ℝ} (hu : HasDerivAt u ub x)
    (hpos : 0 < u x) :
    HasDerivAt (fun y => dmi y (u y))
      (-(1 / Real.sqrt (u x)) + (x - u x / 2) / (2 * u x * Real.sqrt (u x)) * ub) x := by
  have hne : Real.sqrt (u x) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq : Real.sqrt (u x) ^ 2 = u x := Real.sq_sqrt hpos.le
  have hnum : HasDerivAt (fun y : ℝ => -y - u y / 2) (-1 - ub / 2) x :=
    (hasDerivAt_id x).neg.sub (hu.div_const 2)
  have hden : HasDerivAt (fun y : ℝ => Real.sqrt (u y)) (ub / (2 * Real.sqrt (u x))) x := by
    have hc := (Real.hasDerivAt_sqrt hpos.ne').comp x hu
    rw [Function.comp_def] at hc
    exact hc.congr_deriv (by field_simp)
  have hq := hnum.div hden hne
  unfold dmi
  refine hq.congr_deriv ?_
  field_simp [hsq]
  simp only [hsq]
  ring

/-- The `k`-chain of `e^k·Φ(d₋(k, u(k)))` through a moving `u` — the strike
side of the Black form. -/
private theorem hasDerivAt_exp_Phi_dmi_comp {u : ℝ → ℝ} {x ub : ℝ} (hu : HasDerivAt u ub x)
    (hpos : 0 < u x) :
    HasDerivAt (fun y => Real.exp y * Phi (dmi y (u y)))
      (Real.exp x * Phi (dmi x (u x))
        + Real.exp x * (gaussianPDFReal 0 1 (dmi x (u x))
          * (-(1 / Real.sqrt (u x)) + (x - u x / 2) / (2 * u x * Real.sqrt (u x)) * ub))) x := by
  have hdmi := hasDerivAt_dmi_comp hu hpos
  have hPhi := (hasDerivAt_Phi (dmi x (u x))).comp x hdmi
  rw [Function.comp_def] at hPhi
  exact ((hasDerivAt_exp x).mul hPhi).congr_deriv (by ring)

/-- The `k`-chain of the whole Black form through a moving `u`:
`C_k/F = ϕ(d₊)·∂_k d₊^{comp} − [e^k Φ(d₋) + e^k ϕ(d₋)·∂_k d₋^{comp}]`. -/
private theorem hasDerivAt_blackForm_comp {u : ℝ → ℝ} {x ub : ℝ} (hu : HasDerivAt u ub x)
    (hpos : 0 < u x) :
    HasDerivAt (fun y => blackForm y (u y))
      (gaussianPDFReal 0 1 (dpl x (u x))
          * (-(1 / Real.sqrt (u x)) + (x + u x / 2) / (2 * u x * Real.sqrt (u x)) * ub)
        - (Real.exp x * Phi (dmi x (u x))
          + Real.exp x * (gaussianPDFReal 0 1 (dmi x (u x))
            * (-(1 / Real.sqrt (u x)) + (x - u x / 2) / (2 * u x * Real.sqrt (u x)) * ub)))) x := by
  have hdpl := hasDerivAt_dpl_comp hu hpos
  have hPhiP := (hasDerivAt_Phi (dpl x (u x))).comp x hdpl
  rw [Function.comp_def] at hPhiP
  have hex := hasDerivAt_exp_Phi_dmi_comp hu hpos
  unfold blackForm
  exact hPhiP.sub hex

/-- The `w`-chain of the Black form at fixed `k` (single slot): `∂_w c = ϕ(d₊)/(2√w)`. -/
private theorem hasDerivAt_blackForm_w {k w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun z => blackForm k z)
      (gaussianPDFReal 0 1 (dpl k w) / (2 * Real.sqrt w)) w := by
  have hne : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  have hsq : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw.le
  have hden : HasDerivAt (fun z : ℝ => Real.sqrt z) (1 / (2 * Real.sqrt w)) w :=
    Real.hasDerivAt_sqrt hw.ne'
  have hnP : HasDerivAt (fun z : ℝ => -k + z / 2) (1 / 2) w := by
    have h0 : HasDerivAt (fun z : ℝ => z / 2 + -k) (1 / 2) w :=
      ((hasDerivAt_id w).div_const 2).add_const (-k)
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards with z
    ring
  have hnM : HasDerivAt (fun z : ℝ => -k - z / 2) (-(1 / 2)) w := by
    have h1 : HasDerivAt (fun z : ℝ => z / 2) (1 / 2) w := (hasDerivAt_id w).div_const 2
    exact h1.const_sub (-k)
  have hdP := hnP.div hden hne
  have hdM := hnM.div hden hne
  have hPhiP := (hasDerivAt_Phi (dpl k w)).comp w hdP
  rw [Function.comp_def] at hPhiP
  have hPhiM := (hasDerivAt_Phi (dmi k w)).comp w hdM
  rw [Function.comp_def] at hPhiM
  have hexp := (hasDerivAt_const w (Real.exp k)).mul hPhiM
  have hfull := hPhiP.sub hexp
  refine (hfull.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with z
    unfold blackForm dpl dmi
    simp only [Pi.sub_apply, Pi.mul_apply]
  · rw [← exp_mul_pdf_dmi hw]
    field_simp [hsq]
    simp only [hsq]
    ring

/-- The `k`-chain of the vega-density quotient `ϕ(d₊(k,u(k)))/(2√(u(k)))` — the
B_w-value composite: its `k`-derivative is `B_wk + B_ww·u'` with
`B_wk = d₊ϕ(d₊)/(2w)` and `B_ww = ϕ(d₊)(k²−w−w²/4)/(4w^{5/2})`. -/
private theorem hasDerivAt_Bw_comp {u : ℝ → ℝ} {x ub : ℝ} (hu : HasDerivAt u ub x)
    (hpos : 0 < u x) :
    HasDerivAt (fun y => gaussianPDFReal 0 1 (dpl y (u y)) / (2 * Real.sqrt (u y)))
      (dpl x (u x) * gaussianPDFReal 0 1 (dpl x (u x)) / (2 * u x)
        + gaussianPDFReal 0 1 (dpl x (u x)) * (x ^ 2 - u x - u x ^ 2 / 4)
            / (4 * u x ^ 2 * Real.sqrt (u x)) * ub) x := by
  have hne : Real.sqrt (u x) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq : Real.sqrt (u x) ^ 2 = u x := Real.sq_sqrt hpos.le
  have hdpl := hasDerivAt_dpl_comp hu hpos
  have hphi := (hasDerivAt_gaussianPDFReal_zero_one (dpl x (u x))).comp x hdpl
  rw [Function.comp_def] at hphi
  have hden : HasDerivAt (fun y : ℝ => 2 * Real.sqrt (u y)) (ub / Real.sqrt (u x)) x := by
    have hc := (Real.hasDerivAt_sqrt hpos.ne').comp x hu
    rw [Function.comp_def] at hc
    refine (hc.const_mul 2).congr_deriv ?_
    field_simp
  have hdenne : 2 * Real.sqrt (u x) ≠ 0 :=
    (mul_pos two_pos (Real.sqrt_pos.mpr hpos)).ne'
  refine (hphi.div hden hdenne).congr_deriv ?_
  unfold dpl
  field_simp [hsq]
  simp only [hsq]
  ring

/-- The `k`-derivative of the *slope-value function* of `d±` through a moving
`u` with its own derivative function `v` (so `v x = u' x`, `v' = c`): the
second-order chain building block behind `C_kk`. With
`f = −(√(u))⁻¹ + (y + sgn·u/2)/(2u√u)·v`,
`f' = b/(2√u) + (1 + sgn·b/2)·v₀/(2u√u) − (y + sgn·u/2)·3b·v₀/(4u²√u)
      + (y + sgn·u/2)·(2u√u)⁻¹·c`
at the point (verified: for `u = id`, `v = 1` at `x = 1`, `sgn = ±1` it
reproduces `∓(1/4)·y^{-1/2}`-type composites' derivatives). -/
private theorem hasDerivAt_slopeval_comp {u v : ℝ → ℝ} {x b c sgn : ℝ}
    (hu : HasDerivAt u b x) (hv : HasDerivAt v c x) (hpos : 0 < u x) :
    HasDerivAt (fun y => -(Real.sqrt (u y))⁻¹ + (y + sgn * (u y / 2))
        / (2 * u y * Real.sqrt (u y)) * v y)
      (b / (2 * u x * Real.sqrt (u x))
        + (1 + sgn * (b / 2)) * v x / (2 * u x * Real.sqrt (u x))
        + (x + sgn * (u x / 2)) * (-(3 * b / (4 * u x ^ 2 * Real.sqrt (u x)))) * v x
        + (x + sgn * (u x / 2)) * (2 * u x * Real.sqrt (u x))⁻¹ * c) x := by
  have hne : Real.sqrt (u x) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hne2 : 2 * u x * Real.sqrt (u x) ≠ 0 :=
    (mul_pos (mul_pos two_pos hpos) (Real.sqrt_pos.mpr hpos)).ne'
  have hsq : Real.sqrt (u x) ^ 2 = u x := Real.sq_sqrt hpos.le
  -- term 1: y ↦ -(√(u y))⁻¹
  have hsqfun : HasDerivAt (fun y : ℝ => Real.sqrt (u y)) (b / (2 * Real.sqrt (u x))) x := by
    have hc := (Real.hasDerivAt_sqrt hpos.ne').comp x hu
    rw [Function.comp_def] at hc
    exact hc.congr_deriv (by field_simp)
  have ht1 : HasDerivAt (fun y : ℝ => -(Real.sqrt (u y))⁻¹)
      (b / (2 * u x * Real.sqrt (u x))) x := by
    refine ((hsqfun.inv hne).neg).congr_deriv ?_
    field_simp [hsq]
    try (simp only [hsq])
    try ring
  -- term 2: y ↦ (y + sgn * (u y / 2)) * ((2 * u y * √(u y))⁻¹) * v y
  have hA : HasDerivAt (fun y : ℝ => y + sgn * (u y / 2)) (1 + sgn * (b / 2)) x := by
    have h1 : HasDerivAt (fun y : ℝ => u y / 2) (b / 2) x := hu.div_const 2
    exact (hasDerivAt_id x).add (h1.const_mul sgn)
  have hB : HasDerivAt (fun y : ℝ => (2 * u y * Real.sqrt (u y))⁻¹)
      (-(3 * b / (4 * u x ^ 2 * Real.sqrt (u x)))) x := by
    have h2u : HasDerivAt (fun y : ℝ => 2 * u y) (2 * b) x := hu.const_mul 2
    have hprod := h2u.mul hsqfun
    refine (hprod.inv hne2).congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp [hsq]
    simp only [hsq]
    ring
  have ht2 := (hA.mul hB).mul hv
  have hsum := ht1.add ht2
  refine (hsum.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with y
    simp only [Pi.mul_apply, Pi.add_apply]
    field_simp
    try ring
  · try simp only [Pi.mul_apply, Pi.add_apply]
    field_simp [hsq, hne, hne2]
    try (simp only [hsq])
    ring

/-! ## The call's own chains: `C_k`, `C_T`, `C_kk` -/

/-- The value functions of the `d±` slope composites, `D± = ∂_k d± + ∂_w d±·m`
(sgn = ±1), and their `k`-derivative values `V±` — packaged as defs so the
second-derivative layer stays readable. -/
private noncomputable def dplus (k w m : ℝ) : ℝ :=
  -(1 / Real.sqrt w) + (k + w / 2) / (2 * w * Real.sqrt w) * m

private noncomputable def dminus (k w m : ℝ) : ℝ :=
  -(1 / Real.sqrt w) + (k - w / 2) / (2 * w * Real.sqrt w) * m

private noncomputable def vsgn (k w m mm sgn : ℝ) : ℝ :=
  m / (2 * w * Real.sqrt w)
  + (1 + sgn * (m / 2)) * m / (2 * w * Real.sqrt w)
  + (k + sgn * (w / 2)) * (-(3 * m / (4 * w ^ 2 * Real.sqrt w))) * m
  + (k + sgn * (w / 2)) * (2 * w * Real.sqrt w)⁻¹ * mm

/-- The smile surface is affine in `k`, so positivity at one point spreads to a
neighborhood. -/
private theorem smileSurface_eventually_pos_k {σ ψ₁ T₀ ε T k : ℝ} (hS : 0 < T + T₀)
    (hk : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    ∀ᶠ y in nhds k, 0 < smileSurface σ ψ₁ T₀ ε y T := by
  have hcont : Continuous (fun y : ℝ => smileSurface σ ψ₁ T₀ ε y T) := by
    unfold smileSurface
    exact continuous_const.add (((continuous_const).mul continuous_id).div
      continuous_const (fun _ => (Real.sqrt_pos.mpr hS).ne'))
  exact (show ContinuousAt (fun _ : ℝ => (0:ℝ)) k from continuousAt_const).eventually_lt
    hcont.continuousAt hk

/-- Same along the maturity axis: `σ̃(t) = σ + εψ₁k/√(t+T₀)` is continuous at
`T`, and `t > 0` holds eventually at `T > 0`. -/
private theorem smileSurface_eventually_pos_t {σ ψ₁ T₀ ε k T : ℝ} (hT : 0 < T)
    (hS : 0 < T + T₀) (hk : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    ∀ᶠ t in nhds T, 0 < smileSurface σ ψ₁ T₀ ε k t ∧ 0 < t := by
  have hadd : ContinuousAt (fun t : ℝ => t + T₀) T :=
    (continuous_id.add continuous_const).continuousAt
  have hsca : ContinuousAt (fun t : ℝ => Real.sqrt (t + T₀)) T :=
    (Real.continuous_sqrt.continuousAt).comp hadd
  have hcst : ContinuousAt (fun _ : ℝ => ε * ψ₁ * k) T := continuousAt_const
  have hca : ContinuousAt (fun t : ℝ => smileSurface σ ψ₁ T₀ ε k t) T := by
    unfold smileSurface
    exact continuousAt_const.add (hcst.div hsca (Real.sqrt_pos.mpr hS).ne')
  filter_upwards [(show ContinuousAt (fun _ : ℝ => (0:ℝ)) T from continuousAt_const).eventually_lt
    hca hk, eventually_gt_nhds hT] with t h1t h2t
  exact ⟨h1t, h2t⟩

/-- **The `k`-chain of the call price** (both `k`-channels: strike `F·e^k` and
surface tilt), from `hasDerivAt_blackForm_comp` at the variance composite. -/
private theorem hasDerivAt_bsCallSmile_k {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T)
    (hS : 0 < T + T₀) (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    HasDerivAt (fun y => bsCallSmile F σ ψ₁ T₀ ε y T)
      (F * (gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
            * (-(1 / Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
                + (k + totalVar σ ψ₁ T₀ ε k T / 2)
                  / (2 * totalVar σ ψ₁ T₀ ε k T * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
                  * (2 * smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ / Real.sqrt (T + T₀)) * T))
          - (Real.exp k * Phi (dmi k (totalVar σ ψ₁ T₀ ε k T))
              + Real.exp k * (gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T))
                * (-(1 / Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
                    + (k - totalVar σ ψ₁ T₀ ε k T / 2)
                      / (2 * totalVar σ ψ₁ T₀ ε k T * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
                      * (2 * smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ / Real.sqrt (T + T₀)) * T)))))) k := by
  have hwpos : 0 < totalVar σ ψ₁ T₀ ε k T := mul_pos (pow_pos hst 2) hT
  have huc := hasDerivAt_totalVar_k (σ := σ) (ψ₁ := ψ₁) (T₀ := T₀) (ε := ε) (T := T) (x := k) hS
  have hcore := hasDerivAt_blackForm_comp huc hwpos
  refine (hcore.const_mul F).congr_of_eventuallyEq ?_
  filter_upwards [smileSurface_eventually_pos_k hS hst] with y hy
  exact bsCallSmile_eq hF hT hy

/-- **The `T`-chain of the call price** (single `(k,w)` slot: the maturity moves
only through `w`), from `hasDerivAt_blackForm_w` composed with the variance
`T`-chain. -/
private theorem hasDerivAt_bsCallSmile_t {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T)
    (hS : 0 < T + T₀) (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    HasDerivAt (fun t => bsCallSmile F σ ψ₁ T₀ ε k t)
      (F * (gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
          / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T)))
        * (smileSurface σ ψ₁ T₀ ε k T ^ 2
          - smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ * k) * T
            / ((T + T₀) * Real.sqrt (T + T₀)))) T := by
  have hwpos : 0 < totalVar σ ψ₁ T₀ ε k T := mul_pos (pow_pos hst 2) hT
  have hwt := hasDerivAt_totalVar_t (σ := σ) (ψ₁ := ψ₁) (T₀ := T₀) (ε := ε) (k := k) hT hS
  have hcomp := (hasDerivAt_blackForm_w (k := k) hwpos).comp T hwt
  rw [Function.comp_def] at hcomp
  refine ((hcomp.const_mul F).congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards [smileSurface_eventually_pos_t hT hS hst] with t ht
  exact bsCallSmile_eq hF ht.2 ht.1

/-- The variance slope function `w'(y) = 2σ̃(y)·(εψ₁/√(T+T₀))·T` (affine in `y`). -/
private noncomputable def wSlope (σ ψ₁ T₀ ε T y : ℝ) : ℝ :=
  2 * smileSurface σ ψ₁ T₀ ε y T * (ε * ψ₁ / Real.sqrt (T + T₀)) * T

/-- Its chain: `w'' = 2·(εψ₁/√(T+T₀))²·T`, constant in `y`. -/
private theorem hasDerivAt_wSlope {σ ψ₁ T₀ ε T k : ℝ} (hS : 0 < T + T₀) :
    HasDerivAt (fun y => wSlope σ ψ₁ T₀ ε T y)
      (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T) k := by
  have h1 : HasDerivAt (fun y : ℝ => smileSurface σ ψ₁ T₀ ε y T)
      (ε * ψ₁ / Real.sqrt (T + T₀)) k := hasDerivAt_smileSurface_k hS
  have h2 : HasDerivAt (fun y : ℝ =>
      2 * T * (ε * ψ₁ / Real.sqrt (T + T₀)) * smileSurface σ ψ₁ T₀ ε y T)
      (2 * T * (ε * ψ₁ / Real.sqrt (T + T₀)) * (ε * ψ₁ / Real.sqrt (T + T₀))) k :=
    h1.const_mul _
  have hfun : (fun y : ℝ => wSlope σ ψ₁ T₀ ε T y)
      = fun y => 2 * T * (ε * ψ₁ / Real.sqrt (T + T₀)) * smileSurface σ ψ₁ T₀ ε y T := by
    funext y
    unfold wSlope
    ring
  exact (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (congrFun hfun))).congr_deriv
    (by ring)

/-! ## The second `k`-chain: `C_kk` and the Gatheral form of the ratio -/

/-- The standard normal density is strictly positive (needed to cancel the common
vega-density factor between Dupire's numerator and denominator). -/
private theorem gaussianPDFReal_zero_one_pos (x : ℝ) : 0 < gaussianPDFReal 0 1 x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

/-- **The `k`-derivative of the call price, collapsed**: the spelled chain value of
`hasDerivAt_bsCallSmile_k` simplifies (via the magic identity `e^k·ϕ(d₋) = ϕ(d₊)`) to
`C_k = F·(B_w·m − e^k·Φ(d₋))` with `B_w = ϕ(d₊)/(2√w)` and `m = w'` — the vega-density
composite times the variance slope, minus the exercise side. -/
private theorem deriv_bsCallSmile_k_value {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T)
    (hS : 0 < T + T₀) (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    deriv (fun x => bsCallSmile F σ ψ₁ T₀ ε x T) k
      = F * (gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
            / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T)) * wSlope σ ψ₁ T₀ ε T k
          - Real.exp k * Phi (dmi k (totalVar σ ψ₁ T₀ ε k T))) := by
  have hw : 0 < totalVar σ ψ₁ T₀ ε k T := mul_pos (pow_pos hst 2) hT
  rw [(hasDerivAt_bsCallSmile_k hF hT hS hst).deriv]
  rw [show Real.exp k * (gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T))
        * (-(1 / Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
          + (k - totalVar σ ψ₁ T₀ ε k T / 2)
            / (2 * totalVar σ ψ₁ T₀ ε k T * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
            * (2 * smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ / Real.sqrt (T + T₀)) * T)))
      = (Real.exp k * gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T)))
        * (-(1 / Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
          + (k - totalVar σ ψ₁ T₀ ε k T / 2)
            / (2 * totalVar σ ψ₁ T₀ ε k T * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
            * (2 * smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ / Real.sqrt (T + T₀)) * T)) from
    (mul_assoc _ _ _).symm,
    exp_mul_pdf_dmi hw]
  simp only [wSlope]
  field_simp [hw.ne', (Real.sqrt_pos.mpr hw).ne', (Real.sqrt_pos.mpr hS).ne']
  ring

/-- **The second `k`-chain `C_kk`** (the second `k`-derivative of the call
price, the remaining ingredient Dupire's ratio needs beyond `C_k`):
the `k`-derivative of the `k`-derivative of the call price, assembled from the
`B_w` composite chain (`hasDerivAt_Bw_comp`), the variance-slope chain
(`hasDerivAt_wSlope`) and the exercise-side chain
(`hasDerivAt_exp_Phi_dmi_comp`) — each factor evaluated on the *collapsed*
first-derivative function of `deriv_bsCallSmile_k_value`, so the normalization
stays at the level of one small `ring` congruence per `y`. -/
private theorem hasDerivAt_deriv_bsCallSmile_k {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T)
    (hS : 0 < T + T₀) (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    HasDerivAt (fun y => deriv (fun x => bsCallSmile F σ ψ₁ T₀ ε x T) y)
      (F * ((dpl k (totalVar σ ψ₁ T₀ ε k T)
              * gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
              / (2 * totalVar σ ψ₁ T₀ ε k T)
            + gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
              * (k ^ 2 - totalVar σ ψ₁ T₀ ε k T - totalVar σ ψ₁ T₀ ε k T ^ 2 / 4)
              / (4 * totalVar σ ψ₁ T₀ ε k T ^ 2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
              * wSlope σ ψ₁ T₀ ε T k) * wSlope σ ψ₁ T₀ ε T k
          + gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
              / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
            * (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)
          - (Real.exp k * Phi (dmi k (totalVar σ ψ₁ T₀ ε k T))
            + Real.exp k * (gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T))
              * dminus k (totalVar σ ψ₁ T₀ ε k T) (wSlope σ ψ₁ T₀ ε T k))))) k := by
  have hwpos : 0 < totalVar σ ψ₁ T₀ ε k T := mul_pos (pow_pos hst 2) hT
  have hu : HasDerivAt (fun y => totalVar σ ψ₁ T₀ ε y T) (wSlope σ ψ₁ T₀ ε T k) k :=
    hasDerivAt_totalVar_k hS
  have hBw := hasDerivAt_Bw_comp hu hwpos
  have hm : HasDerivAt (fun y => wSlope σ ψ₁ T₀ ε T y)
      (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T) k := hasDerivAt_wSlope hS
  have hprod := hBw.mul hm
  have hexp := hasDerivAt_exp_Phi_dmi_comp hu hwpos
  refine ((hprod.sub hexp).const_mul F).congr_of_eventuallyEq ?_
  filter_upwards [smileSurface_eventually_pos_k hS hst] with y hy
  exact deriv_bsCallSmile_k_value hF hT hS hy

/-! ## The Gatheral form of the ratio -/

/-- The `T`-chain of the total variance as a named function: `w_T = σ̃² − σ̃εψ₁kT/(T+T₀)^{3/2}`
(the numerator of Dupire's ratio in `(k, w)` coordinates). -/
private noncomputable def smileN (σ ψ₁ T₀ ε k T : ℝ) : ℝ :=
  smileSurface σ ψ₁ T₀ ε k T ^ 2
    - smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ * k) * T / ((T + T₀) * Real.sqrt (T + T₀))

/-- The Gatheral denominator deformation `δ = −k·w_k/w + w_k²·(k²−w−w²/4)/(4w²) + w_kk/2`
(specialized to this surface, so `w_kk/2` is spelled in unfolded form); Dupire's ratio
is `w_T/(1 + δ)`. -/
private noncomputable def smileDelta (σ ψ₁ T₀ ε k T : ℝ) : ℝ :=
  -k * wSlope σ ψ₁ T₀ ε T k / totalVar σ ψ₁ T₀ ε k T
    + wSlope σ ψ₁ T₀ ε T k ^ 2 * (k ^ 2 - totalVar σ ψ₁ T₀ ε k T
        - totalVar σ ψ₁ T₀ ε k T ^ 2 / 4) / (4 * totalVar σ ψ₁ T₀ ε k T ^ 2)
    + (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T

/-- **`dupireRatio_eq`** — the exact identity behind the whole lesson: in `(k, w)`
coordinates, Dupire's zero-rates ratio on the tilted surface is the rational function
`R = w_T/(1 + δ)` (the Gatheral form). Everything downstream is calculus on the
explicit right-hand side. -/
theorem dupireRatio_eq {F σ ψ₁ T₀ ε k T : ℝ} (hF : 0 < F) (hT : 0 < T) (hS : 0 < T + T₀)
    (hst : 0 < smileSurface σ ψ₁ T₀ ε k T) :
    dupireRatio F σ ψ₁ T₀ ε k T
      = smileN σ ψ₁ T₀ ε k T / (1 + smileDelta σ ψ₁ T₀ ε k T) := by
  have hw : 0 < totalVar σ ψ₁ T₀ ε k T := mul_pos (pow_pos hst 2) hT
  have hsne : Real.sqrt (totalVar σ ψ₁ T₀ ε k T) ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  have hI :
      (F * ((dpl k (totalVar σ ψ₁ T₀ ε k T)
                * gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
                / (2 * totalVar σ ψ₁ T₀ ε k T)
              + gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
                * (k ^ 2 - totalVar σ ψ₁ T₀ ε k T - totalVar σ ψ₁ T₀ ε k T ^ 2 / 4)
                / (4 * totalVar σ ψ₁ T₀ ε k T ^ 2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
                * wSlope σ ψ₁ T₀ ε T k) * wSlope σ ψ₁ T₀ ε T k
            + gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
                / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T))
              * (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)
            - (Real.exp k * Phi (dmi k (totalVar σ ψ₁ T₀ ε k T))
              + Real.exp k * (gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T))
                * dminus k (totalVar σ ψ₁ T₀ ε k T) (wSlope σ ψ₁ T₀ ε T k))))
        - F * (gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
              / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T)) * wSlope σ ψ₁ T₀ ε T k
            - Real.exp k * Phi (dmi k (totalVar σ ψ₁ T₀ ε k T))))
      = F * gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
          / Real.sqrt (totalVar σ ψ₁ T₀ ε k T) * (1 + smileDelta σ ψ₁ T₀ ε k T) := by
    have hexp : Real.exp k * (gaussianPDFReal 0 1 (dmi k (totalVar σ ψ₁ T₀ ε k T))
        * dminus k (totalVar σ ψ₁ T₀ ε k T) (wSlope σ ψ₁ T₀ ε T k))
        = gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
          * dminus k (totalVar σ ψ₁ T₀ ε k T) (wSlope σ ψ₁ T₀ ε T k) := by
      rw [← mul_assoc, exp_mul_pdf_dmi hw]
    rw [hexp]
    simp only [dminus, dpl]
    unfold smileDelta
    field_simp [hw.ne', hsne]
    ring
  unfold dupireRatio
  rw [(hasDerivAt_bsCallSmile_t hF hT hS hst).deriv, deriv_bsCallSmile_k_value hF hT hS hst,
    (hasDerivAt_deriv_bsCallSmile_k hF hT hS hst).deriv, hI]
  have hA : F * gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
      / Real.sqrt (totalVar σ ψ₁ T₀ ε k T) ≠ 0 :=
    div_ne_zero (mul_ne_zero hF.ne' (gaussianPDFReal_zero_one_pos _).ne') hsne
  have htwo : 2 * (F * (gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
        / (2 * Real.sqrt (totalVar σ ψ₁ T₀ ε k T)))
        * (smileSurface σ ψ₁ T₀ ε k T ^ 2
          - smileSurface σ ψ₁ T₀ ε k T * (ε * ψ₁ * k) * T / ((T + T₀) * Real.sqrt (T + T₀))))
      = F * gaussianPDFReal 0 1 (dpl k (totalVar σ ψ₁ T₀ ε k T))
          / Real.sqrt (totalVar σ ψ₁ T₀ ε k T) * smileN σ ψ₁ T₀ ε k T := by
    unfold smileN
    field_simp
  rw [htwo]
  field_simp [hA, (gaussianPDFReal_zero_one_pos _).ne']

/-! ## The `k = 0` extraction -/

/-- At the money the total variance is `σ²T`, independent of the tilt. -/
private theorem totalVar_zero (σ ψ₁ T₀ ε T : ℝ) : totalVar σ ψ₁ T₀ ε 0 T = σ ^ 2 * T := by
  unfold totalVar
  rw [smileSurface_atm]

/-- At the money the variance slope is `m₀ = 2σ·(εψ₁/√(T+T₀))·T` — linear in `ε`. -/
private theorem wSlope_zero (σ ψ₁ T₀ ε T : ℝ) :
    wSlope σ ψ₁ T₀ ε T 0 = 2 * σ * (ε * ψ₁ / Real.sqrt (T + T₀)) * T := by
  unfold wSlope
  rw [smileSurface_atm]

/-- The `T`-chain numerator at the money: `w_T(ε, 0) = σ²`, tilt-free. -/
private theorem smileN_zero (σ ψ₁ T₀ ε T : ℝ) : smileN σ ψ₁ T₀ ε 0 T = σ ^ 2 := by
  unfold smileN
  rw [smileSurface_atm]
  ring

/-- The `k`-slope of the numerator at the money (the value of `hasDerivAt_smileN_k`). -/
private noncomputable def smileNk (σ ψ₁ T₀ ε T : ℝ) : ℝ :=
  2 * σ * (ε * ψ₁ / Real.sqrt (T + T₀))
    - σ * (ε * ψ₁) * T / ((T + T₀) * Real.sqrt (T + T₀))

private theorem smileNk_zero (σ ψ₁ T₀ T : ℝ) : smileNk σ ψ₁ T₀ 0 T = 0 := by
  unfold smileNk
  simp

/-- The `k`-slope of the Gatheral deformation at the money (the value of
`hasDerivAt_smileDelta_k`). -/
private noncomputable def smileDk (σ ψ₁ T₀ ε T : ℝ) : ℝ :=
  -(wSlope σ ψ₁ T₀ ε T 0 / totalVar σ ψ₁ T₀ ε 0 T)
    + ((((2 * 0 - wSlope σ ψ₁ T₀ ε T 0 - totalVar σ ψ₁ T₀ ε 0 T * wSlope σ ψ₁ T₀ ε T 0 / 2)
            * wSlope σ ψ₁ T₀ ε T 0 ^ 2
        + (0 ^ 2 - totalVar σ ψ₁ T₀ ε 0 T - totalVar σ ψ₁ T₀ ε 0 T ^ 2 / 4)
            * (2 * wSlope σ ψ₁ T₀ ε T 0 * (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)))
        * (4 * totalVar σ ψ₁ T₀ ε 0 T ^ 2)
      - (0 ^ 2 - totalVar σ ψ₁ T₀ ε 0 T - totalVar σ ψ₁ T₀ ε 0 T ^ 2 / 4)
          * wSlope σ ψ₁ T₀ ε T 0 ^ 2 * (4 * (2 * totalVar σ ψ₁ T₀ ε 0 T * wSlope σ ψ₁ T₀ ε T 0)))
      / (4 * totalVar σ ψ₁ T₀ ε 0 T ^ 2) ^ 2)

private theorem smileDelta_zero (σ ψ₁ T₀ T : ℝ) : smileDelta σ ψ₁ T₀ 0 0 T = 0 := by
  unfold smileDelta
  rw [totalVar_zero, wSlope_zero]
  simp

private theorem smileDk_zero (σ ψ₁ T₀ T : ℝ) : smileDk σ ψ₁ T₀ 0 T = 0 := by
  unfold smileDk
  rw [totalVar_zero, wSlope_zero]
  simp

/-- The numerator of the ATM `k`-slope of the ratio: quotient-rule value
`N'(0)·D(0) − N(0)·D'(0)` in the `(k = 0)` slice. -/
private noncomputable def slopeNum (σ ψ₁ T₀ ε T : ℝ) : ℝ :=
  smileNk σ ψ₁ T₀ ε T * (1 + smileDelta σ ψ₁ T₀ ε 0 T)
    - smileN σ ψ₁ T₀ ε 0 T * smileDk σ ψ₁ T₀ ε T

private theorem slopeNum_zero (σ ψ₁ T₀ T : ℝ) : slopeNum σ ψ₁ T₀ 0 T = 0 := by
  unfold slopeNum
  rw [smileNk_zero, smileDelta_zero, smileN_zero, smileDk_zero]
  simp

/-- The `k`-chain of the numerator `w_T` at the money. -/
private theorem hasDerivAt_smileN_k {σ ψ₁ T₀ ε T : ℝ} (hS : 0 < T + T₀) :
    HasDerivAt (fun k => smileN σ ψ₁ T₀ ε k T) (smileNk σ ψ₁ T₀ ε T) 0 := by
  have hs : HasDerivAt (fun k => smileSurface σ ψ₁ T₀ ε k T) (ε * ψ₁ / Real.sqrt (T + T₀)) 0 :=
    hasDerivAt_smileSurface_k hS
  have hs2 : HasDerivAt (fun k => smileSurface σ ψ₁ T₀ ε k T ^ 2)
      (2 * smileSurface σ ψ₁ T₀ ε 0 T ^ (2 - 1) * (ε * ψ₁ / Real.sqrt (T + T₀))) 0 := by
    have h := (hasDerivAt_pow 2 (smileSurface σ ψ₁ T₀ ε 0 T)).comp 0 hs
    rw [Function.comp_def] at h
    exact h
  have hkm : HasDerivAt (fun k => smileSurface σ ψ₁ T₀ ε k T * k)
      ((ε * ψ₁ / Real.sqrt (T + T₀)) * 0 + smileSurface σ ψ₁ T₀ ε 0 T * 1) 0 :=
    hs.mul (hasDerivAt_id 0)
  have hsub := hs2.sub (hkm.const_mul (ε * ψ₁ * T / ((T + T₀) * Real.sqrt (T + T₀))))
  refine (hsub.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with k
    simp only [Pi.sub_apply]
    unfold smileN
    ring
  · rw [smileSurface_atm]
    unfold smileNk
    ring

/-- The `k`-chain of the Gatheral deformation `δ` at the money. -/
private theorem hasDerivAt_smileDelta_k {σ ψ₁ T₀ ε T : ℝ} (hσ : 0 < σ) (hT : 0 < T)
    (hS : 0 < T + T₀) :
    HasDerivAt (fun k => smileDelta σ ψ₁ T₀ ε k T) (smileDk σ ψ₁ T₀ ε T) 0 := by
  have hw0 : 0 < totalVar σ ψ₁ T₀ ε 0 T := by rw [totalVar_zero]; positivity
  have hw0ne := hw0.ne'
  have hm : HasDerivAt (fun k => wSlope σ ψ₁ T₀ ε T k)
      (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T) 0 := hasDerivAt_wSlope hS
  have hw : HasDerivAt (fun k => totalVar σ ψ₁ T₀ ε k T) (wSlope σ ψ₁ T₀ ε T 0) 0 :=
    hasDerivAt_totalVar_k hS
  have hkm : HasDerivAt (fun k => k * wSlope σ ψ₁ T₀ ε T k)
      (1 * wSlope σ ψ₁ T₀ ε T 0 + 0 * (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)) 0 :=
    (hasDerivAt_id 0).mul hm
  have ht1 := (hkm.div hw hw0ne).neg
  have hk2 : HasDerivAt (fun k => k ^ 2) ((2:ℝ) * 0 ^ (2 - 1)) 0 := hasDerivAt_pow 2 0
  have hc2 : HasDerivAt (fun k => totalVar σ ψ₁ T₀ ε k T ^ 2)
      (2 * totalVar σ ψ₁ T₀ ε 0 T ^ (2 - 1) * wSlope σ ψ₁ T₀ ε T 0) 0 := by
    have h := (hasDerivAt_pow 2 (totalVar σ ψ₁ T₀ ε 0 T)).comp 0 hw
    rw [Function.comp_def] at h
    exact h
  have hA := (hk2.sub hw).sub (hc2.div_const 4)
  have hm2 : HasDerivAt (fun k => wSlope σ ψ₁ T₀ ε T k ^ 2)
      (2 * wSlope σ ψ₁ T₀ ε T 0 ^ (2 - 1) * (2 * (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)) 0 := by
    have h := (hasDerivAt_pow 2 (wSlope σ ψ₁ T₀ ε T 0)).comp 0 hm
    rw [Function.comp_def] at h
    exact h
  have hAm := hA.mul hm2
  have h4 : HasDerivAt (fun k => 4 * totalVar σ ψ₁ T₀ ε k T ^ 2)
      (4 * (2 * totalVar σ ψ₁ T₀ ε 0 T ^ (2 - 1) * wSlope σ ψ₁ T₀ ε T 0)) 0 := hc2.const_mul 4
  have h4ne : 4 * totalVar σ ψ₁ T₀ ε 0 T ^ 2 ≠ 0 := by rw [totalVar_zero]; positivity
  have ht2 := hAm.div h4 h4ne
  have ht3 : HasDerivAt (fun k : ℝ => (ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T) 0 0 :=
    hasDerivAt_const 0 ((ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)
  have hsum := ht1.add (ht2.add ht3)
  refine (hsum.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with k
    unfold smileDelta
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply]
    ring
  · unfold smileDk
    simp only [Pi.sub_apply, Pi.mul_apply]
    field_simp [hw0ne, h4ne]
    ring

/-- **The ATM `k`-chain of Dupire's ratio itself**: at every tilt `ε` with nondegenerate
denominator, `∂_k R(ε, ·, T)|₀ = slopeNum/(1 + δ₀)²` — the quotient rule on
`dupireRatio_eq`. -/
private theorem hasDerivAt_dupireRatio_k_zero {F σ ψ₁ T₀ ε T : ℝ} (hF : 0 < F) (hσ : 0 < σ)
    (hT : 0 < T) (hS : 0 < T + T₀) (hD0ne : 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0) :
    HasDerivAt (fun k => dupireRatio F σ ψ₁ T₀ ε k T)
      (slopeNum σ ψ₁ T₀ ε T / (1 + smileDelta σ ψ₁ T₀ ε 0 T) ^ 2) 0 := by
  have hst : 0 < smileSurface σ ψ₁ T₀ ε 0 T := by rw [smileSurface_atm]; exact hσ
  have hN : HasDerivAt (fun k => smileN σ ψ₁ T₀ ε k T) (smileNk σ ψ₁ T₀ ε T) 0 :=
    hasDerivAt_smileN_k hS
  have hD : HasDerivAt (fun k => smileDelta σ ψ₁ T₀ ε k T) (smileDk σ ψ₁ T₀ ε T) 0 :=
    hasDerivAt_smileDelta_k hσ hT hS
  have hcone : HasDerivAt (fun k : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const 0 (1 : ℝ)
  have hD1 : HasDerivAt (fun k => 1 + smileDelta σ ψ₁ T₀ ε k T) (smileDk σ ψ₁ T₀ ε T) 0 :=
    (hcone.add hD).congr_deriv (by ring)
  have hQ := hN.div hD1 hD0ne
  refine hQ.congr_of_eventuallyEq ?_
  filter_upwards [smileSurface_eventually_pos_k hS hst] with k hk
  exact dupireRatio_eq hF hT hS hk

/-! ## The `ε`-extraction at zero tilt -/

/-- The ATM Gatheral deformation is exactly quadratic in the tilt:
`δ(ε, 0) = ε²·d₂` with `d₂` tilt-free. -/
private noncomputable def smileD2 (σ ψ₁ T₀ T : ℝ) : ℝ :=
  (2 * σ * (ψ₁ / Real.sqrt (T + T₀)) * T) ^ 2
    * (0 ^ 2 - σ ^ 2 * T - (σ ^ 2 * T) ^ 2 / 4) / (4 * (σ ^ 2 * T) ^ 2)
  + (ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T

private theorem smileDelta_zero_fac {σ ψ₁ T₀ T : ℝ} (ε : ℝ) :
    smileDelta σ ψ₁ T₀ ε 0 T = ε ^ 2 * smileD2 σ ψ₁ T₀ T := by
  unfold smileDelta smileD2
  rw [totalVar_zero, wSlope_zero]
  ring

/-- Near zero tilt the deformed denominator stays nondegenerate. -/
private theorem eventually_one_add_smileDelta_ne_zero {σ ψ₁ T₀ T : ℝ} :
    ∀ᶠ ε in nhds 0, 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0 := by
  have hc : Continuous fun ε => ε ^ 2 * smileD2 σ ψ₁ T₀ T := by continuity
  have ht : Filter.Tendsto (fun ε => ε ^ 2 * smileD2 σ ψ₁ T₀ T) (nhds 0) (nhds 0) := by
    have h := hc.tendsto (0 : ℝ)
    simpa using h
  have habs : ∀ᶠ y in nhds (0 : ℝ), |y| < 1 := by
    filter_upwards [(isOpen_Ioo.mem_nhds ⟨by norm_num, by norm_num⟩ :
      Set.Ioo (-(1 : ℝ)) (1 : ℝ) ∈ nhds (0 : ℝ))] with y hy
    rw [abs_lt]
    exact hy
  filter_upwards [ht.eventually habs] with ε hε
  intro hcontra
  rw [smileDelta_zero_fac] at hcontra
  have hX : ε ^ 2 * smileD2 σ ψ₁ T₀ T = -1 := by linarith
  rw [hX] at hε
  simp at hε

/-- The `ε`-chain of `N'(0; ε)` — linear in the tilt. -/
private theorem hasDerivAt_smileNk_eps {σ ψ₁ T₀ T : ℝ} :
    HasDerivAt (fun ε => smileNk σ ψ₁ T₀ ε T)
      (2 * σ * ψ₁ / Real.sqrt (T + T₀) - σ * ψ₁ * T / ((T + T₀) * Real.sqrt (T + T₀))) 0 := by
  have hcore := (hasDerivAt_id 0).const_mul
    (2 * σ * ψ₁ / Real.sqrt (T + T₀) - σ * ψ₁ * T / ((T + T₀) * Real.sqrt (T + T₀)))
  refine (hcore.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards with ε
  unfold smileNk
  simp only [id_eq]
  ring

/-- The `ε`-chain of the ATM numerator `N(ε, 0) = σ²` — constant in the tilt. -/
private theorem hasDerivAt_smileN_zero_eps {σ ψ₁ T₀ T : ℝ} :
    HasDerivAt (fun ε => smileN σ ψ₁ T₀ ε 0 T) 0 0 := by
  refine (hasDerivAt_const 0 (σ ^ 2)).congr_of_eventuallyEq ?_
  filter_upwards with ε
  exact smileN_zero σ ψ₁ T₀ ε T

/-- The `ε`-chain of the deformed denominator `1 + δ(ε, 0) = 1 + ε²d₂`. -/
private theorem hasDerivAt_one_add_smileDelta_eps {σ ψ₁ T₀ T : ℝ} :
    HasDerivAt (fun ε => 1 + smileDelta σ ψ₁ T₀ ε 0 T) 0 0 := by
  have hcore := (hasDerivAt_const 0 (1 : ℝ)).add
    ((hasDerivAt_pow 2 0).const_mul (smileD2 σ ψ₁ T₀ T))
  refine (hcore.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards with ε
  simp only [Pi.add_apply]
  rw [smileDelta_zero_fac]
  ring

/-- The `ε`-chain of the ATM deformation slope `δ'(0; ε)`: tilt-linear part from the
`−k·w_k/w` term; every other term is `O(ε²)` at the money. -/
private theorem hasDerivAt_smileDk_eps {σ ψ₁ T₀ T : ℝ} (hσ : 0 < σ) (hT : 0 < T)
    (hS : 0 < T + T₀) :
    HasDerivAt (fun ε => smileDk σ ψ₁ T₀ ε T)
      (-(2 * σ * (ψ₁ / Real.sqrt (T + T₀)) * T / (σ ^ 2 * T))) 0 := by
  have hWne : σ ^ 2 * T ≠ 0 := mul_ne_zero (pow_ne_zero 2 hσ.ne') hT.ne'
  have hDENne : (4 * (σ ^ 2 * T) ^ 2) ^ 2 ≠ 0 := by positivity
  have hM : HasDerivAt (fun ε => 2 * σ * (ε * ψ₁ / Real.sqrt (T + T₀)) * T)
      (2 * σ * (ψ₁ / Real.sqrt (T + T₀)) * T) 0 := by
    have hcore := (hasDerivAt_id 0).const_mul (2 * σ * (ψ₁ / Real.sqrt (T + T₀)) * T)
    refine (hcore.congr_of_eventuallyEq ?_).congr_deriv (by ring)
    filter_upwards with ε
    simp only [id_eq]
    ring
  have hM2 := (hasDerivAt_pow 2 (2 * σ * (0 * ψ₁ / Real.sqrt (T + T₀)) * T)).comp 0 hM
  rw [Function.comp_def] at hM2
  have hid : HasDerivAt (fun ε => ε * ψ₁ / Real.sqrt (T + T₀))
      (ψ₁ / Real.sqrt (T + T₀)) 0 := by
    have hcore := (hasDerivAt_id 0).const_mul (ψ₁ / Real.sqrt (T + T₀))
    refine (hcore.congr_of_eventuallyEq ?_).congr_deriv (by ring)
    filter_upwards with ε
    simp only [id_eq]
    ring
  have hq := (hasDerivAt_pow 2 (0 * ψ₁ / Real.sqrt (T + T₀))).comp 0 hid
  rw [Function.comp_def] at hq
  have hq2 := (hq.const_mul 2).const_mul T
  have hW : HasDerivAt (fun _ : ℝ => σ ^ 2 * T) 0 0 := hasDerivAt_const 0 (σ ^ 2 * T)
  have hAp := ((hasDerivAt_const 0 (0 : ℝ)).sub hM).sub ((hW.mul hM).div_const 2)
  have hA0 : HasDerivAt (fun _ : ℝ => 0 ^ 2 - σ ^ 2 * T - (σ ^ 2 * T) ^ 2 / 4) 0 0 :=
    hasDerivAt_const 0 (0 ^ 2 - σ ^ 2 * T - (σ ^ 2 * T) ^ 2 / 4)
  have hmid := (hAp.mul hM2).add (hA0.mul ((hM.mul hq2).const_mul 2))
  have hNUM := (hmid.mul (hasDerivAt_const 0 (4 * (σ ^ 2 * T) ^ 2))).sub
    (hA0.mul (hM2.mul (((hW.mul hM).const_mul 4).const_mul 2)))
  have hDENc : HasDerivAt (fun _ : ℝ => (4 * (σ ^ 2 * T) ^ 2) ^ 2) 0 0 :=
    hasDerivAt_const 0 ((4 * (σ ^ 2 * T) ^ 2) ^ 2)
  have hBIG := hNUM.div hDENc hDENne
  have htot := (hM.div hW hWne).neg.add hBIG
  refine (htot.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with ε
    unfold smileDk
    rw [totalVar_zero, wSlope_zero]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply]
    ring
  · field_simp [hWne, hDENne]
    ring

/-- **The `ε`-chain of the ATM slope numerator**: `∂_ε[slopeNum]|₀ = L`, the eq-10.8
coefficient. -/
private theorem hasDerivAt_slopeNum {σ ψ₁ T₀ T : ℝ} (hσ : 0 < σ) (hT : 0 < T)
    (hS : 0 < T + T₀) :
    HasDerivAt (fun ε => slopeNum σ ψ₁ T₀ ε T)
      (2 * σ * ψ₁ * ((3 / 2) * T + 2 * T₀) / ((T + T₀) * Real.sqrt (T + T₀))) 0 := by
  have h1 : HasDerivAt (fun ε => smileNk σ ψ₁ T₀ ε T)
      (2 * σ * ψ₁ / Real.sqrt (T + T₀) - σ * ψ₁ * T / ((T + T₀) * Real.sqrt (T + T₀))) 0 :=
    hasDerivAt_smileNk_eps
  have h2 : HasDerivAt (fun ε => 1 + smileDelta σ ψ₁ T₀ ε 0 T) 0 0 :=
    hasDerivAt_one_add_smileDelta_eps
  have h3 : HasDerivAt (fun ε => smileN σ ψ₁ T₀ ε 0 T) 0 0 :=
    hasDerivAt_smileN_zero_eps
  have h4 : HasDerivAt (fun ε => smileDk σ ψ₁ T₀ ε T)
      (-(2 * σ * (ψ₁ / Real.sqrt (T + T₀)) * T / (σ ^ 2 * T))) 0 :=
    hasDerivAt_smileDk_eps hσ hT hS
  have hcomb := (h1.mul h2).sub (h3.mul h4)
  refine (hcomb.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with ε
    simp only [Pi.sub_apply, Pi.mul_apply]
    unfold slopeNum
    rfl
  · rw [smileDelta_zero, smileNk_zero, smileN_zero]
    field_simp [hσ.ne', hT.ne', (Real.sqrt_pos.mpr hS).ne']
    ring

/-- **Eq 10.8**: the ATM `k`-slope of Dupire's ratio has ε-slope
`2σψ₁·((3/2)T + 2T₀)/(T+T₀)^{3/2}` — the local-vol variance skew implied by the
tilted surface (image-verified numerator; see the module header for the typography
note on the chapter's printed form). -/
theorem dupireRatio_k_slope {F σ ψ₁ T₀ T : ℝ} (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < T)
    (h₀ : 0 < T₀) :
    deriv (fun ε => deriv (fun k => dupireRatio F σ ψ₁ T₀ ε k T) 0) 0
      = 2 * σ * ψ₁ * ((3 / 2) * T + 2 * T₀) / ((T + T₀) * Real.sqrt (T + T₀)) := by
  have hS : 0 < T + T₀ := by linarith
  have hev : ∀ᶠ ε in nhds 0, 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0 :=
    eventually_one_add_smileDelta_ne_zero
  have hval : ∀ᶠ ε in nhds 0, deriv (fun k => dupireRatio F σ ψ₁ T₀ ε k T) 0
      = slopeNum σ ψ₁ T₀ ε T / (1 + smileDelta σ ψ₁ T₀ ε 0 T) ^ 2 := by
    filter_upwards [hev] with ε hε
    exact (hasDerivAt_dupireRatio_k_zero hF hσ hT hS hε).deriv
  have hD0ε : HasDerivAt (fun ε => 1 + smileDelta σ ψ₁ T₀ ε 0 T) 0 0 :=
    hasDerivAt_one_add_smileDelta_eps
  have hD2ε := (hasDerivAt_pow 2 (1 + smileDelta σ ψ₁ T₀ 0 0 T)).comp 0 hD0ε
  rw [Function.comp_def] at hD2ε
  have hD2ne : (1 + smileDelta σ ψ₁ T₀ 0 0 T) ^ 2 ≠ 0 := by
    rw [smileDelta_zero]; norm_num
  have hSn : HasDerivAt (fun ε => slopeNum σ ψ₁ T₀ ε T)
      (2 * σ * ψ₁ * ((3 / 2) * T + 2 * T₀) / ((T + T₀) * Real.sqrt (T + T₀))) 0 :=
    hasDerivAt_slopeNum hσ hT hS
  have hQ := hSn.div hD2ε hD2ne
  refine (hQ.congr_deriv ?_).congr_of_eventuallyEq hval |>.deriv
  rw [smileDelta_zero, slopeNum_zero]
  norm_num

/-! ## The `σ_loc` reading -/

/-- **The local-vol ATM skew** (eq 10.8's square-root reading): the ε-slope of the
ATM `k`-slope of `√R` — the local vol implied by the surface — is
`ψ₁·((3/2)T + 2T₀)/(T+T₀)^{3/2}`: twice the implied ATM skew at `T = 0`
(`ruleOfTwo`), `(3/2)ψ₁/√T` asymptotically (`localSkew_tendsto`). -/
theorem dupireRatio_sqrt_slope {F σ ψ₁ T₀ T : ℝ} (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < T)
    (h₀ : 0 < T₀) :
    deriv (fun ε => deriv (fun k => Real.sqrt (dupireRatio F σ ψ₁ T₀ ε k T)) 0) 0
      = ψ₁ * ((3 / 2) * T + 2 * T₀) / ((T + T₀) * Real.sqrt (T + T₀)) := by
  have hS : 0 < T + T₀ := by linarith
  have hev : ∀ᶠ ε in nhds 0, 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0 :=
    eventually_one_add_smileDelta_ne_zero
  have hR0ne : ∀ ε : ℝ, 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0 →
      dupireRatio F σ ψ₁ T₀ ε 0 T ≠ 0 := by
    intro ε hε
    have hst : 0 < smileSurface σ ψ₁ T₀ ε 0 T := by rw [smileSurface_atm]; exact hσ
    rw [dupireRatio_eq hF hT hS hst, smileN_zero]
    exact div_ne_zero (pow_ne_zero 2 hσ.ne') hε
  have hR0sq : ∀ ε : ℝ, 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0 →
      Real.sqrt (dupireRatio F σ ψ₁ T₀ ε 0 T)
        = σ / Real.sqrt (1 + smileDelta σ ψ₁ T₀ ε 0 T) := by
    intro ε _
    have hst : 0 < smileSurface σ ψ₁ T₀ ε 0 T := by rw [smileSurface_atm]; exact hσ
    rw [dupireRatio_eq hF hT hS hst, smileN_zero, Real.sqrt_div (sq_nonneg σ),
      Real.sqrt_sq hσ.le]
  have hchain : ∀ ε : ℝ, 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0 →
      deriv (fun k => Real.sqrt (dupireRatio F σ ψ₁ T₀ ε k T)) 0
        = (1 / (2 * (σ / Real.sqrt (1 + smileDelta σ ψ₁ T₀ ε 0 T))))
          * (slopeNum σ ψ₁ T₀ ε T / (1 + smileDelta σ ψ₁ T₀ ε 0 T) ^ 2) := by
    intro ε hε
    have hBigk := hasDerivAt_dupireRatio_k_zero hF hσ hT hS hε
    have hsq := (Real.hasDerivAt_sqrt (hR0ne ε hε)).comp 0 hBigk
    rw [Function.comp_def] at hsq
    rw [hsq.deriv, hR0sq ε hε]
  have hSn : HasDerivAt (fun ε => slopeNum σ ψ₁ T₀ ε T)
      (2 * σ * ψ₁ * ((3 / 2) * T + 2 * T₀) / ((T + T₀) * Real.sqrt (T + T₀))) 0 :=
    hasDerivAt_slopeNum hσ hT hS
  have hD0ε : HasDerivAt (fun ε => 1 + smileDelta σ ψ₁ T₀ ε 0 T) 0 0 :=
    hasDerivAt_one_add_smileDelta_eps
  have hD0ne : (1 : ℝ) + smileDelta σ ψ₁ T₀ 0 0 T ≠ 0 := by rw [smileDelta_zero]; norm_num
  have hsD0 := (Real.hasDerivAt_sqrt hD0ne).comp 0 hD0ε
  rw [Function.comp_def] at hsD0
  have hD2ε := (hasDerivAt_pow 2 (1 + smileDelta σ ψ₁ T₀ 0 0 T)).comp 0 hD0ε
  rw [Function.comp_def] at hD2ε
  have hD2ne : (1 + smileDelta σ ψ₁ T₀ 0 0 T) ^ 2 ≠ 0 := by
    rw [smileDelta_zero]; norm_num
  have hV := hSn.div hD2ε hD2ne
  have hprod := hV.mul hsD0
  have h2σ : HasDerivAt (fun _ : ℝ => 2 * σ) 0 0 := hasDerivAt_const 0 (2 * σ)
  have hfin := hprod.div h2σ (mul_ne_zero two_pos.ne' hσ.ne')
  refine (hfin.congr_deriv ?_).congr_of_eventuallyEq ?_ |>.deriv
  · rw [show (1 : ℝ) + smileDelta σ ψ₁ T₀ 0 0 T = 1 from by rw [smileDelta_zero]; norm_num,
      Real.sqrt_one, slopeNum_zero]
    field_simp [hσ.ne', hT.ne', hS.ne', (Real.sqrt_pos.mpr hS).ne']
    ring
  · filter_upwards [hev] with ε hε
    rw [hchain ε hε]
    simp only [Pi.mul_apply, Pi.div_apply]
    by_cases hD : 0 < 1 + smileDelta σ ψ₁ T₀ ε 0 T
    · have hs0 : Real.sqrt (1 + smileDelta σ ψ₁ T₀ ε 0 T) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr hD)
      have hD0 : 1 + smileDelta σ ψ₁ T₀ ε 0 T ≠ 0 := ne_of_gt hD
      field_simp [hσ.ne', hs0, hD0]
    · have hsq0 : Real.sqrt (1 + smileDelta σ ψ₁ T₀ ε 0 T) = 0 :=
        (Real.sqrt_eq_zero' (x := 1 + smileDelta σ ψ₁ T₀ ε 0 T)).mpr (not_lt.mp hD)
      rw [hsq0]
      simp

/-! ## Corollaries -/

/-- **The rule of two, recovered** (chapter p. 182): at `T = 0` the local-skew
factor `ψ₁((3/2)·0 + 2T₀)/((0+T₀)√(0+T₀))`, rescaled by today's implied-skew
yardstick `√T₀`, is exactly `2ψ₁` — the local ATM skew is twice the implied ATM
skew `ψ₁/√T₀`. -/
theorem ruleOfTwo (ψ₁ T₀ : ℝ) (h₀ : 0 < T₀) :
    Real.sqrt T₀ * (ψ₁ * ((3 / 2) * 0 + 2 * T₀) / ((0 + T₀) * Real.sqrt (0 + T₀)))
      = 2 * ψ₁ := by
  norm_num
  try field_simp [(Real.sqrt_pos.mpr h₀).ne']
  try ring

/-- **The calendar-time asymptotic** of the local skew: `√T` times the eq-10.8
value tends to `(3/2)ψ₁` — "by ten years it is a third of today's" is the
finite-`T` shadow of this limit. -/
theorem localSkew_tendsto (ψ₁ T₀ : ℝ) :
    Filter.Tendsto (fun T => ψ₁ * ((3 / 2) * T + 2 * T₀) / ((T + T₀) * Real.sqrt (T + T₀))
        * Real.sqrt T) Filter.atTop (nhds ((3 / 2) * ψ₁)) := by
  have hADD : Filter.Tendsto (fun T : ℝ => T + T₀) Filter.atTop Filter.atTop := by
    intro s hs
    rw [Filter.mem_map]
    rw [Filter.mem_atTop_sets] at hs
    obtain ⟨b, hb⟩ := hs
    filter_upwards [(Filter.tendsto_id (α := ℝ)).eventually_gt_atTop (b - T₀)] with T hT
    simp only [id_eq] at hT
    exact hb (T + T₀) (by linarith)
  have hinv : Filter.Tendsto (fun T : ℝ => (T + T₀)⁻¹) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hADD
  have hA : Filter.Tendsto (fun T : ℝ => (3 / 2 : ℝ) + (T₀ / 2) * (T + T₀)⁻¹)
      Filter.atTop (nhds ((3 / 2 : ℝ) + (T₀ / 2) * 0)) :=
    (tendsto_const_nhds (x := (3 / 2 : ℝ))).add ((tendsto_const_nhds (x := T₀ / 2)).mul hinv)
  rw [show ((3 : ℝ) / 2 + (T₀ / 2) * 0) = 3 / 2 from by norm_num] at hA
  have hM0 : Filter.Tendsto (fun T : ℝ => 1 - T₀ * (T + T₀)⁻¹) Filter.atTop (nhds (1 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := T₀)).mul hinv))
  have hM : Filter.Tendsto (fun T : ℝ => Real.sqrt (1 - T₀ * (T + T₀)⁻¹)) Filter.atTop
      (nhds (1 : ℝ)) := by
    have hc := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hM0
    rw [Function.comp_def, Real.sqrt_one] at hc
    exact hc
  have hfin := (tendsto_const_nhds (x := ψ₁)).mul (hA.mul hM)
  rw [mul_one] at hfin
  rw [show ψ₁ * ((3 : ℝ) / 2) = (3 / 2) * ψ₁ from by ring] at hfin
  refine hfin.congr' ?_
  filter_upwards [(Filter.tendsto_id (α := ℝ)).eventually_gt_atTop (-T₀),
    (Filter.tendsto_id (α := ℝ)).eventually_ge_atTop 0] with T hT hT0
  simp only [id_eq] at hT hT0
  have hne : T + T₀ ≠ 0 := by linarith
  have hpos : 0 < T + T₀ := by linarith
  have hinner : 1 - T₀ * (T + T₀)⁻¹ = T / (T + T₀) := by
    field_simp [hne]
    ring
  rw [hinner, Real.sqrt_div hT0]
  field_simp [hne, (Real.sqrt_pos.mpr hpos).ne']
  ring

/-- **Eq 10.9, anchored**: the chapter's forward skew — half the local skew at the
forward date (the rule-of-two-in-reverse step, chapter math anchored on
`dupireRatio_sqrt_slope`) — is `ψ_fwd(t) = ½ψ₁((3/2)t + 2T₀)/(t+T₀)^{3/2}`. -/
theorem forwardSkew_eq_half {F σ ψ₁ T₀ t : ℝ} (hF : 0 < F) (hσ : 0 < σ) (ht : 0 < t)
    (h₀ : 0 < T₀) :
    (1 / 2) * deriv (fun ε => deriv (fun k => Real.sqrt (dupireRatio F σ ψ₁ T₀ ε k t)) 0) 0
      = ψ₁ * ((3 / 2) * t + 2 * T₀) / (2 * (t + T₀) * Real.sqrt (t + T₀)) := by
  rw [dupireRatio_sqrt_slope hF hσ ht h₀]
  have hpos : 0 < t + T₀ := by linarith
  field_simp [hpos.ne', (Real.sqrt_pos.mpr hpos).ne']

/-- **Eq 10.9's asymptotic**: `√t` times the forward skew tends to `(3/4)ψ₁`. -/
theorem forwardSkew_tendsto (ψ₁ T₀ : ℝ) :
    Filter.Tendsto (fun t => ψ₁ * ((3 / 2) * t + 2 * T₀)
        / (2 * (t + T₀) * Real.sqrt (t + T₀)) * Real.sqrt t) Filter.atTop
      (nhds ((3 / 4) * ψ₁)) := by
  have h := localSkew_tendsto ψ₁ T₀
  have hhalf := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul h
  rw [show (1 / 2 : ℝ) * ((3 / 2) * ψ₁) = (3 / 4) * ψ₁ from by ring] at hhalf
  refine hhalf.congr' ?_
  filter_upwards [(Filter.tendsto_id (α := ℝ)).eventually_gt_atTop (-T₀)] with t ht
  simp only [id_eq] at ht
  have hpos : 0 < t + T₀ := by linarith
  field_simp [hpos.ne', (Real.sqrt_pos.mpr hpos).ne']

/-- The chapter's numeric reading at `t = 1` (σ = 20%, ψ₁ = −0.10, `T₀ = 1/12`):
the forward skew is `10/(13√13) ≈ 0.2133` of today's implied skew — "a fifth". -/
theorem skewRatio_one :
    (1 / 2) * ((3 / 2) * (1 : ℝ) + 2 * (1 / 12)) * Real.sqrt (1 / 12)
        / ((1 + 1 / 12) * Real.sqrt (1 + 1 / 12))
      = 10 / (13 * Real.sqrt 13) := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
    show (1 : ℝ) + 1 / 12 = 13 / 12 from by norm_num,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 13), Real.sqrt_one]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne',
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 13)).ne']
  ring

/-- The chapter's numeric reading at `t = 4`: `37/343 ≈ 0.1079` — "an eighth". -/
theorem skewRatio_four :
    (1 / 2) * ((3 / 2) * (4 : ℝ) + 2 * (1 / 12)) * Real.sqrt (1 / 12)
        / ((4 + 1 / 12) * Real.sqrt (4 + 1 / 12))
      = 37 / 343 := by
  have h7 : Real.sqrt 49 = 7 := by
    rw [show (49 : ℝ) = 7 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 7)]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
    show (4 : ℝ) + 1 / 12 = 49 / 12 from by norm_num,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 49), h7, Real.sqrt_one]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne']
  ring

/-- The chapter's numeric reading at `t = 10`: `91/1331 ≈ 0.0684` — "under a
tenth". -/
theorem skewRatio_ten :
    (1 / 2) * ((3 / 2) * (10 : ℝ) + 2 * (1 / 12)) * Real.sqrt (1 / 12)
        / ((10 + 1 / 12) * Real.sqrt (10 + 1 / 12))
      = 91 / 1331 := by
  have h11 : Real.sqrt 121 = 11 := by
    rw [show (121 : ℝ) = 11 ^ 2 from by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 11)]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
    show (10 : ℝ) + 1 / 12 = 121 / 12 from by norm_num,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 121), h11, Real.sqrt_one]
  field_simp [(Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 12)).ne']
  ring

end MathFin.ForwardSmile
