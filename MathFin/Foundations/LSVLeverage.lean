/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.BlackScholes.BreedenLitzenberger

/-!
# LSV leverage-posterior core

Chapter 11's theorem *shape* is `L²(t,K) · E[v_t | S_t = K] = σ_loc²(t,K)` (eq. 11.1): the
local-stochastic-volatility leverage function `L` is pinned by the posterior mean of the
stochastic variance on the state, and everything about the fit flows through that equation.
This file proves the **algebraic and analytic core behind the form** — the parts that follow
from measure theory and exact real arithmetic, with no stochastic-process hypotheses:

* the conditioning step itself: `E[v | σ(S)]` *is* a Borel function of the state
  (Doob–Dynkin; Thm 11.2 reads `E[v_t | S_t = K]` as a function of `K` exactly this way),
  and `L²(S)` crosses the conditional expectation (`lsv_condExp_factors_through_state`,
  `lsv_condExp_pullout`);
* the pinned product and its extremes (`lsv_pinned_product`, eq. 11.6): `m ≡ 1` recovers
  pure local vol, `m = σ_loc²` switches the leverage off (Ex. 11.1);
* the coin-toss λ-dial family (§11.4 / Calc 11.3): branch variances `29/400 ∓ λ/20` keep
  `E[v^λ]` pinned at `29/400` for every λ; the λ = 0 endpoint is flat leverage with
  squared value `25/29` at `σ_loc = 1/4` — the chapter's "0.93", exact;
* the coin-toss leverage function of Ex. 11.2 as exact inequalities: ATM posterior on the
  high branch `< 1/2`, ATM leverage below the unconditional mean, posterior on the high
  branch → 1 in BOTH wings (the log-density ratio is a downward parabola in `ln(K/F)`),
  and nonconstancy of the leverage function.

## Status block (proved / hypothesized / gated — the honest boundary)

* **Proved here:** every declaration in this file, with no proof holes left open; every
  public theorem prints the standard three axioms.
* **Not here (gated chapter mathematics, by design):** Thm 11.2's *iff* content (that the
  leverage-defined model reprices the market — needs Gyöngy-mimicry flow uniqueness, weak
  existence on the local-vol side, the Dupire surface formula on a non-Gaussian carrier,
  and the McKean–Vlasov existence question, "not settled in general", PDF p. 200);
  §11.3's grid and particle machinery; every decimal figure of the chapter tables
  (22.9%, 26.9%, 0.98, 1.09 → 0.71). The build proves exact statements, not decimals.
* **Stretch (gated — see the record at the bottom of this file):** the condExp
  characterization of the coin-toss posterior on a two-branch mixture measure. The gating
  engine is the *integral* lognormal change of variables (density pushforward); the AC
  face carries only the differential identity. Details recorded below.
-/

@[expose] public section

namespace MathFin.LSV

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-! ## B1–B2: the conditioning layer -/

set_option linter.unusedVariables false in
/-- **B1 — Doob–Dynkin factorization of the state conditional expectation.**
For an integrable `v`, the conditional expectation `E[v | σ(S)]` is a *pointwise* Borel
function of the state: there is `m : ℝ → ℝ`, `Measurable m`, with
`μ[v | σ(S)] ω = m (S ω)` for every `ω`. This is the measure-theoretic content of reading
Thm 11.2's `E[v_t | S_t = K]` as a genuine function of the strike `K` (eq. 11.2): the
posterior is *carried by the state*, not by the path.

Engine: `stronglyMeasurable_condExp` (the conditional expectation is `σ(S)`-strongly
measurable — unconditional in this Mathlib rev) + `StronglyMeasurable.exists_eq_measurable_comp`
(the Doob–Dynkin lemma, `FactorsThrough.lean`), read at `Real.measurableSpace.comap S`.
Re-derived here as a public wrapper (a corresponding construction is
file-private in this program's sibling sources);
the integrability hypothesis keeps the statement honest (without it `condExp` degenerates
to `0` by convention, and the factorization is vacuous), but Doob–Dynkin itself uses none
of it. -/
theorem lsv_condExp_factors_through_state {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S v : Ω → ℝ} (hv : Integrable v μ) :
    ∃ m : ℝ → ℝ, Measurable m ∧ ∀ ω,
      μ[v | Real.measurableSpace.comap S] ω = m (S ω) := by
  obtain ⟨m, hm, hmeq⟩ :=
    (stronglyMeasurable_condExp (f := v)).exists_eq_measurable_comp (f := S)
  exact ⟨m, hm.measurable, fun ω => congrFun hmeq ω⟩

#print axioms lsv_condExp_factors_through_state

/-- **B2 — `L²` crosses the conditional expectation (the factoring step of Thm 11.2).**
For Borel `L` (the leverage function) and integrable `v` with `L²(S) · v` integrable,
`E[L²(S) · v | σ(S)] = L²(S) · E[v | σ(S)]` a.e. This is exactly the chapter's factoring
sentence (PDF p. 197): "L²(t,S_t) comes out of the conditional expectation because … it
is a deterministic function of the thing being conditioned on."

Engine: `condExp_mul_of_stronglyMeasurable_right` (`PullOut.lean`); the `σ(S)`-strong
measurability of `L² ∘ S` is the comap-factorization of a Borel function through the
state (`MeasurableSpace.comap_comp`). -/
theorem lsv_condExp_pullout {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S v : Ω → ℝ} {L : ℝ → ℝ}
    (hL : Measurable L)
    (hv : Integrable v μ)
    (hLv : Integrable (fun ω => (L (S ω)) ^ 2 * v ω) μ) :
    μ[fun ω => (L (S ω)) ^ 2 * v ω | Real.measurableSpace.comap S] =ᵐ[μ]
      μ[v | Real.measurableSpace.comap S] * fun ω => (L (S ω)) ^ 2 := by
  have hcomp : Measurable[Real.measurableSpace.comap S] (L ∘ S) := by
    rw [measurable_iff_comap_le, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp hL)
  have hg : StronglyMeasurable[Real.measurableSpace.comap S]
      (fun ω => (L (S ω)) ^ 2) := (hcomp.pow measurable_const).stronglyMeasurable
  have hflip : (fun ω => (L (S ω)) ^ 2 * v ω) = fun ω => v ω * (L (S ω)) ^ 2 := by
    funext ω; exact mul_comm _ _
  have hLv' : Integrable (fun ω => v ω * (L (S ω)) ^ 2) μ := by
    rw [← hflip]; exact hLv
  rw [hflip]
  exact condExp_mul_of_stronglyMeasurable_right hg hLv' hv

#print axioms lsv_condExp_pullout

/-! ## B3: the pinned product and its extremes -/

/-- **B3 — the pinned product (eq. 11.6 shape).** The leverage function of an LSV model is
`L = σ_loc / √m`, where `m(K)` is the posterior mean of the stochastic variance at strike
`K`; the defining product `L² · m = σ_loc²` is an identity as soon as `m > 0`. Everything
downstream (the λ-family, the endpoint values) is this telescope plus arithmetic. -/
theorem lsv_pinned_product (σ_loc m : ℝ → ℝ) (hm : ∀ x, 0 < m x) (x : ℝ) :
    (σ_loc x / Real.sqrt (m x)) ^ 2 * m x = σ_loc x ^ 2 := by
  rw [div_pow, Real.sq_sqrt ((hm x).le), div_mul_cancel₀ _ (hm x).ne']

/-- **The pinned product holds for the whole dial family at once** (eq. 11.6's per-λ form):
whatever `m_λ` the λ-dial produces, `(σ_loc/√m_λ)² · m_λ = σ_loc²` — λ changes the answer,
never the calibration. -/
theorem lsv_pinned_product_family {ι : Type*} (σ_loc : ℝ → ℝ) (m : ι → ℝ → ℝ)
    (hm : ∀ i x, 0 < m i x) (i : ι) (x : ℝ) :
    (σ_loc x / Real.sqrt (m i x)) ^ 2 * m i x = σ_loc x ^ 2 :=
  lsv_pinned_product σ_loc (m i) (fun x => hm i x) x

/-- **First extreme (Ex. 11.1): `m ≡ 1` ⇒ `L = σ_loc`.** With no stochastic content the
leverage is the local volatility itself — pure local vol. -/
theorem lsv_leverage_of_m_one (σ_loc m : ℝ → ℝ) (x : ℝ) (h : m x = 1) :
    σ_loc x / Real.sqrt (m x) = σ_loc x := by
  simp [h]

/-- **Second extreme (Ex. 11.1): `m = σ_loc²` ⇒ `L = 1`.** When the stochastic part already
fits the surface, `E[v | S = K] = σ_loc²(K)` and the leverage "switches itself off". -/
theorem lsv_leverage_switches_off (σ_loc m : ℝ → ℝ) (x : ℝ) (hσ : 0 < σ_loc x)
    (h : m x = σ_loc x ^ 2) : σ_loc x / Real.sqrt (m x) = 1 := by
  rw [h, Real.sqrt_sq hσ.le]
  exact div_self hσ.ne'

/-! ## B4: the coin-toss λ-dial family (§11.4, Calc 11.3) -/

/-- The λ-dial branch variances of Calc 11.3: a flat 25%-volatility surface split into a
low and a high branch, `v_lo(λ) = 29/400 − λ/20` and `v_hi(λ) = 29/400 + λ/20`. At `λ = 1`
these are the Ex. 11.2 coin toss `9/400 = 0.15²` and `49/400 = 0.35²`; at `λ = 0` the dial
collapses to the single deterministic variance `29/400 = (0.269…)²`. -/
noncomputable def cointossVLo (lam : ℝ) : ℝ := 29 / 400 - lam / 20

/-- The high branch of the λ-dial (see `cointossVLo`). -/
noncomputable def cointossVHi (lam : ℝ) : ℝ := 29 / 400 + lam / 20

/-- **λ-invariance of the branch mean:** for every λ, the two-branch average of the variance
is exactly `29/400`. The dial moves variance between the branches without moving the mean —
"λ changes the answer, does not change the calibration, and therefore cannot be determined
by it" (PDF p. 203). -/
theorem cointoss_family_mean (lam : ℝ) :
    (cointossVLo lam + cointossVHi lam) / 2 = 29 / 400 := by
  unfold cointossVLo cointossVHi; ring

/-- The low branch stays positive across the whole dial `λ ∈ [0, 1]` (at `λ = 1` it is
`9/400 > 0`). -/
theorem cointoss_vLo_pos (lam : ℝ) (h1 : lam ≤ 1) : 0 < cointossVLo lam := by
  unfold cointossVLo; linarith

/-- The high branch is positive for every nonnegative λ (at `λ = 0` it is `29/400 > 0`). -/
theorem cointoss_vHi_pos (lam : ℝ) (h0 : 0 ≤ lam) : 0 < cointossVHi lam := by
  unfold cointossVHi; linarith

/-- **The λ = 0 endpoint in ratio form (Calc 11.3):** the dial collapses to a single
deterministic variance `m ≡ E[v⁰] = 29/400`, so the squared leverage is the flat ratio
`σ_loc² / (29/400)`. -/
theorem cointoss_endpoint_l0_sq (σ_loc : ℝ) :
    (σ_loc / Real.sqrt (29 / 400)) ^ 2 = σ_loc ^ 2 / (29 / 400) := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 29 / 400)]

/-- The λ = 0 endpoint in pinned-product form: the constant posterior `29/400` telescopes
with the squared leverage to `σ_loc²`. -/
theorem cointoss_endpoint_l0_pinned (σ_loc : ℝ) :
    (σ_loc / Real.sqrt (29 / 400)) ^ 2 * (29 / 400) = σ_loc ^ 2 :=
  lsv_pinned_product (fun _ => σ_loc) (fun _ => 29 / 400) (fun _ => by norm_num) 0

/-- **The chapter's flat "0.93", exact:** at `σ_loc = 1/4` the λ = 0 squared leverage is
`L⁰² = 25/29` (Calc 11.3's `L⁰ ≈ 0.93` is the square root of this rational). -/
theorem cointoss_endpoint_l0_quarter :
    ((1:ℝ) / 4 / Real.sqrt (29 / 400)) ^ 2 = 25 / 29 := by
  rw [cointoss_endpoint_l0_sq]; norm_num

#print axioms lsv_pinned_product
#print axioms lsv_pinned_product_family
#print axioms lsv_leverage_of_m_one
#print axioms lsv_leverage_switches_off
#print axioms cointoss_family_mean
#print axioms cointoss_vLo_pos
#print axioms cointoss_vHi_pos
#print axioms cointoss_endpoint_l0_sq
#print axioms cointoss_endpoint_l0_pinned
#print axioms cointoss_endpoint_l0_quarter

/-! ## B5: the coin-toss leverage function (Ex. 11.2) -/

/-- The branch density of the coin-toss example: the Black–Scholes lognormal terminal
density with spot `F`, zero rate, unit maturity and branch volatility `σ`, evaluated at
strike `K` — Ex. 11.2's `φ_c(K)` (`MathFin.lognormalTerminalPDF` at `S_0 = F, r = 0,
T = 1`; branch means the coin came up `σ = σ_lo` or `σ = σ_hi`). -/
noncomputable def cointossPhi (F σ K : ℝ) : ℝ :=
  lognormalTerminalPDF F 0 σ 1 K

/-- The branch density is strictly positive wherever `σ, K > 0` (the Gaussian tail is
positive and the Jacobian `K σ √T` is positive). -/
theorem cointossPhi_pos {F σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K) :
    0 < cointossPhi F σ K := by
  unfold cointossPhi lognormalTerminalPDF
  rw [Real.sqrt_one]
  exact div_pos (gaussianPDFReal_pos 0 1 _ one_ne_zero) (by positivity)

/-- At the money the `d₂` of a branch density collapses to `−σ/2` (`r = 0`, `T = 1`,
`K = S_0 = F`). -/
theorem cointoss_bsd2_atm {F σ : ℝ} (hF : 0 < F) (hσ : 0 < σ) :
    bsd2 F F 0 σ 1 = -σ / 2 := by
  have h1 : Real.log (F / F) = 0 := by
    rw [Real.log_div hF.ne' hF.ne', sub_self]
  rw [bsd2_eq hσ one_pos, h1, Real.sqrt_one, mul_one, zero_add, zero_sub]
  field_simp

/-- The ATM branch density in product form: the Gaussian normalization constant times the
Jacobian telescope to `exp(−σ²/8)`. (Auxiliary engine for the ATM comparisons; the
`√(2π)` is the normalization constant of `gaussianPDFReal 0 1`.) -/
theorem cointossPhi_atm_prod {F σ : ℝ} (hF : 0 < F) (hσ : 0 < σ) :
    cointossPhi F σ F * (F * σ) * Real.sqrt (2 * Real.pi * ((1:ℝ≥0) : ℝ)) =
      Real.exp (-(σ ^ 2 / 8)) := by
  unfold cointossPhi lognormalTerminalPDF
  rw [cointoss_bsd2_atm hF hσ, Real.sqrt_one]
  simp only [gaussianPDFReal, sub_zero, mul_one]
  push_cast
  have hFs : (F * σ : ℝ) ≠ 0 := mul_ne_zero hF.ne' hσ.ne'
  have hS : Real.sqrt (2 * Real.pi * (1:ℝ)) ≠ 0 := by positivity
  have hcan : ∀ c x : ℝ, c ≠ 0 → c⁻¹ * x * c = x := by
    intro c x hc
    rw [mul_comm c⁻¹ x, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  rw [div_mul_cancel₀ _ hFs, hcan _ _ hS]
  congr 1
  ring

/-- **The ATM density ratio** — both exact content and the engine of every ATM comparison
that follows: the flatter branch is the denser branch at the money, with exact ratio
`(σ_hi/σ_lo) · exp((σ_hi² − σ_lo²)/8) > 1`. -/
theorem cointoss_pdf_ratio_atm {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) :
    cointossPhi F σ_lo F / cointossPhi F σ_hi F =
      (σ_hi / σ_lo) * Real.exp ((σ_hi ^ 2 - σ_lo ^ 2) / 8) := by
  have hlo' : 0 < σ_hi := lt_trans hlo hhi
  have e1 := cointossPhi_atm_prod hF hlo
  have e2 := cointossPhi_atm_prod hF hlo'
  have hEdiv : Real.exp (-(σ_lo ^ 2 / 8)) / Real.exp (-(σ_hi ^ 2 / 8)) =
      Real.exp ((σ_hi ^ 2 - σ_lo ^ 2) / 8) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [← hEdiv, ← e1, ← e2]
  field_simp

/-- **At the money, the wider branch is the denser branch:** `φ_hi(F) < φ_lo(F)` —
the two-line chapter fact `ln(σ_lo/σ_hi) < 0 < (σ_hi²−σ_lo²)/8`, in exact form. -/
theorem cointoss_pdf_atm_lt {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) :
    cointossPhi F σ_hi F < cointossPhi F σ_lo F := by
  rw [← one_lt_div (cointossPhi_pos (lt_trans hlo hhi) hF),
    cointoss_pdf_ratio_atm hF hlo hhi]
  have h1 : (1:ℝ) < σ_hi / σ_lo := (one_lt_div hlo).2 hhi
  have h2 : (1:ℝ) < Real.exp ((σ_hi ^ 2 - σ_lo ^ 2) / 8) := by
    rw [Real.one_lt_exp_iff]
    have hs2 : σ_lo ^ 2 < σ_hi ^ 2 := by nlinarith [hhi, hlo]
    linarith
  have h3 : (0:ℝ) < σ_hi / σ_lo := by positivity
  have h4 : (0:ℝ) < Real.exp ((σ_hi ^ 2 - σ_lo ^ 2) / 8) := by positivity
  nlinarith [h1, h2, h3, h4]

/-- The posterior weight of the high branch at strike `K` under equal branch priors —
Ex. 11.2's Bayes ratio `P(hi | S_T = K) = φ_hi(K)/(φ_lo(K) + φ_hi(K))`. -/
noncomputable def cointossPostHi (F σ_lo σ_hi K : ℝ) : ℝ :=
  cointossPhi F σ_hi K / (cointossPhi F σ_lo K + cointossPhi F σ_hi K)

/-- **The ATM posterior on the high branch is below one half** (the chapter's table entry
`P(hi | S_T = F) = 0.30 < 1/2`, exact). Engine: `cointoss_pdf_atm_lt` plus the positivity
of both densities. -/
theorem cointoss_posterior_atm_lt_half {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) :
    cointossPostHi F σ_lo σ_hi F < 1 / 2 := by
  have hlo' : 0 < σ_hi := lt_trans hlo hhi
  have hφlo : 0 < cointossPhi F σ_lo F := cointossPhi_pos hlo hF
  have hφhi : 0 < cointossPhi F σ_hi F := cointossPhi_pos hlo' hF
  have hden : 0 < cointossPhi F σ_lo F + cointossPhi F σ_hi F := add_pos hφlo hφhi
  have halt := cointoss_pdf_atm_lt hF hlo hhi
  unfold cointossPostHi
  rw [div_lt_iff₀ hden]
  nlinarith [halt]

/-- The posterior mean of the variance at strike `K` — the leverage-relevant function
`m(K) = (v_lo φ_lo K + v_hi φ_hi K)/(φ_lo K + φ_hi K)` of Thm 11.2's eq. 11.1, in the
strike-weighted form (the `K`'s cancel for `K ≠ 0`; see `cointossM_cancel`). -/
noncomputable def cointossM (F σ_lo σ_hi v_lo v_hi K : ℝ) : ℝ :=
  (v_lo * cointossPhi F σ_lo K * K + v_hi * cointossPhi F σ_hi K * K) /
    (cointossPhi F σ_lo K * K + cointossPhi F σ_hi K * K)

/-- For `K ≠ 0` the strike weights cancel and `m` is the plain density-weighted branch
average. -/
theorem cointossM_cancel {F σ_lo σ_hi v_lo v_hi K : ℝ} (hK : K ≠ 0)
    (hne : cointossPhi F σ_lo K + cointossPhi F σ_hi K ≠ 0) :
    cointossM F σ_lo σ_hi v_lo v_hi K =
      (v_lo * cointossPhi F σ_lo K + v_hi * cointossPhi F σ_hi K) /
        (cointossPhi F σ_lo K + cointossPhi F σ_hi K) := by
  unfold cointossM
  field_simp

/-- **The ATM leverage sits below the unconditional variance mean** (the chapter's "wrong
by four volatility points at the money": calibrating to the unconditional `E[v]` while the
true ATM input is the posterior `m(F) < (v_lo + v_hi)/2`). Engine: the pinned algebra
`(v_hi − v_lo)(φ_lo(F) − φ_hi(F)) > 0`. -/
theorem cointoss_leverage_atm_lt_uncond {F σ_lo σ_hi v_lo v_hi : ℝ} (hF : 0 < F)
    (hlo : 0 < σ_lo) (hhi : σ_lo < σ_hi) (hvhi : v_lo < v_hi) :
    cointossM F σ_lo σ_hi v_lo v_hi F < (v_lo + v_hi) / 2 := by
  have hlo' : 0 < σ_hi := lt_trans hlo hhi
  have hφlo : 0 < cointossPhi F σ_lo F := cointossPhi_pos hlo hF
  have hφhi : 0 < cointossPhi F σ_hi F := cointossPhi_pos hlo' hF
  have hden : 0 < cointossPhi F σ_lo F + cointossPhi F σ_hi F := add_pos hφlo hφhi
  have halt := cointoss_pdf_atm_lt hF hlo hhi
  rw [cointossM_cancel hF.ne' hden.ne', div_lt_div_iff₀ hden zero_lt_two]
  nlinarith [mul_pos (sub_pos.mpr hvhi) (sub_pos.mpr halt)]

#print axioms cointossPhi_pos
#print axioms cointoss_bsd2_atm
#print axioms cointossPhi_atm_prod
#print axioms cointoss_pdf_ratio_atm
#print axioms cointoss_pdf_atm_lt
#print axioms cointoss_posterior_atm_lt_half
#print axioms cointossM_cancel
#print axioms cointoss_leverage_atm_lt_uncond

/-- For `r = 0`, `T = 1`, `K > 0`: the branch `d₂` is `−(x + σ²/2)/σ` in the log-moneyness
variable `x = ln(K/F)`. (Auxiliary to the wing limits.) -/
theorem cointoss_bsd2_log {F σ K : ℝ} (hF : 0 < F) (hσ : 0 < σ) (hK : 0 < K) :
    bsd2 F K 0 σ 1 = (-Real.log (K / F) - σ ^ 2 / 2) / σ := by
  have h1 : Real.log (F / K) = -Real.log (K / F) := by
    rw [Real.log_div hF.ne' hK.ne', Real.log_div hK.ne' hF.ne']
    ring
  rw [bsd2_eq hσ one_pos, h1, Real.sqrt_one, mul_one, zero_sub]
  ring

/-- **The log-density ratio is a downward parabola in log-moneyness** — the engine of both
wing limits: `log(φ_lo/φ_hi) = b − a·(ln(K/F))²` with
`a = (σ_hi² − σ_lo²)/(2σ_lo²σ_hi²) > 0` and intercept `b = ln(σ_hi/σ_lo) +
(σ_hi² − σ_lo²)/8`. In both wings `|ln(K/F)| → ∞` drives the ratio `φ_lo/φ_hi` to `0`,
i.e. the posterior piles onto the wide branch. -/
theorem cointoss_pdf_ratio_log {F σ_lo σ_hi K : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) (hK : 0 < K) :
    Real.log (cointossPhi F σ_lo K / cointossPhi F σ_hi K) =
      (Real.log (σ_hi / σ_lo) + (σ_hi ^ 2 - σ_lo ^ 2) / 8) -
        (σ_hi ^ 2 - σ_lo ^ 2) / (2 * σ_lo ^ 2 * σ_hi ^ 2) * (Real.log (K / F)) ^ 2 := by
  have hlo' : 0 < σ_hi := lt_trans hlo hhi
  -- the Gaussian ratio of the two branch densities
  have hgr : ∀ d₁ d₂ : ℝ,
      gaussianPDFReal 0 1 d₁ / gaussianPDFReal 0 1 d₂ = Real.exp ((d₂ ^ 2 - d₁ ^ 2) / 2) := by
    intro d₁ d₂
    have hstep : gaussianPDFReal 0 1 d₁ / gaussianPDFReal 0 1 d₂ =
        Real.exp (-(d₁ ^ 2 / 2)) / Real.exp (-(d₂ ^ 2 / 2)) := by
      simp only [gaussianPDFReal, sub_zero]
      push_cast
      rw [mul_div_mul_left _ _ (by positivity : (Real.sqrt (2 * Real.pi * (1:ℝ)))⁻¹ ≠ 0)]
      norm_num
      simp only [neg_div]
    rw [hstep, ← Real.exp_sub]
    congr 1
    ring
  -- the strike-ratio assembly (the `K` Jacobians cancel between the branches)
  have hφratio : cointossPhi F σ_lo K / cointossPhi F σ_hi K =
      (σ_hi / σ_lo) * Real.exp (((Real.log (K / F) + σ_hi ^ 2 / 2) ^ 2 / σ_hi ^ 2
        - (Real.log (K / F) + σ_lo ^ 2 / 2) ^ 2 / σ_lo ^ 2) / 2) := by
    have hdiv : ∀ g₁ g₂ a b : ℝ, a ≠ 0 → b ≠ 0 →
        (g₁ / a) / (g₂ / b) = (g₁ / g₂) * (b / a) := by
      intro g₁ g₂ a b ha hb
      field_simp
    unfold cointossPhi lognormalTerminalPDF
    rw [cointoss_bsd2_log hF hlo hK, cointoss_bsd2_log hF hlo' hK, Real.sqrt_one, mul_one,
      mul_one,
      hdiv _ _ _ _ (mul_ne_zero hK.ne' hlo.ne') (mul_ne_zero hK.ne' hlo'.ne'), hgr]
    have hscalar : (K * σ_hi) / (K * σ_lo) = σ_hi / σ_lo := by
      rw [mul_div_mul_left _ _ hK.ne']
    rw [hscalar, mul_comm (Real.exp _)]
    congr 1
    congr 1
    ring
  -- take the log of the assembled ratio
  have hQ : (((Real.log (K / F) + σ_hi ^ 2 / 2) ^ 2 / σ_hi ^ 2
      - (Real.log (K / F) + σ_lo ^ 2 / 2) ^ 2 / σ_lo ^ 2) / 2) =
      (σ_hi ^ 2 - σ_lo ^ 2) / 8 -
        (σ_hi ^ 2 - σ_lo ^ 2) / (2 * σ_lo ^ 2 * σ_hi ^ 2) * (Real.log (K / F)) ^ 2 := by
    have h1 : (σ_lo ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ hlo.ne'
    have h2 : (σ_hi ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ hlo'.ne'
    field_simp
    ring
  rw [hφratio, Real.log_mul (div_pos hlo' hlo).ne' (Real.exp_pos _).ne', Real.log_exp, hQ]
  ring

/-- The posterior weight rewrites as `1/(1 + φ_lo/φ_hi)` — the form the wing limits feed
into. -/
theorem cointoss_posterior_eq {F σ_lo σ_hi K : ℝ} (hlo : 0 < σ_lo) (hlo' : 0 < σ_hi)
    (hK : 0 < K) :
    cointossPostHi F σ_lo σ_hi K =
      1 / (1 + cointossPhi F σ_lo K / cointossPhi F σ_hi K) := by
  have hφlo : 0 < cointossPhi F σ_lo K := cointossPhi_pos hlo hK
  have hφhi : 0 < cointossPhi F σ_hi K := cointossPhi_pos hlo' hK
  unfold cointossPostHi
  field_simp
  ring

/-- The shared engine of both wing limits: whenever the squared log-moneyness diverges to
`+∞` along a filter on which strikes are eventually positive, the posterior weight on the
wide branch tends to `1`. (Private; the two public forms below instantiate `l`.) -/
private theorem cointoss_posterior_limit_aux {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) {l : Filter ℝ}
    (hu2 : Filter.Tendsto (fun K : ℝ => (Real.log (K / F)) ^ 2) l Filter.atTop)
    (hpos : ∀ᶠ K in l, (0:ℝ) < K) :
    Filter.Tendsto (cointossPostHi F σ_lo σ_hi) l (𝓝 1) := by
  have hlo' : 0 < σ_hi := lt_trans hlo hhi
  set a : ℝ := (σ_hi ^ 2 - σ_lo ^ 2) / (2 * σ_lo ^ 2 * σ_hi ^ 2) with ha_def
  set b : ℝ := Real.log (σ_hi / σ_lo) + (σ_hi ^ 2 - σ_lo ^ 2) / 8 with hb_def
  have hnum : (0:ℝ) < σ_hi ^ 2 - σ_lo ^ 2 := by nlinarith [hhi, hlo]
  have hA : (0:ℝ) < a := by
    rw [ha_def]
    exact div_pos hnum (mul_pos (mul_pos zero_lt_two (pow_pos hlo 2)) (pow_pos hlo' 2))
  -- the linear tail `b - a · t` drives `atBot`
  have hlin : Filter.Tendsto (fun t : ℝ => b - a * t) Filter.atTop Filter.atBot := by
    intro s hs
    obtain ⟨m, hm⟩ := Filter.mem_atBot_sets.mp hs
    simp only [Filter.mem_map]
    filter_upwards [Filter.eventually_gt_atTop ((b - m) / a)] with t ht
    have h1 : b - m < a * t := by
      rw [div_lt_iff₀ hA] at ht
      linarith
    exact hm _ (by linarith)
  -- so the log-ratio tends to atBot, and exponentiating gives the density ratio → 0
  have hlogR : Filter.Tendsto (fun K : ℝ =>
      Real.log (cointossPhi F σ_lo K / cointossPhi F σ_hi K)) l Filter.atBot :=
    (hlin.comp hu2).congr' (by
      filter_upwards [hpos] with K hK
      exact (cointoss_pdf_ratio_log hF hlo hhi hK).symm)
  have hR : Filter.Tendsto (fun K : ℝ => cointossPhi F σ_lo K / cointossPhi F σ_hi K) l
      (𝓝 0) := by
    refine (Real.tendsto_exp_atBot.comp hlogR).congr' ?_
    filter_upwards [hpos] with K hK
    exact Real.exp_log (div_pos (cointossPhi_pos hlo hK) (cointossPhi_pos hlo' hK))
  -- and `1/(1 + ·)` is continuous at `0` with value `1`
  have hcont : Filter.Tendsto (fun t : ℝ => 1 / (1 + t)) (𝓝 0) (𝓝 1) := by
    have h : Filter.Tendsto (fun t : ℝ => 1 / (1 + t)) (𝓝 0) (𝓝 ((1:ℝ) / ((1:ℝ) + 0))) :=
      (tendsto_const_nhds (x := (1:ℝ))).div
        ((tendsto_const_nhds (x := (1:ℝ))).add tendsto_id) (by norm_num)
    simpa using h
  exact (hcont.comp hR).congr' (by
    filter_upwards [hpos] with K hK
    exact (cointoss_posterior_eq hlo hlo' hK).symm)

/-- **Upper wing limit (Ex. 11.2's table, `K → ∞`):** the posterior weight on the wide
branch tends to `1` — the chapter's `0.98` at `K = 160`, as a limit statement. The
log-density ratio is a downward parabola in `ln(K/F)`, so the branch densities separate
exponentially in the wing. -/
theorem cointoss_posterior_wing_limit_atTop {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) :
    Filter.Tendsto (cointossPostHi F σ_lo σ_hi) Filter.atTop (𝓝 1) := by
  have hu : Filter.Tendsto (fun K : ℝ => Real.log (K / F)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      ((tendsto_id : Filter.Tendsto (fun K : ℝ => K) Filter.atTop Filter.atTop).atTop_div_const hF)
  exact cointoss_posterior_limit_aux hF hlo hhi
    ((hu.atTop_mul_atTop₀ hu).congr'
      (Filter.Eventually.of_forall (fun _ => (pow_two _).symm)))
    (Filter.eventually_gt_atTop 0)

/-- **Lower wing limit (Ex. 11.2's table, `K → 0⁺`):** the posterior weight on the wide
branch tends to `1` in the lower wing as well — the chapter's `0.96` at `K = 60`. Same
parabola, read at `ln(K/F) → −∞`. -/
theorem cointoss_posterior_wing_limit_atZero {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) :
    Filter.Tendsto (cointossPostHi F σ_lo σ_hi) (𝓝[>] 0) (𝓝 1) := by
  have hx : Filter.Tendsto (fun K : ℝ => Real.log (K / F)) (𝓝[>] 0) Filter.atBot := by
    intro s hs
    obtain ⟨a, ha⟩ := Filter.mem_atBot_sets.mp hs
    have hFa : (0:ℝ) < F * Real.exp a := by positivity
    have hmem : Set.Iio (F * Real.exp a) ∈ 𝓝 (0:ℝ) := Iio_mem_nhds hFa
    have hmem' : Set.Iio (F * Real.exp a) ∈ 𝓝[>] (0:ℝ) :=
      Filter.le_def.mp nhdsWithin_le_nhds _ hmem
    simp only [Filter.mem_map]
    filter_upwards [Filter.inter_mem self_mem_nhdsWithin hmem'] with K hK
    obtain ⟨hK2, hK1⟩ := hK
    have hK2' : (0:ℝ) < K := by simpa using hK2
    have hK1' : K < F * Real.exp a := by simpa using hK1
    have h1 : K / F < Real.exp a := by
      rw [div_lt_iff₀ hF, mul_comm]
      linarith
    refine ha _ (le_of_lt ?_)
    exact (Real.log_lt_log (div_pos hK2' hF) h1).trans_le (Real.log_exp a).le
  have hsq : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atBot Filter.atTop := by
    have hsqT : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop :=
      ((tendsto_id : Filter.Tendsto (fun x : ℝ => x) Filter.atTop Filter.atTop).atTop_mul_atTop₀
        tendsto_id).congr' (Filter.Eventually.of_forall (fun _ => (pow_two _).symm))
    exact (hsqT.comp tendsto_neg_atBot_atTop).congr'
      (Filter.Eventually.of_forall (fun x => by
        simp only [Function.comp_apply]; ring))
  exact cointoss_posterior_limit_aux hF hlo hhi (hsq.comp hx) self_mem_nhdsWithin

/-- For positive strikes the posterior mean is the flat branch mix
`m(K) = v_lo + (v_hi − v_lo) · P(hi | K)` — the leverage-relevant reading of the posterior
weight. -/
theorem cointossM_eq_of_pos {F σ_lo σ_hi v_lo v_hi K : ℝ} (hlo : 0 < σ_lo) (hlo' : 0 < σ_hi)
    (hK : 0 < K) :
    cointossM F σ_lo σ_hi v_lo v_hi K =
      v_lo + (v_hi - v_lo) * cointossPostHi F σ_lo σ_hi K := by
  have hφlo : 0 < cointossPhi F σ_lo K := cointossPhi_pos hlo hK
  have hφhi : 0 < cointossPhi F σ_hi K := cointossPhi_pos hlo' hK
  rw [cointossM_cancel hK.ne' (add_pos hφlo hφhi).ne']
  unfold cointossPostHi
  field_simp
  ring

/-- **The leverage function's upper-wing limit:** `m(K) → v_hi` as `K → ∞` — the posterior
mean of the variance converges to the wide branch in both wings (the hump shape of the
chapter's table). -/
theorem cointossM_wing_limit_atTop {F σ_lo σ_hi v_lo v_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) :
    Filter.Tendsto (fun K : ℝ => cointossM F σ_lo σ_hi v_lo v_hi K) Filter.atTop (𝓝 v_hi) := by
  have h1 : Filter.Tendsto (fun K : ℝ => (v_hi - v_lo) * cointossPostHi F σ_lo σ_hi K)
      Filter.atTop (𝓝 ((v_hi - v_lo) * 1)) :=
    (tendsto_const_nhds (x := v_hi - v_lo)).mul (cointoss_posterior_wing_limit_atTop hF hlo hhi)
  simp only [mul_one] at h1
  have h2 : Filter.Tendsto (fun K : ℝ => v_lo + (v_hi - v_lo) * cointossPostHi F σ_lo σ_hi K)
      Filter.atTop (𝓝 v_hi) := by
    have h3 := (tendsto_const_nhds (x := v_lo)).add h1
    simpa using h3
  exact h2.congr' (by
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with K hK
    exact (cointossM_eq_of_pos hlo (lt_trans hlo hhi) hK).symm)

/-- **The leverage function is not constant** (Ex. 11.2's punchline: the posterior `m` is a
genuine function of the strike, so no single-volatility shortcut reproduces it). If `m`
were constant it would equal its own upper-wing limit `v_hi`; but at the money
`m(F) < (v_lo + v_hi)/2 < v_hi`. -/
theorem cointoss_leverage_nonconstant {F σ_lo σ_hi v_lo v_hi : ℝ} (hF : 0 < F)
    (hlo : 0 < σ_lo) (hhi : σ_lo < σ_hi) (hvhi : v_lo < v_hi) :
    ¬ ∃ c : ℝ, ∀ K : ℝ, cointossM F σ_lo σ_hi v_lo v_hi K = c := by
  rintro ⟨c, hc⟩
  have h1 : Filter.Tendsto (fun K : ℝ => cointossM F σ_lo σ_hi v_lo v_hi K) Filter.atTop (𝓝 c) :=
    (tendsto_const_nhds (x := c)).congr'
      (Filter.Eventually.of_forall (fun K => (hc K).symm))
  have h3 : v_hi = c :=
    tendsto_nhds_unique (cointossM_wing_limit_atTop hF hlo hhi) h1
  have h4 : cointossM F σ_lo σ_hi v_lo v_hi F < (v_lo + v_hi) / 2 :=
    cointoss_leverage_atm_lt_uncond hF hlo hhi hvhi
  have h5 : cointossM F σ_lo σ_hi v_lo v_hi F = c := hc F
  linarith

#print axioms cointoss_bsd2_log
#print axioms cointoss_pdf_ratio_log
#print axioms cointoss_posterior_eq
#print axioms cointoss_posterior_wing_limit_atTop
#print axioms cointoss_posterior_wing_limit_atZero
#print axioms cointossM_eq_of_pos
#print axioms cointossM_wing_limit_atTop
#print axioms cointoss_leverage_nonconstant

/-! ## Gated stretch: `cointoss_condExp_characterization` (recorded, not proved)

**The would-be statement.** On the two-branch mixture space `Ω := ℝ ⊕ ℝ` with
`μ_mix := (1/2) • (Measure.map Sum.inl γ) + (1/2) • (Measure.map Sum.inr γ)`
(`γ := ProbabilityTheory.gaussianReal 0 1`), terminal state
`S_T (Sum.inl z) = F · exp (σ_lo · z − σ_lo²/2)`, `S_T (Sum.inr z) = F · exp (σ_hi · z − σ_hi²/2)`
and branch variance `v (Sum.inl _) = v_lo`, `v (Sum.inr _) = v_hi`, the posterior function
of B5 *is* the conditional expectation:

  `μ_mix[v | Real.measurableSpace.comap S_T] =ᵐ[μ_mix] (fun p => cointossM F σ_lo σ_hi v_lo v_hi (S_T p))`.

**Why it gates (the honest engine inventory, verified on this build's faces):**

* The proof reduces, via the condExp characterization (`StronglyMeasurable[comap]` +
  `∀ s ∈ comap S_T, ∫ x in s, g x ∂μ_mix = ∫ x in s, v x ∂μ_mix`) and branch-split
  integrals (`integral_add` + real-`smul` + `integral_map` over the two pushforwards), to
  the **integral lognormal change of variables**
  `∫ z, h (T_c z) ∂γ = ∫ K in Ioi 0, h K * cointossPhi F σ_c K ∂volume` with
  `T_c z = F · exp (σ_c z − σ_c²/2)`.
* The library's `lognormalTerminalPDF_change_of_variables` carries only the
  **differential** identity
  (`MathFin/BlackScholes/BreedenLitzenberger.lean:197`:
  `φ_c K · (K σ √T) = gaussianPDFReal 0 1 (bsd2 K)`). The differential identity is exactly the
  integrand-level Jacobian, but promoting it to the integral pushforward
  (`Measure.map T_c γ = φ_c • (volume.restrict (Ioi 0))`) needs either:
  - the Mathlib Jacobian API (`Mathlib/MeasureTheory/Function/Jacobian.lean:1127`,
    `map_withDensity_abs_det_fderiv_eq_addHaar`) with the full `ContDiffOn`/injectivity/
    `HasFDerivWithinAt` bookkeeping for `T_c` *and* its inverse, or
  - an FTOC-plus-CDF route (an antiderivative of `φ_c` via the chain rule on the Gaussian
    CDF, plus the wing limits of §B5 read at `K → 0⁺` and `K → ∞`).
  Both are genuine build items (est. 80–150 lines of measure-plumbing each), not a
  stretch-sized addendum to this file.
* Mathlib (81a5d257) has **no** lognormal-distribution module to import the pushforward
  from (checked: `Mathlib/Probability/Distributions/` has no `Lognormal.lean`).

**What is nevertheless true and proved here:** every *analytic property* of the posterior
that the characterization would transport — the defining pointwise identity
`cointossM · (φ_lo + φ_hi) = v_lo φ_lo + v_hi φ_hi` (implicit in `cointossM_cancel`,
`cointossM_eq_of_pos`), the ATM inequalities, both wing limits, and nonconstancy. The gap
is only the measure-theoretic *interpretation* of `cointossM ∘ S_T` as the condExp on the
mixture; that interpretation stays chapter-sourced (Ex. 11.2's Bayes computation). -/



