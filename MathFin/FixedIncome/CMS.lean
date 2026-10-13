/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.FixedIncome.InterestRateSwap
public import MathFin.Foundations.CarrMadan
public import MathFin.Foundations.Numeraire
public import MathFin.FixedIncome.ConvexitySensitivity

/-!
# CMS convexity adjustment: the par-rate functional under the annuity measure

A constant-maturity swap leg pays, at the fixing date `T`, the *then-prevailing*
par swap rate — a nonlinear functional of the curve state, discounted through an
annuity that is itself random. Taking today's par rate as its price is wrong by
the **convexity adjustment**. This module lands the model-free adjustment at
statement level on the swap layer of `MathFin/FixedIncome/InterestRateSwap.lean`
(`payerSwapValue` / `parSwapRate` / `annuity`):

* **The par-rate functional.** `cmsCurveRate P₀ δ C x = (P₀ − x)/(δ·(C + x))` —
  the par rate of a curve whose final discount factor is `x`, other factors
  fixed. Two bridges tie it to the swap layer: `annuity_update_eq` (the annuity
  of an updated curve splits into fixed part + new factor) and
  `parSwapRate_update_eq` / `payerSwapValue_update_eq_zero_iff` (the par
  identity of `payerSwapValue_eq_zero_iff` transports verbatim).
* **Convexity in the discount factor.** `cmsCurveRate_convexOn`: on `(0, ∞)`
  the rate is convex given `0 ≤ P₀ + C` — via the shifted-inverse engine
  `convexOn_inv_shift` and the `ConvexOn.smul` / `.add_const` / `.congr`
  combination pattern. First and second derivatives are landed explicitly
  (`hasDerivAt_cmsCurveRate`, `hasDerivAt_cmsCurveRate'`):
  `S''(x) = 2(P₀+C)/(δ(C+x)³) > 0`.
* **The annuity measure.** `annuityMeasure`: the change-of-numéraire measure
  with the annuity `A_T` in the numéraire seat against the money market
  `B_t = e^{rt}` — an execution of `MathFin.changeOfNumeraire`
  (`Foundations/Numeraire.lean`), alongside the stock and the `T`-bond (the
  forward measure of `FixedIncome/ForwardMeasure.lean`). `annuityMeasure_price`
  proves the fair-value identity `A₀·𝔼^{Qᴬ}[S] = 𝔼^Q[e^{−rT}·S·A_T]`;
  `annuityMeasure_isProbabilityMeasure` proves `Qᴬ` is a probability *given the
  annuity repricing condition* `𝔼^Q[e^{−rT}A_T] = A₀` — that normalization is
  where the martingale content enters, and it is taken as an explicit
  hypothesis (the honest out; no model-free proof exists).
* **The headline.** `cms_adjustment_nonneg`: Jensen under the annuity measure
  (Mathlib's `ConvexOn.map_integral_le`) gives

    `S(x₀) ≤ 𝔼^{Qᴬ}[S(W)]` whenever `𝔼^{Qᴬ}[W] = x₀`,

  i.e. the CMS forward dominates the rate evaluated at the annuity-measure mean
  of the curve state: the convexity adjustment is nonnegative
  (`cms_adjustment_delta_nonneg` states the adjustment itself).
* **The replication seed.** `cmsCurveRate_spanning`: Carr–Madan static
  replication of the rate functional — cash + forward + put strip + call strip
  with strictly positive weights `2(P₀+C)/(δ(C+K)³)` (`cmsStrip_weight_pos`);
  `cmsCurveRate_strip_nonneg` turns it into the model-free pointwise statement
  that the rate minus its first-order expansion is nonnegative.
* **The convexity tie-in.** `convexityNumerator_nonneg`: the bond convexity
  `ConvNum` of `ConvexitySensitivity` — the quantity that weights the
  adjustment's second-order term (`bondPriceDisc_secondDeriv_eq_convexity_times_price`)
  — is nonnegative under honest hypotheses.

Structural note: the model-free adjustment is what lands here. The model-based
adjustment (a calibrated-volatility input into `𝔼^{Qᴬ}[S_T]`) is not
model-free and is out of scope; the spanning is the compact-strike-range
version (`[L, U]` with `L > −C`), the unbounded-window passage (tail analysis)
likewise. The swap-rate functional is *not* a log payoff, so the seed consumes
`carrMadan_spanning` — the shared core of which `carrMadan_log_spanning` is the
log instance (its proof is one instantiation).

## Result

Public definitions: `cmsCurveRate`, `annuityRandom`, `annuityMeasure`.

Public lemmas (all in `namespace MathFin.CMS`):

* `parSwapRate_update_eq`, `payerSwapValue_update_eq_zero_iff` — the bridges
  from the curve update to the swap layer;
* `hasDerivAt_cmsCurveRate`, `hasDerivAt_cmsCurveRate'`, `cmsCurveRate_convexOn`
  — first and second derivatives and convexity of the rate functional;
* `annuityMeasure_isProbabilityMeasure`, `annuityMeasure_price` — the annuity
  measure and its fair-value identity;
* `cms_adjustment_nonneg`, `cms_adjustment_delta_nonneg` — the convexity
  adjustment is nonnegative;
* `cmsCurveRate_spanning`, `cmsCurveRate_strip_nonneg`,
  `convexityNumerator_nonneg` — the replication seed and the convexity tie-in.

Supporting lemmas (`annuity_update_eq`, `cmsCurveRate_eq`,
`differentiableOn_cmsCurveRate`, `continuousOn_cmsCurveRate`,
`convexOn_inv_shift`, `annuityRandom_pos`, `cmsStrip_weight_pos`) are
`private`.
-/

@[expose] public section

namespace MathFin.CMS

open MeasureTheory Real MathFin

/-! ### 1. The par-rate functional in the discount factor -/

/-- **The CMS curve rate**: the par swap rate of a curve whose final discount
factor is `x`, all other discount factors fixed. The floating leg is `P₀ − x`,
the annuity `δ·(C + x)` with `C` the sum of the remaining discount factors —
mirroring `MathFin.parSwapRate P₀ x (annuity δ P s)` for the curve `P` updated
at the final payment index (`parSwapRate_update_eq` below). -/
noncomputable def cmsCurveRate (P0 δ C x : ℝ) : ℝ := (P0 - x) / (δ * (C + x))

/-- The annuity of an updated curve splits into the fixed part of the schedule
plus the new factor: `annuity δ (update P n x) s = δ·(∑_{i ≠ n} P i + x)`. -/
private theorem annuity_update_eq {ι : Type*} [DecidableEq ι] (δ : ℝ) (P : ι → ℝ)
    (s : Finset ι) {n : ι} (hn : n ∈ s) (x : ℝ) :
    annuity δ (Function.update P n x) s = δ * ((∑ i ∈ s.erase n, P i) + x) := by
  have hsum : ∑ i ∈ s.erase n, Function.update P n x i + Function.update P n x n
      = ∑ i ∈ s, Function.update P n x i := Finset.sum_erase_add s _ hn
  have hrest : ∑ i ∈ s.erase n, Function.update P n x i = ∑ i ∈ s.erase n, P i :=
    Finset.sum_congr rfl fun i hi ↦ Function.update_of_ne (Finset.ne_of_mem_erase hi) x P
  show δ * ∑ i ∈ s, Function.update P n x i = δ * ((∑ i ∈ s.erase n, P i) + x)
  rw [← hsum, hrest, Function.update_self]

/-- **The bridge to the swap layer**: the par rate of the updated curve *is*
the CMS curve rate. -/
theorem parSwapRate_update_eq {ι : Type*} [DecidableEq ι] (P0 δ x : ℝ) (P : ι → ℝ)
    (s : Finset ι) {n : ι} (hn : n ∈ s) :
    parSwapRate P0 (Function.update P n x n)
        (annuity δ (Function.update P n x) s)
      = cmsCurveRate P0 δ (∑ i ∈ s.erase n, P i) x := by
  show (P0 - Function.update P n x n) / (annuity δ (Function.update P n x) s)
      = cmsCurveRate P0 δ (∑ i ∈ s.erase n, P i) x
  rw [Function.update_self, annuity_update_eq δ P s hn x]
  rfl

/-- **The par identity in curve form** — the CMS instantiation of
`payerSwapValue_eq_zero_iff`: the fixed rate zeroing the payer swap over the
updated curve is exactly the CMS curve rate. -/
theorem payerSwapValue_update_eq_zero_iff {ι : Type*} [DecidableEq ι] (P0 δ K x : ℝ)
    (P : ι → ℝ) (s : Finset ι) {n : ι} (hn : n ∈ s) (hδ : 0 < δ) (hx : 0 < x)
    (hP : ∀ i ∈ s, 0 < P i) :
    payerSwapValue P0 (Function.update P n x n) K (annuity δ (Function.update P n x) s) = 0
      ↔ K = cmsCurveRate P0 δ (∑ i ∈ s.erase n, P i) x := by
  have hup : ∀ i ∈ s, 0 < Function.update P n x i := by
    intro i hi
    by_cases hIn : i = n
    · rw [hIn, Function.update_self]; exact hx
    · rw [Function.update_of_ne hIn x P]
      exact hP i hi
  have hA := annuity_pos hδ hup (⟨n, hn⟩ : s.Nonempty)
  rw [payerSwapValue_eq_zero_iff P0 (Function.update P n x n) K hA.ne',
    parSwapRate_update_eq P0 δ x P s hn]

/-! ### 2. Derivatives and convexity of the rate functional -/

/-- Rewritten form (affine-in-inverse): with `a = P₀ + C`,
`S(x) = a/δ · (C + x)⁻¹ − 1/δ` — the one-line reason the rate is convex when
`P₀ + C ≥ 0` and has second derivative `2a/(δ(C+x)³)`. -/
private theorem cmsCurveRate_eq (P0 δ C x : ℝ) (hx : C + x ≠ 0) (hδ : δ ≠ 0) :
    cmsCurveRate P0 δ C x = (P0 + C) / δ * (C + x)⁻¹ - 1 / δ := by
  rw [cmsCurveRate]
  field_simp
  ring

/-- **First derivative**: `S'(x) = −(P₀ + C)/(δ(C + x)²)`. -/
theorem hasDerivAt_cmsCurveRate (P0 δ C x : ℝ) (hx : C + x ≠ 0) (hδ : δ ≠ 0) :
    HasDerivAt (cmsCurveRate P0 δ C) (-(P0 + C) / (δ * (C + x) ^ 2)) x := by
  have hf : HasDerivAt (fun y : ℝ ↦ P0 - y) (-1 : ℝ) x :=
    HasDerivAt.const_sub P0 (hasDerivAt_id x)
  have hd : HasDerivAt (fun y : ℝ ↦ δ * (y + C)) (δ * 1) x :=
    HasDerivAt.const_mul δ ((hasDerivAt_id x).add_const C)
  have hdx : δ * (x + C) ≠ 0 := by
    refine mul_ne_zero hδ ?_
    rw [add_comm]
    exact hx
  have hdiv : HasDerivAt (fun y : ℝ ↦ (P0 - y) / (δ * (y + C)))
      (((-1 : ℝ) * (δ * (x + C)) - (P0 - x) * (δ * 1)) / (δ * (x + C)) ^ 2) x :=
    HasDerivAt.fun_div hf hd hdx
  rw [show cmsCurveRate P0 δ C = fun y : ℝ ↦ (P0 - y) / (δ * (y + C)) from by
      funext y
      show (P0 - y) / (δ * (C + y)) = (P0 - y) / (δ * (y + C))
      rw [add_comm C y],
    show (-(P0 + C) / (δ * (C + x) ^ 2))
      = (((-1 : ℝ) * (δ * (x + C)) - (P0 - x) * (δ * 1)) / (δ * (x + C)) ^ 2) from by
      rw [div_eq_div_iff (mul_ne_zero hδ (pow_ne_zero 2 hx))
        (pow_ne_zero 2 (mul_ne_zero hδ (by rw [add_comm]; exact hx)))]
      ring]
  exact hdiv

/-- **Second derivative**: `S''(x) = 2(P₀ + C)/(δ(C + x)³)` — strictly positive
on the curve's domain whenever `P₀ + C > 0` (`cmsStrip_weight_pos`). -/
theorem hasDerivAt_cmsCurveRate' (P0 δ C t : ℝ) (ht : C + t ≠ 0) (hδ : δ ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ -(P0 + C) / (δ * (C + y) ^ 2))
      (2 * (P0 + C) / (δ * (C + t) ^ 3)) t := by
  -- work in the `(y + C)` convention, then convert at the end
  have hu : HasDerivAt (fun y : ℝ ↦ y + C) (1 : ℝ) t := (hasDerivAt_id t).add_const C
  have htc : t + C ≠ 0 := by rw [add_comm]; exact ht
  have hinv : HasDerivAt (fun y : ℝ ↦ (y + C)⁻¹) (-((t + C) ^ 2)⁻¹ * 1) t :=
    (hasDerivAt_inv htc).comp t hu
  have hpow : HasDerivAt (fun y : ℝ ↦ (y + C)⁻¹ * (y + C)⁻¹)
      (-((t + C) ^ 2)⁻¹ * 1 * (t + C)⁻¹ + (t + C)⁻¹ * (-((t + C) ^ 2)⁻¹ * 1)) t :=
    hinv.mul hinv
  have hres := hpow.const_mul (-(P0 + C) / δ)
  rw [show (fun y : ℝ ↦ (-(P0 + C) / δ) * ((y + C)⁻¹ * (y + C)⁻¹))
        = fun y : ℝ ↦ -(P0 + C) / (δ * (y + C) ^ 2) from by
          funext y; field_simp,
      show ((-(P0 + C) / δ) * (-((t + C) ^ 2)⁻¹ * 1 * (t + C)⁻¹
            + (t + C)⁻¹ * (-((t + C) ^ 2)⁻¹ * 1)))
        = 2 * (P0 + C) / (δ * (t + C) ^ 3) from by
        field_simp [mul_inv, inv_pow]
        ring,
      show (fun y : ℝ ↦ -(P0 + C) / (δ * (y + C) ^ 2))
        = fun y : ℝ ↦ -(P0 + C) / (δ * (C + y) ^ 2) from by funext y; ring,
      show (2 * (P0 + C) / (δ * (t + C) ^ 3)) = 2 * (P0 + C) / (δ * (C + t) ^ 3) from by
        rw [add_comm t C]] at hres
  exact hres

/-- Differentiability of the rate functional on the nonnegative half-line —
there the denominator stays `≥ C > 0`. -/
private theorem differentiableOn_cmsCurveRate (P0 δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    DifferentiableOn ℝ (cmsCurveRate P0 δ C) (Set.Ici 0) :=
  fun x hx ↦ ((hasDerivAt_cmsCurveRate P0 δ C x
    (ne_of_gt (show (0 : ℝ) < C + x by linarith [Set.mem_Ici.1 hx])) hδ.ne').differentiableAt).differentiableWithinAt

/-- Continuity on the nonnegative half-line — the regularity Jensen consumes. -/
private theorem continuousOn_cmsCurveRate (P0 δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ContinuousOn (cmsCurveRate P0 δ C) (Set.Ici 0) :=
  (differentiableOn_cmsCurveRate P0 δ C hδ hC).continuousOn

/-- **Convexity of the shifted inverse** `x ↦ (C + x)⁻¹` on the nonnegative
half-line — the convexity engine behind the CMS rate's convexity. The two-point
inequality `(u(C+x)+v(C+y))⁻¹ ≤ u(C+x)⁻¹ + v(C+y)⁻¹` is the AM–GM identity
`(ua+vb)(u/a+v/b) − 1 = uv(a−b)²/(ab) ≥ 0` for `a, b > 0`, `u + v = 1`. -/
private theorem convexOn_inv_shift (C : ℝ) (hC : 0 < C) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ (C + x)⁻¹) := by
  refine ⟨convex_Ici 0, fun x hx y hy u v hu hv huv ↦ ?_⟩
  show (C + (u * x + v * y))⁻¹ ≤ u * (C + x)⁻¹ + v * (C + y)⁻¹
  have hx0 : (0 : ℝ) ≤ x := Set.mem_Ici.1 hx
  have hy0 : (0 : ℝ) ≤ y := Set.mem_Ici.1 hy
  have hxa : 0 < C + x := by linarith
  have hya : 0 < C + y := by linarith
  have hxu : 0 ≤ u * x := mul_nonneg hu hx0
  have hxv : 0 ≤ v * y := mul_nonneg hv hy0
  have hcomb : C + (u * x + v * y) = u * (C + x) + v * (C + y) := by
    have hCmul : u * C + v * C = C := by linear_combination C * huv
    linarith
  rw [hcomb]
  have hA : 0 < u * (C + x) + v * (C + y) := by rw [← hcomb]; linarith
  have hkey2 : (C + x) * (C + y)
      ≤ (u * (C + x) + v * (C + y)) * (u * (C + y) + v * (C + x)) := by
    have h1 : 0 ≤ u * v * (x - y) ^ 2 := mul_nonneg (mul_nonneg hu hv) (sq_nonneg _)
    have h2 : 0 ≤ (C + x) * (C + y) * ((u + v) ^ 2 - 1) := by rw [huv]; simp
    -- certificate: RHS − LHS = uv(x−y)² + (C+x)(C+y)·((u+v)² − 1), an identity
    nlinarith [h1, h2]
  have hkey : 1 ≤ (u * (C + x)⁻¹ + v * (C + y)⁻¹) * (u * (C + x) + v * (C + y)) := by
    field_simp
    nlinarith
  -- last step: `A⁻¹ ≤ B ↔ 1 ≤ B * A`, avoiding the generic-lemma instance mismatch
  rw [inv_eq_one_div, div_le_iff₀ hA]
  exact hkey

/-- **The CMS rate is convex in the discount factor on the nonnegative
half-line**. Hypotheses are the weakest honest ones: `δ > 0` (daycount),
`C > 0` (the rate functional is defined on the whole half-line) and `P₀ + C ≥ 0`
(the convexity coefficient `S'' = 2(P₀+C)/(δ(C+x)³)` has the right sign;
economically `P₀` and every remaining discount factor are positive, so this is
free). -/
theorem cmsCurveRate_convexOn (P0 δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hPC : 0 ≤ P0 + C) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (cmsCurveRate P0 δ C) := by
  have hcoef : (0 : ℝ) ≤ (P0 + C) / δ := div_nonneg hPC hδ.le
  refine (ConvexOn.add_const ((convexOn_inv_shift C hC).smul hcoef) (-1 / δ)).congr ?_
  intro x hx
  have hxne : C + x ≠ 0 :=
    ne_of_gt (show (0 : ℝ) < C + x by linarith [Set.mem_Ici.1 hx])
  simp only [Pi.add_apply, smul_eq_mul]
  rw [cmsCurveRate_eq P0 δ C x hxne hδ.ne']
  ring

/-! ### 3. The annuity measure -/

section Annuity

variable {Ω ι : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The random annuity at the fixing date: `A_T(ω) = δ · ∑_{i ∈ s} P(ω, T_i)` —
the PVBP of the underlying swap along the curve state. -/
noncomputable def annuityRandom (δ : ℝ) (P : Ω → ι → ℝ) (s : Finset ι) : Ω → ℝ :=
  fun ω ↦ annuity δ (P ω) s

omit [MeasurableSpace Ω] in
/-- The annuity is strictly positive along every curve state with positive
discount factors. -/
private theorem annuityRandom_pos {δ : ℝ} (hδ : 0 < δ) {P : Ω → ι → ℝ} {s : Finset ι}
    (hs : s.Nonempty) (hP : ∀ ω i, i ∈ s → 0 < P ω i) (ω : Ω) :
    0 < annuityRandom δ P s ω :=
  annuity_pos hδ (fun i hi ↦ hP ω i hi) hs

/-- **The annuity measure** `Qᴬ`: the change-of-numéraire measure with the
annuity `A_T` in the numéraire seat against the money market `B_t = e^{rt}` —
an execution of `MathFin.changeOfNumeraire`, alongside the stock and the
`T`-bond (the forward measure of `FixedIncome/ForwardMeasure.lean`).
Density: `dQᴬ/dQ = A_T·e^{−rT}/A₀`. -/
noncomputable def annuityMeasure (Q : Measure Ω) (r T δ : ℝ) (P : Ω → ι → ℝ)
    (s : Finset ι) (A0 : ℝ) : Measure Ω :=
  numeraireMeasure Q (fun _ ↦ Real.exp (r * T)) (annuityRandom δ P s) 1 A0

/-- **The annuity measure is a probability measure** under the annuity-repricing
condition `𝔼^Q[e^{−rT}·A_T] = A₀` — the numéraire engine's normalization
`𝔼^Q[N_T/B_T] = N₀/B₀` read with `N = A`, `B` the money market. This hypothesis
is where the martingale content of the CMS construction enters and it is taken
explicitly (the honest out — no model-free proof exists). -/
theorem annuityMeasure_isProbabilityMeasure {Q : Measure Ω} (r T δ : ℝ)
    (P : Ω → ι → ℝ) (s : Finset ι) (A0 : ℝ) (hδ : 0 < δ) (hs : s.Nonempty)
    (hP : ∀ ω i, i ∈ s → 0 < P ω i) (hA0 : 0 < A0)
    (hint : Integrable (fun ω ↦ annuityRandom δ P s ω * Real.exp (-(r * T))) Q)
    (hrepr : ∫ ω, annuityRandom δ P s ω * Real.exp (-(r * T)) ∂Q = A0) :
    IsProbabilityMeasure (annuityMeasure Q r T δ P s A0) := by
  have hpos : ∀ ω, 0 < annuityRandom δ P s ω := fun ω ↦ annuityRandom_pos hδ hs hP ω
  have hdiv : (fun ω : Ω ↦ annuityRandom δ P s ω / Real.exp (r * T))
      = fun ω ↦ annuityRandom δ P s ω * Real.exp (-(r * T)) := by
    funext ω
    rw [Real.exp_neg]
    field_simp
  refine numeraireMeasure_isProbabilityMeasure hpos (fun ω ↦ Real.exp_pos _) one_pos hA0
    (by rw [hdiv]; exact hint) (by rw [hdiv, hrepr]; simp)

/-- **The CMS fair-value identity** — the annuity in the numéraire seat. For any
rate claim `S` paid at the fixing date,

  `A₀ · 𝔼^{Qᴬ}[S] = 𝔼^Q[e^{−rT} · S · A_T]`,

an execution of `changeOfNumeraire`. (The constant-rate schematic
`𝔼_Q[e^{−rT}S_T] = P(0,T)·𝔼^A[S_T]` is the degenerate case; the honest identity
keeps the random `A_T` on the `Q` side — and that `A_T` is exactly where the
convexity adjustment comes from.) -/
theorem annuityMeasure_price {Q : Measure Ω} (r T δ : ℝ) (P : Ω → ι → ℝ)
    (s : Finset ι) (A0 : ℝ) (S : Ω → ℝ) (hδ : 0 < δ) (hs : s.Nonempty)
    (hP : ∀ ω i, i ∈ s → 0 < P ω i) (hA0 : 0 < A0)
    (hAmeas : Measurable (annuityRandom δ P s)) :
    A0 * ∫ ω, S ω ∂(annuityMeasure Q r T δ P s A0)
      = ∫ ω, Real.exp (-(r * T)) * (S ω * annuityRandom δ P s ω) ∂Q := by
  have hpos : ∀ ω, 0 < annuityRandom δ P s ω := fun ω ↦ annuityRandom_pos hδ hs hP ω
  have h := changeOfNumeraire (Q := Q) (BT := fun _ ↦ Real.exp (r * T))
    (NT := annuityRandom δ P s) (B0 := (1 : ℝ)) (N0 := A0)
    (fun ω ↦ S ω * annuityRandom δ P s ω) hAmeas
    measurable_const hpos (fun ω ↦ Real.exp_pos _) (by norm_num) hA0
  have hcongr : ∀ ω : Ω, annuityRandom δ P s ω ≠ 0 →
      S ω * annuityRandom δ P s ω / annuityRandom δ P s ω = S ω := by
    intro ω hY
    simp [hY]
  rw [integral_congr_ae (ae_of_all _ fun ω ↦ hcongr ω (ne_of_gt (hpos ω)))] at h
  have h2 : 1 * ∫ ω, S ω * annuityRandom δ P s ω / Real.exp (r * T) ∂Q
      = ∫ ω, Real.exp (-(r * T)) * (S ω * annuityRandom δ P s ω) ∂Q := by
    rw [one_mul]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    show S ω * annuityRandom δ P s ω / Real.exp (r * T)
      = Real.exp (-(r * T)) * (S ω * annuityRandom δ P s ω)
    rw [div_eq_mul_inv, Real.exp_neg]
    ring
  rw [← h2]
  exact h

/-! ### 4. The headline: the adjustment is nonnegative -/

-- the Jensen application carries heavy higher-order unification
set_option maxHeartbeats 1000000 in
/-- **The CMS convexity-adjustment theorem** (the headline). Under the annuity
measure `Qᴬ` of the previous section, with `W` the `T`-state of the final
discount factor and `x₀` its `Qᴬ`-forward value, Jensen for the convex rate
functional gives: today's par rate `S(x₀)` lower-bounds the annuity-measure
expectation of the CMS rate. The martingale content enters through `hfwd`
(`𝔼^{Qᴬ}[W] = x₀` — the curve state is a `Qᴬ`-martingale), taken explicitly per
the honest-out rule; the integrability hypotheses `hWint`, `hSint` are the two
measurability-sized prices of running Jensen on a general measure. -/
theorem cms_adjustment_nonneg {Q : Measure Ω} (r T δ P0 C A0 x₀ : ℝ)
    (P : Ω → ι → ℝ) (s : Finset ι) (W : Ω → ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hPC : 0 ≤ P0 + C) (hs : s.Nonempty) (hP : ∀ ω i, i ∈ s → 0 < P ω i)
    (hA0 : 0 < A0)
    (hint : Integrable (fun ω ↦ annuityRandom δ P s ω * Real.exp (-(r * T))) Q)
    (hrepr : ∫ ω, annuityRandom δ P s ω * Real.exp (-(r * T)) ∂Q = A0)
    (hWpos : ∀ ω, 0 ≤ W ω)
    (hWint : Integrable W (annuityMeasure Q r T δ P s A0))
    (hSint : Integrable (fun ω ↦ cmsCurveRate P0 δ C (W ω))
      (annuityMeasure Q r T δ P s A0))
    (hfwd : ∫ ω, W ω ∂(annuityMeasure Q r T δ P s A0) = x₀) :
    cmsCurveRate P0 δ C x₀
      ≤ ∫ ω, cmsCurveRate P0 δ C (W ω) ∂(annuityMeasure Q r T δ P s A0) := by
  haveI hprob := annuityMeasure_isProbabilityMeasure r T δ P s A0 hδ hs hP hA0 hint hrepr
  have hfs : ∀ᵐ ω ∂(annuityMeasure Q r T δ P s A0), W ω ∈ Set.Ici (0 : ℝ) :=
    ae_of_all _ fun ω ↦ Set.mem_Ici.2 (hWpos ω)
  have hj := ConvexOn.map_integral_le (f := W) (g := cmsCurveRate P0 δ C)
    (s := Set.Ici (0 : ℝ)) (cmsCurveRate_convexOn P0 δ C hδ hC hPC)
    (continuousOn_cmsCurveRate P0 δ C hδ hC) isClosed_Ici hfs hWint hSint
  rwa [hfwd] at hj

/-- The adjustment itself: `𝔼^{Qᴬ}[CMS rate] − today's par rate ≥ 0`. -/
theorem cms_adjustment_delta_nonneg {Q : Measure Ω} (r T δ P0 C A0 x₀ : ℝ)
    (P : Ω → ι → ℝ) (s : Finset ι) (W : Ω → ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hPC : 0 ≤ P0 + C) (hs : s.Nonempty) (hP : ∀ ω i, i ∈ s → 0 < P ω i)
    (hA0 : 0 < A0)
    (hint : Integrable (fun ω ↦ annuityRandom δ P s ω * Real.exp (-(r * T))) Q)
    (hrepr : ∫ ω, annuityRandom δ P s ω * Real.exp (-(r * T)) ∂Q = A0)
    (hWpos : ∀ ω, 0 ≤ W ω)
    (hWint : Integrable W (annuityMeasure Q r T δ P s A0))
    (hSint : Integrable (fun ω ↦ cmsCurveRate P0 δ C (W ω))
      (annuityMeasure Q r T δ P s A0))
    (hfwd : ∫ ω, W ω ∂(annuityMeasure Q r T δ P s A0) = x₀) :
    0 ≤ ∫ ω, cmsCurveRate P0 δ C (W ω) ∂(annuityMeasure Q r T δ P s A0)
      - cmsCurveRate P0 δ C x₀ :=
  sub_nonneg.2 (cms_adjustment_nonneg r T δ P0 C A0 x₀ P s W hδ hC hPC hs hP hA0 hint
    hrepr hWpos hWint hSint hfwd)

end Annuity

/-! ### 5. The replication seed: Carr–Madan spanning of the rate functional -/

/-- The CMS strip weight `S''(K) = 2(P₀+C)/(δ(C+K)³)` is strictly positive on
the rate functional's domain — the replication face of the convexity. -/
private theorem cmsStrip_weight_pos (P0 δ C K : ℝ) (hδ : 0 < δ) (hPC : 0 < P0 + C)
    (hK : 0 < C + K) : 0 < 2 * (P0 + C) / (δ * (C + K) ^ 3) :=
  div_pos (mul_pos two_pos hPC) (mul_pos hδ (pow_pos hK 3))

-- the Carr–Madan instantiation carries heavy higher-order unification
set_option maxHeartbeats 1000000 in
/-- **The replication seed**: the CMS rate functional spanned as cash + forward
+ static OTM option strips on the discount factor (Carr–Madan, compact strike
range `[L, U]` with `L > −C`). The strip weights are the strictly positive
`S''` (`cmsStrip_weight_pos`) — the static-replication form of the convexity
adjustment. The swap-rate functional is not a log payoff, so this consumes
`carrMadan_spanning`, the shared core of which `carrMadan_log_spanning` is the
log instance. The unbounded-window limit (tail analysis) is outside the present
scope. -/
theorem cmsCurveRate_spanning (P0 δ C : ℝ) (hδ : 0 < δ)
    {L U κ S : ℝ} (hL : -C < L) (hLκ : L ≤ κ) (hκU : κ ≤ U) (hS : S ∈ Set.Icc L U) :
    cmsCurveRate P0 δ C S = cmsCurveRate P0 δ C κ
      + (-(P0 + C) / (δ * (C + κ) ^ 2)) * (S - κ)
      + (∫ K in L..κ, (2 * (P0 + C) / (δ * (C + K) ^ 3)) * max (K - S) 0)
      + (∫ K in κ..U, (2 * (P0 + C) / (δ * (C + K) ^ 3)) * max (S - K) 0) := by
  have hCK : ∀ K ∈ Set.Icc L U, 0 < C + K := by
    intro K hK
    have h1 : -C < K := by have := hK.1; linarith
    linarith
  exact carrMadan_spanning (f := cmsCurveRate P0 δ C)
    (f' := fun t ↦ -(P0 + C) / (δ * (C + t) ^ 2))
    (f'' := fun K ↦ 2 * (P0 + C) / (δ * (C + K) ^ 3)) hLκ hκU hS
    (fun t ht ↦ hasDerivAt_cmsCurveRate P0 δ C t (ne_of_gt (hCK t ht)) hδ.ne')
    (fun t ht ↦ hasDerivAt_cmsCurveRate' P0 δ C t (ne_of_gt (hCK t ht)) hδ.ne')
    (show ContinuousOn (fun K : ℝ ↦ 2 * (P0 + C) / (δ * (C + K) ^ 3)) (Set.Icc L U) from
      ContinuousOn.div continuousOn_const
        (show ContinuousOn (fun K : ℝ ↦ δ * (C + K) ^ 3) (Set.Icc L U) from
          (Continuous.mul continuous_const
            ((continuous_const.add continuous_id).pow 3)).continuousOn)
        fun K hK ↦ mul_ne_zero hδ.ne' (pow_ne_zero 3 (ne_of_gt (hCK K hK))))

/-- **The model-free pointwise adjustment**: the CMS rate dominates its
first-order expansion around the reference point, and the excess is exactly the
option strips — nonnegative because `S'' ≥ 0` (from `P₀ + C ≥ 0`). -/
theorem cmsCurveRate_strip_nonneg (P0 δ C : ℝ) (hδ : 0 < δ) (hPC : 0 ≤ P0 + C)
    {L U κ S : ℝ} (hL : -C < L) (hLκ : L ≤ κ) (hκU : κ ≤ U) (hS : S ∈ Set.Icc L U) :
    0 ≤ cmsCurveRate P0 δ C S - cmsCurveRate P0 δ C κ
        - (-(P0 + C) / (δ * (C + κ) ^ 2)) * (S - κ) := by
  have hspan := cmsCurveRate_spanning P0 δ C hδ hL hLκ hκU hS
  have hCKpos : ∀ K ∈ Set.Icc L U, 0 < C + K := by
    intro K hK
    have h1 : -C < K := by have := hK.1; linarith
    linarith
  have hput : 0 ≤ ∫ K in L..κ, (2 * (P0 + C) / (δ * (C + K) ^ 3)) * max (K - S) 0 :=
    intervalIntegral.integral_nonneg hLκ fun K hK ↦
      mul_nonneg
        (div_nonneg (mul_nonneg two_pos.le hPC)
          (mul_nonneg hδ.le (pow_nonneg (le_of_lt (hCKpos K
            ⟨hK.1, hK.2.trans hκU⟩)) 3)))
        (le_max_right (K - S) (0 : ℝ))
  have hcall : 0 ≤ ∫ K in κ..U, (2 * (P0 + C) / (δ * (C + K) ^ 3)) * max (S - K) 0 :=
    intervalIntegral.integral_nonneg hκU fun K hK ↦
      mul_nonneg
        (div_nonneg (mul_nonneg two_pos.le hPC)
          (mul_nonneg hδ.le (pow_nonneg (le_of_lt (hCKpos K
            ⟨hLκ.trans hK.1, hK.2⟩)) 3)))
        (le_max_right (S - K) (0 : ℝ))
  linarith

/-! ### 6. The convexity tie-in: the bond's second-order weight -/

/-- **The bond convexity is nonnegative**: each cashflow contributes
`t_i(t_i+1)·c_i/(1+y)^{t_i+2} ≥ 0` for `y > −100%` and nonnegative coupons.
This is the sign of the `P''` exhibited by
`bondPriceDisc_secondDeriv_eq_convexity_times_price` — the quantity that
weights the CMS adjustment's second-order term. -/
theorem convexityNumerator_nonneg {ι : Type*} (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ)
    {y : ℝ} (hy : 0 < 1 + y) (hc : ∀ i ∈ s, 0 ≤ c i) :
    0 ≤ convexityNumerator s t c y := by
  refine Finset.sum_nonneg fun i hi ↦ ?_
  exact div_nonneg
    (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (t i : ℝ) from Nat.cast_nonneg (α := ℝ) (t i))
      (by linarith [Nat.cast_nonneg (α := ℝ) (t i)])) (hc i hi))
    (pow_nonneg hy.le (t i + 2))

end MathFin.CMS
