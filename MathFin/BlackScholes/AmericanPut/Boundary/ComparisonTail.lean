/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.GaugeTransform

/-!
# Uniform right-hand control of the comparison difference

Explicit exponential bounds imply convergence to -1 uniformly for ALL `t>=0`
when `c>0` and `d<=0`. No decay rate for the American price is assumed: its
elementary bounds `0<=p<=1` suffice.

## Result

Public entry points include `rootProfile_exp_lower`, `rootProfile_exp_upper`, `leadingWeight`,
`leadingWeight_pos`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.Comparison

open Filter
open scoped Topology

theorem rootProfile_exp_lower {u v : ℝ} (hu : 0 < u) (hv : v < 0) (z : ℝ) :
    (-v / (u - v)) * Real.exp (u * z) ≤ rootProfile u v z := by
  have heq : rootProfile u v z = (u / (u - v)) * Real.exp (v * z) +
      (-v / (u - v)) * Real.exp (u * z) := by unfold rootProfile; ring
  rw [heq]
  have huv : 0 < u - v := by linarith
  have hn : 0 ≤ (u / (u - v)) * Real.exp (v * z) := by positivity
  linarith

theorem rootProfile_exp_upper {u v z : ℝ} (hu : 0 < u) (hv : v < 0) (hz : 0 ≤ z) :
    rootProfile u v z ≤ Real.exp (u * z) := by
  have huv : 0 < u - v := by linarith
  have he : Real.exp (v * z) ≤ Real.exp (u * z) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hz)
  unfold rootProfile
  apply (div_le_iff₀ huv).mpr
  nlinarith [mul_le_mul_of_nonneg_left he hu.le]

/-- The coefficient of the growing exponential in a positive-rate profile. -/
noncomputable def leadingWeight (β ρ : ℝ) : ℝ :=
  -negativeRoot β ρ / (positiveRoot β ρ - negativeRoot β ρ)

theorem leadingWeight_pos {β ρ : ℝ} (hρ : 0 < ρ) : 0 < leadingWeight β ρ := by
  obtain ⟨hu, hv⟩ := roots_signs (β := β) hρ
  unfold leadingWeight
  exact div_pos (neg_pos.mpr hv) (by linarith)

theorem profile_exp_lower {β ρ : ℝ} (hρ : 0 < ρ) (z : ℝ) :
    leadingWeight β ρ * Real.exp (positiveRoot β ρ * z) ≤ profile β ρ z := by
  obtain ⟨hu, hv⟩ := roots_signs (β := β) hρ
  simpa only [profile, hρ.ne', ↓reduceIte, leadingWeight] using rootProfile_exp_lower hu hv z

/-- The zero-rate profile is constant, even if its characteristic polynomial
has another positive root. Its actual growth exponent is therefore zero. -/
noncomputable def growthRate (β ρ : ℝ) : ℝ := if ρ = 0 then 0 else positiveRoot β ρ

theorem growthRate_nonneg {β ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ growthRate β ρ := by
  by_cases hz : ρ = 0
  · simp [growthRate, hz]
  · simpa only [growthRate, hz, ↓reduceIte] using
      (roots_signs (β := β) (lt_of_le_of_ne hρ (Ne.symm hz))).1.le

theorem growthRate_equation {β ρ : ℝ} (hρ : 0 ≤ ρ) :
    growthRate β ρ ^ 2 + β * growthRate β ρ - ρ = 0 := by
  by_cases hz : ρ = 0
  · simp [growthRate, hz]
  · simpa only [growthRate, hz, ↓reduceIte] using (roots_equations (β := β) hρ).1

theorem profile_exp_upper {β ρ z : ℝ} (hρ : 0 ≤ ρ) (hz : 0 ≤ z) :
    profile β ρ z ≤ Real.exp (growthRate β ρ * z) := by
  by_cases hr : ρ = 0
  · simp [profile, growthRate, hr]
  · obtain ⟨hu, hv⟩ := roots_signs (β := β) (lt_of_le_of_ne hρ (Ne.symm hr))
    simpa only [profile, growthRate, hr, ↓reduceIte] using rootProfile_exp_upper hu hv hz

/-- A purely pointwise tail estimate. The only price input is `0<=p(x,t)<=1`;
the remaining hypotheses describe the explicit exponential profiles. -/
theorem normalizedDifference_exp_bound {p : ℝ → ℝ → ℝ} {f g : ℝ → ℝ}
    {A lam μ c d x t : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hgap : μ + 1 < lam)
    (hf : ∀ z, A * Real.exp (lam * z) ≤ f z)
    (hg0 : ∀ z, 0 ≤ g z) (hg : ∀ z, 0 ≤ z → g z ≤ Real.exp (μ * z))
    (hc : 0 ≤ c) (hd : d ≤ 0) (hx : 0 ≤ x) (ht : 0 ≤ t)
    (hp0 : 0 ≤ p x t) (hp1 : p x t ≤ 1) :
    |normalizedDifference p f g c d x t + 1| ≤
      A⁻¹ * (Real.exp (-lam * x) + Real.exp (-(lam - μ - 1) * x)) := by
  let z := x + c * t - d
  have hxz : x ≤ z := by dsimp [z]; nlinarith [mul_nonneg hc ht]
  have hz : 0 ≤ z := hx.trans hxz
  have hAz : 0 < A * Real.exp (lam * z) := mul_pos hA (Real.exp_pos _)
  have hfpos : 0 < f z := hAz.trans_le (hf z)
  have hfx : A * Real.exp (lam * x) ≤ f z :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hxz hlam.le)) hA.le).trans (hf z)
  have hfirst : p x t / f z ≤ A⁻¹ * Real.exp (-lam * x) := by
    calc
      p x t / f z ≤ 1 / f z := div_le_div_of_nonneg_right hp1 hfpos.le
      _ ≤ 1 / (A * Real.exp (lam * x)) :=
        div_le_div_of_nonneg_left zero_le_one (mul_pos hA (Real.exp_pos _)) hfx
      _ = A⁻¹ * Real.exp (-lam * x) := by rw [neg_mul, Real.exp_neg]; field_simp
  have hsecond : Real.exp x * g z / f z ≤ A⁻¹ * Real.exp (-(lam - μ - 1) * x) := by
    calc
      Real.exp x * g z / f z ≤ Real.exp x * Real.exp (μ * z) / f z :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hg z hz)
          (Real.exp_pos _).le) hfpos.le
      _ ≤ Real.exp x * Real.exp (μ * z) / (A * Real.exp (lam * z)) :=
        div_le_div_of_nonneg_left (by positivity) hAz (hf z)
      _ = A⁻¹ * Real.exp (x + (μ - lam) * z) := by
        rw [show x + (μ - lam) * z = x + μ * z - lam * z by ring, Real.exp_sub, Real.exp_add]
        field_simp
      _ ≤ A⁻¹ * Real.exp (-(lam - μ - 1) * x) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hA.le)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonpos_of_nonpos_of_nonneg (show μ - lam ≤ 0 by linarith)
          (sub_nonneg.mpr hxz)]
  have heq : normalizedDifference p f g c d x t + 1 =
      p x t / f z + Real.exp x * g z / f z := by
    change (p x t - (f z - Real.exp x * g z)) / f z + 1 = _
    field_simp [hfpos.ne']
    ring
  rw [heq, abs_of_nonneg (add_nonneg (div_nonneg hp0 hfpos.le)
    (div_nonneg (mul_nonneg (Real.exp_pos _).le (hg0 z)) hfpos.le))]
  nlinarith

/-- The normalized difference for the fully explicit comparison. -/
noncomputable def straightDifference (p : ℝ → ℝ → ℝ) (k h c d : ℝ) : ℝ → ℝ → ℝ :=
  normalizedDifference p (profile (k - h - 1 - c) k)
    (profile (k - h - 1 + 2 - c) h) c d

theorem straightDifference_tail_estimate {k h c d : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k h p b) (hc : 0 < c) (hd : d ≤ 0) :
    ∃ C lam δ : ℝ, 0 < C ∧ 0 < lam ∧ 0 < δ ∧
      ∀ x, 0 ≤ x → ∀ t, 0 ≤ t →
        |straightDifference p k h c d x t + 1| ≤
          C * (Real.exp (-lam * x) + Real.exp (-δ * x)) := by
  let lam := positiveRoot (k - h - 1 - c) k
  let μ := growthRate (k - h - 1 + 2 - c) h
  let A := leadingWeight (k - h - 1 - c) k
  have hlam : 0 < lam := (roots_signs (β := k - h - 1 - c) hp.rate_pos).1
  have hA : 0 < A := leadingWeight_pos hp.rate_pos
  have hgap : μ + 1 < lam := positive_root_gap rfl hp.rate_pos hc
    (growthRate_nonneg hp.dividend_nonneg) (growthRate_equation hp.dividend_nonneg)
  refine ⟨A⁻¹, lam, lam - μ - 1, inv_pos.mpr hA, hlam, by linarith, ?_⟩
  intro x hx t ht
  exact normalizedDifference_exp_bound hA hlam hgap (profile_exp_lower hp.rate_pos)
    (fun z => (profile_data hp.dividend_nonneg).pos z |>.le)
    (fun _ hz => profile_exp_upper hp.dividend_nonneg hz) hc.le hd hx ht
    ((putPayoff_nonneg x).trans (hp.dominates x t ht)) (hp.bounded x t ht)

/-- Uniform-in-time version of (17), expressed without an interchange of limits. -/
theorem straightDifference_uniform_tail {k h c d : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k h p b) (hc : 0 < c) (hd : d ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 0 < X ∧ ∀ x, X ≤ x → ∀ t, 0 ≤ t →
      |straightDifference p k h c d x t + 1| < ε := by
  obtain ⟨C, lam, δ, _, hlam, hδ, hbound⟩ := straightDifference_tail_estimate hp hc hd
  have hL : Tendsto (fun x : ℝ => Real.exp (-lam * x)) atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_mul, id_eq] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hlam)
  have hD : Tendsto (fun x : ℝ => Real.exp (-δ * x)) atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_mul, id_eq] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hδ)
  have hT : Tendsto (fun x : ℝ => C * (Real.exp (-lam * x) + Real.exp (-δ * x)))
      atTop (nhds 0) := by simpa using (hL.add hD).const_mul C
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hT.eventually (Iio_mem_nhds hε))
  refine ⟨max 1 X, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx t ht
  have hx0 : 0 ≤ x := (zero_le_one.trans (le_max_left _ _)).trans hx
  exact (hbound x hx0 t ht).trans_lt (hX x ((le_max_right _ _).trans hx))

/-- A single positive right endpoint works for every nonnegative time, even
before any epsilon shift is applied. -/
theorem straightDifference_right_negative {k h c d : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k h p b) (hc : 0 < c) (hd : d ≤ 0) :
    ∃ X : ℝ, 0 < X ∧ ∀ x, X ≤ x → ∀ t, 0 ≤ t → straightDifference p k h c d x t < 0 := by
  obtain ⟨X, hX, htail⟩ :=
      straightDifference_uniform_tail hp hc hd (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨X, hX, ?_⟩
  intro x hx t ht
  have hb := (abs_lt.mp (htail x hx t ht)).2
  linarith

/-- At zero dividends, `straightDifference_uniform_tail` with the constant second
profile `1`. This is tail control, not a curvature theorem. -/
theorem zeroDividend_uniform_tail {k c d : ℝ} {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k 0 p b) (hc : 0 < c) (hd : d ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, 0 < X ∧ ∀ x, X ≤ x → ∀ t, 0 ≤ t →
      |normalizedDifference p (profile (k - 1 - c) k) (fun _ => 1) c d x t + 1| < ε := by
  simpa only [straightDifference, sub_zero, profile, ↓reduceIte] using
    straightDifference_uniform_tail hp hc hd hε

end MathFin.BlackScholes.AmericanPut.Boundary.Comparison
