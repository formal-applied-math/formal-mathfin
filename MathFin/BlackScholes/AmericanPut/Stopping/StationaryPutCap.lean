/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.UpperSupportComparison

/-! # A stationary payoff-matching upper barrier

This is a supersolution, not an asserted perpetual option price. Its exponential
branch is tangent to the payoff at `d` and is an upper support even at the join.

## Result

Public entry points include `stationaryPutTail`, `stationaryPutCap`, `stationaryPutTail_at_join`,
`stationaryPutCap_continuous`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter Boundary
open scoped Topology ContDiff

/-- The exponential branch `(1-exp d) * exp (-m*(x-d))`, taking the value `1-exp d` at `x = d`. -/
noncomputable def stationaryPutTail (m d x : ℝ) : ℝ :=
  (1-Real.exp d)*Real.exp (-m*(x-d))

/-- The intrinsic value `1-exp x` below the join `d`, and `stationaryPutTail m d` above it. -/
noncomputable def stationaryPutCap (m d x : ℝ) : ℝ :=
  if x ≤ d then 1-Real.exp x else stationaryPutTail m d x

theorem stationaryPutTail_at_join (m d : ℝ) : stationaryPutTail m d d = 1-Real.exp d := by
  simp [stationaryPutTail]

theorem stationaryPutCap_continuous (m d : ℝ) : Continuous (stationaryPutCap m d) := by
  unfold stationaryPutCap
  apply Continuous.if_le (by fun_prop) (by unfold stationaryPutTail; fun_prop)
    continuous_id continuous_const
  intro x hx
  change x = d at hx
  simpa only [hx] using (stationaryPutTail_at_join m d).symm

theorem stationaryPutTail_ge_intrinsic {m d : ℝ} (hm : 0 < m)
    (hd : Real.exp d = m / (1 + m)) (x : ℝ) : 1-Real.exp x ≤ stationaryPutTail m d x := by
  have hd0 : 0 < 1+m := by linarith
  have hdx : Real.exp x = Real.exp d * Real.exp (x-d) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he1 := Real.add_one_le_exp (-m*(x-d))
  have he2 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x-d)) hm.le
  unfold stationaryPutTail
  rw [hdx,hd]
  apply (mul_le_mul_iff_left₀ hd0).mp
  field_simp
  simp only [neg_mul] at he1
  nlinarith

theorem stationaryPutTail_nonneg {m d : ℝ} (hd : d < 0) (x : ℝ) :
    0 ≤ stationaryPutTail m d x := by
  exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr hd.le)) (Real.exp_pos _).le

theorem stationaryPutCap_ge_payoff {m d : ℝ} (hm : 0 < m) (hd0 : d < 0)
    (hd : Real.exp d = m / (1 + m)) (x : ℝ) : putPayoff x ≤ stationaryPutCap m d x := by
  unfold stationaryPutCap putPayoff
  split_ifs with hx
  · rw [max_eq_left (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (hx.trans hd0.le)))]
  · exact max_le (stationaryPutTail_ge_intrinsic hm hd x) (stationaryPutTail_nonneg hd0 x)

theorem stationaryPutCap_nonneg {m d : ℝ} (hm : 0 < m) (hd0 : d < 0)
    (hd : Real.exp d = m / (1 + m)) (x : ℝ) : 0 ≤ stationaryPutCap m d x :=
  (le_max_right _ _).trans (stationaryPutCap_ge_payoff hm hd0 hd x)

theorem stationaryPutCap_le_tail {m d : ℝ} (hm : 0 < m)
    (hd : Real.exp d = m / (1 + m)) (x : ℝ) : stationaryPutCap m d x ≤ stationaryPutTail m d x := by
  unfold stationaryPutCap
  split_ifs
  · exact stationaryPutTail_ge_intrinsic hm hd x
  · rfl

theorem stationaryPutTail_hasDeriv (m d x : ℝ) :
    HasDerivAt (stationaryPutTail m d) (-m*stationaryPutTail m d x) x := by
  unfold stationaryPutTail
  convert! ((((hasDerivAt_id x).sub_const d).const_mul (-m)).exp.const_mul (1-Real.exp d)) using 1
  simp only [id_eq]
  ring

theorem stationaryPutTail_pricingOperator (m d k h : ℝ) (z : ℝ × ℝ) :
    pricingOperator k h (fun w => stationaryPutTail m d w.1) z =
      (k+(k-h-1)*m-m^2)*stationaryPutTail m d z.1 := by
  have hd : deriv (stationaryPutTail m d) = fun x => -m*stationaryPutTail m d x :=
    funext fun x => (stationaryPutTail_hasDeriv m d x).deriv
  unfold pricingOperator
  dsimp only
  rw [deriv_const,hd,deriv_const_mul_field,hd]
  ring

theorem intrinsic_pricingOperator (k h : ℝ) (z : ℝ × ℝ) :
    pricingOperator k h (fun w => 1-Real.exp w.1) z = k-h*Real.exp z.1 := by
  unfold pricingOperator
  simp only [deriv_const,deriv_const_sub',Real.deriv_exp,deriv.fun_neg']
  ring

theorem pricingOperator_add_constant (F : ℝ × ℝ → ℝ) (k h ε : ℝ) (z : ℝ × ℝ) :
    pricingOperator k h (fun w => F w+ε) z = pricingOperator k h F z+k*ε := by
  unfold pricingOperator
  simp only [deriv_add_const']
  ring

theorem stationaryPutCap_upper_support {k h m d : ℝ} (hk : 0 ≤ k)
    (hh : 0 ≤ h) (hhk : h ≤ k) (hm : 0 < m) (hd0 : d < 0)
    (hd : Real.exp d = m / (1 + m)) (hmQ : 0 ≤ k + (k - h-1) * m-m^2)
    {ε : ℝ} (hε : 0 ≤ ε) (z : ℝ × ℝ) :
    ∃ F : ℝ × ℝ → ℝ, ContDiffAt ℝ 2 F z ∧ F z = stationaryPutCap m d z.1+ε ∧
      (∀ᶠ w in 𝓝 z, stationaryPutCap m d w.1+ε ≤ F w) ∧
        0 ≤ pricingOperator k h F z := by
  by_cases hx : z.1 < d
  · refine ⟨fun w => (1-Real.exp w.1)+ε,by fun_prop,?_,?_,?_⟩
    · simp only [stationaryPutCap,if_pos hx.le]
    · filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hx] with w hw
      simp only [stationaryPutCap,if_pos (show w.1 ≤ d from hw.le),le_refl]
    · rw [pricingOperator_add_constant,intrinsic_pricingOperator]
      have he : Real.exp z.1 ≤ 1 := Real.exp_le_one_iff.mpr (hx.trans hd0).le
      have hhx := mul_le_mul_of_nonneg_left he hh
      nlinarith [mul_nonneg hk hε]
  · refine ⟨fun w => stationaryPutTail m d w.1+ε,?_,?_,?_,?_⟩
    · unfold stationaryPutTail
      fun_prop
    · by_cases he : z.1 = d
      · simp only [stationaryPutCap,he,le_refl,ite_true,stationaryPutTail_at_join]
      · simp only
          [stationaryPutCap,if_neg (not_le.mpr (lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm he)))]
    · exact Filter.Eventually.of_forall (fun w => by
        dsimp only
        linarith [stationaryPutCap_le_tail hm hd w.1])
    · rw [pricingOperator_add_constant,stationaryPutTail_pricingOperator]
      exact add_nonneg (mul_nonneg hmQ (stationaryPutTail_nonneg hd0 z.1)) (mul_nonneg hk hε)

/-- A small positive exponential slope always gives a supersolution. -/
theorem exists_stationaryPutCap_parameters {k h : ℝ} (hk : 0 < k) :
    ∃ m d : ℝ, 0 < m ∧ d < 0 ∧ Real.exp d = m/(1+m) ∧
      0 ≤ k+(k-h-1)*m-m^2 := by
  let A := |k-h-1|+1
  have hA : 0 < A := by dsimp [A]; positivity
  let m := min 1 (k/(2*A))
  have hm : 0 < m := lt_min (by norm_num) (div_pos hk (by positivity))
  have hm1 : m ≤ 1 := min_le_left _ _
  have hm2 : m ≤ k/(2*A) := min_le_right _ _
  have hmk : m*(2*A) ≤ k := (le_div_iff₀ (by positivity : 0 < 2*A)).mp hm2
  have hα : -|k-h-1| ≤ k-h-1 := neg_abs_le _
  have hprod := mul_le_mul_of_nonneg_right hα hm.le
  have hQ : 0 ≤ k+(k-h-1)*m-m^2 := by
    dsimp [A] at hmk
    nlinarith [sq_nonneg m,mul_nonneg hm.le (sub_nonneg.mpr hm1)]
  have hratio : 0 < m/(1+m) := div_pos hm (by linarith)
  have hratio1 : m/(1+m) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  exact ⟨m,Real.log (m/(1+m)),hm,Real.log_neg hratio hratio1,Real.exp_log hratio,hQ⟩

end MathFin.BlackScholes.AmericanPut.Stopping
