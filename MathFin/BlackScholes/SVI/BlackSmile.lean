/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.SVI.Derivatives
public import MathFin.Foundations.GaussianCDFDeriv

/-! # The Black call with an SVI smile

Part of the SVI polynomial-sign certificate (#174).

The forward-normalised Black call as a function of log-strike and of strike, with total variance
given by raw SVI, and the derivatives of its `d₊`, `d₋` terms and of its delta
(`blackDelta_hasDerivAt`).
-/

@[expose] public section

namespace MathFin
namespace SVI
open Real ProbabilityTheory

/-- The square root `√w(k)` of the SVI total variance. -/
noncomputable def rootVariance (p : Params) (k : ℝ) : ℝ := Real.sqrt (variance p k)
/-- The Black term `d₊ = −k/√w + √w/2` at log-strike `k`. -/
noncomputable def blackPlus (p : Params) (k : ℝ) : ℝ := -k / rootVariance p k + rootVariance p k / 2
/-- The Black term `d₋ = −k/√w − √w/2` at log-strike `k`. -/
noncomputable def blackMinus (p : Params) (k : ℝ) : ℝ := -k / rootVariance p k - rootVariance p k / 2
/-- The explicit derivative of `blackMinus` in log-strike (`blackMinus_hasDerivAt`). -/
noncomputable def blackMinusSlope (p : Params) (k : ℝ) : ℝ :=
  -1 / rootVariance p k + k*slope p k / (2*(rootVariance p k)^3) - slope p k / (4*rootVariance p k)

/-- Forward-normalized Black call, as a function of log strike. -/
noncomputable def logBlackCall (p : Params) (k : ℝ) : ℝ :=
  MathFin.Phi (blackPlus p k) - Real.exp k * MathFin.Phi (blackMinus p k)

/-- The explicit derivative of `logBlackCall` in log-strike, divided by `eᵏ`: the smile term minus `Φ(d₋)`. -/
noncomputable def blackDelta (p : Params) (k : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (blackMinus p k) * slope p k / (2*rootVariance p k) -
    MathFin.Phi (blackMinus p k)

/-- Forward-normalized Black call, as a function of positive strike ratio. -/
noncomputable def blackCall (p : Params) (K : ℝ) : ℝ := logBlackCall p (Real.log K)

theorem rootVariance_pos (p : Params) (k : ℝ) (hw : 0 < variance p k) :
    0 < rootVariance p k := Real.sqrt_pos.mpr hw

theorem rootVariance_sq (p : Params) (k : ℝ) (hw : 0 ≤ variance p k) :
    (rootVariance p k)^2 = variance p k := Real.sq_sqrt hw

theorem rootVariance_hasDerivAt (p : Params) (hs : 0 < p.sigma) (k : ℝ)
    (hw : 0 < variance p k) :
    HasDerivAt (rootVariance p) (slope p k / (2*rootVariance p k)) k :=
  (variance_hasDerivAt p hs k).sqrt (ne_of_gt hw)

theorem blackMinus_hasDerivAt (p : Params) (hs : 0 < p.sigma) (k : ℝ)
    (hw : 0 < variance p k) :
    HasDerivAt (blackMinus p) (blackMinusSlope p k) k := by
  have hr := rootVariance_hasDerivAt p hs k hw
  have hn := ne_of_gt (rootVariance_pos p k hw)
  have h := (((hasDerivAt_id k).neg).div hr hn).sub (hr.div_const 2)
  convert h using 1 <;> try rfl
  dsimp [blackMinusSlope]
  field_simp
  ring

theorem blackPlus_hasDerivAt (p : Params) (hs : 0 < p.sigma) (k : ℝ)
    (hw : 0 < variance p k) :
    HasDerivAt (blackPlus p)
      (blackMinusSlope p k + slope p k / (2*rootVariance p k)) k := by
  have h := (blackMinus_hasDerivAt p hs k hw).add (rootVariance_hasDerivAt p hs k hw)
  convert h using 1 <;> try rfl
  funext x
  dsimp [blackPlus, blackMinus]
  ring

/-- The Gaussian density cancellation underlying Black's strike derivatives. -/
theorem black_density_identity (p : Params) (k : ℝ) (hw : 0 < variance p k) :
    gaussianPDFReal 0 1 (blackPlus p k) =
      Real.exp k * gaussianPDFReal 0 1 (blackMinus p k) := by
  have hn := ne_of_gt (rootVariance_pos p k hw)
  have he : -(blackPlus p k)^2 / 2 = k + (-(blackMinus p k)^2 / 2) := by
    dsimp [blackPlus, blackMinus]
    field_simp
    ring
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [he, Real.exp_add]
  ring

theorem logBlackCall_hasDerivAt (p : Params) (hs : 0 < p.sigma) (k : ℝ)
    (hw : 0 < variance p k) :
    HasDerivAt (logBlackCall p) (Real.exp k * blackDelta p k) k := by
  have hp := (MathFin.hasDerivAt_Phi (blackPlus p k)).comp k (blackPlus_hasDerivAt p hs k hw)
  have hm := (MathFin.hasDerivAt_Phi (blackMinus p k)).comp k (blackMinus_hasDerivAt p hs k hw)
  have h := hp.sub ((Real.hasDerivAt_exp k).mul hm)
  convert h using 1 <;> try rfl
  rw [black_density_identity p k hw]
  dsimp [blackDelta]
  ring

/-- The derivative of the strike delta is the positive Gaussian factor times
Durrleman's expression. -/
theorem blackDelta_hasDerivAt (p : Params) (hs : 0 < p.sigma) (k : ℝ)
    (hw : 0 < variance p k) :
    HasDerivAt (blackDelta p)
      (gaussianPDFReal 0 1 (blackMinus p k) / rootVariance p k * durrleman p k) k := by
  have hm := blackMinus_hasDerivAt p hs k hw
  have hp := (MathFin.hasDerivAt_gaussianPDFReal_zero_one (blackMinus p k)).comp k hm
  have hc := (MathFin.hasDerivAt_Phi (blackMinus p k)).comp k hm
  have hr := rootVariance_hasDerivAt p hs k hw
  have hn := ne_of_gt (rootVariance_pos p k hw)
  have h := ((hp.mul (slope_hasDerivAt p hs k)).div (hr.const_mul 2)
    (mul_ne_zero (by norm_num) hn)).sub hc
  convert h using 1 <;> try rfl
  dsimp [durrleman, blackMinusSlope, blackMinus]
  rw [← rootVariance_sq p k hw.le]
  field_simp
  ring

end SVI
end MathFin
