/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin, Raphael Coelho
-/
module

public import MathFin.BlackScholes.ForwardSmile
public import MathFin.BlackScholes.SVI.Derivatives
public import MathFin.Foundations.GaussianCDFDeriv

/-! # The Black call with an SVI smile

Part of the SVI polynomial-sign certificate (#174).

The forward-normalised Black call as a function of log-strike and of strike, with total variance
given by raw SVI, and the derivatives of its `d₊`, `d₋` terms and of its delta
(`blackDelta_hasDerivAt`).

The Black terms are the abstract-variance ones of `BlackScholes/ForwardSmile.lean` at the SVI total
variance `w(k)`: `blackPlus p k = dpl k (w k)` (`blackPlus_eq_dpl`), `blackMinus` is `dmi`
(`blackMinus_eq_dmi`) and `logBlackCall` is `blackForm` (`logBlackCall_eq_blackForm`). The Gaussian
density cancellation `black_density_identity` is `exp_mul_pdf_dmi` at `w(k)`.
`durrleman_eq_one_add_smileDelta` relates Durrleman's function to the denominator deformation
`1 + smileDelta` of Dupire's ratio.
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
noncomputable def blackMinus (p : Params) (k : ℝ) : ℝ := -k / rootVariance p k -
    rootVariance p k / 2
/-- The SVI Black term `d₊` is `ForwardSmile.dpl` at the SVI total variance. -/
theorem blackPlus_eq_dpl (p : Params) (k : ℝ) : blackPlus p k = ForwardSmile.dpl k (variance p k) :=
  (ForwardSmile.dpl_eq k _).symm

/-- The SVI Black term `d₋` is `ForwardSmile.dmi` at the SVI total variance. -/
theorem blackMinus_eq_dmi (p : Params) (k : ℝ) : blackMinus p k = ForwardSmile.dmi k (variance p k) :=
  (ForwardSmile.dmi_eq k _).symm

/-- The explicit derivative of `blackMinus` in log-strike (`blackMinus_hasDerivAt`). -/
noncomputable def blackMinusSlope (p : Params) (k : ℝ) : ℝ :=
  -1 / rootVariance p k + k*slope p k / (2*(rootVariance p k)^3) - slope p k / (4*rootVariance p k)

/-- Forward-normalized Black call, as a function of log strike. -/
noncomputable def logBlackCall (p : Params) (k : ℝ) : ℝ :=
  MathFin.Phi (blackPlus p k) - Real.exp k * MathFin.Phi (blackMinus p k)

/-- The SVI Black call is `ForwardSmile.blackForm` at the SVI total variance. -/
theorem logBlackCall_eq_blackForm (p : Params) (k : ℝ) :
    logBlackCall p k = ForwardSmile.blackForm k (variance p k) := by
  rw [logBlackCall, ForwardSmile.blackForm, blackPlus_eq_dpl, blackMinus_eq_dmi]

/-- The explicit derivative of `logBlackCall` in log-strike, divided by `eᵏ`: the smile term minus
`Φ(d₋)`. -/
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
  rw [blackPlus_eq_dpl, blackMinus_eq_dmi]
  exact (ForwardSmile.exp_mul_pdf_dmi hw).symm

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

/-- **`1 + smileDelta` is Durrleman's function.** The denominator deformation `1 + δ` of Dupire's
ratio on the tilted surface (`smileDelta`) has the algebraic form of Durrleman's `g`: at a log-strike
where the SVI slice and the tilted surface have the same total variance, slope and curvature
(`w'' = 2(εψ₁/√(T+T₀))²T`, the surface's constant `∂_kk w`), with the variance nonzero,
`durrleman p k = 1 + smileDelta σ ψ₁ T₀ ε k T`. -/
theorem durrleman_eq_one_add_smileDelta (p : Params) {σ ψ₁ T₀ ε k T : ℝ}
    (hw : variance p k = ForwardSmile.totalVar σ ψ₁ T₀ ε k T)
    (hw0 : ForwardSmile.totalVar σ ψ₁ T₀ ε k T ≠ 0)
    (hs : slope p k = ForwardSmile.wSlope σ ψ₁ T₀ ε T k)
    (hc : curvature p k = 2 * ((ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)) :
    durrleman p k = 1 + ForwardSmile.smileDelta σ ψ₁ T₀ ε k T := by
  rw [durrleman, hw, hs, hc, ForwardSmile.smileDelta]
  field_simp
  ring

end SVI
end MathFin
