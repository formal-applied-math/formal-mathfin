/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.SVI.HermiteIdentity
public import MathFin.BlackScholes.SVI.ClearedSignature
public import MathFin.BlackScholes.SVI.PolynomialCertificate

/-! # The determinant certificate

Part of the SVI polynomial-sign certificate (#174).

For a nonconstant polynomial of degree at most ten, the signature combination of four explicit
denominator-free matrices equals four times the number of distinct positive critical points with
a negative value (`matrixCountFour_eq`). `matrixCertificate`, a root-free predicate covering every
degree branch, is equivalent to nonnegativity on `(0, ∞)` for degree at most ten
(`matrixCertificate_iff`).
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- The four explicit, denominator-free matrices count exactly the forbidden
positive critical points, including all multiplicity and tangency cases. -/
theorem matrixCountFour_eq (P : ℝ[X]) (hd : P.natDegree ≤ 10)
    (hn : P.natDegree ≠ 0) : matrixCountFour P = 4 * (badCriticalCount P : ℤ) := by
  have hf : P.derivative ≠ 0 := derivative_ne_zero.mpr hn
  unfold matrixCountFour
  simp_rw [certificateMatrix_signature P hd hn, hermite_signature _ _ hf]
  simpa [tarskiQuery, criticalRoots, badCriticalCount] using
    four_query_count (criticalRoots P) P.eval

/-- A root-free determinant predicate for all degree branches. For degree one
the matrices are empty and their signature combination is automatically zero. -/
noncomputable def matrixCertificate (P : ℝ[X]) : Prop :=
  if P.natDegree = 0 then 0 ≤ P.coeff 0
  else 0 < P.leadingCoeff ∧ 0 ≤ P.coeff 0 ∧ matrixCountFour P = 0

theorem matrixCertificate_iff_criticalCertificate (P : ℝ[X]) (hd : P.natDegree ≤ 10) :
    matrixCertificate P ↔ criticalCertificate P := by
  unfold matrixCertificate criticalCertificate
  split_ifs with hn
  · rfl
  · rw [matrixCountFour_eq P hd hn, coeff_zero_eq_eval_zero]
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or, Int.natCast_eq_zero]

theorem matrixCertificate_iff (P : ℝ[X]) (hd : P.natDegree ≤ 10) :
    matrixCertificate P ↔ ∀ t : ℝ, 0 < t → 0 ≤ P.eval t := by
  rw [matrixCertificate_iff_criticalCertificate P hd, criticalCertificate_iff]

/-- The full boundary-safe determinant certificate for the smooth,
positive-variance SVI Durrleman condition. -/
theorem svi_matrixCertificate_iff (p : Params) (hs : 0 < p.sigma)
    (hb : 0 ≤ p.b) (hr : 0 ≤ 1-p.rho^2) (hg : varianceGate p) :
    matrixCertificate (polynomial p) ↔ ∀ k : ℝ, 0 ≤ durrleman p k := by
  rw [matrixCertificate_iff_criticalCertificate _ (degree_le_ten p)]
  exact svi_criticalCertificate_iff p hs hb hr hg

end SVI
end MathFin
