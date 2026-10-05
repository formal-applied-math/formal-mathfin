/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.SVI.MatrixSignature
public import MathFin.BlackScholes.SVI.CriticalPoints

/-! # Signature of a rank-one form

Part of the SVI polynomial-sign certificate (#174).

`formSignature Q` is `sigPos Q − sigNeg Q`. If `Q x = a·(l x)²` for a nonzero linear form `l`, the
signature is the sign of `a` (`formSignature_rankOne`).
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- The signature `sigPos − sigNeg` of a real quadratic form. -/
noncomputable def formSignature {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) : ℤ := (sigPos Q : ℤ) - (sigNeg Q : ℤ)

theorem sigPos_eq_zero_of_nonpos {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) (hQ : ∀ x, Q x ≤ 0) : sigPos Q = 0 := by
  obtain ⟨W, hW, hp⟩ := exists_finrank_eq_sigPos_and_posDef Q
  have hbot : W = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    by_contra hn
    have hh := hp ⟨x, hx⟩ (by simpa using hn)
    exact (not_lt_of_ge (hQ x)) hh
  rw [hbot, finrank_bot] at hW
  exact hW.symm

theorem one_le_sigPos_of_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) (v : V) (hv : 0 < Q v) :
    1 ≤ sigPos Q := by
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hp : (Q.restrict (ℝ ∙ v)).PosDef := by
    intro x hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.property
    have hc0 : c ≠ 0 := by
      intro h
      apply hx
      apply Subtype.ext
      simpa [h] using hc.symm
    change 0 < Q (x : V)
    rw [← hc, Q.map_smul]
    simpa only [smul_eq_mul, pow_two] using mul_pos (sq_pos_of_ne_zero hc0) hv
  have hh := le_sigPos_of_posDef Q hp
  rw [finrank_span_singleton hv0] at hh
  exact hh

theorem sigPos_le_one_of_rankOne {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) (l : V →ₗ[ℝ] ℝ)
    (a : ℝ) (hQ : ∀ x, Q x = a*(l x)^2) : sigPos Q ≤ 1 := by
  obtain ⟨W, hW, hp⟩ := exists_finrank_eq_sigPos_and_posDef Q
  let L := l.comp W.subtype
  have hinj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hzero : l (x : V) = 0 := hx
    by_contra hn
    have hh := hp x hn
    change 0 < Q (x : V) at hh
    rw [hQ, hzero] at hh
    norm_num at hh
  have hh := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [hW] using hh

/-- The signature of any nonzero linear evaluation squared is the sign of
its coefficient; a zero coefficient is allowed. -/
theorem formSignature_rankOne {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) (l : V →ₗ[ℝ] ℝ)
    (v : V) (hv : l v ≠ 0) (a : ℝ) (hQ : ∀ x, Q x = a*(l x)^2) :
    formSignature Q = sign a := by
  have hneg : ∀ x, (-Q) x = (-a)*(l x)^2 := by intro x; simp [hQ]
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have hp : sigPos Q = 0 := sigPos_eq_zero_of_nonpos Q (by
      intro x; rw [hQ]; exact mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg _))
    have hnp : 1 ≤ sigPos (-Q) := one_le_sigPos_of_pos (-Q) v (by
      rw [hneg]; exact mul_pos (neg_pos.mpr ha) (sq_pos_of_ne_zero hv))
    have hnle := sigPos_le_one_of_rankOne (-Q) l (-a) hneg
    have hn : sigPos (-Q) = 1 := by omega
    simp [formSignature, ← sigPos_neg, hp, hn, sign, ha, not_lt_of_ge ha.le]
  · have hp := sigPos_eq_zero_of_nonpos Q (by intro x; simp [hQ])
    have hn := sigPos_eq_zero_of_nonpos (-Q) (by intro x; simp [hneg])
    simp [formSignature, ← sigPos_neg, hp, hn, sign]
  · have hn : sigPos (-Q) = 0 := sigPos_eq_zero_of_nonpos (-Q) (by
      intro x; rw [hneg]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
    have hpp := one_le_sigPos_of_pos Q v (by rw [hQ]; exact mul_pos ha (sq_pos_of_ne_zero hv))
    have hple := sigPos_le_one_of_rankOne Q l a hQ
    have hp : sigPos Q = 1 := by omega
    simp [formSignature, ← sigPos_neg, hp, hn, sign, ha]

end SVI
end MathFin
