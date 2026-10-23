/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Boundary.ParabolicMaximum

/-! # Compact ordered equal-time triples in a moving strip 
## Result

Public entry points include `sameTimeTriple`, `orderedTriples`, `orderedTriples_isCompact`,
`sameTimeTriple_mem`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Set

/-- Three space-time points, each a pair `(x, t)`. -/
abbrev SpaceTimeTriple := (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)

/-- The triple of `x`, `y` and `z` at the common time `t`. -/
def sameTimeTriple (x y z t : ℝ) : SpaceTimeTriple := ((x,t),(y,t),(z,t))

/-- Triples of points of `Q` sharing a time, with spatial coordinates in increasing order. -/
def orderedTriples (Q : Set (ℝ × ℝ)) : Set SpaceTimeTriple :=
  (Q ×ˢ Q ×ˢ Q) ∩ {w | w.1.2 = w.2.1.2 ∧ w.1.2 = w.2.2.2 ∧
    w.1.1 ≤ w.2.1.1 ∧ w.2.1.1 ≤ w.2.2.1}

theorem orderedTriples_isCompact {Q : Set (ℝ × ℝ)} (hQ : IsCompact Q) :
    IsCompact (orderedTriples Q) := by
  have h1 : IsClosed {w : SpaceTimeTriple | w.1.2 = w.2.1.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have h2 : IsClosed {w : SpaceTimeTriple | w.1.2 = w.2.2.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have h3 : IsClosed {w : SpaceTimeTriple | w.1.1 ≤ w.2.1.1} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have h4 : IsClosed {w : SpaceTimeTriple | w.2.1.1 ≤ w.2.2.1} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact (hQ.prod (hQ.prod hQ)).inter_right (h1.inter (h2.inter (h3.inter h4)))

theorem sameTimeTriple_mem {b : ℝ → ℝ} {R a T x y z t : ℝ}
    (ha : a ≤ t) (hT : t ≤ T) (hb : b t ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hR : z ≤ R) :
    sameTimeTriple x y z t ∈ orderedTriples (movingStrip b R a T) := by
  refine ⟨⟨?_,?_,?_⟩,rfl,rfl,hxy,hyz⟩
  · exact ⟨ha,hT,hb,(hxy.trans hyz).trans hR⟩
  · exact ⟨ha,hT,hb.trans hxy,hyz.trans hR⟩
  · exact ⟨ha,hT,(hb.trans hxy).trans hyz,hR⟩

end MathFin.BlackScholes.AmericanPut.Boundary
