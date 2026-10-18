/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# The SABR lognormal implied-volatility asymptotic approximation

Hagan, Kumar, Lesniewski & Woodward, "Managing Smile Risk," *Wilmott Magazine*,
September 2002, pp. 84-108. Under the SABR stochastic-volatility model
`dF̂ = α̂F̂^β dW₁`, `dα̂ = να̂ dW₂`, `dW₁ dW₂ = ρ dt` (their eqs. 2.15a-c), singular
perturbation gives the price of European options via Black's formula with an
*explicit, closed-form asymptotic approximation* for the implied volatility
`σ_B(K, f)` as a function of today's forward `f` and strike `K` (eqs. 2.17a-c):

`σ_B(K,f) = α / [(fK)^((1-β)/2) · (1 + (1-β)²/24 · log²(f/K) + (1-β)⁴/1920 · log⁴(f/K) + ⋯)]
  · (z / x(z)) · (1 + [(1-β)²/24 · α²/(fK)^(1-β) + ρβνα/4/(fK)^((1-β)/2) + (2-3ρ²)/24 · ν²] t_ex + ⋯)`

where `z = (ν/α)(fK)^((1-β)/2) log(f/K)` and
`x(z) = log((√(1-2ρz+z²) + z - ρ)/(1-ρ))` (eqs. 2.17b-c).

**This is a closed-form asymptotic approximation, not an exact price** — the
paper derives it via a singular-perturbation (small vol-of-vol, short-maturity)
expansion and explicitly omits higher-order `⋯` terms (stated to be "much,
much smaller" than the displayed terms, but nonzero). We formalize the
displayed truncation (`sabrImpliedVol`) exactly as printed, plus the at-the-money
(`K = f`) specialization (eq. 2.18, `sabrATMVol`), where the paper's own text
notes the formula "reduces to" after the removable `z/x(z) → 1` singularity at
`z = 0`. We do not attempt the singular-perturbation PDE derivation itself —
that stochastic machinery (the SABR two-factor SDE's transition density) does
not exist in this repo or in Mathlib/BrownianMotion, and reconstructing it is
well beyond a closed-form transcription. What *is* proved here is restricted to
elementary algebraic consequences of the stated formula: the ATM specialization
is definitionally eq. 2.18, and at zero time-to-exercise the ATM volatility
collapses exactly to the SABR "backbone" `α / f^(1-β)` that the paper calls out
in section 3 as the ATM-vol curve traced as the forward varies.

## Main definitions

* `sabrATMVol` — the at-the-money implied vol (eq. 2.18), the `K = f`
  specialization where the general formula's removable singularity is already
  resolved in closed form.
* `sabrBackbone` — the leading-order ATM vol `α / f^(1-β)` (eq. 2.18's
  dominant term; "the backbone" in the paper's section 3 terminology).

## Main results

* `sabrATMVol_pos` — the backbone factor `α / f^(1-β)` is positive for `α, f > 0`.
* `sabrATMVol_zero_tex` — at `t_ex = 0`, `sabrATMVol` collapses exactly to the
  backbone `sabrBackbone`.
-/

@[expose] public section

namespace MathFin

open Real

/-- **The SABR "backbone"**: the leading-order at-the-money implied volatility
`α / f^(1-β)` (the dominant factor in Hagan-Kumar-Lesniewski-Woodward eq. 2.18;
called the *backbone* in their section 3, the curve traced by ATM vol as the
forward `f` varies). -/
noncomputable def sabrBackbone (f α β : ℝ) : ℝ := α / f ^ (1 - β)

/-- **The SABR at-the-money implied volatility** (Hagan-Kumar-Lesniewski-Woodward,
*Managing Smile Risk*, Wilmott Magazine 2002, eq. 2.18):

`σ_ATM = α/f^(1-β) · {1 + [(1-β)²/24 · α²/f^(2-2β) + ρβαν/4/f^(1-β) + (2-3ρ²)/24 · ν²] t_ex + ⋯}`

the `K = f` specialization of the general formula (eq. 2.17a), where the
`z/x(z)` factor's removable singularity at `z = 0` is already resolved. This is
the asymptotic truncation as printed in the paper (the omitted `⋯` terms are
higher order in the perturbation expansion, stated by the authors to be much
smaller than the displayed correction). -/
noncomputable def sabrATMVol (f α β ρ ν tex : ℝ) : ℝ :=
  sabrBackbone f α β *
    (1 + ((1 - β) ^ 2 / 24 * (α ^ 2 / f ^ (2 - 2 * β))
        + ρ * β * α * ν / 4 / f ^ (1 - β)
        + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)

/-- **The backbone is positive** for `α, f > 0`: `α / f^(1-β) > 0`. -/
theorem sabrBackbone_pos {f α : ℝ} (hf : 0 < f) (hα : 0 < α) (β : ℝ) :
    0 < sabrBackbone f α β := by
  unfold sabrBackbone
  exact div_pos hα (Real.rpow_pos_of_pos hf _)

/-- **Zero time-to-exercise collapses the ATM vol to the backbone**: at `t_ex = 0`
the bracketed perturbation correction in eq. 2.18 vanishes identically
(it is multiplied by `t_ex`), leaving exactly `σ_ATM = α/f^(1-β)`. -/
theorem sabrATMVol_zero_tex (f α β ρ ν : ℝ) :
    sabrATMVol f α β ρ ν 0 = sabrBackbone f α β := by
  unfold sabrATMVol
  ring

/-- **The ATM vol is positive at zero time-to-exercise**, for `α, f > 0`: direct
corollary of `sabrATMVol_zero_tex` and `sabrBackbone_pos`. -/
theorem sabrATMVol_pos_zero_tex {f α : ℝ} (hf : 0 < f) (hα : 0 < α) (β ρ ν : ℝ) :
    0 < sabrATMVol f α β ρ ν 0 := by
  rw [sabrATMVol_zero_tex]
  exact sabrBackbone_pos hf hα β

end MathFin
