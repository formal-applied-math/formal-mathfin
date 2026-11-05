/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.BlackScholes.SABRImpliedVol

/-!
# SABR chain-rule Greeks (at-the-money)

Hagan, Kumar, Lesniewski & Woodward, "Managing Smile Risk," *Wilmott Magazine*,
September 2002, pp. 84-108, §3.2 ("Managing smile risk"): since the SABR implied vol
`σ_B(K, f)` is itself a function of the forward `f` and of `α`, a European option
`V = BS(f, K, σ_B(K, f), t_ex)` (their eq. 3.5) has genuine price sensitivities that combine
the ordinary Black-Scholes sensitivity with the *vol smile's own movement*, via the chain
rule — their eq. 3.9 (the Δ risk) and eq. 3.6 (the vega risk, in `α`):

`Δ_SABR = Δ_BS + Λ_BS · ∂σ_B/∂f`,   `Λ_SABR^α = Λ_BS · ∂σ_B/∂α`

where `Δ_BS`, `Λ_BS` are the ordinary Black-Scholes delta/vega evaluated at `σ = σ_B(K, f)`.

**What is proved here, and what is not (read this before citing the theorems below).**
Eq. 3.9 needs `∂σ_B(K, f)/∂f` at a FIXED strike `K` as `f` varies — `sabrImpliedVol`'s
general formula (`SABRImpliedVol.lean` eq. 2.17a) differentiated in its *second* argument.
That is not attempted here. At `K = f` the formula's `z / x(z)` factor is `0/0`, which Lean
evaluates to `0`, so the literal `f ↦ sabrImpliedVol K f ⋯` is not even continuous at
`f = K` (`SABRImpliedVol.lean` resolves only the `K → f` *limit* there,
`tendsto_sabrImpliedVol_atm`, from `x'(0) = 1`); a fixed-strike Delta at `K = f` would
first need the ATM value redefined by that limit, and then `x''(0)` (the second
derivative of `sabrX` at `0`, not established in this repository). Away from `K = f`
(where `z ≠ 0`) no singularity arises, but the chain rule
through eq. 2.17a's `(f·K)^((1-β)/2)`, `log(f/K)` and `z / x(z)` factors is left as future
work.

What **is** proved here is the chain rule for the Black call with its strike held FIXED at
`K = f` and the spot `s` moving, priced at the *ATM-vol curve evaluated at the spot*,
`σ_ATM(s) = sabrATMVol s α β ρ ν tex` (eq. 2.18, the paper's own ATM closed form, read as a
function of the forward alone — the "backbone" of `SABRImpliedVol.lean` §"The backbone law",
generalized from its log-log slope to the plain derivative), via a genuine total-derivative
(`HasFDerivAt`-level) argument, not just formula-splicing. This is a well-defined, useful
risk quantity (the Delta under a "vol re-marks along the backbone" convention: the
strike-`K` option is re-marked at the ATM vol of the new forward), but it is **not** eq. 3.9
restricted to `K = f`: eq. 3.9 differentiates the fixed-strike smile `f ↦ σ_B(K, f)`,
whereas the theorem below differentiates the ATM curve `f ↦ σ_B(f, f)`; the two curves agree
at `f = K` but their slopes there differ by the smile's ATM strike-slope. Nor is it eq. 3.10
(the Δ with `σ_ATM` held fixed).

## Main definitions / results

* `hasDerivAt_bsV_S_chainRule` — general Black-Scholes machinery, independent of SABR: if
  the implied vol is itself a differentiable function `v` of the spot/forward (`v s`
  substituted for both arguments of `bsV` at once), the call price's derivative is
  `Δ_BS + Λ_BS · v'`. Proved via the actual bivariate Fréchet derivative of `bsV` in
  `(S, σ)` (built from `hasDerivAt_bsV_S`/`hasDerivAt_bsV_sigma` plus uniqueness of
  derivatives), not by only combining the two formulas.
* `hasDerivAt_bsV_param_chainRule` — the companion one-variable case: the spot/forward is
  held fixed and only the vol moves (through some other parameter, e.g. `α`); this is the
  ordinary single-variable chain rule through `hasDerivAt_bsV_sigma`.
* `hasDerivAt_sabrATMVol_F`, `hasDerivAt_sabrATMVol_alpha` — the real derivatives of the
  closed form `sabrATMVol` (eq. 2.18) in `f` and in `α` respectively.
* `sabrATMVol_bsV_delta_chainRule`, `sabrATMVol_bsV_vega_chainRule` — the two combined:
  the derivative at `s = f` of `s ↦ bsV f 0 (sabrATMVol s α β ρ ν tex) s tex` (strike fixed
  at `f`, spot `s` and the vol curve's argument moving) and of `a ↦ bsV f 0 (sabrATMVol f a
  β ρ ν tex) f tex` (spot/strike fixed at `f`, only `α` moving).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-! ### General Black-Scholes machinery: chain rule when the vol is itself a function

Neither of these two lemmas mentions SABR — they hold for ANY differentiable vol
function `v`, so they are stated here as standalone additions to the Black-Scholes
Greeks toolkit (`PDE.lean`, `HigherGreeks.lean`) and then instantiated at `sabrATMVol`
below. -/

/-- **The vol-curve Delta chain rule**: if the implied vol used to price a call is
itself a differentiable function `v` of the spot/forward — substituted for *both*
arguments of `bsV` simultaneously, `s ↦ bsV K r (v s) s τ` — the price's derivative at
`S` is `Δ_BS + Λ_BS · v'`, the ordinary Black-Scholes delta and vega (both evaluated at
`σ = v S`) combined with the vol curve's own slope `v'`.

The proof is a genuine total derivative, not formula-splicing: `bsV` is shown
differentiable as a function of `(S, σ) ∈ ℝ × ℝ` jointly (`fun_prop` over its elementary
pieces, with `Phi`'s own `HasDerivAt` supplied for the two composed `Phi ∘ bsd1`,
`Phi ∘ bsd2` legs), and the resulting unknown Fréchet derivative's two partial
directions are identified with the already-proved `hasDerivAt_bsV_S`/`hasDerivAt_bsV_sigma`
values via uniqueness of one-variable derivatives
(`HasFDerivAt.comp_hasDerivAt` along the two coordinate paths). Composing that Fréchet
derivative with the diagonal path `s ↦ (s, v s)` and using linearity gives the stated
sum. -/
theorem hasDerivAt_bsV_S_chainRule {K r : ℝ} (hK : 0 < K) {S σ τ : ℝ} (hS : 0 < S)
    (hσ : 0 < σ) (hτ : 0 < τ) {v : ℝ → ℝ} {v' : ℝ} (hv : HasDerivAt v v' S) (hvS : v S = σ) :
    HasDerivAt (fun s ↦ bsV K r (v s) s τ)
      (Phi (bsd1 S K r σ τ) + S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) * Real.sqrt τ * v')
      S := by
  have h1 : S / K ≠ 0 := div_ne_zero hS.ne' hK.ne'
  have h2 : σ * Real.sqrt τ ≠ 0 := mul_ne_zero hσ.ne' (Real.sqrt_pos.mpr hτ).ne'
  have hd1 : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ bsd1 p.1 K r p.2 τ) (S, σ) := by
    unfold bsd1; fun_prop (disch := assumption)
  have hd2 : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ bsd2 p.1 K r p.2 τ) (S, σ) := by
    unfold bsd2 bsd1; fun_prop (disch := assumption)
  have hPhi1 : DifferentiableAt ℝ Phi (bsd1 S K r σ τ) := (hasDerivAt_Phi _).differentiableAt
  have hPhi2 : DifferentiableAt ℝ Phi (bsd2 S K r σ τ) := (hasDerivAt_Phi _).differentiableAt
  have hcomp1 : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ Phi (bsd1 p.1 K r p.2 τ)) (S, σ) :=
    DifferentiableAt.comp (f := fun p : ℝ × ℝ ↦ bsd1 p.1 K r p.2 τ) (x := (S, σ)) hPhi1 hd1
  have hcomp2 : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ Phi (bsd2 p.1 K r p.2 τ)) (S, σ) :=
    DifferentiableAt.comp (f := fun p : ℝ × ℝ ↦ bsd2 p.1 K r p.2 τ) (x := (S, σ)) hPhi2 hd2
  have hg : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ bsV K r p.2 p.1 τ) (S, σ) := by
    unfold bsV; fun_prop (disch := assumption)
  set g : ℝ × ℝ → ℝ := fun p ↦ bsV K r p.2 p.1 τ with hgdef
  obtain ⟨f', hf'⟩ := hg
  -- Extract the S-partial and identify it with the known Delta value.
  have hpathS : HasDerivAt (fun s : ℝ ↦ ((s, σ) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) S :=
    (hasDerivAt_id S).prodMk (hasDerivAt_const S σ)
  have hextractS : HasDerivAt (fun s ↦ g (s, σ)) (f' (1, 0)) S :=
    (hf'.comp_hasDerivAt S hpathS : HasDerivAt (g ∘ fun s : ℝ ↦ (s, σ)) (f' (1, 0)) S)
  have hextractS' : HasDerivAt (fun s ↦ bsV K r σ s τ) (f' (1, 0)) S := hextractS
  have hS_eq : f' (1, 0) = Phi (bsd1 S K r σ τ) :=
    hextractS'.unique (hasDerivAt_bsV_S hK hσ hS hτ)
  -- Extract the σ-partial and identify it with the known Vega value.
  have hpathSig : HasDerivAt (fun s : ℝ ↦ ((S, s) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) σ :=
    (hasDerivAt_const σ S).prodMk (hasDerivAt_id σ)
  have hextractSig : HasDerivAt (fun s ↦ g (S, s)) (f' (0, 1)) σ :=
    (hf'.comp_hasDerivAt σ hpathSig : HasDerivAt (g ∘ fun s : ℝ ↦ (S, s)) (f' (0, 1)) σ)
  have hextractSig' : HasDerivAt (fun s ↦ bsV K r s S τ) (f' (0, 1)) σ := hextractSig
  have hSig_eq : f' (0, 1) = S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) * Real.sqrt τ :=
    hextractSig'.unique (hasDerivAt_bsV_sigma hK hS hσ hτ)
  -- Compose with the diagonal path s ↦ (s, v s), then use linearity of f'.
  have hpath : HasDerivAt (fun s : ℝ ↦ ((s, v s) : ℝ × ℝ)) ((1 : ℝ), v') S :=
    (hasDerivAt_id S).prodMk hv
  have hvalAt : (S, v S) = (S, σ) := by rw [hvS]
  have hfinal : HasDerivAt (fun s ↦ g (s, v s)) (f' (1, v')) S := by
    rw [← hvalAt] at hf'
    exact hf'.comp_hasDerivAt S hpath
  have hlin : f' (1, v') = f' (1, 0) + v' • f' (0, 1) := by
    have hre : ((1 : ℝ), v') = (1, (0 : ℝ)) + v' • ((0 : ℝ), (1 : ℝ)) := by simp
    rw [hre, map_add, map_smul]
  rw [hS_eq, hSig_eq] at hlin
  have hh : HasDerivAt (fun s ↦ bsV K r (v s) s τ) (f' (1, v')) S := hfinal
  rw [hlin] at hh
  convert hh using 1
  ring

/-- **The vol-parameter Vega chain rule**: if the spot/forward is held FIXED and the vol
moves only through some other parameter `a` (e.g. `α`), the price's derivative in `a` is
just the ordinary Black-Scholes vega times the vol's own sensitivity, `Λ_BS · v'` — the
plain one-variable chain rule through `hasDerivAt_bsV_sigma` (no bivariate argument
needed, since only one argument of `bsV` moves). -/
theorem hasDerivAt_bsV_param_chainRule {K r S σ τ : ℝ} (hK : 0 < K) (hS : 0 < S)
    (hσ : 0 < σ) (hτ : 0 < τ) {v : ℝ → ℝ} {v' x : ℝ} (hv : HasDerivAt v v' x)
    (hvx : v x = σ) :
    HasDerivAt (fun a ↦ bsV K r (v a) S τ)
      (S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) * Real.sqrt τ * v') x := by
  subst hvx
  exact (hasDerivAt_bsV_sigma hK hS hσ hτ).comp x hv

/-! ### The ATM-vol curve's own sensitivities -/

/-- **`∂σ_ATM/∂f`**: the real derivative of the closed-form ATM vol `sabrATMVol`
(eq. 2.18) with respect to the forward, for `f > 0`. -/
theorem hasDerivAt_sabrATMVol_F {f α β ρ ν tex : ℝ} (hf : 0 < f) :
    HasDerivAt (fun x ↦ sabrATMVol x α β ρ ν tex)
      ((-(α * ((1 - β) * f ^ (1 - β - 1))) / (f ^ (1 - β)) ^ 2) *
          (1 + ((1 - β) ^ 2 / 24 * (α ^ 2 / f ^ (2 - 2 * β))
              + ρ * β * α * ν / 4 / f ^ (1 - β) + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)
        + (α / f ^ (1 - β)) *
          (((1 - β) ^ 2 / 24 * (-(α ^ 2 * ((2 - 2 * β) * f ^ (2 - 2 * β - 1)))
                / (f ^ (2 - 2 * β)) ^ 2)
              + (-(ρ * β * α * ν / 4 * ((1 - β) * f ^ (1 - β - 1))) / (f ^ (1 - β)) ^ 2))
            * tex))
      f := by
  have hpow1 : HasDerivAt (fun x : ℝ ↦ x ^ (1 - β)) ((1 - β) * f ^ (1 - β - 1)) f :=
    hasDerivAt_rpow_const (Or.inl hf.ne')
  have hpow2 : HasDerivAt (fun x : ℝ ↦ x ^ (2 - 2 * β)) ((2 - 2 * β) * f ^ (2 - 2 * β - 1)) f :=
    hasDerivAt_rpow_const (Or.inl hf.ne')
  have hp1ne : f ^ (1 - β) ≠ 0 := (Real.rpow_pos_of_pos hf _).ne'
  have hp2ne : f ^ (2 - 2 * β) ≠ 0 := (Real.rpow_pos_of_pos hf _).ne'
  have hBb := (hasDerivAt_const f α).div hpow1 hp1ne
  have hterm1 := (hasDerivAt_const f (α ^ 2)).div hpow2 hp2ne |>.const_mul ((1 - β) ^ 2 / 24)
  have hterm2 := (hasDerivAt_const f (ρ * β * α * ν / 4)).div hpow1 hp1ne
  have hbracket := (hterm1.add hterm2).add (hasDerivAt_const f ((2 - 3 * ρ ^ 2) / 24 * ν ^ 2))
  have hCf := (hbracket.mul_const tex).const_add (1 : ℝ)
  have hfinal := hBb.mul hCf
  unfold sabrATMVol sabrBackbone
  convert hfinal using 1
  simp only [Pi.div_apply, Pi.add_apply]
  ring

/-- **`∂σ_ATM/∂α`**: the real derivative of the closed-form ATM vol `sabrATMVol`
(eq. 2.18) with respect to `α`. Unlike the `f`-derivative, this holds unconditionally
(`sabrATMVol` is a genuine polynomial in `α`, with no `α`-dependent rpow base). -/
theorem hasDerivAt_sabrATMVol_alpha {f β ρ ν tex : ℝ} (α : ℝ) :
    HasDerivAt (fun a ↦ sabrATMVol f a β ρ ν tex)
      (1 / f ^ (1 - β) *
          (1 + ((1 - β) ^ 2 / 24 * (α ^ 2 / f ^ (2 - 2 * β))
              + ρ * β * α * ν / 4 / f ^ (1 - β) + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)
        + α / f ^ (1 - β) *
          (((1 - β) ^ 2 / 24 * (2 * α / f ^ (2 - 2 * β)) + ρ * β * ν / 4 / f ^ (1 - β)) * tex))
      α := by
  unfold sabrATMVol sabrBackbone
  have hBb : HasDerivAt (fun a : ℝ ↦ a / f ^ (1 - β)) (1 / f ^ (1 - β)) α := by
    have h := (hasDerivAt_id' α).div_const (f ^ (1 - β))
    convert h using 1
  have hbr : HasDerivAt (fun a : ℝ ↦ (1 - β) ^ 2 / 24 * (a ^ 2 / f ^ (2 - 2 * β))
      + ρ * β * a * ν / 4 / f ^ (1 - β) + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2)
      ((1 - β) ^ 2 / 24 * (2 * α / f ^ (2 - 2 * β)) + ρ * β * ν / 4 / f ^ (1 - β)) α := by
    have h1 : HasDerivAt (fun a : ℝ ↦ (1 - β) ^ 2 / 24 * (a ^ 2 / f ^ (2 - 2 * β)))
        ((1 - β) ^ 2 / 24 * (2 * α / f ^ (2 - 2 * β))) α := by
      have h := ((hasDerivAt_pow 2 α).div_const (f ^ (2 - 2 * β))).const_mul ((1 - β) ^ 2 / 24)
      convert h using 1
      ring
    have h2 : HasDerivAt (fun a : ℝ ↦ ρ * β * a * ν / 4 / f ^ (1 - β))
        (ρ * β * ν / 4 / f ^ (1 - β)) α := by
      have h :=
        (((hasDerivAt_id' α).const_mul (ρ * β)).mul_const ν).div_const 4 |>.div_const (f ^ (1 - β))
      convert h using 1
      ring
    have h3 : HasDerivAt (fun _ : ℝ ↦ (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) 0 α := hasDerivAt_const α _
    have hsum := (h1.add h2).add h3
    convert hsum using 1
    ring
  have hCf : HasDerivAt (fun a : ℝ ↦ 1 + ((1 - β) ^ 2 / 24 * (a ^ 2 / f ^ (2 - 2 * β))
      + ρ * β * a * ν / 4 / f ^ (1 - β) + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)
      ((((1 - β) ^ 2 / 24 * (2 * α / f ^ (2 - 2 * β)) + ρ * β * ν / 4 / f ^ (1 - β))) * tex) α
      := by
    have h := (hbr.mul_const tex).const_add (1 : ℝ)
    convert h using 1
  have hres := hBb.mul hCf
  convert hres using 1

/-! ### The combined chain-rule Greeks -/

/-- **The SABR ATM chain-rule Delta**: the derivative at spot `s = f` of the Black call
with strike held fixed at `K = f`, priced at spot `s` with the ATM vol curve evaluated at
that spot, `σ_ATM(s) = sabrATMVol s α β ρ ν tex` — spot and the vol's own forward-dependence
moving together, strike fixed — equals `Δ_BS + Λ_BS · ∂σ_ATM/∂f`. See the file docstring
for exactly what this is (and is not) relative to Hagan's eq. 3.9. `hσ` (vol positivity) is
a standing domain hypothesis, assumed rather than derived — as `BSCallHyp.σ_pos` is for
`sabrATMVol_black_futures_price` (`SABRImpliedVol.lean`; its `sabrATMVol_bsV_gt_backbone_bsV`
instead *derives* positivity from `0 < α` and a positive correction bracket). -/
theorem sabrATMVol_bsV_delta_chainRule {f α β ρ ν tex : ℝ} (hf : 0 < f)
    (hσ : 0 < sabrATMVol f α β ρ ν tex) (htex : 0 < tex) :
    HasDerivAt (fun s ↦ bsV f 0 (sabrATMVol s α β ρ ν tex) s tex)
      (Phi (bsd1 f f 0 (sabrATMVol f α β ρ ν tex) tex)
        + f * gaussianPDFReal 0 1 (bsd1 f f 0 (sabrATMVol f α β ρ ν tex) tex) * Real.sqrt tex *
          ((-(α * ((1 - β) * f ^ (1 - β - 1))) / (f ^ (1 - β)) ^ 2) *
              (1 + ((1 - β) ^ 2 / 24 * (α ^ 2 / f ^ (2 - 2 * β))
                  + ρ * β * α * ν / 4 / f ^ (1 - β) + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)
            + (α / f ^ (1 - β)) *
              (((1 - β) ^ 2 / 24 * (-(α ^ 2 * ((2 - 2 * β) * f ^ (2 - 2 * β - 1)))
                    / (f ^ (2 - 2 * β)) ^ 2)
                  + (-(ρ * β * α * ν / 4 * ((1 - β) * f ^ (1 - β - 1))) / (f ^ (1 - β)) ^ 2))
                * tex)))
      f :=
  hasDerivAt_bsV_S_chainRule hf hf hσ htex (hasDerivAt_sabrATMVol_F hf) rfl

/-- **The SABR ATM chain-rule Vega**: the derivative, in `α`, of the Black call priced at
the ATM strike `K = f` (spot and strike both fixed at `f`, only `α` moving through the
vol) with vol `σ_ATM = sabrATMVol f α β ρ ν tex`, equals `Λ_BS · ∂σ_ATM/∂α`. -/
theorem sabrATMVol_bsV_vega_chainRule {f α β ρ ν tex : ℝ} (hf : 0 < f)
    (hσ : 0 < sabrATMVol f α β ρ ν tex) (htex : 0 < tex) :
    HasDerivAt (fun a ↦ bsV f 0 (sabrATMVol f a β ρ ν tex) f tex)
      (f * gaussianPDFReal 0 1 (bsd1 f f 0 (sabrATMVol f α β ρ ν tex) tex) * Real.sqrt tex *
        (1 / f ^ (1 - β) *
            (1 + ((1 - β) ^ 2 / 24 * (α ^ 2 / f ^ (2 - 2 * β))
                + ρ * β * α * ν / 4 / f ^ (1 - β) + (2 - 3 * ρ ^ 2) / 24 * ν ^ 2) * tex)
          + α / f ^ (1 - β) *
            (((1 - β) ^ 2 / 24 * (2 * α / f ^ (2 - 2 * β)) + ρ * β * ν / 4 / f ^ (1 - β))
              * tex)))
      α :=
  hasDerivAt_bsV_param_chainRule hf hf hσ htex (hasDerivAt_sabrATMVol_alpha α) rfl

end MathFin
