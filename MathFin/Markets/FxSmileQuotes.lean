/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.LocalVol.ForwardSmile
public import MathFin.Probability.Gaussian.NormalQuantile
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# FX smile quotes: risk reversal and butterfly in delta space

The FX options market quotes a smile not by strike but by **delta**: at each expiry the
three quoted pillars are the ATM volatility and, at each wing level `Δ` (25Δ by market
convention), the risk reversal and the butterfly. Following Bossens, Rayée, Skantzos and
Deelstra (arXiv:0904.1074v3), §3.3, for a smile given in delta space — a function `v` whose
value at `d` is the implied volatility of the option whose (driftless forward) Black delta
is `d`, calls on `d > 0` and puts on `d < 0` — the two wing quotes are

* the **risk reversal** (their eq. (9)): `RR_Δ(v) = v(Δ) − v(−Δ)`, the call wing minus the
  put wing;
* the **(2-vol) butterfly** (their eq. (10)): `BF_Δ(v, σ_ATM) = (v(Δ) + v(−Δ))/2 − σ_ATM`,
  the midpoint of the wings minus the ATM pillar.

This file defines both quotes as functionals of the delta-space smile `v` (the ATM pillar
enters the butterfly as a separate argument, exactly as it is quoted) and proves the
algebra of the quoting convention: the wing vols are recovered from the quote triple by
`v(Δ) = σ_ATM + BF + RR/2` and `v(−Δ) = σ_ATM + BF − RR/2` (the reconstruction a smile
builder runs, immediate from eqs. (9)–(10) though the paper itself does not write it), the
quote triple determines the two wing vols, the risk reversal is antisymmetric under the
mirror `d ↦ −d` while the butterfly is mirror-invariant, a delta-even smile has zero risk
reversal and its butterfly degenerates to the wing-ATM spread, and the butterfly is
nonnegative exactly when the ATM pillar does not exceed the wing midpoint.

The second half is the strike substrate the delta parametrization rests on, on the flat
(single-volatility) Black slice in the library's `(k, w)` coordinates (log-moneyness `k`,
total variance `w`, as in `MathFin.Models.LocalVol.ForwardSmile`): the driftless forward
delta of the flat call at log-strike `k` is `Φ(d₊)` (BRSD eq. (4); here via the library's
`hasDerivAt_bsV_S`), so the `Φ(z)`-delta strike is `k = w/2 − √w·z`, it exists and is
unique, the `Δ`-call and `Δ`-put strikes are reflections of each other about the ATM
strike `w/2` (BRSD eq. (5): `K_ATM = F·e^{w/2}` in the delta-neutral-straddle convention),
the ATM strike carries delta exactly `1/2`, and the at-the-money-forward point `k = 0`
carries delta strictly above `1/2` — the forward point is not the delta-neutral point,
which is why the market's ATM strike is displaced from it.

## Scope

The quoting conventions are maps from smile data to quotes, and what is proved here is
their algebra plus the flat-slice strike geometry. What is **not** proved: nothing
probabilistic appears (no process, no measure, no price); no market-data construction
turns the quote triple into a full smile (the `1`-vol broker strangle of BRSD eq. (11) and
the vega-weighted approximation eq. (13) are not treated); no-arbitrage content of the
quotes is not addressed; and the strike solving is proved only on the flat slice — on a
non-flat smile the `Δ`-strike solves `Φ(d₊(k, σ(k)²τ)) = Δ` in `k`, whose existence and
uniqueness is the smile's no-butterfly-arbitrage property (the Durrleman condition of
`MathFin/Models/ModelFree/SVI/Assembly.lean`), not assumed or proved here. The
premium-included delta convention (BRSD eq. (3)) is not treated; `v` is read in the
driftless forward delta of BRSD eq. (4).

## Main definitions

* `fxRiskReversal`: `RR_Δ(v) = v(Δ) − v(−Δ)` (BRSD eq. (9)).
* `fxSmileButterfly`: `BF_Δ(v, σ_ATM) = (v(Δ) + v(−Δ))/2 − σ_ATM` (BRSD eq. (10)).
* `fxDeltaStrike`: the flat-slice log-strike `w/2 − √w·z` whose call carries
  driftless forward delta `Φ(z)`.

## Main results

Quoting algebra:

* `fxCallWingVol_eq`, `fxPutWingVol_eq`: the reconstruction `v(Δ) = σ_ATM + BF + RR/2`,
  `v(−Δ) = σ_ATM + BF − RR/2`.
* `fxWingVols_eq_of_quotes_eq`: the quote triple determines both wing vols.
* `fxRiskReversal_mirror`: `RR_Δ(v ∘ neg) = −RR_Δ(v)`; `fxSmileButterfly_mirror`: the
  butterfly is mirror-invariant.
* `fxRiskReversal_eq_zero_iff`: `RR = 0 ↔ v(Δ) = v(−Δ)`; `fxRiskReversal_eq_zero_of_even`
  and `fxSmileButterfly_eq_sub_of_even`: on a delta-even smile `RR = 0` and
  `BF = v(Δ) − σ_ATM`.
* `fxSmileButterfly_nonneg_iff`: `0 ≤ BF ↔ σ_ATM ≤ (v(Δ) + v(−Δ))/2`.

Flat-slice strike geometry:

* `fxFlatCall_delta`: the driftless forward delta of the flat call at `S = F`,
  `K = F·e^k` is `Φ(dpl k w)` — via the library's `hasDerivAt_bsV_S`.
* `dpl_fxDeltaStrike`: `d₊(w/2 − √w·z, w) = z`; `fxDelta_eq_iff` and
  `existsUnique_fxDelta_eq`: the `Δ`-delta strike exists, is unique and is
  `w/2 − √w·Φ⁻¹(Δ)`.
* `fxDeltaStrike_call_add_put`: the `Δ`-call and `Δ`-put strikes satisfy
  `k_c + k_p = w` — reflections about the ATM strike `w/2`, not about the forward `k = 0`.
* `fxAtmStrike_delta`: the delta-neutral-straddle ATM strike `w/2` (BRSD eq. (5)) carries
  delta exactly `1/2`; `fxForwardPoint_delta_gt_half`: the at-the-money-forward point
  `k = 0` carries delta `Φ(√w/2)`, strictly above `1/2` — the two points differ.

## References

* [F. Bossens, G. Rayée, N. S. Skantzos and G. Deelstra, *Vanna-Volga methods applied to FX
derivatives: from theory to market practice*][BossensRayeeSkantzosDeelstra2010], §3.1–§3.3

## Tags

risk reversal, butterfly, FX smile, delta space, quoting convention, smile skew, smile
convexity, ATM strike, delta-neutral straddle, MSC 91G15, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Real
open MathFin.ForwardSmile (dpl dmi dpl_eq bsd1_eq_dpl)

/-! ## The quoting conventions in delta space -/

/-- **The risk reversal** (Bossens–Rayée–Skantzos–Deelstra eq. (9)): for a smile `v` given
in delta space — `v d` is the implied volatility of the option whose driftless forward
Black delta is `d`, calls on `d > 0`, puts on `d < 0` — the `Δ`-level risk reversal is the
call-wing volatility minus the put-wing volatility. The market standard level is
`Δ = 0.25`. -/
def fxRiskReversal (v : ℝ → ℝ) (Δ : ℝ) : ℝ := v Δ - v (-Δ)

/-- **The smile butterfly** (Bossens–Rayée–Skantzos–Deelstra eq. (10), the 2-vol
convention): the midpoint of the `Δ`-wing volatilities minus the ATM pillar volatility
`atm`. The ATM pillar enters as a separate argument exactly as the market quotes it: its
strike is set by convention (the delta-neutral straddle), not by a fixed delta. -/
noncomputable def fxSmileButterfly (v : ℝ → ℝ) (Δ atm : ℝ) : ℝ := (v Δ + v (-Δ)) / 2 - atm

/-- **The reconstruction of the call wing** from the quote triple: immediate from eqs.
(9)–(10) — `v(Δ) = σ_ATM + BF + RR/2`. Together with `fxPutWingVol_eq` this is the map a
smile builder runs from the three market quotes to the three volatility pillars. -/
theorem fxCallWingVol_eq (v : ℝ → ℝ) (Δ atm : ℝ) :
    v Δ = atm + fxSmileButterfly v Δ atm + fxRiskReversal v Δ / 2 := by
  unfold fxSmileButterfly fxRiskReversal
  ring

/-- **The reconstruction of the put wing**: `v(−Δ) = σ_ATM + BF − RR/2`, as
`fxCallWingVol_eq`. -/
theorem fxPutWingVol_eq (v : ℝ → ℝ) (Δ atm : ℝ) :
    v (-Δ) = atm + fxSmileButterfly v Δ atm - fxRiskReversal v Δ / 2 := by
  unfold fxSmileButterfly fxRiskReversal
  ring

/-- **The quote triple determines the wings**: two smiles with the same risk reversal,
butterfly and ATM pillar agree at both `Δ`-wings. With `fxCallWingVol_eq` and
`fxPutWingVol_eq`, the quote triple and the wing pair carry the same information. -/
theorem fxWingVols_eq_of_quotes_eq {v v' : ℝ → ℝ} {Δ atm : ℝ}
    (hrr : fxRiskReversal v Δ = fxRiskReversal v' Δ)
    (hbf : fxSmileButterfly v Δ atm = fxSmileButterfly v' Δ atm) :
    v Δ = v' Δ ∧ v (-Δ) = v' (-Δ) := by
  have hc := fxCallWingVol_eq v Δ atm
  have hc' := fxCallWingVol_eq v' Δ atm
  have hp := fxPutWingVol_eq v Δ atm
  have hp' := fxPutWingVol_eq v' Δ atm
  rw [← hrr, ← hbf] at hc' hp'
  exact ⟨by linarith, by linarith⟩

/-- **Skew is antisymmetric**: mirroring the smile in delta space (the counter-currency
view of the same market) negates the risk reversal. The quote that measures the smile's
skew changes sign with the direction the skew is read in. -/
theorem fxRiskReversal_mirror (v : ℝ → ℝ) (Δ : ℝ) :
    fxRiskReversal (fun d ↦ v (-d)) Δ = -fxRiskReversal v Δ := by
  simp only [fxRiskReversal]
  ring_nf

/-- **Convexity is mirror-blind**: the butterfly of the mirrored smile is the butterfly of
the smile — the quote that measures the smile's curvature does not see the direction of
its skew. -/
theorem fxSmileButterfly_mirror (v : ℝ → ℝ) (Δ atm : ℝ) :
    fxSmileButterfly (fun d ↦ v (-d)) Δ atm = fxSmileButterfly v Δ atm := by
  simp only [fxSmileButterfly]
  ring_nf

/-- **Zero risk reversal means equal wings**: `RR_Δ(v) = 0 ↔ v(Δ) = v(−Δ)`. -/
theorem fxRiskReversal_eq_zero_iff (v : ℝ → ℝ) (Δ : ℝ) :
    fxRiskReversal v Δ = 0 ↔ v Δ = v (-Δ) := by
  unfold fxRiskReversal
  constructor
  · intro h; linarith
  · intro h; rw [h, sub_self]

/-- **A delta-even smile has no skew**: if `v` is even (`v(d) = v(−d)` for every `d`), the
risk reversal vanishes at every level. -/
theorem fxRiskReversal_eq_zero_of_even {v : ℝ → ℝ} (heven : ∀ d, v d = v (-d)) (Δ : ℝ) :
    fxRiskReversal v Δ = 0 :=
  (fxRiskReversal_eq_zero_iff v Δ).2 (heven Δ)

/-- **A delta-even smile's butterfly is the wing-ATM spread**: with no skew both wings sit
at `σ_ATM + BF`, so `BF` reads directly as the distance of either wing from the ATM
pillar. -/
theorem fxSmileButterfly_eq_sub_of_even {v : ℝ → ℝ} (heven : ∀ d, v d = v (-d))
    (Δ atm : ℝ) : fxSmileButterfly v Δ atm = v Δ - atm := by
  simp only [fxSmileButterfly]
  rw [← heven Δ]
  ring

/-- **The butterfly is the wing midpoint above the ATM pillar**: `BF ≥ 0` exactly when the
ATM volatility does not exceed the midpoint of the two wing volatilities — the reading of
the quote as the smile's convexity at the wings. -/
theorem fxSmileButterfly_nonneg_iff (v : ℝ → ℝ) (Δ atm : ℝ) :
    0 ≤ fxSmileButterfly v Δ atm ↔ atm ≤ (v Δ + v (-Δ)) / 2 := by
  unfold fxSmileButterfly
  constructor <;> intro h <;> linarith

/-! ## The flat slice: delta strikes in `(k, w)` coordinates -/

/-- **The `Φ(z)`-delta strike on the flat slice**: the log-strike `k = w/2 − √w·z` at which
the flat (single-volatility) call's driftless forward delta is `Φ(z)` — the strike an FX
quote names through its delta. On the flat slice `d₊` is affine in `k` with slope `−1/√w`,
so the parametrization by `z` (equivalently by `Φ(z) ∈ (0, 1)`) is a bijection; see
`dpl_fxDeltaStrike`, `fxDelta_eq_iff`, `existsUnique_fxDelta_eq`. -/
noncomputable def fxDeltaStrike (w z : ℝ) : ℝ := w / 2 - Real.sqrt w * z

/-- **The flat-slice delta is `Φ(d₊)`** (BRSD eq. (4), the driftless forward delta): the
spot derivative of the zero-rate call at spot `S = F`, strike `K = F·e^k`, volatility `σ`,
maturity `T` is `Φ(dpl k w)` with total variance `w = σ²T`. This is the library's delta
(`hasDerivAt_bsV_S`) read in the smile's `(k, w)` coordinates — the bridge through which
the quoting conventions above rest on the Black–Scholes delta. -/
theorem fxFlatCall_delta {F k σ T : ℝ} (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < T) :
    HasDerivAt (fun S ↦ bsV (F * Real.exp k) 0 σ S T) (Phi (dpl k (σ ^ 2 * T))) F := by
  have hK : 0 < F * Real.exp k := by positivity
  have h := hasDerivAt_bsV_S (r := 0) hK hσ hF hT
  convert h using 1
  rw [bsd1_eq_dpl hF.ne' hσ hT]

/-- The delta strike lands on its delta: `d₊` at `fxDeltaStrike w z` is `z`. -/
theorem dpl_fxDeltaStrike {w z : ℝ} (hw : 0 < w) : dpl (fxDeltaStrike w z) w = z := by
  have hs : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  unfold dpl fxDeltaStrike
  field_simp
  ring

/-- The parametrization by `z` is a bijection: `Φ(d₊(k, w)) = Φ(z)` exactly at the delta
strike `k = w/2 − √w·z`. With `strictMono_Phi` this is the uniqueness of the delta strike
on the flat slice. -/
theorem fxDelta_eq_iff {w z k : ℝ} (hw : 0 < w) :
    Phi (dpl k w) = Phi z ↔ k = fxDeltaStrike w z := by
  have hs : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  constructor
  · intro h
    have hd : dpl k w = z := strictMono_Phi.injective h
    unfold dpl at hd
    unfold fxDeltaStrike
    field_simp at hd
    linarith
  · intro h
    rw [h, dpl_fxDeltaStrike hw]

/-- **The delta strike exists and is unique**: for every level `Δ ∈ (0, 1)` and total
variance `w > 0` there is exactly one flat-slice log-strike whose call carries driftless
forward delta `Δ` — the `w/2 − √w·Φ⁻¹(Δ)` of `fxDeltaStrike`. On a non-flat smile the same
statement is the smile's no-butterfly-arbitrage property and is not proved here. -/
theorem existsUnique_fxDelta_eq {w : ℝ} (hw : 0 < w) {Δ : ℝ} (hΔ : Δ ∈ Set.Ioo 0 1) :
    ∃! k : ℝ, Phi (dpl k w) = Δ :=
  ⟨fxDeltaStrike w (PhiInv Δ), by
    change Phi (dpl (fxDeltaStrike w (PhiInv Δ)) w) = Δ
    rw [dpl_fxDeltaStrike hw]
    exact Phi_PhiInv hΔ, by
    intro k hk
    refine (fxDelta_eq_iff hw).1 ?_
    rw [hk]
    exact (Phi_PhiInv hΔ).symm⟩

/-- **The `Δ`-call and `Δ`-put strikes are reflections about the ATM strike**: their
log-strikes sum to `w`, so both sit at distance `√w·|Φ⁻¹(Δ)|` from the delta-neutral-straddle
ATM strike `w/2` (BRSD eq. (5): `K_ATM = F·e^{σ²_ATM τ/2}`). The `Δ`-put wing is read
through `Φ(d₊) = 1 − Δ` — at a common strike the driftless put delta is the call delta
minus one, the parity identity of the BRSD eq. (4) deltas, not formalized here; the
reflection itself is the `Φ⁻¹(1 − Δ) = −Φ⁻¹(Δ)` symmetry. -/
theorem fxDeltaStrike_call_add_put {w : ℝ} {Δ : ℝ} (hΔ : Δ ∈ Set.Ioo 0 1) :
    fxDeltaStrike w (PhiInv Δ) + fxDeltaStrike w (PhiInv (1 - Δ)) = w := by
  rw [PhiInv_one_sub hΔ]
  unfold fxDeltaStrike
  ring

/-- The delta-neutral-straddle ATM strike is the `1/2`-delta point: `fxDeltaStrike w 0` is
the log-strike `w/2` of BRSD eq. (5), and `fxAtmStrike_delta` below says its delta is
exactly `1/2`. -/
theorem fxDeltaStrike_zero (w : ℝ) : fxDeltaStrike w 0 = w / 2 := by
  unfold fxDeltaStrike
  ring

/-- **The ATM pillar's delta is exactly `1/2`** — the delta-neutral straddle convention:
at the ATM strike the call carries driftless forward delta `1/2` (and the put, read
through the same `Φ(d₊)`, carries `−1/2`). -/
theorem fxAtmStrike_delta {w : ℝ} (hw : 0 < w) :
    Phi (dpl (fxDeltaStrike w 0) w) = 1 / 2 := by
  rw [dpl_fxDeltaStrike hw, Phi_zero]

/-- **The at-the-money-forward point is not the delta-neutral point**: at `k = 0` (strike
equal to the forward) the flat call's delta is `Φ(√w/2)`, strictly above `1/2` for
`w > 0` — the displacement `w/2` of the market's ATM strike from the forward, which is why
the ATM pillar is quoted at its own strike rather than read off a fixed delta. -/
theorem fxForwardPoint_delta_gt_half {w : ℝ} (hw : 0 < w) : 1 / 2 < Phi (dpl 0 w) := by
  have hsq : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have hpos : (0:ℝ) < Real.sqrt w / 2 := by linarith
  have hd : dpl 0 w = Real.sqrt w / 2 := by rw [dpl_eq, neg_zero, zero_div, zero_add]
  rw [hd, ← Phi_zero]
  exact Phi_lt_Phi hpos

/-- **The out-of-the-money call wing sits above the ATM strike**: for a level `Δ < 1/2`
the `Δ`-call strike is strictly beyond the ATM strike `w/2` (and, by
`fxDeltaStrike_call_add_put`, the `Δ`-put strike strictly below it) — the market picture of
the two wings straddling the ATM pillar. -/
theorem fxDeltaStrike_call_gt_atm {w : ℝ} (hw : 0 < w) {Δ : ℝ}
    (hΔ : Δ ∈ Set.Ioo 0 1) (h : Δ < 1 / 2) : w / 2 < fxDeltaStrike w (PhiInv Δ) := by
  have hnzi : PhiInv Δ ≠ 0 := by
    intro h0
    have h1 : Δ = 1 / 2 := by
      have hpp := Phi_PhiInv hΔ
      rw [h0, Phi_zero] at hpp
      exact hpp.symm
    linarith
  have hneg : PhiInv Δ < 0 := by
    rcases lt_or_ge (PhiInv Δ) 0 with hn | hp
    · exact hn
    · exfalso
      have hc : 0 < PhiInv Δ := lt_of_le_of_ne hp (Ne.symm hnzi)
      have hlt := (PhiInv_pos_iff hΔ).1 hc
      linarith
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have hmul : Real.sqrt w * PhiInv Δ < 0 := mul_neg_of_pos_of_neg hs hneg
  unfold fxDeltaStrike
  linarith

end MathFin

