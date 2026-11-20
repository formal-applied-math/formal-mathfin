# Convexity of the American put exercise boundary

Reference page for the American put results in `MathFin/Models/BlackScholes/American/`. In the
constant-parameter Black–Scholes model, with strike `K > 0`, risk-free rate `r > 0`, volatility
`σ > 0` and dividend yield `0 ≤ q ≤ r`, the early-exercise boundary of the American put is convex in
the time to expiry `τ > 0`, in two forms: its logarithm is convex, and the boundary itself is
strictly convex.

These are chord-inequality statements. The development does not assert classical second
derivatives of the boundary, strictly positive logarithmic curvature, or convexity when `q > r`.

[`open-problems.md`](open-problems.md) (Tier 1, §1) records the case `0 < q < r` as open in the
literature and these theorems as covering it: convexity was known at `q = 0` (Chen–Chadam–Cheng–Saunders;
Ekström) and fails for `q > r`. The statements below include both endpoints `q = 0` and `q = r`.

## Statements

Import `MathFin.Models.BlackScholes.American.Stopping.PhysicalBoundaryConvexity`. The declarations
are in the namespace `MathFin.BlackScholes.AmericanPut.Stopping`, and each has exactly the
hypotheses `0 < K`, `0 < r`, `0 ≤ q`, `q ≤ r`, `0 < σ`.

```lean
theorem brownianUsualLogBoundary_convexOn {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ) :
    ConvexOn ℝ (Ioi 0)
      (fun τ : ℝ => Real.log (brownianUsualExerciseBoundary K r q σ τ.toNNReal / K))

theorem brownianUsualStockBoundary_strictConvexOn {K r q σ : ℝ}
    (hK : 0 < K) (hr : 0 < r) (hq : 0 ≤ q) (hqr : q ≤ r) (hσ : 0 < σ) :
    StrictConvexOn ℝ (Ioi 0)
      (fun τ : ℝ => brownianUsualExerciseBoundary K r q σ τ.toNNReal)
```

`τ.toNNReal` makes the function total; the domain is strictly positive real time, where the
conversion does not change time. Corpus entries: `mf-american-put-log-boundary-convex` and
`mf-american-put-stock-boundary-strict-convex`
([`benchmarks/american_put_boundary.json`](../benchmarks/american_put_boundary.json)). The module
also proves strict decrease and local Lipschitz continuity of the boundary, and the convexity
results for `q = 0` and for `q + σ²/2 ≤ r` under their own hypotheses.

`aeAmericanPutValue_eq` and `aeExerciseThreshold_eq` (`Stopping/AEHorizonValue.lean`) show that
allowing stopping times bounded by the horizon only almost surely gives the same value and
threshold, by clipping on the exceptional null set.

## Definitions: which boundary is convex

The files below are under `MathFin/Models/BlackScholes/American/Stopping/`.

* `Rules.lean`, `Reward.lean` and `AmericanValue.lean` define the value `americanPutValue` as a
  supremum of expected discounted put payoffs over all stopping times of the filtration bounded by
  the horizon. The stock is geometric Brownian motion with drift `r − q` and volatility `σ`, and
  discounting uses `r`. No exercise grid replaces the supremum.
* `UsualBrownianValue.lean` instantiates the value with the constructed Brownian process, the
  completed Gaussian measure and its completed, null-augmented, right-continuous natural
  filtration. `brownianUsualExerciseBoundary` is the `exerciseThreshold` of that value, the
  supremum of the payoff-contact stock prices in `[0,K]` (`ExerciseRegion.lean`).
* `CanonicalPrice.lean` and `StrictExerciseGeometry.lean` specialise to strike one and volatility
  `√2`. `PositiveExerciseBoundary.lean` proves a positive lower bound before defining
  `canonicalLogBoundary`, so the logarithm does not mask a zero threshold.
* `ActualLogConvexity.lean` proves `canonicalLogBoundary_convexOn` from the actual stopping price,
  and `ActualBoundaryNormalization.lean` identifies the physical and canonical boundaries from
  price normalisation and payoff contact.

The result is for the explicitly constructed Brownian space and filtration; it does not quantify
over arbitrary probability-space representations of Black–Scholes.

## Proof sketch

Normalise `x = log(S/K)` and `t = σ²τ/2`, with `k = 2r/σ²`, `h = 2q/σ²` and `α = k − h − 1`. For a
decreasing line `ℓ(t) = d − ct`, construct a solution of the pricing equation
`p̂(x,t) = f(x − ℓ(t)) − eˣ g(x − ℓ(t))`. The two constant-coefficient ODE profiles treat the
constant and exponential parts of the payoff separately, and their initial conditions impose value
matching and smooth fit on the line. A nonnegative forcing term, using `k ≥ h`, makes `p̂` dominate
the payoff below the strike.

Dividing the price difference by the positive profile `f` removes the zero-order term from its
parabolic equation. A Riccati identity gives the initial difference interval-shaped positive
superlevel sets, and a three-point maximum argument preserves that property: at a violating
maximum the three spatial first derivatives vanish, so the drift drops out and the time-derivative
signs contradict one another. A terminal rectangle barrier then excludes a boundary contact
between two times when the actual boundary lies below the comparison line. This interval property,
the near-expiry estimate and the monotonicity of the boundary give the chord inequality for the
logarithm. A separate no-flat-tail barrier gives strict decrease, and strict convexity of the
exponential gives strict convexity of `B`.

## Scope

A second development in the same directory is conditional. The boundary-geometry modules
(`Boundary/NearExpiry`, `IncrementPositivity`, `StrictBoundarySpeed`, `FlatTail`,
`StockConclusion`, and others) and the PDE-facing `Stopping/Classical*` modules are stated over an
assumed classical solution `Boundary.DividendPutSolution`. That structure extends
`ContinuousBoundaryPutSolution`, which the actual stopping price is proved to satisfy
(`canonicalPrice_continuousBoundaryPutSolution`), so the one field no declaration shows inhabited
is `boundary_smooth`, the smoothness of the boundary at positive times. The conditional track ends
in `brownian_boundary_curvature_of_price_identification` (`Stopping/ClassicalBridge.lean`), whose
docstring names its hypothesis `hprice` an outstanding verification obligation. Results there,
including `brownianUsual_boundary_conclusions`, the only `B'' > 0` statement in the tree, are of
unknown vacuity. The two headline declarations carry no such hypothesis and do not depend on the
conditional track. The landmark entry in [`landmarks.toml`](landmarks.toml) separately records the
verification principle `value_eq_of_attained`, in which the supermartingale is a hypothesis.

## Verification

`lake build` is the canonical check. The generated axiom audit (`MathFin/AxiomAuditGen.lean`) and
`MathFin/AxiomAudit.lean` pin the axioms of `brownianUsualLogBoundary_convexOn`,
`brownianUsualStockBoundary_strictConvexOn`, `aeAmericanPutValue_eq` and
`aeExerciseThreshold_eq` to `[propext, Classical.choice, Quot.sound]`. Some BrownianMotion modules
carry `sorry` warnings; none is a dependency of these four theorems. This is an axiom audit, not a
kernel replay of the full closure. The two corpus entries are tracked by the verification ledger.

## Provenance

Ported from Robert Martin's
[AmericanPutConvexity](https://github.com/robertmartin8/AmericanPutConvexity), Apache-2.0, with the
manuscript *Log-convexity of the exercise boundary of an American put option*; the modules carry
his name in their headers. The author reports that the proof and formalization were substantially
AI-assisted (ChatGPT-6 Pro (Astra) for the proof, Fable 5.1 for checking, gpt-6-astra-high in
Codex for the Lean). Those reports are provenance, not independent review or verification
evidence. See [`sources.md`](sources.md).
