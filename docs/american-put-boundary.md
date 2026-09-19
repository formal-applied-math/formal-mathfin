# American put option exercise-boundary convexity

This contribution addresses [issue #175](https://github.com/formal-applied-math/formal-mathfin/issues/175)
in the constant-parameter Black–Scholes model. For strike `K > 0`, risk-free
interest rate `r > 0`, volatility `σ > 0`, and dividend yield `0 ≤ q ≤ r`, it
proves, on positive time-to-expiry:

- convexity of `τ ↦ log(B(τ) / K)`;
- strict convexity of the stock-price exercise boundary `τ ↦ B(τ)`.

These are geometric, chord-inequality statements. The contribution does not
assert classical boundary second derivatives, strictly positive logarithmic
curvature, or convexity when `q > r`.

**This resolves an open problem.** `docs/open-problems.md` Tier 1 §1 recorded
`0 < q < r` as open in the literature: convexity was proved at `q = 0`
(Chen–Chadam–Cheng–Saunders; Ekström) and disproved for `q > r`. The theorems
below cover `0 ≤ q ≤ r`, the whole open region and both endpoints, and the proof
is machine-checked and axiom-clean.

**A second, conditional development also ships here.** About 36 of the 173 modules
(~3,500 lines) reach neither headline theorem: the six `Stopping/Classical*` modules
and `Boundary/{NearExpiry, IncrementPositivity, StrictBoundarySpeed, FlatTail,
StockConclusion, …}`. They are stated over an assumed classical solution
`Boundary.DividendPutSolution`, a 17-field structure that **nothing in this port shows
inhabited**, and they terminate in `Stopping/ClassicalBridge.lean`'s
`brownian_boundary_curvature_of_price_identification`, whose own docstring names
`hprice` an outstanding verification obligation. Results on that track — including
`brownianUsual_boundary_conclusions`, the only `B'' > 0` statement in the tree — are
therefore of unknown vacuity. The two headline declarations carry no such hypothesis
and route around the track entirely; that is the point of the stopping-value
construction. The source development's classical-regularity results are present in the
import closure but are **not claimed by these two entries**.

## Public declarations and benchmark entries

Import [`MathFin.BlackScholes.AmericanPut.Stopping.PhysicalBoundaryConvexity`](../MathFin/BlackScholes/AmericanPut/Stopping/PhysicalBoundaryConvexity.lean).
Both principal declarations are in namespace
`MathFin.BlackScholes.AmericanPut.Stopping`:

| Declaration | Conclusion | Benchmark ID |
|---|---|---|
| `brownianUsualLogBoundary_convexOn` | `ConvexOn ℝ (Set.Ioi 0) (fun τ : ℝ => Real.log (brownianUsualExerciseBoundary K r q σ τ.toNNReal / K))` | `mf-american-put-log-boundary-convex` |
| `brownianUsualStockBoundary_strictConvexOn` | `StrictConvexOn ℝ (Set.Ioi 0) (fun τ : ℝ => brownianUsualExerciseBoundary K r q σ τ.toNNReal)` | `mf-american-put-stock-boundary-strict-convex` |

Each has exactly the parameter hypotheses `0 < K`, `0 < r`, `0 ≤ q`,
`q ≤ r`, and `0 < σ`. Neither assumes a classical pricing solution,
smoothness of the exercise boundary, or an interval-preservation property.
`τ.toNNReal` makes the function total; the theorem's domain restricts it to
strictly positive real time-to-expiry, where the conversion does not change time.

## Which boundary is proved convex?

The following files are under `MathFin/BlackScholes/AmericanPut/Stopping/`.

1. `Rules.lean`, `Reward.lean`, and `AmericanValue.lean` define the value as
   a supremum of expected discounted put payoffs over **all** stopping times
   of the specified filtration that are pointwise bounded by the horizon.
   The stock is explicit GBM with drift `r-q`, volatility `σ`, and initial
   value `S`; discounting uses `r`. No exercise grid or family of candidate
   hitting times replaces that supremum. `AEHorizonValue.lean` proves
   `aeAmericanPutValue_eq` and `aeExerciseThreshold_eq`: allowing extended
   stopping times bounded by the horizon only almost surely gives exactly
   the same value and threshold, by clipping on the exceptional null set.
2. `UsualBrownianValue.lean` instantiates the value with the constructed
   Brownian process, the completed Gaussian probability measure, and its
   completed, null-augmented, right-continuous natural filtration.
   `ExerciseRegion.lean` defines the boundary as the supremum of payoff-contact
   stock prices in `[0,K]`.
3. `CanonicalPrice.lean` and `StrictExerciseGeometry.lean` specialize
   these stopping objects to strike one and volatility `sqrt 2`.
   `PositiveExerciseBoundary.lean` proves a positive lower bound before
   defining `canonicalLogBoundary`; it also identifies payoff contact with
   being below that boundary. Thus the logarithm is not masking a zero
   exercise threshold.
4. `ActualLogConvexity.lean` proves `canonicalLogBoundary_convexOn` from the
   actual stopping price. `ActualBoundaryNormalization.lean` proves the
   physical/canonical boundary identity from price normalization and payoff
   contact; it does not introduce an assumed free-boundary solution.

This is a result for the explicitly constructed Brownian probability space
and filtration. The principal declarations do not quantify over arbitrary
probability-space representations of Black–Scholes. Auxiliary conditional
verification theorems elsewhere in the import closure should not be confused
with assumptions of these two declarations.

## Proof sketch

Normalize `x = log(S/K)` and `t = σ²τ/2`, writing `k = 2r/σ²`,
`h = 2q/σ²`, and `α = k-h-1`. For a decreasing line `ℓ(t) = d-ct`,
construct a pricing-equation solution

\[
\widehat p(x,t)=f(x-\ell(t))-e^x g(x-\ell(t)).
\]

The two constant-coefficient ODE profiles treat the constant and exponential
parts of the payoff separately. Their initial conditions impose value
matching and smooth fit on the line. A nonnegative forcing term, using
`k ≥ h`, makes this comparison dominate the payoff below the strike.

Dividing the price difference by the positive profile `f` removes the
zero-order term from its parabolic equation. A Riccati identity gives the
initial difference interval-shaped positive superlevel sets. A three-point
maximum argument preserves that property: at a violating maximum the three
spatial first derivatives vanish, so the drift drops out and the time
derivative signs contradict one another.

An explicit terminal rectangle barrier then excludes a boundary contact
between two times when the actual boundary lies below the comparison line.
This time-interval property, the near-expiry estimate, and nonincrease of the
boundary give the chord inequality for the logarithmic boundary. A separate
no-flat-tail barrier yields strict decrease; strict convexity of the
exponential gives strict convexity of `B`. No second derivative of the
exercise boundary is required for these geometric conclusions.

## Verification and provenance

The canonical build command is `lake build`. The two short, explicit
consumer statements live in
[`benchmarks/american_put_boundary.json`](../benchmarks/american_put_boundary.json).
The repository's [contribution checklist](../CONTRIBUTING.md) governs the
regression tests, generated axiom audit and freshness-tracked
[`verification_ledger.json`](../verification_ledger.json). A successful
source-development audit is not a substitute for checking this port against
MathFin's pinned toolchain and dependencies. Kernel validation of formal
statements and correspondence with the intended financial model remain
distinct checks.

The port was checked natively with the repository's pinned Lean 4.32.0,
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, and BrownianMotion
`4d52fa776130a29d4ad7d6eda2035a919c0b4696`. No Docker or dependency upgrade
was needed. An explicit `lake env lean` probe reported the following axiom
set for each of `brownianUsualLogBoundary_convexOn`,
`brownianUsualStockBoundary_strictConvexOn`, `aeAmericanPutValue_eq`, and
`aeExerciseThreshold_eq`:

```text
[propext, Classical.choice, Quot.sound]
```

These checks are also pinned by `#guard_msgs` in `MathFin/AxiomAudit.lean`.
Some imported BrownianMotion modules have existing `sorry` warnings; the
reported dependency sets show those gaps are not dependencies of these four
theorems. This is an axiom audit, not a new full-proof-closure kernel replay.

The native default `lake build` completed successfully (9,178 jobs), including
both axiom-audit modules and otherwise unimported library leaves. The two
intentional `sorry` declarations in the repository's pre-existing Comparator
`Challenge.lean` are statement placeholders, not dependencies of these results.

The two benchmark re-export statements were then checked with the ledger's
native execution mode, at proof commit `e986c38`:

```sh
LEDGER_EXEC_LOCAL=1 python -m tools.verify.ledger verify --exec
python -m tools.verify.ledger status
python -m pytest tests/ -q
```

Results: two new entries verified, zero failures; 371 fresh ledger entries,
zero stale or missing; 49 tests passed and one skipped. Python tests used an
isolated native virtual environment. `formalization.yaml` and the generated
axiom audit also passed their freshness checks. These local checks do not
claim a fresh-runner CI result.

Ported from Robert Martin's
[`AmericanPutConvexity`](https://github.com/robertmartin8/AmericanPutConvexity/tree/9b2b208520341a63b64eef43c1ecb3c5708a8e63)
development (Apache-2.0), with the manuscript *Log-convexity of the exercise
boundary of an American put option*. The proof and formalization were
substantially AI-assisted: the author reports development with ChatGPT-6 Pro
(Astra), checking with Fable 5.1, and Lean formalization primarily with
gpt-6-astra-high in Codex. Those reports are provenance, not independent
peer review or new verification evidence for this port. MathFin, Mathlib,
and the BrownianMotion library supply underlying financial, analytic and
probabilistic infrastructure.
