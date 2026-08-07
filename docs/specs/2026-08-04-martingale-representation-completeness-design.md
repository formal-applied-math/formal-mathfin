# Design: martingale representation and continuous-time market completeness

- **Date:** 2026-08-04
- **Status:** approved design, pre-implementation
- **Author:** Raphael Coelho
- **Topic:** the martingale representation theorem on the Brownian filtration,
  stated as a **surjectivity** theorem for the Itô integral, and its finance
  reading: completeness of the continuous-time market and uniqueness of the
  equivalent martingale measure.

## 1. Goal

Two statements, one theorem.

**Analytic form (the artifact).** With `I := itoIntegralCLM_T hB T hBmeas` the
continuous Itô integral, already a `LinearIsometry` out of the predictable
`L²(dt ⊗ dμ)`:

> `I` is **surjective onto the centered part of `L²(Ω, 𝓕_T^B, μ)`**. Equivalently,
> every square-integrable `𝓕_T`-measurable `F` decomposes uniquely as
> `F =ᵐ 𝔼[F] + I(φ)`.

The Itô isometry is upgraded from an isometry to a **unitary**, bundled as a
`LinearIsometryEquiv` onto centered `lpMeas ℝ ℝ (𝓕 T) 2 μ`.

**Finance form (the crown).** The continuous-time Black–Scholes market is
**complete**: every `L²` contingent claim on `𝓕_T` is replicated by a
self-financing strategy whose initial cost is the risk-neutral price, and the
equivalent martingale measure is therefore unique.

The corpus entry `gir-thm-9.3.4` currently encodes the martingale representation
theorem as a structure whose conclusion is a `Prop` field, read off by
projection. It is `reduced_core` for exactly that reason. This design replaces it
with a derivation.

## 2. Why this, and why now

The library has the first fundamental theorem in discrete and continuous form,
and the Girsanov ladder up to bounded predictable `θ`, so the equivalent
martingale measure is *constructed*. What is missing is the other half: that it
is the *only* one, and that the price it assigns is attainable rather than merely
consistent. Completeness is the statement that makes a price a hedge.

The second fundamental theorem exists in the library only in
`Binomial/SecondFTAP.lean`, single-period and two-state. Everything continuous
stops at existence.

Structurally, martingale representation is the converse of what the Itô tower
already proves. `itoIntegralCLM_T` is an isometry out of a complete space, so its
range is closed for free; the entire theorem is the assertion that this closed
range, plus the constants, exhausts `L²(𝓕_T)`. That is the reusable abstraction
this tower has been missing, and it is the shape a Mathlib maintainer would ask
for.

## 3. Scope — locked decisions

- **Driver:** `IsPreBrownianReal B μ` with measurable evaluations and continuous
  paths, `IsProbabilityMeasure μ`, bounded horizon `[0,T]`. The tower's standard
  setting; identical hypotheses to `ito_formula_expBrownian`.
- **Filtration:** `ItoIntegralL2.natFiltration hBmeas`, the natural Brownian
  filtration already carried by `trimMeasure_T`. No augmentation beyond what the
  tower uses.
- **Measurability idiom:** `lpMeas ℝ ℝ (𝓕 T) 2 μ` — Mathlib's own subspace of
  `Lp` functions a.e.-strongly-measurable with respect to a sub-σ-algebra. We do
  not invent a predicate for "`F` is `𝓕_T`-measurable in `L²`".
- **Both forms are in scope.** The corpus entry is stated in *process* form
  (`M_t = M₀ + ∫₀ᵗ φ_s dB_s` for all `t`), so the terminal form alone would not
  honestly flip it. The terminal form is the engine; the process form is obtained
  by conditioning it, using the existing `ItoIntegralProcess*` layer.
- **Strategy class for completeness:** the Itô-integrable predictable class, a
  deliberate enlargement of `ContinuousMarket.SimpleStrategy`. Replication of a
  general `L²` claim is not achievable with piecewise-constant holdings, so this
  extension is forced by the mathematics, not chosen. It is additive: the simple
  class and its no-arbitrage predicate are untouched.

### Out of scope, named

- **Multi-dimensional martingale representation** (vector Brownian driver). The
  one-dimensional result is the theorem; the `d`-asset version waits on the
  two-process Itô formula (`sc-thm-7.5.2`).
- **The converse direction of the second FTAP** — uniqueness of the EMM implying
  completeness. That needs extreme-point / Jacod–Yor arguments on the set of
  martingale measures and is a separate project. We deliver
  `complete ⟹ EMM unique` and say so in the module docstring, in the same idiom
  `ContinuousMarket.lean` uses to draw its Delbaen–Schachermayer boundary.
- **`L¹` / `H¹` martingale representation**, and the Clark–Ocone formula, which
  needs Malliavin calculus.
- **Novikov (`gir-thm-9.1.7`) and Lévy's characterization (`sc-thm-9.1.1`)**.
  Issue #49 bundles the latter with martingale representation under the heading
  "adapted-integrand Itô consequences". That framing is wrong for our route:
  representation on the Brownian filtration is a Hilbert-space totality theorem
  and needs no general Itô formula, whereas Lévy's characterization genuinely
  needs continuous local martingales with pathwise quadratic variation. Splitting
  #49 is the first deliverable of this program.

## 4. The mathematical spine

Let `F ∈ L²(μ)` be `𝓕_T`-measurable with `𝔼[F] = 0` and `F ⊥ range I`. The
theorem is `F = 0`.

| step | content | status |
|---|---|---|
| S0 | `range I` is closed | free: `I` is an isometry out of a complete space |
| S1 | `exp(σB_T − ½σ²T) − 1 ∈ range I` for constant `σ` | **already proven** — `ItoFormulaGBM.discountedGBM_eq_itoIntegral` at `S₀ = 1`, with `ItoIntegralBrownian.eval_zero_ae` |
| S2 | `E(h)_T − 1 ∈ range I` for deterministic step `h` | **new, the crux** — §5 |
| S3 | `F ⊥ {E(h)_T}` gives `𝔼[F·exp(Σⱼ λⱼ B_{tⱼ})] = 0` for all `λ ∈ ℝⁿ` | algebra: `∫h dB = Σ hᵢ ΔBᵢ`, Abel summation, and `exp(−½∫h²)` is a positive constant |
| S4 | hence `𝔼[F ∣ σ(B_{t₁},…,B_{tₙ})] = 0` | split `F = F⁺ − F⁻`, compare the pushforward measures on `ℝⁿ` by their moment generating functions; `F ∈ L²` and `exp⟨λ,X⟩ ∈ L^p` for all `p` make `integrableExpSet = univ` |
| S5 | hence `F = 0` | Lévy's upward theorem along `𝓖ₙ = σ(B_q : q ∈ Qₙ)`, with `⨆ₙ 𝓖ₙ = 𝓕_T` from path continuity |
| S6 | process form `M_t = M₀ + ∫₀ᵗ φ dB` for all `t` | condition the terminal form; `ItoIntegralProcess*` carries the integral process |
| S7 | completeness, EMM uniqueness, superreplication equality | §6 |

Upstream availability for S4 and S5 was checked against the pinned Mathlib, not
assumed: `Measure.ext_of_charFun` and `Probability/Moments/ComplexMGF.lean` for
S4, `Integrable.tendsto_ae_condExp` and `Integrable.tendsto_eLpNorm_condExp`
(named "Lévy's upward theorem" in the source) for S5.

## 5. The crux: S2

`E(h)_T` for a step `h = Σ hₖ·1_{(tₖ,tₖ₊₁]}` telescopes into cell factors
`E_{k+1} − E_k = E_k·(exp(hₖ ΔBₖ − ½hₖ²Δtₖ) − 1)`. S1 gives each parenthesis as
an Itô integral over its cell. What is missing is the right to pull the
`𝓕_{tₖ}`-measurable factor `E_k` inside:

> **`𝓕_a`-linearity of the Itô integral.** For `a ≤ b ≤ T` and `Z` bounded and
> `𝓕_a`-measurable, `Z · I(φ·1_{(a,b]}) = I(Z·φ·1_{(a,b]})`.

This is the local property of the stochastic integral. It is proved on simple
integrands, where it is the definition, and extended by density and continuity —
the tower's established pattern, the same one `itoIntegralCLM_T` itself was built
by. `E_k` is lognormal rather than bounded, so it is reached by truncation, for
which `ItoIntegralBrownian.clampM` already exists.

Worth building on its own terms: `𝓕_a`-linearity is a general structural fact
about the stochastic integral, not an artifact of this proof, and nothing else in
the tower currently has it.

**Fallback if it resists.** Generalize `ito_formula_itoProcess` from constant
`(b,σ)` to piecewise-constant `(b,σ)` and read S2 off directly. Comparable work,
strictly less reusable, so it is the fallback rather than the plan.

## 6. The finance layer (S7)

Three consequences, in increasing order of what they cost.

1. **Completeness.** Every `L²` claim `H` on `𝓕_T` is replicable: the
   representation integrand of the martingale `t ↦ 𝔼_Q[e^{−r(T−t)}H ∣ 𝓕_t]` is
   the hedge ratio, and the initial value is the risk-neutral price. The hedge
   becomes a theorem rather than a definition.
2. **EMM uniqueness.** If every claim is replicable then any two equivalent
   martingale measures agree on every claim, hence agree. Cheap once (1) holds,
   and it lands directly on `ContinuousMarket.IsEMM`.
3. **Superreplication equality, in continuous time.** Replication makes the
   superreplication price equal the EMM price by construction, so the complete
   market satisfies the duality *equality*, not merely the bound.

   This does **not** close issue #39. `SuperhedgingDuality` is a finite-state
   one-period matrix model (`z : Fin M → Fin N → ℝ`), and its open direction is
   gated on a polyhedral Farkas fact that continuous-time completeness has no
   bearing on. What we get is the continuous-time analogue, reached by a
   different route: the finite-state equality needs separation, the complete
   continuous market needs martingale representation. Recording that the same
   duality holds for two structurally different reasons is the coherence
   content; claiming the Mathlib gap is closed would be false.

## 7. Coherence and integration

The point of the program is not one more theorem. Two commitments.

**Consume, do not reprove.** Named dependencies, each of which stays the single
source of its fact:

| step | consumed | not rebuilt |
|---|---|---|
| S0 | `ItoIntegralCovariation.itoIsometry_T` (already a bundled `LinearIsometry`) | a second isometry statement |
| S1 | `ItoFormulaGBM.discountedGBM_eq_itoIntegral` | the exponential Itô formula |
| S2 | `SimpleDoleansExponential` cell scaffolding, `ItoIntegralBrownian.clampM` | a bespoke partition apparatus |
| S4 | Mathlib `ComplexMGF`, `Measure.ext_of_charFun` | any wrapper around them |
| S5 | Mathlib `Integrable.tendsto_eLpNorm_condExp` | a restatement of Lévy upward |
| all | Mathlib `lpMeas` | a hand-rolled "measurable in `L²`" predicate |

S4 runs the same analytic-continuation pattern `GirsanovConstantTheta` already
uses. If the shared content is real, it is extracted to one root and
`GirsanovConstantTheta` is refactored onto it. That makes an existing file
lighter instead of adding a parallel copy, and it is the honest reading of the
anti-wrapper rule.

**Wire the seams.** `docs/mathematical-architecture.md` gets a new bridge row,
and its content is the architectural claim worth making:

> Girsanov wired pillar I ↔ II in the direction of *existence* — the equivalent
> martingale measure as an explicit change of measure. Martingale representation
> wires the same seam in the direction of *uniqueness and attainability*. The two
> together close it.

Also seamed: `Binomial/SecondFTAP.lean` gains its continuous partner, in the same
discrete/continuous pairing `ContinuousFTAP` has with the binomial EMM;
`PricingFromBrownian` and `BSCallHypFromBrownian` gain the statement that their
price is the *unique* arbitrage-free one; `docs/leaps.md` gains Leap 5.

**Repo-complete upgrade**, per the standing rule that a phase is not done until
the whole repo reflects it: `docs/coverage.md` (flip `gir-thm-9.3.4`, add the new
entries), `docs/bridges.md`, `docs/mathematical-architecture.md`,
`docs/roadmap.md`, `docs/leaps.md`, `docs/patterns.md` (dated batch, at minimum
the `𝓕_a`-linearity pattern and the MGF-comparison route to conditional
vanishing), `README.md` counts, `MathFin/AxiomAudit.lean` plus a regenerated
`AxiomAuditGen.lean`, `@[blueprint]` tags, the verification ledger,
`MathFin.lean` umbrella imports, the issue tree, the values review, and memory.

`MathFin.lean` is a single-file bind mount: after editing it, re-sync into any
running container or restart the service, or the daemon keeps serving the old
import list.

## 8. Module layout

One theorem plus private helpers per file, so Lean re-elaborates only what
changed.

| # | module | content |
|---|---|---|
| 1 | `Foundations/BrownianCylinderGeneration.lean` | `⨆ₙ σ(B_q : q ∈ Qₙ) = 𝓕_T` from path continuity (S5's measure-theoretic half) |
| 2 | `Foundations/ItoIntegralLocality.lean` | `𝓕_a`-linearity of the Itô integral over `(a,b]` (S2's crux, reusable) |
| 3 | `Foundations/DoleansStepRepresentation.lean` | `E(h)_T − 1 ∈ range I` for deterministic step `h` (S2, consuming S1) |
| 4 | `Foundations/WienerExponentialTotality.lean` | S3 + S4 + S5: orthogonality to the exponentials forces `F = 0` |
| 5 | `Foundations/MartingaleRepresentation.lean` | the crown: surjectivity, the `LinearIsometryEquiv`, and the process form |
| 6 | `Foundations/MarketCompleteness.lean` | S7: replication, EMM uniqueness, superreplication equality |

## 9. Risks

| risk | mitigation |
|---|---|
| S2's `𝓕_a`-linearity is harder than the density pattern suggests | the piecewise-constant-coefficient Itô formula fallback (§5); it is a scope swap, not a dead end |
| `⨆ₙ σ(B_q) = 𝓕_T` fights `natFiltration`'s `pastProcess` construction | module 1 exists precisely to isolate it; if it resists, restate the totality over the generating family `natFiltration` actually uses |
| type friction between `lpMeas (𝓕 T)` and `trimMeasure_T`'s predictable σ-algebra | keep the two worlds apart: `I`'s domain stays untouched, `lpMeas` appears only on the codomain side |
| memory — 10 GB box, one Lean process | small modules, daemon-only iteration, `lake build` alone in the slot |

## 10. Acceptance

- Every new module builds under `lake build MathFin`, `lake lint` clean.
- `gir-thm-9.3.4` flips `reduced_core → full`, with the ledger row re-verified.
- New corpus entries for the surjectivity theorem and for market completeness.
- Axiom-clean: pinned in `AxiomAudit.lean`, `AxiomAuditGen.lean` regenerated.
- All values gates and `tests/` green; ledger fully fresh.
- The documentation set in §7 updated in the same phase, not deferred.
- A values review run at the close, producing a ranked backlog rather than a
  verdict.
