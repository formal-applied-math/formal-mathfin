# One trunk: every price through the pricing functional

*Design and execution plan, 2026-11-07. Status: accepted; the decisions are recorded in §9. It
supersedes nothing yet.*

[`mathematical-architecture.md`](../mathematical-architecture.md) already names the goal: not more
theorems, but "the theorems organized around the field's actual organizing principles, with the
deep connections made load-bearing." It records the spine as wired: the separating hyperplane under
both the FTAP and the coherent-risk representation, Girsanov as an explicit change of measure,
martingale representation and completeness, and change of numéraire. This plan starts from a
measurement showing that the spine is wired but the library does not grow from it. The pillars are
joined to each other, while the corpus, where the library's claims live, rests almost entirely
beside them. The plan says what the library should look like when it does grow from the spine. It
then gives the order in which to get there, and the gates that keep it there. It allows changing
module structure, definitions and corpus statements.

## 1. Where the library stands (measured 2026-11-07, main at `27f9b677`)

**The corpus does not reach the trunk.** On the program tree's map
(`tools/verify/tree_map.toml`), the 16 trunk nodes are the market and its pricing functional:
no-arbitrage, EMMs, numéraires, state prices, contracts and their value. There are 266 corpus
entries resting deepest on a limb node, and 259 of them rest on a node with no proof-dependency path
to any trunk node:

| limb | off the trunk | largest hubs (entries) |
|---|---|---|
| pricing models | 156 / 163 | `bs_call_formula` 30, `bs_identity` 23, `hasDerivAt_bsV_S` 18, `zcb` 14, `call_eq_integral_bsV` 12 |
| risk | 57 / 57 | `valueAtRisk` 18, `expectedShortfall` 18, Rockafellar–Uryasev 7 |
| choice | 38 / 38 | `portfolioVarN` 11, `kellyFraction` 7, `sharpeRatio` 5, `beta` 5 |
| markets | 5 / 5 | — |
| insurance | 3 / 3 | `survivalFunction` 3 |

**There is no single pricing functional.** Five parallel objects price claims:

- `statePricePricing` (a finite `q`-sum);
- `Contract.value` and `Contract.valueDisc` (integrals against *any* measure; an EMM enters only as a
  hypothesis of individual lemmas);
- `numeraireMeasure` (a density change);
- `superReplicationPrice` (an infimum over Itô strategies);
- `PricesGainsAtZero` (a predicate standing in for `IsEMM` on Brownian filtrations).

The finite and discrete EMM notions are proved to agree (`hasEMMMultiState_iff_exists_isEMM`,
`isEMM_one_iff_onePeriod`). The continuous-time ones are linked in one direction only
(`measure_eq_of_density`). Outside `Foundations/`, about 15 files use `IsEMM`, `NoArbitrage`,
`numeraireMeasure` or `statePricePricing`. None of the 15 most-imported Foundations modules is a
trunk module. They are the Gaussian and Itô toolkit (`GaussianMoments` 16, `NormalQuantile` 11,
`StandardNormal` 9, …).

**Prices are defined as closed forms.** About 20 Black–Scholes price functions exist:

- `bsV` is the hub;
- `bsP`, `bsVDiv`, `bsVGarman` and `margrabePrice` are proved equal to it;
- `stulzCallMax`, `ptDownOutCall`, `mertonDigitalPrice` and the cash digitals are bare.

`bs_call_formula` is a Gaussian integral under `BSCallHyp`, which says only that some `Z` is
`N(0,1)` under some `Q`. Of the 805 corpus entries:

- 48 cite `bsV`;
- 121 cite `bsV`, `bs_call_formula`, `bsd1`, `bsd2` or `Phi`;
- 12 cite both a closed form and a trunk object.

`bsV`'s docstring calls it "the Black–Scholes call price" with no condition, and at `τ = 0` it
evaluates to `(S − K)/2`, because `bsd1` divides by `σ√0` and Lean's `x/0 = 0` gives `Phi 0 = ½`.
The same pattern is in rates: `zcb r t T = exp(−r(T−t))` is a flat-rate function with 14 entries
on it. There are at least eight bond-price objects, four discount factors and six survival
functions.

**The Black–Scholes theorem is not stated.** Its pieces are all proved:

- `discountedGBM_isEMM` and `bs_discounted_isEMM` give the risk-neutral and Girsanov EMMs.
- `value_europeanCall_pathAssets` gives `Contract.value = bsV` under a pre-Brownian `μ`.
- `BlackScholesPhysical` moves the value between measures.
- `europeanCall_deltaHedge` and `europeanCall_selfFinancing` give the hedge.
- `measure_eq_of_density` gives uniqueness among measures with an `L²` density.
- `superReplication_eq_emm_price` and `exists_replicating_strategy_in_price` give completeness.

What is missing is the statement that joins them: in the Black–Scholes market, every pricing
measure gives the call the value `bsV`, and so does the superreplication price. That statement is
the 1973 result. `bs_call_formula` is its last computational step.

**The templates exist.** Some of the library is already built the right way, and these modules
show how:

- `valueDisc_caplet_black76` (Black's formula through the forward measure);
- `valueDisc_payerSwaption_black` and the CMS family (swap-annuity measure);
- `valueDisc_fixedFlows_{vasicek,hullWhite,gsr,hjm}` and Jamshidian (a short-rate discount under
  `Q`);
- `value_cdsBuyer_coxDefaultTime` (a CDS as a `Contract` under a Cox default time);
- `Binomial/MultiPeriodFTAP` with `Contracts/Models/Binomial`, where the CRR price is
  `Contract.value` and `exists_hedge_eq_value` proves the hedge capital equals it.

**Some hinges exist but are not on the graph.** `isGreatest_integral_mul_expectedShortfall` is
the dual representation of expected shortfall on a general `Ω`. `coherentRisk_isLUB` is the
finite-`Ω` ADEH representation on the `ConvexDuality` root. `kellyNumeraire_isRiskNeutral` (the
two-outcome case) and `condExp_payoff_eq_quote` (the Glosten–Milgrom quote is a conditional
expectation) are two more. None of them carries a blueprint tag that a corpus hub depends on.

**Directories record history, not concepts.** `Foundations/` (219 modules) holds three different
things:

- the probability toolkit;
- the trunk (FTAPs, `EquivMartingaleMeasure`, `Numeraire`, `StatePrices`, `SuperhedgingDuality`,
  `MarketCompleteness`);
- applied models (`AlmgrenChriss`, `MarketMakingRiccati`, `CarrMadan`, `VarianceSwap*`, copulas,
  `ExtremeValue`).

`Bridges/` holds model results, not only bridges. `BlackScholes/` (302) contains the American put
(171) and SVI (43). `tests/test_architecture.py` enforces that the import graph is *connected*. It
does not enforce a *direction*, so a module satisfies it with one edge to anything.

## 2. Diagnosis

Three causes, each a design decision rather than a missing proof.

**(a) "Price" is not an object.** `Contract.value Q D X c` is an integral against whatever `Q` it
is given, so "the price of `c`" has no type. Whether a value is a price is decided lemma by lemma,
in hypotheses. Each area built its own pricing device, and the bridges between the five devices
were proved after the fact.

**(b) The definitions point the wrong way.** A proof-dependency graph runs from definitions up to
the theorems that use them. The theorem that gives an object its *meaning* is a user of the object,
not its foundation. "The arbitrage-free price of the call is `bsV`" sits *above* `bsV`, so the 48
entries computing with `bsV` never pass through it, and the meaning is never load-bearing. Mathlib
defines the concept and proves the closed form as an `_eq_` lemma. The library did the opposite: it
defined the closed form and attached the concept later. The junk value is the symptom. The concept
(`e^{−rτ}𝔼[(S_τ − K)⁺]`) is total and correct at `τ = 0`. The formula is not.

**(c) The structure enforces connection, not direction.** Nothing makes a pricing model import the
pricing functional, or keeps the probability toolkit apart from the market. Directories hold a
mixture of layers, and the architecture test is satisfied by any edge.

What this plan does *not* claim is that every node should reach the trunk. Some objects rest on a
root by their nature:

- `valueAtRisk` is a quantile of a law;
- the Sharpe ratio is a ratio of moments;
- `portfolioVarN` is a quadratic form.

The requirement is narrower. **Everything the library calls a price, value, premium, quote, hedge
or pricing measure is reached through the pricing functional. Everything it calls a coherent risk
measure is reached through the duality that represents it by measures.** A law functional stays on
its root, named as what it is.

## 3. The target state

Five invariants. The library is in the desired state when all five hold and are gated.

**I1. One pricing functional.** A market is a filtered probability space, its traded assets and a
numéraire. A pricing measure is an `IsEMM` for the deflated assets. The price of a claim is its
value under a pricing measure. Every other device is a proved instance:

| device | becomes |
|---|---|
| `statePricePricing` | the price on a finite `Ω`, with `q ω = D ω · Q {ω}` |
| `numeraireMeasure` | `PricingMeasure.changeNumeraire`, with the price invariant under it |
| `superReplicationPrice` | the supremum of prices over pricing measures (an equality where completeness or finite-dimensional duality is proved, a bound elsewhere) |
| `PricesGainsAtZero` | a characterisation of pricing measures on a Brownian filtration (both directions, with a square-integrable density) |
| `Contract.value` / `valueDisc` | one `value` with a stochastic deflator; the deterministic case is `fun t _ ↦ D t` |

**I2. Prices are defined as prices; closed forms are theorems.** A parametric price (Black–Scholes,
Black, Vasicek, Merton) is defined as the price of the contract in a **canonical model**, a
concrete probability space carrying the model's law. A **law-invariance theorem** makes this the
price in every market with that law: the price depends only on the `Q`-law of the deflator and the
observed assets. Each closed form is then an `_eq_` theorem with its conditions, for example
`bsCallPrice_eq_formula : 0 < σ → 0 < τ → bsCallPrice … = S Φ(d₁) − K e^{−rτ} Φ(d₂)`. Calculus on a
formula stays, named as calculus on the formula. A statement about a Greek, a sensitivity or a
bound *of the price* is stated about the price.

**I3. Every limb hangs on its hinge.** Each limb has the classical theorem that makes it part of
pricing theory (§5). The hinge is proved, blueprint-tagged and depended on.

**I4. The module layout is the map, and imports point one way.**

```
MathFin/
  Init.lean
  Probability/        the roots: Discrete/, Brownian/ (Itô, Girsanov, representation, SDE),
                      Jumps/, Gaussian/ (Φ, quantile, Esscher, heat kernel), Analysis/
  Contracts/          the payoff language: Payoff, Contract, measurability, adaptedness
  Pricing/            the trunk: Market, PricingMeasure, price, FTAP/ (one-period, discrete,
                      Dalang–Morton–Willinger, continuous), StatePrices, Numeraire, Replication,
                      Completeness, Superhedging, Duality (the separation root)
  Models/             limb: BlackScholes/ (American/, …), LocalVol/, StochVol/, Jumps/, Rates/,
                      Credit/, Binomial/, Forwards/ (FX, futures, commodities), ModelFree/
                      (Carr–Madan, SVI, variance swaps)
  Risk/               limb: law functionals (VaR), coherent measures and their duals, dependence
  Choice/             limb: utility, portfolios, performance, equilibrium
  Insurance/          limb: survival, premiums, credibility, ruin
  Markets/            limb: price formation, execution, AMMs and lending
```

`Probability/` imports Mathlib and BrownianMotion. `Contracts/` imports `Probability/`. `Pricing/`
imports both. A limb imports these and its own subtree, and another limb only through a declared
edge (a Uniswap v3 position priced as a Black–Scholes covered call is a declared
`Markets → Models` edge). `Bridges/` and `Foundations/` cease to exist: a join belongs to the limb
that consumes it. `Probability/` is also the staging ground for upstream work: what it holds is
Mathlib-shaped (the L0 commons of [`program-architecture.md`](../program-architecture.md)), and the
upstream ledger ages it.

**I5. The measurements are gated.** `tools/verify/trunk_reach.py` computes four counts from the
declaration index and the table in `tools/verify/trunk.toml`. The table lists the trunk anchors,
the price definitions, the parallel devices and the duplicate groups; it is the one judgment the
counts need. Each count is a ratchet in `ratchet.json`, checked in `build.yml`, and falls to zero:

| count | 2026-11-08 | what it counts |
|---|---|---|
| `prices_off_trunk` | 41 | price definitions whose definition does not reach the pricing functional |
| `price_entries_off_trunk` | 171 | corpus entries whose proof reaches a price definition but not the functional |
| `pricing_devices_unbridged` | 5 | parallel pricing devices with no proved instance theorem (`Contracts.bondPrice`, a conditional price, is the fifth) |
| `concept_duplicates` | 9 | encodings of one concept with no theorem tying them to the canonical one |

A fifth count, imports against the layer direction, starts with the move (Phase 1), as part of
the rewritten `tests/test_architecture.py`.

## 4. The trunk, concretely

A sketch for the trunk PR (Phase 2) to settle, not final Lean.

```lean
/-- A market: a filtered probability space, the traded assets and a numéraire. -/
structure Market (ι Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  𝓕 : Filtration ℝ≥0 ‹_›
  asset : ι → ℝ≥0 → Ω → ℝ
  numeraire : ℝ≥0 → Ω → ℝ
  numeraire_pos : ∀ t ω, 0 < numeraire t ω
  adapted : …

/-- `Q` prices the market up to `T`: equivalent to `P`, each deflated asset a `Q`-martingale. -/
def Market.IsPricingMeasure (M : Market ι Ω) (T : ℝ≥0) (Q : Measure Ω) : Prop :=
  ∀ i, IsEMM M.𝓕 M.P (fun t ω ↦ M.asset i t ω / M.numeraire t ω) T Q

/-- The price of a claim under a pricing measure. -/
noncomputable def Market.price (M : Market ι Ω) (Q : Measure Ω) (c : Contract ι) : ℝ :=
  c.value Q (fun t ω ↦ M.numeraire 0 ω / M.numeraire t ω) M.asset
```

The theorems that make it the trunk:

- **Law invariance.** If `(deflator, observations)` has the same law under `Q` and `Q'`, the
  prices agree. This generalises `Contract.value_congr_ae`, and it is what lets a canonical model
  define a parametric price.
- **The FTAPs as statements about `IsPricingMeasure`.** The existing one-period, discrete,
  Dalang–Morton–Willinger and continuous results restate as no-arbitrage iff a pricing measure
  exists. The current notions remain as the proofs' internals, with the agreement bridges already
  proved.
- **Uniqueness and completeness.** On a complete market (binomial; Brownian with `σ ≠ 0`) all
  pricing measures give the same price, and that price is the replication cost. The existing
  `exists_hedge_eq_value`, `measure_eq_of_density` and `exists_replicating_strategy_in_price`
  become instances.
- **Numéraire invariance.** `changeOfNumeraire` restated: the price does not depend on the
  numéraire.
- **Superhedging.** The price is at most the superreplication price for every pricing measure
  (exists, finite `Ω`), with equality where proved (Brownian completeness now, finite `Ω` once the
  Minkowski–Weyl gap closes).

Settled here (§9): `Market` is a structure in `Type`, since it is a chosen object later
definitions compute with (design.md §3), and `Contract.value` absorbs `valueDisc`. Left to the
trunk PR's own spec:

- the index set for time (`ℝ≥0` with discrete markets as sampled, as `IsEMM.sampled` already
  does, or a general `ι`);

## 5. The limbs and their hinges

For each limb: the hinge, what exists, what is missing, and what the limb's prices become.

**Models: Black–Scholes (the pilot).**

- *Hinge:* in the Black–Scholes market, every pricing measure with a square-integrable density gives
  the European call the price `bsCallPrice`, the superreplication price is `bsCallPrice`, and the delta
  hedge replicates it.
- *Exists:* every piece listed in §1.
- *Missing:* the join, and `bsCallPrice` as a definition, i.e. the call priced in the canonical model
  `(ℝ, gaussianReal 0 1)`. It is total and correct at `τ = 0` (the payoff) and at `σ = 0` (the
  discounted forward intrinsic value).
- *Then:* `bsCallPrice_eq_formula`. `bsV` is renamed `bsCallFormula` (and `bsP` `bsPutFormula`). The ~45
  calculus modules split into formula lemmas (named as such)
  and price statements (rewritten through `bsCallPrice_eq_formula`). The 48 corpus entries citing `bsV`
  restate their price claims about `bsCallPrice`. `bsP`, `bsVDiv`, `bsVGarman`, the digitals, power,
  Margrabe and the Merton mixture each become the price of their contract in their canonical model,
  with their closed forms as theorems. The American put (171 modules) is optimal stopping in the
  Brownian model: its value becomes the Snell envelope of the price, and its boundary results stay
  analysis.

**Models: rates.**

- *Hinge:* bond prices are prices. `zcb` is the price of the unit zero-coupon claim under a
  deterministic short rate (a two-line instance of `bondPrice_*` with `valueDisc_const`).
- *Exists:* the templates in §1.
- *Then:* the 14 `zcb` entries and the duration, convexity and key-rate tower rest on it. The
  eight bond objects reduce to one, `bondPrice` under a pricing measure, with the affine closed forms
  as theorems.
- *Missing:* the HJM drift condition and the CIR loadings (frontier, unchanged).

**Models: jumps.**

- *Hinge:* a jump-diffusion market, its Esscher pricing measure, and the call price as the Poisson
  mixture of Black–Scholes prices.
- *Exists:* `JumpDiffusionHyp`, `JumpDiffusionProcess.martingale_iff`, Esscher, the
  compound-Poisson MGF.
- *Missing:* the jump-diffusion as a `Contracts` model, and `IsPricingMeasure` for the Esscher
  measure.
- *Then:* `call_eq_integral_bsV` (12 entries) and the variance-swap log contract (8) become price
  theorems. The variance swap's fair strike is the price of the log contract by Carr–Madan
  (`carrMadan_spanning` exists).

**Models: credit, binomial, forwards.**

- *Credit:* CDS legs as `Contract` values exist (`value_cdsBuyer_coxDefaultTime`). The six survival
  functions unify into one, the survival function of a default time's law, with hazard and force of
  mortality as instances (`SurvivalUnification` already proves two of them equal). CVA becomes the
  price of the default-contingent loss.
- *Binomial:* `BinomialNoArb` is proved equivalent to a pricing measure (`noArbitrage_horizonSpot_iff`
  exists), so this is wiring only.
- *Forwards, futures, FX, commodities:* the forward price comes from `forward_price_from_no_arbitrage`,
  which roadmap.md already requires. Black76 rests on the forward measure (the caplet template). The
  futures–forward convexity stays frontier.

**Models: stochastic and local volatility.** No Heston process is constructed, so Heston pricing
stays out until one is. The PDE profile results are analysis and stay where they are. Dupire rests
on Carr–Madan and the call-price surface, so it becomes a statement about the price surface.

**Risk.**

- *Hinge:* coherent risk measures are worst-case expectations over a set of measures (Pillar I's
  dual side), and expected shortfall's set is the densities bounded by `1/(1−α)`.
- *Exists:* `coherentRisk_isLUB` (finite `Ω`) and `isGreatest_integral_mul_expectedShortfall`
  (general `Ω`).
- *Missing:*
  - the bridge identifying ES's `representingSet` with the bounded densities (the docstring of
    `expectedShortfall_isLUB_representingSet` says it is not proved);
  - tags on both;
  - the superhedging price as a coherent risk measure whose representing set is the pricing measures
    (finite `Ω`; the equality half waits on Minkowski–Weyl, the inequality half is available now).
- *Then:* ES, Rockafellar–Uryasev and spectral measures rest on the dual. `valueAtRisk` stays a law
  functional on the quantile, which is honest: VaR is not coherent, and
  `VaRSuperadditivity` proves it.

**Choice.**

- *Hinges:*
  - the fundamental equation of a finite-state utility maximiser: at the optimum, marginal utility is
    a state-price density, so the optimum *is* a pricing measure (`HasEMMMultiState`). Kelly is the
    log-utility case and the numéraire portfolio; `kellyNumeraire_isRiskNeutral` becomes an instance;
  - a stochastic discount factor affine in the market return gives CAPM, and Cauchy–Schwarz on state
    prices gives the Hansen–Jagannathan bound on the Sharpe ratio.
- *Exists:* the state-price machinery, `kellyGrowth_deriv_at_kelly`, `CAPM_from_market_equilibrium`
  (covariance algebra) and `PosSemidefCauchySchwarz`.
- *Missing:* the finite-state utility problem with its Lagrangian first-order condition, and the
  discount-factor reading of CAPM.
- *Then:* CAPM, Sharpe bounds and Kelly rest on the trunk. Markowitz variance algebra stays
  algebra, named as such.

**Insurance.**

- *Hinge:* a premium is a price. The net premium of a survival-contingent benefit is its `Contract`
  value under a deterministic discount and the survival law, and the Esscher premium is the price
  under the Esscher-tilted measure.
- *Exists:* Esscher, survival unification, the net-premium algebra and `lifeAnnuityDue`
  (`Actuarial/Insurance`).
- *Missing:* the contract reading. Credibility and ruin (Lundberg) do not exist and enter as frontier.

**Markets.**

- *Hinges:*
  - the Glosten–Milgrom quote process is a martingale, so the dealer's information measure is a
    pricing measure (`condExp_payoff_eq_quote` exists);
  - an AMM LP position is a `Contract`, its value under a pricing measure equals the existing lognormal
    integrals (`integral_lpValue_lognormal`, `integral_discounted_v3PositionValue_le`).
- *Missing:* both statements. Kyle does not exist.
- *Moves:* Almgren–Chriss and the market-making Riccati files move here from `Foundations/`.

## 6. Execution

Six phases. Each phase is a set of PRs that leaves main green and the corpus verified. The order
follows the dependencies. The move comes first: it changes no content and depends on none of the
other work, and every PR after it lands in its final place once. The trunk comes before anything
that rests on it, and one pilot before the rest.

Any phase may build the bridge theorems it needs: a proved equality between two encodings of one
object, or a constructor turning one library object into another's hypothesis (design.md §4). They
are built in the phase that first needs them, not batched for later. After the move, a bridge lives
in the module that consumes it, which is the limb's, or `Pricing/` for a bridge between pricing
devices. No `Bridges/` directory is recreated.

**Phase 0: instruments (1 PR).**

- This spec, revised to the maintainer's decisions.
- `tools/verify/trunk_reach.py` and its table `tools/verify/trunk.toml`, computing the four §3 I5
  counts from the declaration index.
- The counts enter `ratchet.json` as baselines, so they may not rise from here.
- The blueprint frontier gains one node per hinge in §5, each with its issue and `Blueprint:` line
  (the blueprint–issues rule).

**Phase 1: the move (1 large mechanical PR, then fixes).**

- A script (`git mv` plus import, snippet, audit, blueprint and docs rewrites) moves every module
  to its §3 place, with no content change. The existing trunk modules (FTAPs,
  `EquivMartingaleMeasure`, `Numeraire`, `StatePrices`, `SuperhedgingDuality`, `MarketCompleteness`,
  `Contracts/Pricing`) go to `Pricing/`, so the new trunk lands beside them. Module names change, so this is a rename release:
  benchmark snippets, `AxiomAudit*`, `Blueprint`, `MathFinTest/`, `MathFinExamples/`, the README
  and the manual all move with it, and no alias is left (CLAUDE.md).
- `tests/test_architecture.py` is rewritten to enforce the layer direction and the declared
  cross-limb edges, replacing the "Foundations imports only Foundations" rule.
- `tree_map.toml` shrinks to the few nodes whose module does not say their place.
- Every ledger row's inputs change, so the corpus re-verifies once on runners
  (`ledger-sweep.yml`, `lean-build.yml`), never locally.
- It lands in a freeze window announced to parallel sessions. `git mv` keeps history, and file
  headers are untouched, so attribution is preserved.

**Phase 2: the trunk (3–5 PRs, in `Pricing/`).**

- `Market`, `IsPricingMeasure`, `price`, law invariance.
- The FTAPs restated.
- The five devices proved to be instances.
- Uniqueness and completeness for the binomial and Brownian markets.
- A `MathFinExamples/` exercise per design.md §6: a binomial and a Black–Scholes market built,
  with every hypothesis discharged.
- No existing statement changes yet. The old devices stay until Phase 4 moves their callers.

**Phase 3: the Black–Scholes pilot (3–4 PRs). This is a go/no-go gate.**

- `bsCallPrice`, the keystone, `bsCallPrice_eq_formula`, and the rename `bsV` → `bsCallFormula`.
- The calculus modules split into formula lemmas and price statements.
- The 48 entries citing `bsV` restated.
- Measured: entries moved onto the trunk, statement size before and after, proof churn, and any
  claim that got weaker.
- *Gate:* the pilot passes if the price statements are no harder to read than the formula
  statements and no claim weakened. If restating Greeks about the price only adds a rewrite with no
  gain in meaning, the plan falls back: the formula lemmas keep their form, and only the keystone
  plus one price-level corollary per Greek is added. The maintainer decides at this gate.

**Phase 4: the limbs (parallel, one PR per hinge plus its migration).** In order of what already
exists:

1. rates (`zcb`; bond-object unification);
2. binomial wiring;
3. risk (ES set bridge, tags, superhedging-as-coherent);
4. credit and survival unification;
5. jumps (the jump-diffusion model and its Esscher measure);
6. choice (the utility first-order condition, then the discount factor for CAPM and
   Hansen–Jagannathan);
7. insurance (premium as price);
8. markets (Glosten–Milgrom martingale, LP as contract).

Each PR follows the CLAUDE.md first step (survey what exists, extend it, never build beside it),
removes the duplicates it touches, and lowers its ratchet baselines.

**Phase 5: close.**

- The ratchets reach their targets and the gates flip from "may not rise" to "must be zero".
- `mathematical-architecture.md` is rewritten around the trunk.
- `architecture.md`'s three tiers are redefined: a Tier-3 closed form is now a theorem about a price.
- The roadmap, beginners' manual and README follow.
- A values review runs.
- A major release (v2.0.0) ships, with the renames and restated entries in its notes and a new
  major version of the HF dataset.

## 7. Corpus policy

A restated entry keeps its id when the new statement implies the old one, as in a Greek of the
price that rewrites to the Greek of the formula. It gets a new id, with the old one retired in the
release notes, when the claim changes. Descriptions are rewritten to the new statements in the
same PR, under the standing prose-versus-statement pass. `formalization_status` is re-audited for
every touched entry: an entry that becomes a theorem about a price may move from `reduced_core` to
`full`, and the audit decides, not the migration. The HF dataset's `subjects` and
`formalization_scope` move with the entries.

## 8. Risks and guards

- **Forcing dependencies.** The goal is that price claims are about prices, not that the graph
  looks connected. A proof routed through the trunk with no change to what its statement means is
  slop and fails review. Law functionals and algebra stay on their roots (§2).
- **Statement inflation.** Price statements carry a market and a pricing measure. The canonical
  model and law invariance keep parametric statements as short as they are now. The Phase 3 gate
  measures this.
- **Scale.** The move touches all 726 modules and every corpus entry. It is one scripted PR in a
  freeze window, verified on runners. This machine runs one Lean process at a time (CLAUDE.md
  memory doctrine), so all full builds and sweeps run in CI.
- **Mathlib gaps.** The superhedging equality on finite `Ω` waits on Minkowski–Weyl
  (`PointedCone.isClosed_span_of_finite`). That is an upstreaming candidate, not something to build
  locally beside Mathlib.
- **Parallel work.** Open PRs are rebased onto the move by the same script. Issues and blueprint
  labels are unaffected, since labels do not change.
- **Contributor credit.** `git mv` keeps authorship, headers are not edited by the move, and merge
  commits stay merge commits.

## 9. Decisions (2026-11-07)

1. **Re-define, not only connect.** Prices are defined through the pricing functional (I2). Adding
   only the keystones would leave a price that is junk at `τ = 0` and a graph in which the meaning
   still sits above the object it explains. That is the situation design.md §2 and the roadmap's
   "derived, not posited" rule already forbid. Phase 3 still tests the cost. If it fails its gate,
   the fallback in Phase 3 applies to the Greeks only, and the redefinition of the prices stands.
2. **Names.**
   - A closed form is named for what it is. `bsV` becomes `bsCallFormula` and `bsP` becomes
     `bsPutFormula`, and other closed forms get the same `…Formula` suffix as their limb is
     re-founded.
   - A price is the value of a contract in a model, written `bsCallPrice` for the canonical
     Black–Scholes case, with `bsCallPrice_eq_formula` between them.
   - `Contract.value` takes a stochastic deflator and absorbs `valueDisc`. A deterministic discount
     is `fun t _ ↦ D t`.
   - `Market` is a structure in `Type`.
   - Every rename moves all callers, with no alias, and is listed in the release notes.
3. **v2.0.0.** Module paths change and corpus statements are restated, which breaks downstream
   imports and the dataset's claims. That is a major version for the library and for the HF
   dataset. The v1 line gets no further releases. v1.11.0 stays citable through its DOI.
4. **Directories as in §3, with `Contracts/` as its own layer.**
   - The payoff language is model-free and measure-free, and keeping it apart from the model is
     the design `Contracts/` was built on (Bilokon, *The Contract Is Not the Model*).
   - `Contract.value` is the pricing functional, so it moves to `Pricing/`. `Contracts/Models/*`
     moves to the limb of each model.
   - The American put goes to `Models/BlackScholes/American/` and SVI to `Models/ModelFree/SVI/`.
   - Module paths under `MathFin.Probability` do not clash with Mathlib's `ProbabilityTheory`
     namespace.
5. **The move goes first** (Phase 1, ahead of the trunk). It is content-free and does not depend
   on any other decision, so the trunk and every re-founded module land in their final place once.
   Doing it now, while few PRs are open, also keeps the rebase cost lowest. It waits only for #448
   to merge and for a freeze window announced to parallel sessions.
