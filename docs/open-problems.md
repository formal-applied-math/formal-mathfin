# Open problems in mathematical finance: the earlier survey and candidate pool

This is the earlier survey and the pool of candidate questions. The maintained catalogue is
[`research-problems/`](research-problems/README.md): structured records with stable IDs
(`MF-OP-NNN`), exact statements, source locators, dated reviews, and separate mathematical and
Lean statuses. Which artefact owns what is set out in that README. An entry below that a record
carries is reduced to a pointer; the record is authoritative. The per-candidate verdicts of the
latest review round are in
[candidates-2026-11-19.json](research-problems/candidates-2026-11-19.json) and its
[audit](research-problems/audit-2026-11-19.md); they supersede the text of the entries here where
the two differ.

The library formalizes known mathematics. This document is the scouting report for the other
activity: problems that are unsolved, and which of them the existing formalization gives leverage
on. The umbrella issue is
[#177](https://github.com/formal-applied-math/formal-mathfin/issues/177).

## Method, and why entries carry an evidence class

Six review rounds have been run against the literature. Rounds 1 to 3 audited the initial claims
and searched for resolutions of the survivors. Round 4 searched for missing problems and re-dated
the assertions of openness. Round 5 swept further areas and drafted the Tier 3 pool. Round 6
re-checked every remaining lead and promoted the verified ones to records.

The pattern in the attrition is the most useful output. Nearly every casualty was an entry whose
openness had been inferred from not finding a resolution. Entries where a source states that the
problem is unsolved survived, unless the stating source had itself aged out. Each entry therefore
carries an evidence class and the date of the most recent source asserting openness.

| class | meaning | track record |
|---|---|---|
| A, asserted | a source explicitly says the problem is unsolved | survived unless the assertion aged out; check the date |
| B, bounded | a proved positive result and a proved negative result bracket the gap | survived |
| C, inferred | no resolution found on search | nearly all the casualties |
| D, candidate | a question drafted from domain knowledge and not yet searched | roughly 40% were already closed |

Class C entries are leads, not facts. Class D entries carry no verification and form the Tier 3
pool. Search engines return topic summaries more often than assertions of openness, so class A
evidence is expensive. Tier 1 stays a small verified core; Tier 3 is a pool that grows faster
and is not to be cited. The original survey used publisher pages, author preprints and mirrors;
later rounds also consulted arXiv.

---

## Tier 1: survey entries

Entries carried by a record are a pointer to it. Solved entries name the declaration that solves
them.

### 1. Convexity of the American exercise boundary for `0 < q < r`: solved ([MF-OP-006](research-problems/README.md))

For `K, r, σ > 0` and `0 ≤ q ≤ r`, `log(B(τ)/K)` is convex and `B(τ)` is strictly convex in time
to expiry `τ > 0`, where `B` is the exercise boundary of the American put on a geometric Brownian
motion with drift `r − q`. The theorems are
`MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualLogBoundary_convexOn` and
`brownianUsualStockBoundary_strictConvexOn` in
`MathFin/Models/BlackScholes/American/Stopping/PhysicalBoundaryConvexity.lean`, from Robert
Martin's proof ([#212](https://github.com/formal-applied-math/formal-mathfin/pull/212)). Convexity
is in the chord sense; `C²` regularity is not claimed, and for `q > r` the boundary is known not
to be convex.

### 2. Explicit semialgebraic no-butterfly domain for 5-parameter SVI: solved ([MF-OP-007](research-problems/README.md))

`MathFin.SVI.fullCertificateFormula_iff` gives a fixed Boolean combination of signs of polynomials
in `(a,b,ρ,m,σ)` that holds exactly when `σ > 0`, `b ≥ 0`, `ρ² ≤ 1`, the variance is positive and
`g(k) ≥ 0` for every `k`. `extendedCertificateFormula_iff_bsSmile_convex` extends it to `σ = 0`
and to convexity of the smiled call, and `butterflyFreeFormula_iff_isNormalizedCallPrice` adds the
tail condition, all in `MathFin/Models/ModelFree/SVI/`. The formula is built by Hermite's
trace-form signatures and is not expanded into a list of inequalities. Constructing the
risk-neutral law from such a call price function is not formalised.

### 3. Multidimensional shadow prices under transaction costs
**Class A · "has remained elusive", restated 2024–25**

Shadow prices can fail to exist even for a log-investor in an arbitrage-free
market with bounded prices and arbitrarily small proportional costs. Short-sale
constraints suffice for existence, even in general multi-currency models with
discontinuous bid–ask spreads. But the multidimensional construction proceeds
asset-by-asset and complete results exist **only in the two-asset case**.

**Open:** existence in genuine multi-asset settings. Dual minimizers always
give a "local" shadow price but need not give a global one.

### 4. Curse of dimensionality for fully nonlinear PDEs
**Class B · a negative theorem delimits the gap (2026)**

Overcome for semilinear parabolic PDEs — multilevel Picard and deep networks,
including gradient-dependent nonlinearities, Lipschitz nonlinearities, and
PIDEs. Every positive result is **semilinear**; none covers a non-affine-linear
coefficient in front of the second-order operator.

**Open, with a negative result to push against:** full-history recursive
multilevel Picard *provably suffers* from the curse of dimensionality for the
HJB equation of a stochastic control problem.

### 5. Sharp no-manipulation characterization for nonlinear and cross-impact
**Class B · necessary and sufficient conditions both proved, and they do not meet**

For linear transient impact, no-dynamic-arbitrage ⟺ positive semi-definiteness
of the propagator kernel `G`; a nonconstant nonincreasing convex decay kernel
gives a unique optimal strategy with no transaction-triggered manipulation, and
manipulation appears as soon as convexity fails near zero.

**Open:** the nonlinear case, where the known conditions are necessary *or*
sufficient but do not meet and the models display pathologies; and multi-asset
cross-impact, where only easily-verifiable *necessary* conditions are known.

*Moving fast — concave cross-impact work appeared mid-2026. Re-check first.*

### 6. Set-theoretic dependence in multidimensional MOT
**Class B · the assumption is explicit in the theorems**

The De March–Touzi irreducible paving is canonical and quasi-sure duality
extends to multiple dimensions. But structure results for optimal couplings
hold in dimensions 1–3 given the target dominated by Lebesgue, and **in general
dimension only under an assumption implied by the Continuum Hypothesis**.

**Open:** removing that dependence. A targeted search found no work doing so.

### 7. The "right space" for Musiela's SPDE
**Class B by bracketing · the openness assertion dates to 2007**

The explicit assertion, to find a state space whose elements admit continuous
modifications *and* which supports global mild solutions, "not solved even in the
case of Brownian noise", dates to the **2007** local-well-posedness paper. The
theory has since grown around it:

- **Positive:** global existence and uniqueness for the HJMM equation in
  *weighted `L²` spaces* under sufficient conditions; for **linear volatility**
  (the Morton case), conditions for global existence in weighted spaces that
  are *close to necessary*, governed by logarithmic growth of the driving
  Laplace exponent.
- **Negative:** Morton's classical blow-up — the HJM drift is quadratic in the
  volatility, and linear-volatility models can explode.

**What survives:** the original formulation question — a single space with
continuous point evaluation carrying global solutions for a natural volatility
class — has no found resolution, and the gap between the near-necessary
weighted-space conditions and function-space regularity is real. But treat this
as a *bracketed gap in a mature theory*, not the pristine open problem the
2007 quote suggests.


### 8. Physical Stefan uniqueness when jumps accumulate at time zero: [MF-OP-002](research-problems/README.md)

Uniqueness, or a counterexample, for physical solutions of the supercooled Stefan problem when
jumps accumulate at time zero.

### 9. Uniqueness of the one-period Gaussian Kyle equilibrium: [MF-OP-008](research-problems/README.md)

Whether the affine equilibrium is unique among Borel strategies. A resolution is reported and
unchecked; the statement is `MathFinFrontier.kyle_equilibrium_unique`. The continuous-time
Kyle–Back question needs its own exact hypotheses and is not catalogued.

### 10. Microfoundation of the square-root impact law
**Class A · "one of the most fascinating puzzles in finance"**

Empirically, metaorder impact is concave — square-root — across assets, eras
and venues. Kyle–Obizhaeva derive the *general form* from dimensional analysis
and leverage neutrality, with the square-root law a knife-edge case requiring
microstructure-invariance assumptions; proposed mechanisms (inventory risk,
latent liquidity) coexist without a canonical derivation.

**Open:** a first-principles equilibrium microfoundation. Connects to the
Tier 2 propagator-endogeneity residual and to §5.


### 11. Equilibrium existence with action-dependent diffusion: [MF-OP-003](research-problems/README.md)

Existence of relaxed equilibria for time-inconsistent control when the control enters the
diffusion coefficient.

### 12. Epstein–Zin consumption–investment in incomplete markets
**Class A + B · "absent from the literature" (2025–26), with an intrinsic nonuniqueness theorem**

For the empirically relevant parameter ranges, the Epstein–Zin aggregator is
neither Lipschitz nor jointly concave. Herdegen–Hobson–et al. give a
comprehensive existence/uniqueness account for the utility *process*, but
**verification is treated only in a Black–Scholes–Merton market**; a complete
treatment of the infinite-horizon problem in incomplete markets *without
artificial restrictions on coefficients or preference parameters* is stated to
be absent from the literature. Bracketing theorem: for `0 < θ < 1` a unique
generalized utility process exists, while for `θ > 1` **nonuniqueness is
intrinsic**.

**Open:** the general incomplete-market problem — and, for `θ > 1`, the right
selection principle.

### 13. AMM design and the LP/arbitrageur/retail equilibrium
**Class A · "major unsolved problem" as of 2025–26**

The single-LP fee problem is largely solved: the LP's expected-utility problem
reduces to an **ergodic control problem** with the optimal fee a pointwise
volatility feedback, characterized under stochastic volatility by a scalar
ergodic HJB plus a linear Poisson equation (2026).

**Open:** the *equilibrium* between LPs, arbitrageurs and fee-elastic retail
flow, and optimal AMM **design** (choice of invariant curve) under general
demand.

### 14. Non-affine finite-dimensional realizations for Lévy HJM
**Class C — inferred. Treat as a lead.**

Tappe characterized *affine* realizations for Lévy term-structure models;
Platen–Tappe extend to the real-world measure, where infinite-activity jumps
typically force a constant market price of risk. Jumps sharply limit which
models admit finite-dimensional realizations.

**Apparently open:** the general non-affine classification, the jump analogue
of Björk–Svensson's Lie-algebraic theory. No source found *asserting* this is
open.

### 15. Optimal execution on AMMs under transient impact
**Class C: nascent rather than open**

First preprints on Uniswap v2/v3 and CPAMM/CLAMM execution appeared in 2026. A young literature is not the same as a hard problem.

---

## Tier 2 — narrowed, closed, or corrected

Questions commonly stated as open that a published result has narrowed or closed,
with the closing result named and what remains. The closing result is usually the
more useful fact.

| Problem as commonly stated | What closed it | Residual |
|---|---|---|
| **[R4]** Short-horizon relative arbitrage in SPT | Fernholz–Karatzas–Ruf answered the qualitative question (negatively); **Larsson–Ruf** characterized and *computed* the critical horizon via a connection to **mean curvature flow** (*Math. Finance* 2021) | Price-impact and transaction-cost versions of SPT (active 2025–26) |
| **[R3]** MFG master equation without monotonicity | Mou–Zhang, *anti-monotonicity conditions* (JEMS 2025); uniqueness with **no** monotonicity constraint via a conservative reading, adapting hyperbolic-systems arguments | Whether a weak-solution notion *selects* Nash equilibria |
| **[R3]** Radner equilibrium beyond smallness | Xing–Žitković, globally solvable Markovian quadratic BSDE systems (*Ann. Prob.*); global existence for incomplete finite-agent Radner equilibrium under Markovian assumptions; limited-participation existence with exponential preferences | Non-Markovian settings; general preferences |
| **[R2]** Bass martingale uniqueness / classification in `d ≥ 2` | The decomposition of stretched Brownian motion into Bass martingales: for non-irreducible pairs, SBM decomposes on a canonical paving into irreducible cells, a Bass martingale on each. What an earlier draft quoted *as* the open state was the resolution. | `q`-Bass extensions; convergence of dual optimising sequences |
| Pathwise uniqueness for rough/square-root Volterra | A claimed resolution does not apply. For kernel `(t−s)^−α`, Prömel–Scheffels require `ξ > 1/[2(1−α)]`, which excludes square-root diffusion for `α > 0`. | Rough-Heston pathwise uniqueness is explicitly still open in Forde–Gerhold–Smith (2026-10-19); [MF-OP-001](research-problems/README.md). |
| **[R2]** Elicitability of systemic risk measures | CoVaR, CoES, MES fail identifiability and elicitability alone; joint elicitability with the reference VaR **also fails** — resolved by *multi-objective* (lexicographically ordered bivariate) scores with Diebold–Mariano-type tests | Set-valued systemic measures; test power |
| No-trade region shape, multi-asset proportional costs | An **ellipsoid** around the frictionless target, shape given by a matrix-valued algebraic Riccati equation, even in high dimensions | Exact solutions beyond independent assets; the case *with return predictability* |
| MOT dual attainment / duality gap | Beiglböck–Nutz–Touzi complete quasi-sure duality on the line; Beiglböck–Lim–Obłój sharpness (`C²` attains, `C^{2−ε}` counterexamples) | Higher dimensions; continuous-time multi-marginal |
| Stability of MOT | Backhoff-Veraguas–Pammer and Wiesel, in great generality — answered Alfonsi–Corbetta–Jourdain positively | Quantitative stability rates |
| Kellerer / mimicking Markov martingales in `d ≥ 2` | Regularized version proven: after Gaussian regularization a strongly Markovian mimicking Itô diffusion exists | Regularization is provably *necessary*; the question is the minimal one |
| N-player → MFG convergence without uniqueness | Lacker (2018): every closed-loop limit point is a weak MFG equilibrium, uniqueness not required | The **converse** — which weak equilibria arise as limits |
| Sharp rates for Markovian approximation of rough vol | Strong rates proven (Bayer–Breneis; superpolynomial in `N` under Lipschitz coefficients) | Weak rates; non-Lipschitz coefficients |
| Characterization of arbitrage-free IV surfaces | Roper (sufficient, close to necessary); Fukasawa (2012); Lucic extended to general continuous IV, linking calendar and strike arbitrage | Folds into the parametric-family problem (§2) |
| Endogenous derivation of the impact propagator | Microfounded via stationary Kyle setups, latent order books, Nash equilibria of permanent-impact games | Empirical power-law decay from equilibrium (see §10); multi-asset microfoundation |
| Hawkes order flow + transient impact | Alfonsi–Blanc closed-form with viability conditions excluding manipulation; 2025 frameworks with Markovian representations | General/power-law kernels beyond completely-monotone approximations |
| Regularity of multidimensional stopping boundaries | Laurence–Salsa (`C^∞`, multi-dim GBM); Peskir (2-D continuity); De Angelis–Peskir (global `C¹` value function) | General theory without problem-specific input; explicit multi-asset solutions |
| Deep hedging / signature methods lack theory | Universal approximation with convergence guarantees; tight dual bounds; convergence proofs for signature methods, primal and dual | Generalization / sample-complexity bounds explaining practice |
| Uniqueness of clearing vectors | Non-uniqueness under bankruptcy costs + fire sales + cross-holdings is *established*; the equilibrium set need not be connected | Characterization and equilibrium selection |
| Ross recovery conditions | Borovička–Hansen–Scheinkman: valid only if the martingale component of the pricing kernel is constant | What identifying restrictions restore recovery |
| Joint SPX/VIX smile calibration (the continuum question is [MF-OP-004](research-problems/README.md) and [MF-OP-005](research-problems/README.md)) | Guyon (2020) via dispersion-constrained martingale transport; continuous time by martingale interpolation; signature and Gaussian-polynomial models (2025) | A parsimonious low-dimensional continuous-time model |
| Positivity-constrained term structure | Filipović–Tappe–Teichmann characterized positivity-preserving models via characteristic coefficients | Essentially closed |
| Minimax rates for risk-measure estimation | Optimal nonparametric ES estimation (2024): optimal properties under minimal assumptions at all finite sample sizes | Essentially closed |

---

---

## Tier 3 — the candidate pool (Class D, **unverified**)

Every entry here is a **specific question drafted from domain knowledge**. Early
audit rounds measured the base rate for this kind of claim: roughly **40–45% turn
out to be already closed**, and the ones that die are overwhelmingly those stated
as "X is open" rather than "X is bounded between these two theorems."

**Do not cite a Tier 3 entry as an open problem.** Its purpose is to be a
queue: a candidate is promoted to Tier 1 only after a resolution search comes
back empty *and* an openness assertion or a bracketing pair of theorems is
found and dated. Most will instead be closed, and should then be moved to
Tier 2 with the closing result named — that is a useful outcome, not a failed
one.

Entries marked ⚑ were touched by a search that returned topic-level material but no
openness assertion; they are the best-informed candidates, not verified ones. A
candidate promoted to a record is marked with its MF-OP id and no longer described
here. Round 6 ([audit](research-problems/audit-2026-11-19.md),
[verdicts](research-problems/candidates-2026-11-19.json)) checked every entry and
supersedes the text below where the two differ.

### Volatility, smiles, and calibration

| # | candidate question |
|---|---|
| D1 | Attainability: given an arbitrage-free surface, characterize when it is generated by a **continuous** martingale versus requiring jumps |
| D2 | Well-posedness of consistent implied-volatility **market models** (Schönbucher, Schweizer–Wissel dynamics) beyond short horizons ⚑ |
| D3 | Full-generality arbitrage-free domain for **eSSVI** across the whole surface, not slice-wise |
| D4 | Uniqueness of the local volatility recovered from a full surface when the underlying has jumps |
| D5 | Validity of the Dupire formula under minimal regularity of the call-price surface |
| D6 | Exact (beyond leading-order) short-maturity implied-vol asymptotics for general jump models |
| D7 | Identifiability and minimax estimation rates for the Hurst parameter `H` in rough volatility |
| D8 | Sharp rigorous large-deviation rate function for rough Bergomi as `H → 0` |

### Rough paths and signature methods

| # | candidate question |
|---|---|
| D9 | Universality of signature methods **with approximation rates**, not just density |
| D10 | Well-posedness of the signature-calibration inverse problem (does the data determine the model?) |
| D11 | Promoted: [MF-OP-009](research-problems/README.md), the expected signature of Brownian motion stopped at a domain exit time |

### Fixed income and term structure

| # | candidate question |
|---|---|
| D12 | Classification of arbitrage-free **multi-curve** HJM term structures |
| D13 | Existence theory for term-structure models with **backward-looking** (SOFR-style) in-arrears fixings |
| D14 | Classification of negative-rate-consistent models: shifted vs. genuinely signed short rates |
| D15 | Invariant measures for the HJMM equation outside weighted Lebesgue spaces ⚑ |

### Credit, default, and systemic risk

| # | candidate question |
|---|---|
| D16 | Sharp contagion thresholds on **sparse random** financial networks |
| D17 | Phase-transition characterization for self-exciting (Hawkes) default contagion |
| D18 | Uniqueness under filtration enlargement in information-based credit models |
| D19 | Equilibrium **selection** among clearing vectors when bankruptcy costs make them non-unique (Tier 2 residual, promoted to a question) |

### Market microstructure

| # | candidate question |
|---|---|
| D20 | Ergodicity of limit-order-book models under **general** state-dependent order flow — known to need proportional cancellation rates; the general case is reportedly undecidable-adjacent ⚑ |
| D21 | Scaling limits of queue-reactive models with cross-level dependence ⚑ |
| D22 | Existence of optimal market-making strategies under adverse selection with general fill probabilities |
| D23 | Equilibrium characterization of latency races: continuous trading vs. frequent batch auctions |
| D24 | A price-formation model reproducing the square-root law, long-memory order flow, **and** diffusive prices simultaneously ⚑ |

### Execution, frictions, and control

| # | candidate question |
|---|---|
| D25 | Growth-optimal (Kelly) investment under proportional transaction costs, **multi-asset** — the lead dropped in round 1 without ever being checked ⚑ |
| D26 | Robust optimal execution when the impact model itself is uncertain |
| D27 | Optimal execution under transient impact with **general power-law** kernels beyond completely-monotone approximations (Tier 2 residual) |
| D28 | Verification theorems for McKean–Vlasov control where the dynamic programming principle fails ⚑ |
| D29 | Time-consistent equilibria for mean-variance control with state-dependent risk aversion, general case |

### Equilibrium, contracts, and asset pricing

| # | candidate question |
|---|---|
| D30 | General existence for principal–agent problems with **multiple agents** and volatility control ⚑ |
| D31 | Equilibrium existence with heterogeneous beliefs **and** portfolio constraints |
| D32 | A microfounded, no-arbitrage-consistent account of price inelasticity (the inelastic-market hypothesis) ⚑ |
| D33 | Identification of the term structure of risk premia without the Ross transition-independence assumption |
| D34 | FTAP for **large financial markets**: sharp no-asymptotic-arbitrage conditions |

### Robust finance and model uncertainty

| # | candidate question |
|---|---|
| D35 | Promoted, narrowed to its residual: [MF-OP-010](research-problems/README.md), robust American duality for non-càdlàg payoffs |
| D36 | Nonconcave stochastic control under model uncertainty in **continuous** time (the discrete case advanced in 2026) ⚑ |
| D37 | Aggregation and time-consistency of nonlinear expectations under non-dominated priors |

### Optimal transport and embeddings

| # | candidate question |
|---|---|
| D38 | Structure of optimal **multi-marginal** Skorokhod embeddings in `d ≥ 2` |
| D39 | Quantitative stability *rates* for MOT (qualitative stability is proved — Tier 2) |
| D40 | Promoted in the raw-filtration form: [MF-OP-011](research-problems/README.md) |

### Filtering and partial information

| # | candidate question |
|---|---|
| D41 | Pathwise uniqueness for Kushner–Stratonovich / Zakai equations under general observation structures ⚑ |
| D42 | Promoted as Zakai uniqueness when control jumps accumulate: [MF-OP-012](research-problems/README.md) |
| D43 | Filtering under model ambiguity: existence of a robust filter for non-dominated prior sets ⚑ |

### Insurance and actuarial control

| # | candidate question |
|---|---|
| D44 | Promoted: [MF-OP-013](research-problems/README.md), the optimal local control for `n ≥ 2` insurers |
| D45 | Optimal dividends for two or more collaborating insurers: explicit solutions beyond strong assumptions ⚑ |
| D46 | Sharp ruin-probability asymptotics under general dependence between claims |
| D47 | Time-consistency of the Solvency II risk margin as a dynamic risk measure |
| D48 | Model-free bounds for longevity-linked liabilities |

### Numerics and machine learning

| # | candidate question |
|---|---|
| D49 | Convergence guarantees for reinforcement learning in **continuous-time** control with function approximation |
| D50 | Identifiability of neural-SDE calibration (does the fit determine the dynamics?) |
| D51 | Curse-of-dimensionality results for **free-boundary** problems in high dimension (American options) |
| D52 | Sample-complexity bounds for deep hedging that match observed practice (Tier 2 residual) |

### Energy and commodities

| # | candidate question |
|---|---|
| D53 | Storage valuation as optimal switching on a **high-dimensional forward curve**: tractable characterization ⚑ |
| D54 | No-arbitrage-consistent modelling of genuinely **negative** electricity prices ⚑ |
| D55 | Equilibrium in intraday electricity markets under renewable intermittency ⚑ |

### XVA and funding

| # | candidate question |
|---|---|
| D56 | Whether FVA belongs in derivative valuation — balance-sheet models reach **conflicting** conclusions ⚑ |
| D57 | A definition of KVA that is agreed rather than "subject to intense debate" ⚑ |
| D58 | Well-posedness of fully nonlinear XVA BSDE systems with asymmetric funding rates ⚑ |

### DeFi and crypto

| # | candidate question |
|---|---|
| D59 | Equilibrium characterization of MEV extraction |
| D60 | Closed-form optimal LP strategies in concentrated-liquidity (CLAMM) pools |
| D61 | Optimal AMM **invariant curve** design under general demand (Tier 1 §13 residual) |

---

---

## Coverage map — what has and has not been swept

Honesty about scope is what keeps the Tier 1 count meaningful.

| area | swept | round |
|---|---|---|
| Volatility surfaces / SVI | ✅ | 1–4 |
| Rough volatility / Volterra | ✅ | 1–3 |
| Market impact & execution | ✅ | 1–4 |
| Transaction costs & shadow prices | ✅ | 1–3 |
| Optimal transport / MOT / Bass | ✅ | 1–3 |
| Mean-field games & Radner | ✅ | 3 |
| Term structure / HJM / Musiela | ✅ | 1–4 |
| Optimal stopping / American | ✅ | 1–2 |
| Risk measures & elicitability | ✅ | 1–2 |
| Numerics / curse of dimensionality | ✅ | 1–3 |
| Stochastic portfolio theory | ✅ | 4 |
| Microstructure equilibrium (Kyle) | ✅ | 4 |
| Recursive utility (Epstein–Zin) | ✅ | 4 |
| Robust finance / model uncertainty | ◐ topic-level only | 5 |
| Filtering / partial information | ◐ topic-level only | 5 |
| Insurance & dividend control | ◐ topic-level only | 5 |
| McKean–Vlasov control | ◐ topic-level only | 5 |
| Limit order books | ◐ topic-level only | 5 |
| Principal–agent | ◐ topic-level only | 5 |
| Energy & commodities | ◐ topic-level only | 5 |
| XVA / counterparty | ◐ topic-level only | 5 |
| Implied-vol market models | ◐ swept, nothing class A | 6 |
| Large-markets FTAP | ✅ | 6 |
| High-frequency econometrics | ◐ two leads | 6 |
| Real options | ◐ one lead | 6 |
| Climate / ESG finance | ❌ | — |
| Behavioural / prospect-theory pricing | ❌ | — |
| Multi-curve & rate-benchmark transition | ❌ | — |

◐ = round 5 searched the area and drafted candidates, but found no openness
assertion, so nothing was promoted to Tier 1.

### Promotion pipeline

```
D (drafted)  →  search for a resolution
                ├── found       →  Tier 2, name the closing result
                └── none found  →  hunt an openness assertion or a bracketing pair
                                   ├── found + dated  →  Tier 1 (class A or B)
                                   └── not found      →  stays Class C lead
```

Anyone extending this document should run that pipeline rather than appending to Tier 1
directly. The direct route produced a 44% error rate in the first audit.

---

## Where this library gives leverage

The ranking criterion is distance from built code, not mathematical interest. The questions
whose answer is a certificate are the ones where a proof assistant adjudicates rather than taxes:
a polynomial positivity, a bounded-parameter convexity argument, or an explicit finite
counterexample. Two of them, entries 1 and 2, are solved. The next candidate of this kind is the
impact-kernel positive-definiteness question of entry 5.

| Entry | Built code it lands on | What is missing |
|---|---|---|
| 5, impact kernels | `Choice/Portfolio/CovariancePSD.covariance_kernel_psd` (a positive semi-definite quadratic form over a kernel), `Markets/Execution/AlmgrenChriss`, `Pricing/NoArbitrageCore` | a propagator with a decay kernel; Almgren–Chriss here is the deterministic permanent and temporary model. A counterexample is an explicit kernel with a finite schedule of negative expected cost |
| 7, Musiela's SPDE | the Itô integral and stochastic Fubini (`MathFin/Probability/Brownian/Ito/StochasticFubini.lean`), planned in `docs/hjm-program.md` | the HJM modules and the SPDE solution notion |
| 14, Lévy HJM realizations | the Itô–Lévy integral and the Poisson random measure modules in `Probability/` | Lie-algebraic and infinite-dimensional geometry that neither this library nor Mathlib carries |

Entries 3, 4, 10, 12 and 13 have little or no built substrate. Formalizing the statement of an
open problem, and its known partial results, is ordinary library work, and it makes a later
resolution checkable without a referee. Before committing to any entry here, re-run the
resolution search: the list lost roughly a third of its entries to each verification round.

---

---

## Sources

Volatility and calibration —
[No Arbitrage SVI (Martini–Mingone, SIAM J. Fin. Math.)](https://epubs.siam.org/doi/10.1137/20M1351060) ·
[Explicit no-arbitrage domain for sub-SVIs](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=3860011) ·
[Refined analysis of the no-butterfly-arbitrage domain for SSVI slices](https://www.risk.net/journal-of-computational-finance/7957920/refined-analysis-of-the-no-butterfly-arbitrage-domain-for-ssvi-slices) ·
[Roper, Arbitrage-free implied volatility surfaces](https://talus.maths.usyd.edu.au/u/pubs/publist/preprints/2010/roper-9.pdf) ·
[Lucic, Normalizing volatility transforms](https://doi.org/10.2139/ssrn.3835233) ·
[Guyon, the joint SPX/VIX puzzle solved](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=3397382)

Rough volatility —
[Weak existence/uniqueness for affine SVEs with `L¹` kernels](https://www.researchgate.net/publication/337966379_Weak_existence_and_uniqueness_for_affine_stochastic_Volterra_equations_with_L1-kernels) ·
[Pathwise uniqueness for singular SVEs with Hölder coefficients](https://arxiv.org/html/2212.08029) ·
[SVEs with Hölder diffusion coefficients](https://www.sciencedirect.com/science/article/abs/pii/S030441492300073X) ·
[Markovian approximations with the fractional kernel](https://www.tandfonline.com/doi/full/10.1080/14697688.2022.2139193)

Market impact and execution —
[Gatheral, No-dynamic-arbitrage and market impact](https://www.tandfonline.com/doi/abs/10.1080/14697680903373692) ·
[Optimal execution with nonlinear transient market impact](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=2539240) ·
[Concave cross impact](https://doi.org/10.2139/ssrn.5046242) ·
[The Market Impact Puzzle (Kyle–Obizhaeva)](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=3124502) ·
[Dimensional analysis: quantifying market impact](https://www.mat.univie.ac.at/~schachermayer/pubs/preprnts/prpr0171.pdf) ·
[The two square-root laws of market impact](https://arxiv.org/pdf/2311.18283) ·
[Dynamic optimal execution in a mixed-market-impact Hawkes model](https://link.springer.com/article/10.1007/s00780-015-0282-y) ·
[A stationary Kyle setup: microfounding propagator models](https://www.researchgate.net/publication/346090035_A_Stationary_Kyle_Setup_Microfounding_propagator_models)

Microstructure equilibrium —
[On uniqueness of equilibrium in the Kyle model (McLennan–Monteiro)](https://link.springer.com/content/pdf/10.1007/s11579-016-0175-7.pdf) ·
[A new approach for the continuous-time Kyle–Back equilibrium problem (FBSDE, small-time uniqueness)](https://arxiv.org/abs/2506.12281) ·
[A continuous-time Kyle model with price-responsive traders](https://arxiv.org/html/2601.09872)

Frictions and preferences —
[Portfolio choice with transaction costs: a user's guide](https://www.guasoni.com/papers/transreview.pdf) ·
[Asymptotic methods for transaction costs](https://arxiv.org/pdf/2407.07100) ·
[Transaction costs, shadow prices and duality in discrete time](https://www.mat.univie.ac.at/~schachermayer/pubs/preprnts/prpr0156.pdf) ·
[Almost perfect shadow prices](https://www.mdpi.com/1911-8074/17/2/70) ·
[Epstein–Zin in unbounded non-Markovian markets](https://www.sciencedirect.com/science/article/abs/pii/S0304414925002492) ·
[Infinite-horizon consumption under Epstein–Zin preferences](https://arxiv.org/html/2606.02945) ·
[Existence and uniqueness of recursive utilities without boundedness](https://arxiv.org/pdf/2008.00963) ·
[Stability of the Epstein–Zin problem](https://arxiv.org/pdf/2208.09895)

Time-inconsistent control —
[On time-inconsistent stochastic control in continuous time](https://link.springer.com/article/10.1007/s00780-017-0327-5) ·
[Equilibrium under time-inconsistency via vanishing entropy regularization](https://arxiv.org/html/2603.10321) ·
[Time-inconsistent LQ control: characterization and uniqueness of equilibrium](https://arxiv.org/pdf/1504.01152) ·
[Extended backward stochastic Volterra integral equations](https://arxiv.org/pdf/2004.14346)

Optimal transport —
[The Bass functional of martingale transport (AAP 2025)](https://projecteuclid.org/journals/annals-of-applied-probability/volume-35/issue-6/The-Bass-functional-of-martingale-transport/10.1214/25-AAP2221.short) ·
[The decomposition of stretched Brownian motion into Bass martingales](https://arxiv.org/abs/2406.10656) ·
[Local structure of multi-dimensional MOT](https://arxiv.org/abs/1805.09469) ·
[Complete duality for MOT on the line](https://projecteuclid.org/journals/annals-of-probability/volume-45/issue-5/Complete-duality-for-martingale-optimal-transport-on-the-line/10.1214/16-AOP1131.full) ·
[Dual attainment for the martingale transport problem](https://www.mat.univie.ac.at/~mathias/GlobalDualAttainment_Bernoulli.pdf) ·
[A regularized Kellerer theorem in arbitrary dimension](https://projecteuclid.org/journals/annals-of-applied-probability/volume-35/issue-2/A-regularized-Kellerer-theorem-in-arbitrary-dimension/10.1214/24-AAP2125.full)

Equilibrium and mean-field —
[Weak solutions to the master equation of potential MFGs](https://pubs.ams.org/ebooks/memo/1600/) ·
[Monotone solutions of the master equation with idiosyncratic noise](https://epubs.siam.org/doi/10.1137/21M1450008) ·
[On non-uniqueness in mean field games](https://arxiv.org/pdf/1908.06207) ·
[Convergence of closed-loop Nash equilibria to the MFG limit (Lacker)](https://arxiv.org/abs/1808.02745) ·
[Radner equilibrium and quadratic BSDEs](https://link.springer.com/article/10.1007/s11579-016-0161-0) ·
[A class of globally solvable Markovian quadratic BSDE systems](https://www.researchgate.net/publication/301841292_A_class_of_globally_solvable_Markovian_quadratic_BSDE_systems_and_applications) ·
[Existence of an equilibrium with limited participation](https://arxiv.org/abs/2206.12399)

Stochastic portfolio theory —
[Relative arbitrage: sharp time horizons and motion by curvature (Larsson–Ruf)](https://onlinelibrary.wiley.com/doi/full/10.1111/mafi.12303) ·
[Volatility and arbitrage (Fernholz–Karatzas–Ruf)](https://arxiv.org/pdf/1608.06121) ·
[Stochastic portfolio theory with price impact](https://arxiv.org/pdf/2506.07993)

Term structure —
[Local well-posedness of Musiela's SPDE with Lévy noise (2007 — source of the "right space" question)](https://arxiv.org/pdf/0704.2380) ·
[HJMM equation with linear volatility](https://arxiv.org/abs/1010.5808) ·
[HJMM equation with Lévy perturbation](https://www.sciencedirect.com/science/article/pii/S0022039612002720) ·
[Existence of affine realizations for Lévy term-structure models](https://arxiv.org/pdf/1907.02363) ·
[Affine realizations for Lévy-driven models under the real-world measure](https://www.uts.edu.au/globalassets/sites/default/files/qfr-archive-03/QFR-rp289.pdf) ·
[Term structure models driven by Wiener process and Poisson measures](https://epubs.siam.org/doi/10.1137/090758593) ·
[Positivity of mild solutions with an application to forward rates](https://link.springer.com/article/10.1007/s11117-025-01159-3)

Optimal stopping —
[Convexity of the free boundary for the American put](https://arxiv.org/pdf/1304.5337) ·
[Optimal exercise boundary for jump diffusions](https://epubs.siam.org/doi/abs/10.1137/080712519) ·
[Continuous differentiability of optimal stopping boundaries](https://arxiv.org/pdf/2405.16636)

Systemic risk and risk measures —
[Free boundary regularity and well-posedness of physical solutions to the supercooled Stefan problem (Muñoz 2025)](https://arxiv.org/abs/2506.18741) ·
[Propagation of minimality in the supercooled Stefan problem](https://projecteuclid.org/journals/annals-of-applied-probability/volume-33/issue-2/Propagation-of-minimality-in-the-supercooled-Stefan-problem/10.1214/22-AAP1850.pdf) ·
[Backtesting systemic risk forecasts using multi-objective elicitability](https://arxiv.org/pdf/2104.10673) ·
[Elicitability and identifiability of set-valued measures of systemic risk](https://link.springer.com/article/10.1007/s00780-020-00446-z) ·
[ES is jointly elicitable with VaR](https://www.risk.net/risk-management/2439862/expected-shortfall-is-jointly-elicitable-with-value-at-risk-implications-for-backtesting) ·
[Bankruptcy costs, fire sales and cross-holdings](https://probability-risk.springeropen.com/articles/10.1186/s41546-017-0020-9)

Numerics and DeFi —
[MLP suffers from the curse of dimensionality for HJB](https://arxiv.org/pdf/2506.23969) ·
[Multilevel Picard research overview](https://www.uni-due.de/mathematik/ag_stochastische_analysis/mlp) ·
[Optimal dynamic fees in AMMs](https://arxiv.org/html/2506.02869) ·
[Optimal dynamic fees: a stochastic control approach to LVR](https://arxiv.org/abs/2606.21769) ·
[Misspecified Recovery (Borovička–Hansen–Scheinkman)](https://www.nber.org/papers/w20209)
