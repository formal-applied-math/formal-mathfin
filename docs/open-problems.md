# Open problems in mathematical finance — a verified survey

**Purpose.** This library formalizes *known* mathematics. This document is the
scouting report for the other activity: genuinely unsolved problems, and which
of them our existing formalization actually gives us leverage on.

## How this list was built, and why it is organized by evidence

Four adversarial rounds were run against current literature (2026-08). Rounds
2–3 searched for *resolutions* of claimed-open problems (false positives);
round 4 searched for *missing* open problems (false negatives) and re-dated
the surviving assertions:

| round | direction | outcome |
|---|---|---|
| 1 | audit of 36 initial claims | 16 wrong or overstated |
| 2 | resolutions of the 16 survivors | 3 closed, 2 substantially narrowed |
| 3 | resolutions of 5 never-re-checked | 2 closed |
| 4 | completeness sweep + assertion re-dating | **4 missing entries found**, 1 folklore item confirmed closed, 1 entry re-dated and demoted |

The attrition in rounds 1–3 was **not uniform**, and the pattern is the most
useful output of the exercise:

> Nearly every casualty was an entry whose openness had been *inferred from
> not finding a resolution*. Entries where a source **states** the problem is
> unsolved survived — unless the stating source had itself aged out.

Round 4 confirmed the second clause the hard way: the entry this document
previously ranked first (Musiela) carried an openness assertion dating to
**2007**, around which the theory has since grown (see §7). Each entry
therefore carries an **evidence class** and the **date of the most recent
source asserting openness**:

| class | meaning | track record |
|---|---|---|
| **A — asserted** | a source explicitly says the problem is unsolved | survived unless the assertion aged out — *check the date* |
| **B — bounded** | a proved positive result and a proved negative result bracket the gap | survived |
| **C — inferred** | no resolution found on search | **essentially all fatalities** |

Class C entries are retained but are *leads*, not facts. And this list is a
**sweep, not a census**: round 4 covered microstructure equilibrium, control,
preferences, and stochastic portfolio theory, but robust finance / model
uncertainty, filtering, insurance and dividend control, McKean–Vlasov control,
implied-volatility *market models* (consistent IV-surface dynamics), and
large-markets FTAP were not swept. One item from the original draft —
growth-optimal (Kelly) investment under frictions, adjacent to our
`Performance/Kelly*` modules — was dropped in round 1 without ever being
checked; it remains an unchecked Class C lead.

arXiv is unreachable from this environment (network policy), so sources are
publisher pages, author preprints, and mirrors. Tier 2's "residual" column
reports what the closing papers say they left open; not independently
re-verified.

---

## Tier 1 — surviving open problems

### 1. Convexity of the American exercise boundary for `0 < q < r`
**Class B · bracketed by theorems on both sides**

A clean trichotomy in the dividend yield `q`:

| regime | status |
|---|---|
| `q = 0` | convexity **proved** (Chen–Chadam–Cheng–Saunders; Ekström) |
| `q > r` | convexity **disproved** — the boundary is not convex |
| `0 < q < r` | **open** — observed numerically, no rigorous proof |

Regularity under jump diffusions is settled separately: `C¹` except at
maturity, `C^∞` under a regularity assumption on the jump distribution, with
continuity and near-maturity estimates proven. The smallest and most sharply
bounded problem on this list — the open region is an interval defined by two
theorems, not by absence of literature.

### 2. Explicit semialgebraic no-butterfly domain for 5-parameter SVI
**Class A · asserted in the characterizing papers; restated 2025–26**

Butterfly-freeness of an SVI slice is `g(k) ≥ 0` for all `k` (Durrleman), where
`w(k) = a + b(ρ(k−m) + √((k−m)² + σ²))`. Martini–Mingone characterized the
domain completely, but their conditions **require numerical minimization of two
functions plus root-finding** — stated in the papers themselves. Explicit
closed forms exist only for sub-SVIs, and the most recent refinement
(*J. Computational Finance*) is again for **SSVI** slices, not full SVI.

**Open:** eliminating the inner numerics — an explicit description of the
domain as polynomial inequalities in `(a,b,ρ,m,σ)`. Substituting `y = (k−m)/σ`,
`z = √(y²+1)` makes this positivity of a polynomial on a real algebraic curve:
a quantifier-elimination problem.

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
**Class B by bracketing · the openness assertion dates to 2007 — demoted in round 4**

Previously this document's top entry, tagged "asserted as of 2025". Round 4
found the tag wrong: the explicit assertion — find a state space whose elements
admit continuous modifications *and* which supports global mild solutions,
"not solved even in the case of Brownian noise" — dates to the **2007**
local-well-posedness paper. The theory has since grown around it:

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

### 8. Short-time uniqueness for the supercooled Stefan problem
**Class A · residual framed by the closing paper (2025)**

Muñoz (2025) proved the free boundary is `C¹` in space and `C^∞` off a
countable set assuming only integrable initial temperature, resolved the
conjecture that jump times cannot accumulate, and proved that **short-time
uniqueness of physical solutions implies global uniqueness**, answering two
previously-open questions. Separate 2026 work gives uniqueness of maximal weak
solutions in 1D and regularity in arbitrary dimensions.

**Open:** short-time uniqueness itself, for initial data outside the current
well-posedness regime — a reduction away from resolution, not a frontier.

### 9. Uniqueness of Kyle equilibrium
**Class A · "longstanding unresolved question"; small-time result 2025 — found in round 4**

Whether the one-period Kyle (1985) model admits an equilibrium *different from*
the closed-form one is explicitly called a longstanding unresolved question
(McLennan–Monteiro). In continuous time, the literature proved existence via
PDE methods within Markovian/bridge structures; a 2025 FBSDE characterization
of *all* equilibria gives uniqueness **for small time horizons** — the first
uniqueness result without structural restriction.

**Open:** global-in-time uniqueness in continuous time; uniqueness beyond the
pricing-rule classes in the static model.

### 10. Microfoundation of the square-root impact law
**Class A · "one of the most fascinating puzzles in finance" — found in round 4**

Empirically, metaorder impact is concave — square-root — across assets, eras
and venues. Kyle–Obizhaeva derive the *general form* from dimensional analysis
and leverage neutrality, with the square-root law a knife-edge case requiring
microstructure-invariance assumptions; proposed mechanisms (inventory risk,
latent liquidity) coexist without a canonical derivation.

**Open:** a first-principles equilibrium microfoundation. Connects to the
Tier 2 propagator-endogeneity residual and to §5.

### 11. Existence for the equilibrium HJB of time-inconsistent control
**Class A · "still an open problem under general model assumptions" (2026)**

Time-inconsistent problems — dynamic mean-variance, non-exponential
discounting — replace optimality by intra-personal equilibrium, characterized
by an *extended/equilibrium* HJB system. Linear-quadratic and various Markovian
cases are settled (some with uniqueness via infinite BSDE families); a 2026
vanishing-entropy-regularization approach is explicitly still building an
existence theory.

**Open:** existence (and uniqueness) of equilibrium solutions to the EHJB
equation under general model assumptions.

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
**Class C — nascent rather than open**

First preprints on Uniswap v2/v3 and CPAMM/CLAMM execution appeared in 2026.
A young literature is not the same as a hard problem.

---

## Tier 2 — narrowed or closed

Entries earlier drafts carried as open — plus, from round 4, folklore items
confirmed closed before they were ever added. The closing result is usually
the more useful fact.

| Problem as commonly stated | What closed it | Residual |
|---|---|---|
| **[R4]** Short-horizon relative arbitrage in SPT | Fernholz–Karatzas–Ruf answered the qualitative question (negatively); **Larsson–Ruf** characterized and *computed* the critical horizon via a connection to **mean curvature flow** (*Math. Finance* 2021) | Price-impact and transaction-cost versions of SPT (active 2025–26) |
| **[R3]** MFG master equation without monotonicity | Mou–Zhang, *anti-monotonicity conditions* (JEMS 2025); uniqueness with **no** monotonicity constraint via a conservative reading, adapting hyperbolic-systems arguments | Whether a weak-solution notion *selects* Nash equilibria |
| **[R3]** Radner equilibrium beyond smallness | Xing–Žitković, globally solvable Markovian quadratic BSDE systems (*Ann. Prob.*); global existence for incomplete finite-agent Radner equilibrium under Markovian assumptions; limited-participation existence with exponential preferences | Non-Markovian settings; general preferences |
| **[R2]** Bass martingale uniqueness / classification in `d ≥ 2` | The decomposition of stretched Brownian motion into Bass martingales: for non-irreducible pairs, SBM decomposes on a canonical paving into irreducible cells, a Bass martingale on each. What an earlier draft quoted *as* the open state was the resolution. | `q`-Bass extensions; convergence of dual optimising sequences |
| **[R2]** Pathwise uniqueness for rough/square-root Volterra | Prömel–Scheffels (2025) for a broad class of singular SVEs; Hölder coefficients `sgn(x)\|x\|^ξ`, `ξ ∈ [1/2,1]`, cover the square-root case and apply to rough Heston | Jump-diffusion settings need extra monotonicity |
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
| Joint SPX/VIX smile calibration | Guyon (2020) via dispersion-constrained martingale transport; continuous time by martingale interpolation; signature and Gaussian-polynomial models (2025) | A parsimonious low-dimensional continuous-time model |
| Positivity-constrained term structure | Filipović–Tappe–Teichmann characterized positivity-preserving models via characteristic coefficients | Essentially closed |
| Minimax rates for risk-measure estimation | Optimal nonparametric ES estimation (2024): optimal properties under minimal assumptions at all finite sample sizes | Essentially closed |

---

## Where *this repo* gives leverage

Ranked by **distance from what we have already built**, not by mathematical
interest. Adjacency is judged against built code; where a target leans on a
planned-but-unbuilt program, that is stated.

Round 4's four new entries did **not** change this ranking: Kyle uniqueness
(§9) and the square-root law (§10) need filtering/FBSDE and equilibrium
machinery the repo lacks (`Foundations/MarketMakingRiccati` is
LQ-approximation market-making, a different animal); time-inconsistent control
(§11) and Epstein–Zin (§12) need EHJB / BSDE substrates absent here. The
incumbents keep their positions for the fourth consecutive round.

### 1. SVI butterfly domain (§2) — strongest built-code adjacency

The butterfly-arbitrage criterion is *already formalized*, in substance:

| Existing | What it gives |
|---|---|
| `BlackScholes/BreedenLitzenberger.deriv2_bsV_eq_exp_neg_rT_pdf` | `∂²V/∂K² = e^{−rT}·density` — butterfly-freeness **is** this second derivative's sign |
| `BreedenLitzenberger.lognormalTerminalPDF_nonneg_via_strike_convexity` | the density-nonnegativity ⟸ strike-convexity route, already proved |
| `BlackScholes/StrikeConvexity.bsV_strike_convexOn`, `bsP_strike_convexOn` | the convexity side for calls and puts |
| `BlackScholes/{ImpliedVolatility,BisectionIV,NewtonRaphsonIV,NewtonConvergence}` | the implied-vol layer, with convergence |
| `PutStrikeConvexity`, `SpotConvexity`, `StaticBounds`, `PriceBounds` | the surrounding static-arbitrage results |

Missing is small and well-defined: an SVI parametrization module and
Durrleman's `g`. Positivity certificates land in the house idiom
(`nlinarith [certificates]`, kernel-checkable, no `native_decide`).

### 2. American boundary convexity for `0 < q < r` (§1) — strong module set, one seam

`Binomial/SnellEnvelope.americanPrice_is_snell_envelope` plus
`Binomial/American`, `AmericanCallNoDividend`, `Bermudan`,
`MertonAmericanCallTree`, `BlackScholes/Dividends`, and the convexity trio
(`StrikeConvexity`, `PutStrikeConvexity`, `SpotConvexity`).
`Binomial/CRRConvergence` is the discrete→continuous seam.

Gap, and it is genuine: our American machinery is **binomial/discrete**, while
the problem concerns the *continuous* free boundary. CRRConvergence makes the
bridge plausible rather than automatic.

### 3. Impact-kernel positive-definiteness (§5) — cheapest decisive output

| Existing | What it gives |
|---|---|
| `Portfolio/CovariancePSD.covariance_kernel_psd`, `portfolioVarN_covariance_nonneg` | a PSD-quadratic-form theorem over a kernel — the exact shape of the no-dynamic-arbitrage criterion |
| `Foundations/AlmgrenChriss.almgrenChrissPath_satisfies_EL` | the execution Euler–Lagrange path |
| `Foundations/NoArbitrageCore`, `TriangleArbitrage` | no-arbitrage predicates to land the statement on |

Gap: our Almgren–Chriss is the deterministic permanent+temporary model with
**no decay kernel** — the propagator must be built. Small build, and refutation
is cheap: a counterexample is an explicit kernel plus a *finite* schedule with
negative expected cost, i.e. rational arithmetic closable by `norm_num`/`ring`.

### 4. Musiela's SPDE (§7) — highest conceptual alignment, longest runway, now double-caveated

`docs/hjm-program.md` names Musiela as node **G4**, the deferred SPDE summit
shipping `placeholder`. But two caveats now stack: **neither
`MathFin/FixedIncome/HJM/` nor `MathFin/Foundations/StochasticFubini*.lean`
exists yet** (the HJM program is *ratified, not built* — the whole F1→C4 chain
precedes G4), and round 4 demoted the problem itself from "best-evidenced open
problem" to a bracketed gap in a mature theory.

### 5. Lévy HJM finite-dimensional realizations (§14) — real tower, heavy missing geometry

The Itô–Lévy tower is genuinely built: `PoissonCompensatedIntegralOperator`,
`PoissonCompensatedIntegralL2{,Dense}`, `PoissonCompensatedIsometryAdapted`,
`PoissonRandomMeasure`, `PoissonSuperposition`, `PoissonThinning`, and the
Itô–Lévy integral CLM in full generality. `docs/hjm-program.md` plans F6, the
Lévy instance of stochastic Fubini.

Two gaps: FDR theory needs Lie-algebraic / infinite-dimensional differential
geometry that neither this library nor Mathlib carries — and the target is
Class C, the evidence class that kept collapsing.

**Weak or absent adjacency.** `Foundations/ExitTime` gives real hitting-time
machinery, but `FixedIncome/FirstToDefault` is constant-hazard with independent
names and `KMVMertonStructural` is one-period Merton — neither a first-passage
model — so the supercooled-Stefan residual (§8) sits on almost nothing.
`RiskMeasures/RockafellarUryasev.gaussianCVaR_isLeast_ruObjective` remains a
seed for scoring-function work, but the systemic-elicitability target closed.
`DeFi/ConstantProductAMM` is direct but thin. Kyle (§9), the square-root law
(§10), time-inconsistent control (§11) and Epstein–Zin (§12) have no substrate
here. The curse-of-dimensionality problem (§4) has **none at all**.

### The recommendation

Unchanged across all four rounds, which is itself the strongest evidence for
it: start where built code and durable evidence overlap — **§2 (SVI)**, **§1
(American convexity for `0 < q < r`)**, and **§5 (impact kernels)**. All three
are certificate-shaped: the answer is a polynomial positivity, a
bounded-parameter-window convexity argument, or an explicit finite
counterexample. That is the one class where a proof assistant adjudicates
rather than taxes.

Avoid Class C entries as *starting* points — they supplied essentially every
casualty across four rounds. And before committing to **any** entry here,
re-run the resolution search: this list decayed at roughly a third per
verification round while it was being written.

Formalizing the *statement* of an open problem, and its known partial results,
is normal library work with a guaranteed floor — and it is what makes a later
resolution instantly checkable rather than referee-dependent. That is an
argument for doing it first, not for gating the mathematics behind it.

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
