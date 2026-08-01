# Open problems in mathematical finance — a verified survey

**Purpose.** This library formalizes *known* mathematics. This document is the
scouting report for the other activity: genuinely unsolved problems, and which
of them our existing formalization actually gives us leverage on.

## How this list was built, and why it is organized by evidence

Three adversarial rounds were run against current literature (2026-08), the
second and third searching for *resolutions* rather than for problems:

| round | entries examined | outcome |
|---|---|---|
| 1 | 36 | 16 wrong or overstated |
| 2 | 16 survivors | 3 closed, 2 substantially narrowed |
| 3 | 5 never-re-checked | 2 closed |

Each pass removed roughly a third of what the previous one left. That is not
sloppiness in the passes — it is what a fast-moving field looks like from
outside. But the attrition was **not uniform**, and the pattern is the useful
output of this exercise:

> Nearly every casualty came from entries whose openness I had *inferred from
> not finding a resolution*. Entries where a source **states** the problem is
> unsolved survived — and the two that did not survive failed because the
> stating source had itself been superseded.

So each entry below carries an **evidence class** and the **date of the most
recent source asserting openness**. Age of the openness claim, not subject
matter, is the best available predictor of whether an entry is real.

| class | meaning | track record |
|---|---|---|
| **A — asserted** | a source explicitly says the problem is unsolved | survived unless the source aged out |
| **B — bounded** | a proved positive result and a proved negative result bracket the gap; the open region is delimited by theorems | survived |
| **C — inferred** | no resolution found on search | **essentially all fatalities** |

Class C entries are retained but should be treated as *leads*, not facts.
Re-verify anything here before spending effort on it; a fourth round would
likely remove one or two more.

arXiv is unreachable from this environment (network policy), so sources are
publisher pages, author preprints, and mirrors. Tier 2's "residual" column
reports what the closing papers say they left open; those residuals were not
independently re-verified.

---

## Tier 1 — surviving open problems

### 1. Global well-posedness of Musiela's SPDE
**Class A · openness asserted as of 2025 · strongest entry here**

The forward-rate curve as a state, `r(t,x) = f(t,t+x)`. Local mild solutions
exist in Filipović's Hilbert space `H_β` of absolutely continuous curves.

**Open:** find the *right* space — one whose elements admit a continuous
modification *and* which supports existence and uniqueness of **global** mild
solutions. The literature states this is **not solved even in the case of
Brownian noise**. Invariant measures have sufficient conditions in weighted
Lebesgue spaces only.

The only entry whose open status is quoted rather than inferred, and it
survived all three rounds untouched.

### 2. Convexity of the American exercise boundary for `0 < q < r`
**Class B · bracketed by theorems on both sides**

A clean trichotomy in the dividend yield `q`:

| regime | status |
|---|---|
| `q = 0` | convexity **proved** (Chen–Chadam–Cheng–Saunders; Ekström) |
| `q > r` | convexity **disproved** — the boundary is not convex |
| `0 < q < r` | **open** — observed numerically, no rigorous proof |

Regularity under jump diffusions is settled separately: `C¹` except at
maturity, `C^∞` under a regularity assumption on the jump distribution, with
continuity and near-maturity estimates proven.

The smallest and most sharply bounded problem on this list — the open region is
an interval defined by two theorems, not by absence of literature.

### 3. Explicit semialgebraic no-butterfly domain for 5-parameter SVI
**Class A · openness asserted as of 2022, restated 2025–26**

Butterfly-freeness of an SVI slice is `g(k) ≥ 0` for all `k` (Durrleman), where
`w(k) = a + b(ρ(k−m) + √((k−m)² + σ²))`. Martini–Mingone characterized the
domain completely, but their conditions **require numerical minimization of two
functions plus root-finding** — stated in the papers themselves. Explicit closed
forms exist only for sub-SVIs, and the most recent refinement
(*J. Computational Finance*) is again for **SSVI** slices, not full SVI.

**Open:** eliminating the inner numerics — an explicit description of the domain
as polynomial inequalities in `(a,b,ρ,m,σ)`. Substituting `y = (k−m)/σ`,
`z = √(y²+1)` makes this positivity of a polynomial on a real algebraic curve:
a quantifier-elimination problem.

### 4. Multidimensional shadow prices under transaction costs
**Class A · "has remained elusive", restated 2024–25**

Shadow prices can fail to exist even for a log-investor in an arbitrage-free
market with bounded prices and arbitrarily small proportional costs. Short-sale
constraints suffice for existence, even in general multi-currency models with
discontinuous bid–ask spreads. But the multidimensional construction proceeds
asset-by-asset and complete results exist **only in the two-asset case**.

**Open:** existence in genuine multi-asset settings. Dual minimizers always give
a "local" shadow price but need not give a global one.

### 5. Curse of dimensionality for fully nonlinear PDEs
**Class B · a negative theorem delimits the gap (2026)**

Overcome for semilinear parabolic PDEs — multilevel Picard and deep networks,
including gradient-dependent nonlinearities, Lipschitz nonlinearities, and
PIDEs. Every positive result is **semilinear**; none covers a non-affine-linear
coefficient in front of the second-order operator.

**Open, with a negative result to push against:** full-history recursive
multilevel Picard *provably suffers* from the curse of dimensionality for the
HJB equation of a stochastic control problem.

### 6. Sharp no-manipulation characterization for nonlinear and cross-impact
**Class B · necessary and sufficient conditions both proved, and they do not meet**

For linear transient impact, no-dynamic-arbitrage ⟺ positive semi-definiteness
of the propagator kernel `G`; a nonconstant nonincreasing convex decay kernel
gives a unique optimal strategy with no transaction-triggered manipulation, and
manipulation appears as soon as convexity fails near zero.

**Open:** the nonlinear case, where the known conditions are necessary *or*
sufficient but do not meet and the models display pathologies; and multi-asset
cross-impact, where only easily-verifiable *necessary* conditions are known.

*Moving fast — concave cross-impact work appeared mid-2026. Re-check first.*

### 7. Set-theoretic dependence in multidimensional MOT
**Class B · the assumption is explicit in the theorems**

The De March–Touzi irreducible paving is canonical and quasi-sure duality
extends to multiple dimensions. But structure results for optimal couplings
hold in dimensions 1–3 given the target dominated by Lebesgue, and **in general
dimension only under an assumption implied by the Continuum Hypothesis**.

**Open:** removing that dependence. A targeted search found no work doing so.

### 8. Short-time uniqueness for the supercooled Stefan problem
**Class A · residual framed by the closing paper (2025)**

*Substantially narrowed in round 2* — this was the first draft's headline pick.
Muñoz (2025) proved the free boundary is `C¹` in space and `C^∞` off a countable
set assuming only integrable initial temperature, resolved the conjecture that
jump times cannot accumulate, and proved that **short-time uniqueness of
physical solutions implies global uniqueness**, answering two previously-open
questions. Separate 2026 work gives uniqueness of maximal weak solutions in 1D
and regularity in arbitrary dimensions.

**Open:** short-time uniqueness itself, for initial data outside the current
well-posedness regime — a reduction away from resolution, not a frontier.

### 9. AMM design and the LP/arbitrageur/retail equilibrium
**Class A · "major unsolved problem" as of 2025–26**

*Narrowed in round 2.* The single-LP fee problem is largely solved: the LP's
expected-utility problem reduces to an **ergodic control problem** with the
optimal fee a pointwise volatility feedback, characterized under stochastic
volatility by a scalar ergodic HJB plus a linear Poisson equation (2026).

**Open:** the *equilibrium* between LPs, arbitrageurs and fee-elastic retail
flow, and optimal AMM **design** (choice of invariant curve) under general
demand.

### 10. Non-affine finite-dimensional realizations for Lévy HJM
**Class C — inferred. Treat as a lead.**

Tappe characterized *affine* realizations for Lévy term-structure models;
Platen–Tappe extend to the real-world measure, where jumps of infinite activity
severely restrict the market price of risk — typically forcing it constant.
Jumps sharply limit which models admit finite-dimensional realizations, in
contrast to the Wiener case.

**Apparently open:** the general non-affine classification, the jump analogue of
Björk–Svensson's Lie-algebraic theory. No source found *asserting* this is open;
the claim rests on not finding one that closes it.

### 11. Optimal execution on AMMs under transient impact
**Class C — nascent rather than open**

First preprints on Uniswap v2/v3 and CPAMM/CLAMM execution appeared in 2026.
Listed for completeness; a young literature is not the same as a hard problem.

---

## Tier 2 — narrowed or closed

Entries earlier drafts carried as open. Recorded rather than deleted: the
closing result is usually the more useful fact. Round marked where relevant.

| Problem as commonly stated | What closed it | Residual |
|---|---|---|
| **[R3]** MFG master equation without monotonicity | Mou–Zhang, *master equations with anti-monotonicity conditions* (JEMS 2025); and uniqueness holds with **no** monotonicity constraint by reading the master equation in a conservative sense, adapting hyperbolic-systems arguments | Whether a weak-solution notion *selects* Nash equilibria — entropy solutions need not |
| **[R3]** Radner equilibrium beyond smallness | Xing–Žitković, globally solvable Markovian quadratic BSDE systems (*Ann. Prob.*), overcame smallness; global existence of incomplete finite-agent Radner equilibrium under Markovian assumptions; limited-participation existence with exponential preferences | Non-Markovian settings; general preferences |
| **[R2]** Bass martingale uniqueness / classification in `d ≥ 2` | The decomposition of stretched Brownian motion into Bass martingales: for non-irreducible pairs, SBM decomposes on a canonical paving into cells that are each irreducible, with a Bass martingale on each. What an earlier draft quoted *as* the open state was the resolution. | `q`-Bass extensions; convergence of dual optimising sequences |
| **[R2]** Pathwise uniqueness for rough/square-root Volterra | Prömel–Scheffels (2025) for a broad class of singular SVEs; Hölder coefficients `sgn(x)\|x\|^ξ`, `ξ ∈ [1/2,1]`, cover the square-root case and apply to rough Heston | Jump-diffusion settings need extra monotonicity |
| **[R2]** Elicitability of systemic risk measures | CoVaR, CoES, MES fail identifiability and elicitability alone; joint identifiability with the reference VaR holds but joint **elicitability fails** — resolved by *multi-objective* (lexicographically ordered bivariate) scores with Diebold–Mariano-type tests | Set-valued systemic measures; test power |
| No-trade region shape, multi-asset proportional costs | An **ellipsoid** around the frictionless target, shape given by a matrix-valued algebraic Riccati equation, even in high dimensions | Exact solutions beyond independent assets; the case *with return predictability* |
| MOT dual attainment / duality gap | Beiglböck–Nutz–Touzi complete quasi-sure duality on the line; Beiglböck–Lim–Obłój sharpness (`C²` attains, `C^{2−ε}` counterexamples) | Higher dimensions; continuous-time multi-marginal |
| Stability of MOT | Backhoff-Veraguas–Pammer and Wiesel, in great generality — answered Alfonsi–Corbetta–Jourdain positively | Quantitative stability rates |
| Kellerer / mimicking Markov martingales in `d ≥ 2` | Regularized version proven: after Gaussian regularization a strongly Markovian mimicking Itô diffusion exists | Counterexamples show regularization is *necessary* and uniqueness fails — the question is the minimal regularization |
| N-player → MFG convergence without uniqueness | Lacker (2018): convergence holds even when the MFG equilibrium is non-unique; every limit point is a weak MFG equilibrium | The **converse** — which weak MFG equilibria arise as limits |
| Sharp rates for Markovian approximation of rough vol | Strong rates proven (Bayer–Breneis; superpolynomial in `N` under Lipschitz coefficients) | Weak rates; non-Lipschitz coefficients |
| Characterization of arbitrage-free IV surfaces | Roper (sufficient, close to necessary); Fukasawa (2012); Lucic extended to general continuous IV and linked calendar to strike arbitrage | Folds into the parametric-family problem (§3) |
| Endogenous derivation of the impact propagator | Microfounded via stationary Kyle setups, latent order books, Nash equilibria of permanent-impact games | Reproducing empirical power-law decay from equilibrium; multi-asset microfoundation |
| Hawkes order flow + transient impact | Alfonsi–Blanc closed-form with viability conditions excluding manipulation; 2025 frameworks with Markovian representations | General/power-law kernels beyond completely-monotone approximations |
| Regularity of multidimensional stopping boundaries | Laurence–Salsa (`C^∞` for multi-dim GBM); Peskir (2-D continuity); De Angelis–Peskir (global `C¹` value function) | General theory without problem-specific input; explicit multi-asset solutions, absent even in the perpetual case |
| Deep hedging / signature methods lack theory | Universal approximation with convergence guarantees; tight dual bounds; convergence proofs for signature methods, primal and dual | Generalization and sample-complexity bounds explaining practice |
| Uniqueness of clearing vectors | Non-uniqueness under bankruptcy costs + fire sales + cross-holdings is *established*; the equilibrium set need not be connected | Characterization and equilibrium selection |
| Ross recovery conditions | Borovička–Hansen–Scheinkman: valid only if the martingale component of the pricing kernel is constant | What alternative identifying restrictions restore recovery |
| Joint SPX/VIX smile calibration | Guyon (2020) via dispersion-constrained martingale transport; continuous time by martingale interpolation; signature and Gaussian-polynomial models (2025) | A parsimonious low-dimensional continuous-time model |
| Positivity-constrained term structure | Filipović–Tappe–Teichmann characterized positivity-preserving models via characteristic coefficients | Essentially closed |
| Minimax rates for risk-measure estimation | Optimal nonparametric ES estimation (2024) attains optimal properties under minimal assumptions at all finite sample sizes | Essentially closed |

---

## Where *this repo* gives leverage

Ranked by **distance from what we have already built**, not by mathematical
interest. Adjacency is judged against built code; where a target leans on a
planned-but-unbuilt program, that is stated. Note that the three rounds of
attrition barely touched this ranking — the targets with the best repo
adjacency were also the ones with the most durable evidence, which is a
coincidence worth not over-reading.

### 1. SVI butterfly domain (§3) — strongest built-code adjacency

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

### 2. American boundary convexity for `0 < q < r` (§2) — strong module set, one seam

`Binomial/SnellEnvelope.americanPrice_is_snell_envelope` plus `Binomial/American`,
`AmericanCallNoDividend`, `Bermudan`, `MertonAmericanCallTree`,
`BlackScholes/Dividends`, and the convexity trio (`StrikeConvexity`,
`PutStrikeConvexity`, `SpotConvexity`). `Binomial/CRRConvergence` is the
discrete→continuous seam.

Gap, and it is genuine: our American machinery is **binomial/discrete**, while
the problem concerns the *continuous* free boundary. CRRConvergence makes the
bridge plausible rather than automatic.

### 3. Impact-kernel positive-definiteness (§6) — cheapest decisive output

| Existing | What it gives |
|---|---|
| `Portfolio/CovariancePSD.covariance_kernel_psd`, `portfolioVarN_covariance_nonneg` | a PSD-quadratic-form theorem over a kernel — the exact shape of the no-dynamic-arbitrage criterion |
| `Foundations/AlmgrenChriss.almgrenChrissPath_satisfies_EL` | the execution Euler–Lagrange path |
| `Foundations/NoArbitrageCore`, `TriangleArbitrage` | no-arbitrage predicates to land the statement on |

Gap: our Almgren–Chriss is the deterministic permanent+temporary model with
**no decay kernel** — the propagator must be built. Small build, and refutation
is cheap: a counterexample is an explicit kernel plus a *finite* schedule with
negative expected cost, i.e. rational arithmetic closable by `norm_num`/`ring`.

### 4. Musiela global well-posedness (§1) — highest conceptual alignment, longest runway

`docs/hjm-program.md` already names Musiela as node **G4**, the deferred SPDE
summit shipping `placeholder`. The problem is on our roadmap by name, and it is
the best-evidenced open problem here.

Honest gap: **neither `MathFin/FixedIncome/HJM/` nor
`MathFin/Foundations/StochasticFubini*.lean` exists yet.** The HJM program is
*ratified, not built* — the whole F1→C4 chain precedes G4. Adjacency is to a
plan, not to code.

### 5. Lévy HJM finite-dimensional realizations (§10) — real tower, heavy missing geometry

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
`RiskMeasures/RockafellarUryasev.gaussianCVaR_isLeast_ruObjective` is a genuine
seed for scoring-function work, but round 2 closed the systemic-elicitability
target, so generalizing RU beyond the Gaussian case is ordinary library work
now, not frontier. `DeFi/ConstantProductAMM` is direct but thin. The
curse-of-dimensionality problem (§5) has **no** adjacency at all.

### The recommendation

Unchanged across all three rounds, which is itself the strongest evidence for
it: start where built code and durable evidence overlap — **§3 (SVI)**, **§2
(American convexity for `0 < q < r`)**, and **§6 (impact kernels)**. All three
are certificate-shaped: the answer is a polynomial positivity, a
bounded-parameter-window convexity argument, or an explicit finite
counterexample. That is the one class where a proof assistant adjudicates
rather than taxes.

Treat **§1 (Musiela)** as the long-horizon target — best-evidenced problem on
the list and already named in our roadmap, but the honest prerequisite is
finishing the HJM program `docs/hjm-program.md` specifies.

Avoid Class C entries as *starting* points. They are the evidence class that
supplied essentially every casualty across three rounds.

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
[Dynamic optimal execution in a mixed-market-impact Hawkes model](https://link.springer.com/article/10.1007/s00780-015-0282-y) ·
[A stationary Kyle setup: microfounding propagator models](https://www.researchgate.net/publication/346090035_A_Stationary_Kyle_Setup_Microfounding_propagator_models)

Frictions —
[Portfolio choice with transaction costs: a user's guide](https://www.guasoni.com/papers/transreview.pdf) ·
[Asymptotic methods for transaction costs](https://arxiv.org/pdf/2407.07100) ·
[Transaction costs, shadow prices and duality in discrete time](https://www.mat.univie.ac.at/~schachermayer/pubs/preprnts/prpr0156.pdf) ·
[Almost perfect shadow prices](https://www.mdpi.com/1911-8074/17/2/70)

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

Term structure —
[Local well-posedness of Musiela's SPDE with Lévy noise](https://arxiv.org/pdf/0704.2380) ·
[Existence of affine realizations for Lévy term-structure models](https://arxiv.org/pdf/1907.02363) ·
[Affine realizations for Lévy driven models under the real-world measure](https://www.uts.edu.au/globalassets/sites/default/files/qfr-archive-03/QFR-rp289.pdf) ·
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
