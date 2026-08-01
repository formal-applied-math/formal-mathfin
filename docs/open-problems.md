# Open problems in mathematical finance — a verified survey

**Purpose.** This library formalizes *known* mathematics. This document is the
scouting report for the other activity: genuinely unsolved problems, and which
of them our existing formalization actually gives us leverage on.

**Method, and what it cost.** Every claim was checked against current
literature (2026-08). The failure mode guarded against is asserting a problem
is open when it was closed — often recently. Two adversarial rounds were run,
the second one searching specifically for *resolutions* rather than for the
problems:

| | entries examined | wrong or overstated |
|---|---|---|
| Round 1 | 36 | 16 |
| Round 2 (adversarial, on the 16 survivors) | 16 | 3 closed, 2 substantially narrowed |

**Treat Tier 1 as having a shelf life.** Each round removed roughly a third of
what survived the previous one. That is not sloppiness in the rounds — it is
what the field's velocity looks like from the outside, and "open problem"
folklore lags the literature by years. Re-run this check before committing
effort to anything here.

arXiv is unreachable from the verification environment (network policy), so
sources are publisher pages, author preprints, and mirrors. Tier 2's
"residual" column reports what the closing papers say they left open; those
residuals were **not** independently re-verified.

---

## Tier 1 — verified open

### 1. Global well-posedness of Musiela's SPDE

The forward-rate curve as a state, `r(t,x) = f(t,t+x)`. Local mild solutions
exist in Filipović's Hilbert space `H_β` of absolutely continuous curves.

**Open, and stated as such in the literature:** find the *right* space to study
Musiela's SPDE — one whose elements admit a continuous modification *and* which
supports existence and uniqueness of **global** mild solutions. This is
**not solved even in the case of Brownian noise**. Invariant measures have
sufficient conditions in weighted Lebesgue spaces only.

*Confidence: high — survived both rounds, with the open status stated
explicitly in the source rather than inferred.*

### 2. Convexity of the American exercise boundary for `0 < q < r`

The status is a clean trichotomy in the dividend yield `q`:

| regime | status |
|---|---|
| `q = 0` | convexity **proved** (Chen–Chadam–Cheng–Saunders; Ekström) |
| `q > r` | convexity **disproved** — the boundary is not convex |
| `0 < q < r` | **open** — observed numerically, no rigorous proof |

Under jump diffusions the *regularity* side is settled separately: the free
boundary is `C¹` except at maturity, `C^∞` under a regularity assumption on the
jump distribution, with continuity and near-maturity estimates proven.

**Open:** the intermediate dividend window. The smallest and most sharply
bounded problem on this list.

*Confidence: high — no 2024–2026 resolution found on a targeted search.*

### 3. Explicit semialgebraic no-butterfly domain for 5-parameter SVI

Butterfly-freeness of an SVI slice is `g(k) ≥ 0` for all `k` (Durrleman), where
`w(k) = a + b(ρ(k−m) + √((k−m)² + σ²))`. Martini–Mingone characterized the
domain completely, but evaluating their conditions **requires numerical
minimization of two functions plus root-finding**. Explicit closed forms exist
only for sub-SVIs (symmetric SVI, SSVI) — and the most recent refinement
(*J. Computational Finance*) is again for **SSVI** slices, not full SVI.

**Open:** eliminating the inner numerics — a fully explicit description of the
domain as polynomial inequalities in `(a,b,ρ,m,σ)`. Substituting
`y = (k−m)/σ`, `z = √(y²+1)` makes this positivity of an explicit polynomial on
a real algebraic curve: a quantifier-elimination problem.

*Confidence: high — survived both rounds.*

### 4. Multidimensional shadow prices under transaction costs

Shadow prices can fail to exist even for a log-investor in an arbitrage-free
market with bounded prices and arbitrarily small proportional costs. Short-sale
constraints are sufficient for existence, even in general multi-currency models
with discontinuous bid–ask spreads. But the multidimensional construction
proceeds asset-by-asset, and complete results exist **only in the two-asset
case**; whether existence holds in generality "has remained elusive."

**Open:** existence in genuine multi-asset settings. Dual minimizers always
give a "local" shadow price but need not give a global one.

*Confidence: high.*

### 5. Curse of dimensionality for fully nonlinear PDEs

Overcome for semilinear parabolic PDEs (multilevel Picard; deep networks —
Hutzenthaler–Jentzen–Kruse–Nguyen and successors, including gradient-dependent
nonlinearities). No result exists for a **non-affine-linear coefficient in
front of the second-order operator**.

**Open, with a negative result to push against:** full-history recursive
multilevel Picard *provably suffers* from the curse of dimensionality for the
HJB equation of a stochastic control problem (2026).

*Confidence: high — round 1 only, but the evidence is a direct negative
theorem rather than an absence of results.*

### 6. Sharp no-manipulation characterization for nonlinear and cross-impact

For linear transient impact, no-dynamic-arbitrage ⟺ positive semi-definiteness
of the propagator kernel `G`; a nonconstant nonincreasing convex decay kernel
gives a unique optimal strategy with no transaction-triggered manipulation, and
manipulation appears as soon as convexity fails near zero.

**Open:** the nonlinear case, where known conditions are necessary *or*
sufficient but do not meet and the models display pathologies; and multi-asset
cross-impact, where only easily-verifiable *necessary* conditions are known.

*Confidence: high, but this area is moving fast — concave cross-impact work
appeared mid-2026. Re-check before committing.*

### 7. MFG master equation without monotonicity

Under monotonicity the master equation has a unique solution. Without it,
classical well-posedness breaks down in finite time and the number of solutions
can grow arbitrarily with the horizon.

**Open, and explicitly called "a great challenge":** a weak-solution notion
that *selects* mean-field Nash equilibria. Entropy-type weak solutions exist
for potential MFGs but need not select.

*Confidence: medium-high — round 1 only.*

### 8. Radner equilibrium in incomplete continuous-time markets

Existence is known under "smallness"-type assumptions. The general problem
reduces to fully-coupled systems of quadratic BSDEs with discontinuous
generators.

**Open:** global existence for those systems. Pareto optimality — the standard
route in complete markets — is unavailable.

*Confidence: medium-high — round 1 only.*

### 9. Multidimensional MOT and its set-theoretic dependence

Better developed than usually stated: the De March–Touzi irreducible paving is
canonical and quasi-sure duality extends to multiple dimensions. But structure
results for optimal couplings hold in dimensions 1–3 given the target dominated
by Lebesgue, and **in general dimension only under an assumption implied by the
Continuum Hypothesis**.

**Open:** removing that dependence. A targeted search found no work doing so.

*Confidence: high — survived both rounds.*

### 10. Non-affine finite-dimensional realizations for Lévy HJM

Tappe characterized *affine* realizations for Lévy term-structure models (2012;
Lévy-driven SPDEs 2019). Jumps severely restrict which models admit
finite-dimensional realizations, in sharp contrast to the Wiener case.

**Open:** the general non-affine classification, the jump analogue of
Björk–Svensson's Lie-algebraic theory.

*Confidence: medium — round 1 only.*

### 11. Short-time uniqueness for the supercooled Stefan problem

*Substantially narrowed in round 2.* This was the first draft's headline pick;
2025–2026 work has taken most of it. Muñoz (2025) proved the free boundary is
`C¹` in space and `C^∞` off a countable set assuming only integrable initial
temperature, resolved the conjecture that jump times cannot accumulate, and —
decisively — proved that **short-time uniqueness of physical solutions implies
global uniqueness**, answering two previously-open questions. Separate 2026
work gives uniqueness of maximal weak solutions in 1D, and regularity in
arbitrary dimensions.

**Open:** short-time uniqueness itself, for initial data outside the current
well-posedness regime. Still open, but now a reduction away from resolution
rather than a frontier.

*Confidence: high on the narrowing; the residual is as the closing paper
frames it.*

### 12. AMM design and the LP/arbitrageur/retail equilibrium

*Narrowed in round 2.* The single-LP fee problem is largely solved: the LP's
expected-utility problem reduces to an **ergodic control problem** with the
optimal fee a pointwise volatility feedback, characterized under stochastic
volatility by a scalar ergodic HJB plus a linear Poisson equation (2026), and
the optimal dynamic fee weakly dominates static and volatility-linked
heuristics.

**Open:** the *equilibrium* between LPs, arbitrageurs and fee-elastic retail
flow, and optimal AMM **design** (the choice of invariant curve) under general
demand.

### 13. Optimal execution on AMMs under transient impact

Nascent rather than deeply open — first preprints on Uniswap v2/v3 and
CPAMM/CLAMM execution appeared in 2026.

---

## Tier 2 — narrowed or closed

Entries that earlier drafts of this list carried as open. Recorded rather than
deleted: the closing result is usually the more useful fact. **Round 2**
additions are marked.

| Problem as commonly stated | What closed it | Residual |
|---|---|---|
| **[R2]** Bass martingale uniqueness / classification in `d ≥ 2` | The decomposition of stretched Brownian motion into Bass martingales: for general non-irreducible pairs, SBM decomposes on a canonical paving into cells that are each irreducible, with a Bass martingale on each — the global process is a mixture. What the first draft quoted *as* the open state was the resolution. | `q`-Bass extensions; convergence of dual optimising sequences |
| **[R2]** Pathwise uniqueness for rough/square-root Volterra | Prömel–Scheffels (2025) establish pathwise uniqueness for a broad class of singular SVEs; Hölder coefficients `sgn(x)|x|^ξ`, `ξ ∈ [1/2,1]`, cover the square-root case and apply to rough Heston | Jump-diffusion settings need extra monotonicity conditions |
| **[R2]** Elicitability of systemic risk measures | CoVaR, CoES and MES fail identifiability and elicitability alone; joint identifiability with the reference VaR holds but joint **elicitability fails** — resolved by a new notion of *multi-objective* (lexicographically ordered bivariate) scores, with Diebold–Mariano-type tests | Set-valued systemic measures; practical test power |
| No-trade region shape, multi-asset proportional costs | The region is an **ellipsoid** around the frictionless target, shape given by a matrix-valued algebraic Riccati equation, even in high dimensions | Exact/non-asymptotic solutions beyond independent assets; the case *with return predictability* |
| MOT dual attainment / duality gap | Beiglböck–Nutz–Touzi complete quasi-sure duality on the line; Beiglböck–Lim–Obłój sharpness (`C²` attains, `C^{2−ε}` counterexamples) | Higher dimensions; continuous-time multi-marginal |
| Stability of MOT | Backhoff-Veraguas–Pammer and Wiesel, in great generality — answered Alfonsi–Corbetta–Jourdain positively | Quantitative stability rates |
| Kellerer / mimicking Markov martingales in `d ≥ 2` | Regularized version proven: after Gaussian regularization a strongly Markovian mimicking Itô diffusion exists | Counterexamples show regularization is *necessary* and uniqueness fails — the question is the minimal regularization |
| N-player → MFG convergence without uniqueness | Lacker (2018): convergence holds even when the MFG equilibrium is non-unique; every limit point is a weak MFG equilibrium | The **converse** — which weak MFG equilibria actually arise as limits |
| Sharp rates for Markovian approximation of rough vol | Strong rates proven (Bayer–Breneis; superpolynomial in `N` under Lipschitz coefficients) | Weak rates; non-Lipschitz coefficients |
| Characterization of arbitrage-free IV surfaces | Roper (sufficient, close to necessary); Fukasawa (2012) `−d₁`/`−d₂` monotonicity; Lucic extended to general continuous IV and linked calendar to strike arbitrage | Folds entirely into the parametric-family problem (Tier 1 §3) |
| Endogenous derivation of the impact propagator | Microfounded via stationary Kyle setups, latent order books, and Nash equilibria of permanent-impact games | Reproducing empirical power-law decay from equilibrium; full multi-asset microfoundation |
| Hawkes order flow + transient impact | Alfonsi–Blanc closed-form with viability conditions excluding manipulation; 2025 frameworks with Markovian representations | General/power-law kernels beyond completely-monotone approximations |
| Regularity of multidimensional stopping boundaries | Laurence–Salsa (`C^∞` for multi-dim GBM); Peskir (2-D continuity); De Angelis–Peskir (global `C¹` value function) | General theory without problem-specific input; explicit multi-asset solutions, absent even in the perpetual case |
| Deep hedging / signature methods lack theory | Universal approximation with convergence guarantees; tight dual bounds; convergence proofs for signature methods, primal and dual, non-Markovian included | Generalization and sample-complexity bounds explaining practice |
| Uniqueness of clearing vectors | Non-uniqueness under bankruptcy costs + fire sales + cross-holdings is an *established result*; the equilibrium set need not be connected | Characterization and equilibrium selection |
| Ross recovery conditions | Borovička–Hansen–Scheinkman: recovery is valid only if the martingale component of the pricing kernel is constant | What alternative identifying restrictions restore recovery |
| Joint SPX/VIX smile calibration | Guyon (2020) via dispersion-constrained martingale transport; continuous time by martingale interpolation; signature and Gaussian-polynomial-volatility models (2025) | A genuinely parsimonious low-dimensional continuous-time model |
| Positivity-constrained term structure | Filipović–Tappe–Teichmann characterized positivity-preserving models via characteristic coefficients | Essentially closed |
| Minimax rates for risk-measure estimation | Optimal nonparametric ES estimation (2024) attains optimal properties under minimal assumptions at all finite sample sizes, adversarially robust | Essentially closed |

---

## Where *this repo* gives leverage

Ranked by **distance from what we have already built**, not by mathematical
interest. Adjacency is judged against built code; where a target leans on a
planned-but-unbuilt program, that is stated.

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
bridge plausible rather than automatic. Rose in this ranking after round 2
sharpened the problem to a bounded dividend window.

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
summit shipping `placeholder`. The problem is on our roadmap by name, and after
round 2 it is also the **best-verified** open problem here.

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

Gap: FDR theory needs Lie-algebraic / infinite-dimensional differential
geometry that neither this library nor Mathlib carries.

### 6. Supercooled Stefan (§11) — substrate weak, and the target shrank

`Foundations/ExitTime` gives genuine hitting-time machinery (`exitTime`,
`isStoppingTime_exitTime`, `isLocalizingSequence_exitTime`).
`FixedIncome/FirstToDefault` and `KMVMertonStructural` give default models —
but `FirstToDefault` is **constant-hazard with independent names**, and
`KMVMertonStructural` is the **one-period Merton** distance-to-default
(`survival_probability_eq_Phi_distanceToDefault`, `merton_equity_eq_bs_call`),
not a first-passage barrier model. The problem needs *interacting* first-passage
times and McKean–Vlasov limits.

Round 2 removed the case for prioritising this: it was the top mathematical
pick on the strength of an open-uniqueness claim that Muñoz has since reduced
to short-time uniqueness.

**Thin or absent.** `RiskMeasures/RockafellarUryasev.gaussianCVaR_isLeast_ruObjective`
is a genuine seed for scoring-function work — CVaR as the *minimizer* of a
one-parameter objective is exactly the variational form behind the (VaR, ES)
consistent score — but round 2 closed the systemic-elicitability target via
multi-objective elicitability, so generalizing RU beyond the Gaussian case is
now ordinary library work, not frontier. `DeFi/ConstantProductAMM` is direct but
thin. The curse-of-dimensionality problem (§5) has **no** adjacency at all.

### The recommendation this produces

Unchanged by round 2, and now better supported: start where built code and open
mathematics overlap — **§3 (SVI)** and **§6 (impact kernels)**, with **§2
(American convexity for `0 < q < r`)** promoted to join them. All three are
certificate-shaped: the answer is a polynomial positivity, an explicit finite
counterexample, or a bounded-parameter-window convexity argument. That is the
one class where a proof assistant adjudicates rather than taxes.

Treat **§1 (Musiela)** as the long-horizon target: it is the best-verified open
problem on the list *and* the one our roadmap already names — but the honest
prerequisite is finishing the HJM program that `docs/hjm-program.md` specifies.

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
[Guyon, the joint SPX/VIX puzzle solved](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=3397382) ·
[Signature-based joint calibration](https://onlinelibrary.wiley.com/doi/10.1111/mafi.12442)

Rough volatility —
[Weak existence/uniqueness for affine SVEs with `L¹` kernels](https://www.researchgate.net/publication/337966379_Weak_existence_and_uniqueness_for_affine_stochastic_Volterra_equations_with_L1-kernels) ·
[Pathwise uniqueness for singular SVEs with Hölder coefficients](https://arxiv.org/html/2212.08029) ·
[Stochastic Volterra equations with Hölder diffusion coefficients](https://www.sciencedirect.com/science/article/abs/pii/S030441492300073X) ·
[Markovian approximations of SVEs with the fractional kernel](https://www.tandfonline.com/doi/full/10.1080/14697688.2022.2139193)

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
[Radner equilibrium and quadratic BSDEs](https://link.springer.com/article/10.1007/s11579-016-0161-0) ·
[On non-uniqueness in mean field games](https://arxiv.org/pdf/1908.06207) ·
[Convergence of closed-loop Nash equilibria to the MFG limit (Lacker)](https://arxiv.org/abs/1808.02745)

Term structure —
[Local well-posedness of Musiela's SPDE with Lévy noise](https://arxiv.org/pdf/0704.2380) ·
[Existence of affine realizations for Lévy term-structure models](https://arxiv.org/pdf/1907.02363) ·
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
