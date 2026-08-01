# Open problems in mathematical finance — a verified survey

**Purpose.** This library formalizes *known* mathematics. This document is the
scouting report for the other activity: genuinely unsolved problems, and which
of them our existing formalization actually gives us leverage on.

**Method and its limits.** Every claim below was checked against current
literature (2026-08). The failure mode being guarded against is the one that
matters — asserting a problem is open when it was closed, sometimes recently.
A first draft of this list had **16 of 36 entries wrong or overstated**, almost
all in that direction; the corrections are recorded in Tier 2 rather than
silently dropped, because *what closed a problem* is usually more useful than
the problem. arXiv is unreachable from the verification environment (network
policy), so sources are publisher pages, author preprints, and mirrors.

Confidence is stated per entry. Tier 2's "residual" column reports what the
closing papers say they left open; those residuals were **not** independently
re-verified.

---

## Tier 1 — verified open

### 1. Uniqueness of physical solutions to the supercooled Stefan problem

McKean–Vlasov dynamics with feedback through hitting times — the mean-field
limit of a particle system, and a genuine model of default cascades. Solutions
blow up; "physical" solutions are those with the correct cascade mechanism.
Cuchiero et al. proved the Delarue–Nadtochiy–Shkolnikov conjecture that minimal
solutions are physical whenever the initial condition is integrable, and
uniqueness is known for bounded, non-oscillatory densities.

**Open:** uniqueness within the physical class for *general* initial
conditions, and whether the unique minimal solution coincides with the physical
one. The sharpest statement on this list.

### 2. Global well-posedness of Musiela's SPDE

The forward-rate curve as a state, `r(t,x) = f(t,t+x)`. Local mild solutions
exist in Filipović's Hilbert space `H_β` of absolutely continuous curves.

**Open, and explicitly so even for Brownian noise:** finding the *right* state
space that simultaneously supports continuous modifications and yields global
mild existence and uniqueness. Invariant measures have sufficient conditions in
weighted Lebesgue spaces only.

### 3. Explicit semialgebraic no-butterfly domain for 5-parameter SVI

Butterfly-freeness of an SVI slice is `g(k) ≥ 0` for all `k` (Durrleman), where
`w(k) = a + b(ρ(k−m) + √((k−m)² + σ²))`. Martini–Mingone characterized the
domain completely, but evaluating their conditions **requires numerical
minimization of two functions plus root-finding**. Explicit closed forms exist
only for sub-SVIs (symmetric SVI, SSVI).

**Open:** eliminating the inner numerics — a fully explicit description of the
domain as polynomial inequalities in `(a,b,ρ,m,σ)`. Substituting
`y = (k−m)/σ`, `z = √(y²+1)` makes this positivity of an explicit polynomial on
a real algebraic curve: a quantifier-elimination problem.

### 4. Curse of dimensionality for fully nonlinear PDEs

Overcome for semilinear parabolic PDEs (multilevel Picard; deep networks —
Hutzenthaler–Jentzen–Kruse–Nguyen and successors, including gradient-dependent
nonlinearities). No result exists for a **non-affine-linear coefficient in
front of the second-order operator**.

**Open, with a negative result to push against:** full-history recursive
multilevel Picard *provably suffers* from the curse of dimensionality for the
HJB equation of a stochastic control problem (2026).

### 5. Convexity of the American exercise boundary

Regularity under jump diffusions is settled: the free boundary is continuously
differentiable except at maturity, infinitely differentiable under a regularity
assumption on the jump distribution, with continuity and near-maturity
estimates proven.

**Open:** convexity — including in plain Black–Scholes **with non-zero dividend
rate**, and within a specific parameter range. The smallest, sharpest problem
here.

### 6. Multidimensional shadow prices under transaction costs

Shadow prices can fail to exist even for a log-investor in an arbitrage-free
market with bounded prices and arbitrarily small proportional costs. Complete
results exist **only in the two-asset case**.

**Open:** existence in genuine multi-asset settings. Dual minimizers always
give a "local" shadow price but need not give a global one.

### 7. MFG master equation without monotonicity

Under monotonicity the master equation has a unique solution. Without it,
classical well-posedness breaks down in finite time and the number of solutions
can grow arbitrarily with the horizon.

**Open, and explicitly called "a great challenge":** a weak-solution notion
that *selects* mean-field Nash equilibria. Entropy-type weak solutions exist
for potential MFGs but need not select.

### 8. Radner equilibrium in incomplete continuous-time markets

Existence is known under "smallness"-type assumptions. The general problem
reduces to fully-coupled systems of quadratic BSDEs with discontinuous
generators.

**Open:** global existence for those systems. Pareto optimality — the standard
route in complete markets — is unavailable.

### 9. Bass martingales / stretched Brownian motion in `d ≥ 2`

Under irreducibility, existence and uniqueness hold and SBM coincides with the
Bass martingale. Without it, SBM decomposes into a possibly-uncountable family
of local Bass martingales on a canonical paving of `ℝᵈ` into relatively open
convex cells.

**Open:** uniqueness and full classification in the general (non-irreducible)
case; convergence rates for the `L²` gradient flow of the Bass functional.

### 10. Sharp no-manipulation characterization for nonlinear and cross-impact

For linear transient impact, no-dynamic-arbitrage ⟺ positive semi-definiteness
of the propagator kernel `G`; a nonconstant nonincreasing convex decay kernel
gives a unique optimal strategy with no transaction-triggered manipulation, and
manipulation appears as soon as convexity fails near zero.

**Open:** the nonlinear case, where known conditions are necessary *or*
sufficient but do not meet and the models display pathologies; and multi-asset
cross-impact, where only easily-verifiable *necessary* conditions are known.

### 11. Multidimensional MOT and its set-theoretic dependence

Better developed than usually stated: the De March–Touzi irreducible paving is
canonical and quasi-sure duality extends to multiple dimensions. But structure
results for optimal couplings hold in dimensions 1–3 given the target dominated
by Lebesgue, and **in general dimension only under an assumption implied by the
Continuum Hypothesis**.

**Open:** removing that dependence. More interesting than the vague
"extremal points" framing this entry originally had.

### 12. Non-affine finite-dimensional realizations for Lévy HJM

Tappe characterized *affine* realizations for Lévy term-structure models (2012;
Lévy-driven SPDEs 2019). Jumps severely restrict which models admit
finite-dimensional realizations, in sharp contrast to the Wiener case.

**Open:** the general non-affine classification, the jump analogue of
Björk–Svensson's Lie-algebraic theory.

### 13. Optimal AMM fee and design

Minimizing loss-versus-rebalancing while maximizing fee revenue is explicitly
described in the literature as a major unsolved problem. Dynamic-fee
constructions exist without optimality proofs; growth-optimal results collapse
to a static constant when volatility is constant.

**Open:** optimality, and the equilibrium between LPs, arbitrageurs, and
fee-elastic retail flow.

### 14. Pathwise uniqueness for rough volatility, and rigorous asymptotics

*Correction to a common overstatement:* weak existence and uniqueness in law
**are** established — Abi Jaber for affine stochastic Volterra equations with
`L¹` kernels, and Abi Jaber–Cuchiero–Larsson–Pulido for convolution-type SVEs.

**Open:** strong/pathwise uniqueness for non-Lipschitz (square-root) Volterra
dynamics; and full rigor for small-time / large-time / `H → 0` expansions,
several of whose steps are justified only formally.

### 15. Optimal execution on AMMs under transient impact

Nascent rather than deeply open — first preprints on Uniswap v2/v3 and
CPAMM/CLAMM execution appeared in 2026.

### 16. Elicitability of systemic risk measures *(medium confidence)*

The (VaR, ES) question is settled: ES is not elicitable alone but **is jointly
elicitable with VaR** (Fissler–Ziegel), enabling joint-score regression tests.
The systemic extension (CoVaR and relatives) and the right regulatory
characterization combining backtestability, robustness and surplus invariance
appear unsettled, but this entry was not pinned as precisely as the others.

---

## Tier 2 — narrowed: headline closed, smaller residual survives

These were on the first draft of this list as open. They are not, or not as
stated. Recorded because the closing result is usually the more valuable fact.

| Problem as commonly stated | What closed it | Residual |
|---|---|---|
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
| Ross recovery conditions | Borovička–Hansen–Scheinkman: recovery is valid only if the martingale component of the pricing kernel is constant; otherwise the recovered measure is a long-term risk-neutral one | What alternative identifying restrictions restore recovery |
| Joint SPX/VIX smile calibration | Guyon (2020) via dispersion-constrained martingale transport; continuous time by martingale interpolation; signature and Gaussian-polynomial-volatility models (2025) | A genuinely parsimonious low-dimensional continuous-time model |
| Positivity-constrained term structure | Filipović–Tappe–Teichmann characterized positivity-preserving models via characteristic coefficients | Essentially closed |
| Minimax rates for risk-measure estimation | Optimal nonparametric ES estimation (2024) attains optimal properties under minimal assumptions at all finite sample sizes, adversarially robust | Essentially closed |

---

## Where *this repo* gives leverage

The ranking above is by mathematical interest. This one is by **distance from
what we have already built** — and the two are close to inverses. That tension
is the main finding of this section, not a footnote.

Adjacency is judged against built code, not roadmap intent. Where a target
leans on a planned-but-unbuilt program, that is stated.

### Ranked by leverage

**1. SVI butterfly domain (Tier 1 §3) — strongest built-code adjacency.**

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

**2. Impact-kernel positive-definiteness and no-manipulation (Tier 1 §10) —
cheapest decisive output.**

| Existing | What it gives |
|---|---|
| `Portfolio/CovariancePSD.covariance_kernel_psd`, `portfolioVarN_covariance_nonneg` | a PSD-quadratic-form theorem over a kernel — the exact shape of the no-dynamic-arbitrage criterion |
| `Foundations/AlmgrenChriss.almgrenChrissPath_satisfies_EL` | the execution Euler–Lagrange path |
| `Foundations/NoArbitrageCore`, `TriangleArbitrage` | no-arbitrage predicates to land the statement on |

Gap: the repo's Almgren–Chriss is the deterministic permanent+temporary model
with **no decay kernel** — the propagator itself must be built. But it is a
small build, and refutation is cheap here: a counterexample is an explicit
kernel plus a *finite* schedule with negative expected cost, i.e. rational
arithmetic closable by `norm_num`/`ring`.

**3. American boundary convexity (Tier 1 §5) — strong module set, one real seam
to cross.**

`Binomial/SnellEnvelope.americanPrice_is_snell_envelope` plus `Binomial/American`,
`AmericanCallNoDividend`, `Bermudan`, `MertonAmericanCallTree`,
`BlackScholes/Dividends`, and the convexity trio (`StrikeConvexity`,
`PutStrikeConvexity`, `SpotConvexity`). `Binomial/CRRConvergence` is the
discrete→continuous seam.

Gap, and it is genuine: our American machinery is **binomial/discrete**, while
the open problem concerns the *continuous* free boundary. CRRConvergence makes
the bridge plausible rather than automatic.

**4. Elicitability (Tier 1 §16) — a real seed, Gaussian-bound.**

`RiskMeasures/RockafellarUryasev.gaussianCVaR_isLeast_ruObjective` is precisely
the variational characterization that underlies the consistent scoring function
for (VaR, ES) — CVaR as the *minimizer* of a one-parameter objective. With
`CoherentAxioms`, `Spectral`, `AcceptanceSet`, `Additivity`, `WorstCaseRisk`.

Gap: the RU result is **Gaussian-specific**. Generalizing it is a prerequisite
and is itself worthwhile library work regardless of the open problem.

**5. Lévy HJM finite-dimensional realizations (Tier 1 §12) — real tower, heavy
missing geometry.**

The Itô–Lévy tower is genuinely built: `PoissonCompensatedIntegralOperator`,
`PoissonCompensatedIntegralL2{,Dense}`, `PoissonCompensatedIsometryAdapted`,
`PoissonRandomMeasure`, `PoissonSuperposition`, `PoissonThinning`, and the
Itô–Lévy integral CLM in full generality. `docs/hjm-program.md` already plans
F6, the Lévy instance of stochastic Fubini.

Gap: FDR theory needs Lie-algebraic / infinite-dimensional differential
geometry that neither this library nor Mathlib carries.

**6. Musiela global well-posedness (Tier 1 §2) — highest conceptual alignment,
longest runway.**

`docs/hjm-program.md` already names Musiela as node **G4**, the deferred SPDE
summit shipping `placeholder`. The problem is on our roadmap by name.

Honest gap: **neither `MathFin/FixedIncome/HJM/` nor
`MathFin/Foundations/StochasticFubini*.lean` exists yet.** The HJM program is
*ratified, not built* — the whole F1→C4 chain precedes G4. Adjacency here is to
a plan, not to code.

**7. Mean-field default / supercooled Stefan (Tier 1 §1) — best mathematics,
weakest substrate.**

`Foundations/ExitTime` gives genuine hitting-time machinery (`exitTime`,
`isStoppingTime_exitTime`, `isLocalizingSequence_exitTime`).
`FixedIncome/FirstToDefault` and `KMVMertonStructural` give default models.

Honest gap, and it is large: `FirstToDefault` is **constant-hazard with
independent names**, and `KMVMertonStructural` is the **one-period Merton**
distance-to-default (`survival_probability_eq_Phi_distanceToDefault`,
`merton_equity_eq_bs_call`) — not a first-passage barrier model. The open
problem needs *interacting* first-passage times and McKean–Vlasov limits. This
is the top mathematical pick and close to the bottom on leverage.

**Thin or absent.** `DeFi/ConstantProductAMM` (`swap_preserves_invariant`,
`internalPrice`, `arbitragePresent`) is direct but thin — the LVR/fee problem
needs a stochastic-control layer we do not have. The curse-of-dimensionality
problem (§4) has **no** adjacency: it is approximation-theoretic and
complexity-theoretic, and nothing in this library speaks to it.

### The recommendation this produces

Start where built code and open mathematics actually overlap: **§3 (SVI)** and
**§10 (impact kernels)**. Both are certificate-shaped — the answer is a
polynomial positivity or an explicit finite counterexample — which is the one
class where a proof assistant is a decisive adjudicator rather than a
bookkeeping tax. Both sit on modules that already exist.

Treat **§1** and **§2** as long-horizon: pursue them for the mathematics, not
because the repo shortens the path. For §2 specifically, the honest
prerequisite is finishing the HJM program that `docs/hjm-program.md` already
specifies.

A note on sequencing that applies to all of them: formalizing the *statement*
of an open problem, and the known partial results, is normal library work with
a guaranteed floor — and it is what makes any later resolution instantly
checkable rather than something a referee must verify by hand. That is an
argument for doing it first, not a reason to gate the mathematics behind it.

---

## Sources

Volatility and calibration —
[No Arbitrage SVI (Martini–Mingone, SIAM J. Fin. Math.)](https://epubs.siam.org/doi/10.1137/20M1351060) ·
[Explicit no-arbitrage domain for sub-SVIs](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=3860011) ·
[eSSVI global parametrization](https://www.researchgate.net/publication/359709309_No_arbitrage_global_parametrization_for_the_eSSVI_volatility_surface) ·
[Roper, Arbitrage-free implied volatility surfaces](https://talus.maths.usyd.edu.au/u/pubs/publist/preprints/2010/roper-9.pdf) ·
[Lucic, Normalizing volatility transforms](https://doi.org/10.2139/ssrn.3835233) ·
[Guyon, the joint SPX/VIX puzzle solved](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=3397382) ·
[Signature-based joint calibration](https://onlinelibrary.wiley.com/doi/10.1111/mafi.12442) ·
[Gaussian polynomial volatility joint calibration](https://doi.org/10.1111/mafi.12451)

Rough volatility —
[Weak existence/uniqueness for affine SVEs with `L¹` kernels](https://www.researchgate.net/publication/337966379_Weak_existence_and_uniqueness_for_affine_stochastic_Volterra_equations_with_L1-kernels) ·
[Markovian approximations of SVEs with the fractional kernel](https://www.tandfonline.com/doi/full/10.1080/14697688.2022.2139193) ·
[Strong convergence rates for Markovian representations](https://arxiv.org/pdf/1902.01471) ·
[Small-time, large-time and `H→0` for rough Heston](https://ideas.repec.org/p/arx/papers/1906.09034.html)

Market impact and execution —
[Gatheral, No-dynamic-arbitrage and market impact](https://www.tandfonline.com/doi/abs/10.1080/14697680903373692) ·
[Cross-impact and no-dynamic-arbitrage](https://arxiv.org/pdf/1612.07742) ·
[Optimal execution with nonlinear transient market impact](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=2539240) ·
[Dynamic optimal execution in a mixed-market-impact Hawkes model](https://link.springer.com/article/10.1007/s00780-015-0282-y) ·
[A stationary Kyle setup: microfounding propagator models](https://www.researchgate.net/publication/346090035_A_Stationary_Kyle_Setup_Microfounding_propagator_models) ·
[Multi-asset execution with stochastic cross-effects](https://arxiv.org/pdf/2503.05594)

Frictions —
[Portfolio choice with transaction costs: a user's guide](https://www.guasoni.com/papers/transreview.pdf) ·
[Asymptotic methods for transaction costs](https://arxiv.org/pdf/2407.07100) ·
[Unified asymptotics for investment under illiquidity](https://arxiv.org/pdf/2407.13547) ·
[Transaction costs, shadow prices and duality in discrete time](https://www.mat.univie.ac.at/~schachermayer/pubs/preprnts/prpr0156.pdf)

Optimal transport —
[The Bass functional of martingale transport](https://www.mat.univie.ac.at/~schachermayer/pubs/preprnts/prpr0184.pdf) ·
[Structure of martingale Benamou–Brenier in `ℝᵈ`](https://arxiv.org/html/2306.11019v2) ·
[Local structure of multi-dimensional MOT](https://arxiv.org/abs/1805.09469) ·
[Complete duality for MOT on the line](https://projecteuclid.org/journals/annals-of-probability/volume-45/issue-5/Complete-duality-for-martingale-optimal-transport-on-the-line/10.1214/16-AOP1131.full) ·
[Dual attainment for the martingale transport problem](https://www.mat.univie.ac.at/~mathias/GlobalDualAttainment_Bernoulli.pdf) ·
[A regularized Kellerer theorem in arbitrary dimension](https://projecteuclid.org/journals/annals-of-applied-probability/volume-35/issue-2/A-regularized-Kellerer-theorem-in-arbitrary-dimension/10.1214/24-AAP2125.full)

Equilibrium and mean-field —
[Radner equilibrium and quadratic BSDEs with discontinuous generators](https://link.springer.com/article/10.1007/s11579-016-0161-0) ·
[On non-uniqueness in mean field games](https://arxiv.org/pdf/1908.06207) ·
[Convergence of closed-loop Nash equilibria to the MFG limit (Lacker)](https://arxiv.org/abs/1808.02745) ·
[Monotone solutions for MFG master equations](https://arxiv.org/pdf/2107.09531)

Term structure —
[Existence of affine realizations for Lévy term-structure models](https://arxiv.org/pdf/1907.02363) ·
[Term structure models driven by Wiener process and Poisson measures: existence and positivity](https://www.researchgate.net/publication/220137790_Term_Structure_Models_Driven_by_Wiener_Process_and_Poisson_Measures_Existence_and_Positivity) ·
[Local well-posedness of Musiela's SPDE with Lévy noise](https://arxiv.org/pdf/0704.2380)

Optimal stopping —
[Convexity of the free boundary for the American put](https://arxiv.org/pdf/1304.5337) ·
[Optimal exercise boundary for jump diffusions](https://epubs.siam.org/doi/abs/10.1137/080712519) ·
[A probabilistic approach to continuous differentiability of optimal stopping boundaries](https://arxiv.org/pdf/2405.16636)

Systemic risk —
[Propagation of minimality in the supercooled Stefan problem](https://projecteuclid.org/journals/annals-of-applied-probability/volume-33/issue-2/Propagation-of-minimality-in-the-supercooled-Stefan-problem/10.1214/22-AAP1850.pdf) ·
[Bankruptcy costs, fire sales and cross-holdings](https://probability-risk.springeropen.com/articles/10.1186/s41546-017-0020-9)

Risk measures, numerics, DeFi —
[ES is jointly elicitable with VaR](https://www.risk.net/risk-management/2439862/expected-shortfall-is-jointly-elicitable-with-value-at-risk-implications-for-backtesting) ·
[Risk measures: robustness, elicitability, backtesting](https://www.annualreviews.org/content/journals/10.1146/annurev-statistics-030718-105122) ·
[MLP suffers from the curse of dimensionality for HJB](https://arxiv.org/pdf/2506.23969) ·
[Multilevel Picard research overview](https://www.uni-due.de/mathematik/ag_stochastische_analysis/mlp) ·
[Optimal dynamic fees in AMMs](https://arxiv.org/html/2506.02869) ·
[Misspecified Recovery (Borovička–Hansen–Scheinkman)](https://www.nber.org/papers/w20209)
