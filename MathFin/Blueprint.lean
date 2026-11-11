/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

import MathFin.Choice.Performance.Kelly
import MathFin.Choice.Performance.Ratios
import MathFin.Choice.Portfolio.CAPMEquilibrium
import MathFin.Choice.Portfolio.ConvexQPKKT
import MathFin.Choice.Portfolio.MarkowitzLagrangian
import MathFin.Choice.Portfolio.MarkowitzNAsset
import MathFin.Choice.Portfolio.RiskParityFOC
import MathFin.Choice.Utility.StatePriceDensity
import MathFin.Choice.Utility.VonNeumannMorgenstern
import MathFin.Contracts.Core
import MathFin.Insurance.SurvivalModel
import MathFin.Markets.DeFi.LPContract
import MathFin.Markets.DeFi.LiquidationAsStructuralDefault
import MathFin.Markets.DeFi.UniswapMechanics
import MathFin.Markets.Microstructure.GlostenMilgromCondExp
import MathFin.Markets.Microstructure.GlostenMilgromMarket
import MathFin.Models.Bachelier.Bachelier
import MathFin.Models.Binomial.CRRClosedForm
import MathFin.Models.Binomial.MartingaleRepresentation
import MathFin.Models.BlackScholes.American.Stopping.ActualOptimality
import MathFin.Models.BlackScholes.BlackScholesPhysical
import MathFin.Models.BlackScholes.Call
import MathFin.Models.BlackScholes.DeltaHedge
import MathFin.Models.BlackScholes.GaussianGirsanov
import MathFin.Models.BlackScholes.Market
import MathFin.Models.BlackScholes.MargrabeGrounding
import MathFin.Models.BlackScholes.PDE
import MathFin.Models.Credit.CVA
import MathFin.Models.Credit.Cox
import MathFin.Models.Credit.KMVMertonStructural
import MathFin.Models.Forwards.FxForwardParity
import MathFin.Models.Forwards.SchwartzOneFactor
import MathFin.Models.Jumps.JumpDiffusionIncompleteness
import MathFin.Models.Jumps.JumpDiffusionMixing
import MathFin.Models.Jumps.JumpDiffusionProcess
import MathFin.Models.Jumps.JumpDiffusionVarianceSwap
import MathFin.Models.LocalVol.Dupire
import MathFin.Models.LocalVol.TimeDependentVol
import MathFin.Models.ModelFree.CarrMadan
import MathFin.Models.Rates.AffineTermStructurePDE
import MathFin.Models.Rates.Caplet
import MathFin.Models.Rates.HJM
import MathFin.Models.Rates.Immunization
import MathFin.Models.Rates.KeyRateDuration
import MathFin.Models.StochVol.Heston
import MathFin.Pricing.ContinuousMarket
import MathFin.Pricing.Duality.ConvexDuality
import MathFin.Pricing.EquivMartingaleMeasure
import MathFin.Pricing.FTAP.FTAPComplete
import MathFin.Pricing.FTAP.FTAPDiscrete
import MathFin.Pricing.FTAP.MarketFTAP
import MathFin.Pricing.ForwardMeasure
import MathFin.Pricing.Market
import MathFin.Pricing.MarketCompleteness
import MathFin.Pricing.Numeraire
import MathFin.Pricing.Parity
import MathFin.Pricing.Value
import MathFin.Probability.Brownian.Girsanov.GirsanovFiltered
import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedProcess
import MathFin.Probability.Brownian.Ito.ItoIntegralCovariation
import MathFin.Probability.Brownian.Ito.ItoLemma2D
import MathFin.Probability.Brownian.Ito.ItoProductRule
import MathFin.Probability.Brownian.Ito.StochasticFubini
import MathFin.Probability.Brownian.LevyCharacterization
import MathFin.Probability.Brownian.MartingaleRepresentation
import MathFin.Probability.Brownian.QuadraticVariationL2
import MathFin.Probability.Brownian.SDE.SDEExistence
import MathFin.Probability.Brownian.SDE.SDEUniqueness
import MathFin.Probability.Dependence.Copula
import MathFin.Probability.Dependence.GaussianCopula
import MathFin.Probability.Dependence.HoeffdingCovariance
import MathFin.Probability.Dependence.MarshallOlkin
import MathFin.Probability.Dependence.Sklar
import MathFin.Probability.Discrete.DoobDecomposition
import MathFin.Probability.Discrete.DoobLpMaximalInequality
import MathFin.Probability.Discrete.L2MartingaleConvergence
import MathFin.Probability.Discrete.MarkovPathMeasure
import MathFin.Probability.Discrete.MartingaleTransform
import MathFin.Probability.Discrete.OptionalSamplingInequality
import MathFin.Probability.Discrete.SnellEnvelope
import MathFin.Probability.Gaussian.FeynmanKacHeatEquation
import MathFin.Probability.Gaussian.NormalQuantile
import MathFin.Probability.Gaussian.StandardNormal
import MathFin.Probability.Jumps.CompoundPoissonMGF
import MathFin.Probability.Laws.Quantile
import MathFin.Probability.Laws.QuantileConvergence
import MathFin.Probability.Martingales.BracketCompensator
import MathFin.Risk.AcceptanceSet
import MathFin.Risk.Coherent
import MathFin.Risk.EntropicRisk
import MathFin.Risk.LawInvariance
import MathFin.Risk.ComponentVaR
import MathFin.Risk.ContractRisk
import MathFin.Risk.Credit.TrancheLeg
import MathFin.Risk.Credit.VasicekIRB
import MathFin.Risk.Elicitability
import MathFin.Risk.ExpectedShortfall
import MathFin.Risk.ExposureMeasures
import MathFin.Risk.GaussianRiskMarkowitz
import MathFin.Risk.Superhedging
import MathFin.Risk.UtilityDerivation
import MathFin.Risk.VaRSuperadditivity
import MathFin.Risk.ValueAtRisk
import Architect

/-!
# The blueprint: a map of the field's landmarks

Declares the blueprint nodes by tagging existing declarations **post hoc** with LeanArchitect's
`attribute [blueprint …]`. The tags live HERE, in a leaf module nothing imports, so the proof
modules are untouched: their sources keep their verification-ledger hashes (zero restale), and
the dependency edges are *inferred from the proof terms* (`Architect.collectUsed` — a transitive
walk that stops at tagged constants, so edges pass through untagged helpers). The graph in
`docs/blueprint.md` is generated ground truth, never hand-drawn.

A node is one of three things (`docs/specs/2026-11-08-organization-design.md`, §5):

1. a **landmark**: a definition or theorem with a textbook name, stated at the generality the
   library proves;
2. a **joint**: a theorem whose statement involves two of valuation, choice and risk;
3. a **shared definition** that the landmarks of more than one cell use.

A waypoint is not a node: a proof step, a hypothesis bundle, a special case of a landmark that
is already a node, or a bridge between two encodings. Its corpus entries hang on the nearest
landmark, and a label that was folded into a landmark is recorded in
`docs/blueprint_retired.toml`, so old issues and pull requests still resolve. The tags below are
grouped by the cell of `docs/taxonomy.toml` that holds the declaration's module.

Titles are textbook names. Any narrowing — a finite state space, one date, a hypothesis in
place of a derivation — is said in the statement, never in the title: `(statement := …)` is one
honest paragraph of what the Lean declaration proves, with the deferrals named.

Regenerate after touching the nodes:

  `lake build MathFin.Blueprint && lake exe blueprint_export MathFin.Blueprint`
  then `python3 tools/blueprint_render.py` (see that file's header).
-/

@[expose] public section

-- ===== upstream: the driving noise =====

attribute [blueprint "def:brownian-motion"
  (title := "Brownian motion (Mathlib, upstream)")
  (statement := /-- The driving noise: independent stationary Gaussian increments, $B_t \sim
  N(0,t)$ — `IsPreBrownianReal`, now in Mathlib. Rémy Degenne's `brownian-motion` package, on
  which this library also builds, supplies the continuous modification and the filtered
  versions. -/)]
  ProbabilityTheory.IsPreBrownianReal

-- ===== probability/discrete: Discrete time =====

attribute [blueprint "thm:markov-path-law"
  (title := "Ionescu–Tulcea theorem: the law of a Markov chain")
  (statement := /-- The law of a countable-state Markov chain, constructed on infinite
  trajectories by Mathlib's Ionescu–Tulcea trajectory kernels from kernels reading only the
  last history coordinate; the finite-path factorization $P(X_0{=}i_0,\dots,X_n{=}i_n) =
  \mathrm{init}(i_0)\prod_k P(i_k,i_{k+1})$ is derived by induction through the comp-product
  recursion of the marginals (Saporito 1.1.2). -/)]
  MathFin.markovPathMeasure_cylinder

attribute [blueprint "thm:snell-envelope"
  (title := "Snell envelope")
  (statement := /-- For an integrable reward with exercise dates $X$ and horizon $N$ on a
  discrete-time filtered probability space, the Snell envelope lies almost surely below every
  supermartingale that dominates the reward at the exercise dates and at $N$: it is the
  smallest such supermartingale (it is one, and dominates the reward, by
  `snellEnvelope_supermartingale` and `snellEnvelope_dominates`). The first-contact time
  attains it in expectation (`snellContact_expected_payoff`). -/)]
  MathFin.snellEnvelope_le_supermartingale

attribute [blueprint "thm:martingale-transform"
  (title := "Martingale transform")
  (statement := /-- For a martingale $M$ and a bounded predictable $A$ on a finite measure
  space, $(A \cdot M)_n = \sum_{k<n} \langle A_{k+1}, M_{k+1} - M_k \rangle$ is a martingale:
  the discrete stochastic integral, and the gains process of a trading strategy. -/)]
  MathFin.martingaleTransform_isMartingale

attribute [blueprint "thm:doob-decomposition"
  (title := "Doob decomposition")
  (statement := /-- Every adapted integrable process $f$ with values in a Banach space, over a
  discrete filtration, is $f = M + A$ with $M$ a martingale and $A$ predictable ($A_{n+1}$ is
  $\mathcal{F}_n$-measurable) with $A_0 = 0$; the decomposition is unique up to almost-sure
  equality. It is Mathlib's `martingalePart` and `predictablePart`, packaged as the textbook
  existence-and-uniqueness statement. -/)]
  MathFin.doob_decomposition

attribute [blueprint "thm:optional-sampling"
  (title := "Optional sampling theorem")
  (statement := /-- For a real submartingale $f$ on a discrete filtration and stopping times
  $\sigma \le \tau \le n$, $f_\sigma \le E[f_\tau \mid \mathcal{F}_\sigma]$ almost surely: the
  conditional form, for stopping times bounded by a constant. -/)]
  MathFin.submartingale_optional_sampling

attribute [blueprint "thm:doob-maximal-inequality"
  (title := "Doob's $L^p$ maximal inequality")
  (statement := /-- For a nonnegative submartingale $f$ on a finite measure space, $p > 1$ and
  $n \ge 0$, $\|\max_{k \le n} f_k\|_p \le \tfrac{p}{p-1}\|f_n\|_p$. -/)]
  MeasureTheory.maximal_ineq_Lp

attribute [blueprint "thm:martingale-convergence"
  (title := "Martingale convergence theorem")
  (statement := /-- A real martingale on a finite measure space with $\sup_n \|f_n\|_{L^2} \le
  R$ converges almost surely and in $L^2$ to its limit process. The $L^2$-bounded case only;
  the $L^1$-bounded theorem by upcrossings is Mathlib's and is not restated. -/)]
  MathFin.martingale_ae_tendsto_and_eLpNorm_two_tendsto

-- ===== probability/martingales: Continuous martingales =====

attribute [blueprint "thm:bracket-compensator"
  (title := "Bracket of the Itô integral")
  (statement := /-- $M^2 - \langle M\rangle$ is a martingale: $\mathbb{E}[M_b^2 - \langle
  M\rangle_b \mid \mathcal{F}_a] = M_a^2 - \langle M\rangle_a$ for $a \le b \le T$. Expanding
  $(M_b-M_a)^2$, the cross term collapses by the martingale property of $M$, and the bracket
  increment splits off the conditional expectation because $\langle M\rangle_a$ is adapted —
  which holds because the predictable $\sigma$-algebra, traced onto a band
  $(a,b]\times\Omega$, is $\mathcal{B}(\mathbb{R}_{\ge 0})\otimes \mathcal{F}_b$-measurable.
  The bracket is the pathwise integral $\int\varphi^2\,dt$; that it is the limit of the
  realized quadratic variation is the frontier node `thm:bracket-quadratic-variation`. -/)]
  MathFin.BracketCompensator.condExp_sq_sub_bracket

-- ===== probability/brownian: Brownian calculus =====

attribute [blueprint "thm:quadratic-variation"
  (title := "Quadratic variation of Brownian motion")
  (statement := /-- Along the uniform partition of $[0,T]$ into $n$ pieces, $\sum_k
  (B_{t_{k+1}}-B_{t_k})^2 \to T$ in $L^2$ at rate $2T^2/n$: realized variance accumulates
  linearly in time at unit rate — the root of the "$\sigma^2 \cdot$ time" that pervades
  pricing. -/)]
  MathFin.QuadraticVariationL2.tendsto_qv

attribute [blueprint "def:ito-integral-clm"
  (title := "Itô integral and Itô isometry")
  (statement := /-- For a real Brownian motion $B$ and a horizon $T$, the Itô integral is a
  linear isometry from the predictable $L^2(P \otimes dt)$ integrands on $[0,T]$ into
  $L^2(P)$: $E[(\int_0^T \varphi\,dB)^2] = E\int_0^T \varphi_t^2\,dt$. It extends the
  elementary integral of simple processes by density (Dynkin $\pi$-$\lambda$ on predictable
  rectangles) and `LinearMap.extendOfNorm`; on adapted simple integrands the cross terms of
  the isometry vanish by the weak Markov property, which is where Itô departs from Wiener. The
  Wiener integral of a deterministic integrand is the special case. -/)]
  MathFin.ItoIntegralCovariation.itoIsometry

attribute [blueprint "thm:ito-formula-c2"
  (title := "Itô's formula")
  (statement := /-- For an Itô process $X = x_0 + \int b\,ds + \int \sigma\,dB$ with adapted
  continuous coefficients (no boundedness) and $f(t,x)$ with jointly continuous $f_t$, $f_x$,
  $f_{xx}$, almost surely for every $t \in [0,T]$ at once $f(t,X_t) = f(0,x_0) + \int_0^t (f_t
  + f_x b + \tfrac12 f_{xx}\sigma^2)(s,X_s)\,ds + \bigl(\int
  f_x(\cdot,X)\,\sigma\,dB\bigr)_t$, the stochastic integral being the localised predictable
  Itô integral. The textbook $C^2$ scope, as an identity of processes. One real Brownian
  motion and a finite horizon $[0,T]$; the multi-dimensional formula and jumps are not
  covered. -/)]
  MathFin.ItoFormulaAdapted.ito_formula_adapted_unbounded_process

attribute [blueprint "thm:martingale-representation"
  (title := "Martingale representation theorem")
  (statement := /-- Let $B$ be a Brownian motion with continuous paths and $\mathbb{F}^B$ its
  natural filtration. Every square-integrable martingale $M$ of $\mathbb{F}^B$ is, up to a
  horizon $T$, its initial value plus an Itô integral process, $M_t = M_0 + (\varphi\cdot
  B)_t$ almost surely for $t \le T$, for a predictable $L^2$ integrand $\varphi$. That $M_0$
  is a.e. constant is not assumed: it is the representation read at $t = 0$. At the horizon,
  every $F \in L^2(\mathcal{F}^B_T)$ is $F = E[F] + \int_0^T \varphi\,dB$ for a *unique*
  $\varphi$ (`exists_itoIntegral_representation`): the range of the Itô isometry is closed,
  and Wiener-exponential totality kills the orthogonal remainder. One dimension, $L^2$ only. -/)]
  MathFin.martingale_representation

attribute [blueprint "thm:girsanov-brownian-characterisation"
  (title := "Girsanov's theorem")
  (statement := /-- For bounded predictable $\theta$ and a horizon $T$, under $Q = Z_T\,\mu$
  with $Z_T = \exp(-\int_0^T\theta\,dB - \tfrac12\int_0^T\theta^2\,dt)$, the process
  $B^\theta$, a modification of $B + \int_0^{\cdot\wedge T}\theta\,ds$, is a pre-Brownian
  motion for the natural filtration of $B$ on all of $[0,\infty)$: $\mathcal{N}(0,t-s)$
  increments independent of $\mathcal{F}_s$. With continuous paths for $B$ it is a Brownian
  motion under $Q$ (`Btheta_isBrownianReal_predictable_of_bdd`). The measure is the
  horizon-$T$ one; unbounded $\theta$ and Novikov's condition are not covered. -/)]
  MathFin.Btheta_isFilteredPreBrownian_predictable_of_bdd

attribute [blueprint "thm:sde-strong-solution"
  (title := "Existence and uniqueness of solutions of Lipschitz SDEs")
  (statement := /-- For Lipschitz $b$, $\sigma$, any horizon $T$ and any initial value in the
  predictable $L^2$ space $E$ on $[0,T]$, the Picard map of $dX = b(X)dt + \sigma(X)dB$ has
  exactly one fixed point in $E$, with no smallness condition: its $n$-th iterate contracts
  with constant $(2(TL_b^2+L_\sigma^2)T)^n/n!$. The fixed point is an $L^2(dt\otimes dP)$
  class; a continuous adapted representative on every horizon is the frontier node
  `thm:sde-continuous-solution`. -/)]
  MathFin.SDEExistence.picardMap_exists_unique_fixedPoint_any_horizon

attribute [blueprint "thm:stochastic-fubini"
  (title := "Stochastic Fubini theorem")
  (statement := /-- For a continuous linear map $I$ out of $L^2(m)$, $m$ finite, and a
  Bochner-integrable family $\varphi : A \to L^2(m)$ with jointly integrable representatives
  $\psi$, $\int I(\varphi_u)\,d\nu(u) = I(g)$ for any $g \in L^2(m)$ representing $x \mapsto
  \int \psi_u(x)\,d\nu(u)$; instances at the horizon-$T$ Itô integral and the Wiener integral
  (`stochFubini_ito`, `stochFubini_wiener`). The swap for the integral as a process in $t$ is
  the frontier node `thm:stochastic-fubini-process`. -/)]
  MathFin.StochasticFubini.stochFubini_ofCLM

attribute [blueprint "thm:ito-product-rule"
  (title := "Itô's product rule")
  (statement := /-- For two Itô processes $X = x_0 + \int b\,ds + \int\sigma\,dB$ and $Y = y_0
  + \int c\,ds + \int\tau\,dB$ driven by one Brownian motion, with continuous adapted
  coefficients and no bounds, almost surely at every $t \le T$ at once, $X_tY_t = x_0y_0 +
  \int_0^t (Xc + Yb + \sigma\tau)\,ds + \int_0^t (X\tau + Y\sigma)\,dB$: the cross term
  $\int\sigma\tau\,ds$ is derived, by polarisation from the one-process formula. This is Itô's
  formula for $f(x,y) = xy$ only. -/)]
  MathFin.ItoFormulaAdapted.ito_product_rule_process

attribute [blueprint "def:gbm"
  (title := "Geometric Brownian motion")
  (statement := /-- The GBM value function $S(t,x) = S_0 \exp((\mu - \tfrac12\sigma^2)t +
  \sigma x)$; at $x = B_t$ it is geometric Brownian motion. -/)]
  MathFin.gbmValue

attribute [blueprint "thm:levy-characterization"
  (title := "Lévy's characterization of Brownian motion")
  (statement := /-- A continuous adapted real process $M$ with $M_0 = 0$ such that $M$ and
  $M_t^2 - t$ are local martingales for a filtration $\mathbb{F}$ is a Brownian motion; the
  filtered version, with increments independent of $\mathbb{F}$, is
  `isFilteredPreBrownian_of_localMartingale`. The hypothesis is that $M^2 - t$ is a local
  martingale, not that a quadratic variation process $\langle M\rangle$ equals $t$: no
  quadratic variation is constructed for a general continuous local martingale. -/)]
  MathFin.LevyCharacterization.isBrownianReal_of_localMartingale

attribute [blueprint "thm:sde-pathwise-uniqueness"
  (title := "Pathwise uniqueness for SDEs with Lipschitz coefficients")
  (statement := /-- Two $L^2$ strong solutions of $dZ = \mu(Z)\,dt + \sigma(Z)\,dB$ with the
  same initial value and driver, for Lipschitz coefficients, agree almost surely at every time
  $t \ge 0$ (an $L^2$-energy Grönwall argument). The Itô isometry bound for the
  stochastic-integral operator is a hypothesis of the structure `IsL2SolutionPair`, supplied
  by the library's Itô integral (`itoProcessCLM_norm_sq`). -/)]
  MathFin.IsL2SolutionPair.uniqueness

-- ===== probability/jumps: Jumps =====

attribute [blueprint "thm:compound-poisson-mgf"
  (title := "Compound Poisson moment generating function")
  (statement := /-- For i.i.d. claims $X_i$, the MGF of the $n$-claim sum averaged over $n
  \sim \mathrm{Poisson}(\lambda)$ is $\exp(\lambda(M_X(t) - 1))$. The statement is in this
  mixture form; no claim-count process is constructed. -/)]
  MathFin.compoundPoisson_mgf

-- ===== probability/gaussian: Gaussian analysis =====

attribute [blueprint "thm:feynman-kac-heat-eq"
  (title := "Feynman–Kac formula for the heat equation")
  (statement := /-- For $t > 0$ and the Gaussian heat kernel $K$, the Feynman–Kac function
  $u(t,x) = \int h(z)\,K(t,z-x)\,dz$ satisfies the heat equation $\partial_t u =
  \tfrac12\partial_{xx}u$: the integral $\int h\,K\,((z-x)^2-t)/(2t^2)$ equals half the
  integral $\int h\,K\,((z-x)^2-t)/t^2$, and for $h$ continuous with $|h(z)| \le e^z$ these
  are $\partial_t u$ and $\tfrac12\partial_{xx}u$ (`hasDerivAt_feynmanU_t`,
  `hasDerivAt_feynmanU_xx`), obtained by differentiating the kernel so that the call's kink is
  never differentiated. The expectation form $E[f(B_t)] = f(0) + \tfrac12\int_0^t
  E[f''(B_s)]\,ds$ for $f$ with $f, f', f''$ bounded and $f''$ continuous is
  `expectation_ito`. Only the heat-equation case: variable coefficients, killing and the
  terminal-value form are the frontier node `thm:feynman-kac-variable-coefficient`. -/)]
  MathFin.FeynmanKacHeatEquation.feynmanU_heat_equation

attribute [blueprint "def:standard-normal-cdf"
  (title := "Standard normal distribution function Φ")
  (statement := /-- $\Phi(x) = P(Z \le x)$ for $Z \sim N(0,1)$: the function the closed-form
  prices, Greeks and Gaussian risk figures of the library are written in. -/)]
  MathFin.Phi

attribute [blueprint "thm:gaussian-quantile"
  (title := "Gaussian quantile function")
  (statement := /-- For $p \in (0,1)$ the $p$-quantile of $N(m, v)$ is $m +
  \sqrt{v}\,\Phi^{-1}(p)$, where $\Phi^{-1}$ is the inverse of $\Phi$ on $(0,1)$
  (`Phi_PhiInv`). -/)]
  MathFin.quantile_gaussianReal

-- ===== probability/laws: Laws =====

attribute [blueprint "def:quantile"
  (title := "Quantile function")
  (statement := /-- The quantile function of a law $\mu$ on $\mathbb{R}$, $q_\mu(p) = \inf\{x
  \mid p \le F_\mu(x)\}$, the generalized inverse of its CDF. Its values are meaningful for $p
  \in (0,1)$. -/)]
  MathFin.quantile

attribute [blueprint "thm:quantile-transform"
  (title := "Quantile transform and probability integral transform")
  (statement := /-- For a probability measure $\mu$ on $\mathbb{R}$ the quantile function
  pushes the uniform law on $(0,1)$ to $\mu$. Conversely, if $X$ has law $\mu$ with continuous
  distribution function $F$, then $F(X)$ is uniform on $(0,1)$ (`hasLaw_cdf`). -/)]
  MathFin.hasLaw_quantile

-- ===== probability/dependence: Dependence =====

attribute [blueprint "thm:marshall-olkin"
  (title := "Marshall–Olkin first-to-default")
  (statement := /-- With independent exponential clocks $T_0, T_1, T_2$ of positive rates and
  default times $\min(T_0,T_2)$, $\min(T_1,T_2)$ (a common shock $T_2$), the first default
  survives past $t \ge 0$ with probability $e^{-(\lambda_0+\lambda_1+\lambda_2)t}$. The
  default-indicator covariance is `covariance_indicator_marshallOlkin`; it is not normalised
  to a correlation. -/)]
  MathFin.marshallOlkin_firstToDefault_survival

attribute [blueprint "def:gaussian-factor-copula"
  (title := "One-factor Gaussian copula")
  (statement := /-- The copula on $n$ names of the latent vector $X_i = \rho Z_0 +
  \sqrt{1-\rho^2}\,Z_i$ with independent standard normals; it is a copula for $\rho \in
  [-1,1]$ (`isCopula_gaussianFactorCopula`, the tagged declaration). -/)]
  MathFin.isCopula_gaussianFactorCopula

attribute [blueprint "def:copula"
  (title := "Copula")
  (statement := /-- A copula on $\mathbb{R}^\iota$ is a probability measure every coordinate
  of which is uniformly distributed on $(0,1)$ (the measure-first definition); its
  distribution function $u \mapsto C(u)$ is a copula in the sense of McNeil–Frey–Embrechts,
  Definition 7.1. -/)]
  MathFin.IsCopula

attribute [blueprint "thm:frechet-hoeffding"
  (title := "Fréchet–Hoeffding bounds")
  (statement := /-- For a copula $C$ on $\mathbb{R}^\iota$, $C(u) \le u_i$ for every
  coordinate $i$ and every $u \in [0,1]^\iota$, so $C \le \min_i u_i$; and $C(u) \ge \sum_i
  u_i - (d-1)$ (`sum_sub_le_measureReal_Iic`). For $d \ge 3$ the lower bound is not itself a
  copula (`not_exists_isCopula_frechetLower`). -/)]
  MathFin.IsCopula.measureReal_Iic_le

attribute [blueprint "thm:sklar"
  (title := "Sklar's theorem")
  (statement := /-- Let $X$ be a random vector on a probability space with continuous marginal
  distribution functions $F_i$. Then $P(X \le x) = C(F_1(x_1), \dots, F_d(x_d))$ for the
  copula $C$ of $X$, the joint law of the probability-integral transforms $F_i(X_i)$
  (`copulaOf`, a copula by `isCopula_copulaOf`). Conversely, for any copula $C$ and any
  margins $\mu_i$, the quantile transform $(q_{\mu_i}(V_i))_i$ of $V \sim C$ has joint
  distribution function $C(F_{\mu_i}(x_i))$ (`measureReal_quantile_le_eq`). Continuous margins
  for the first statement: the general case is the frontier node `thm:sklar-general`. -/)]
  MathFin.measureReal_le_eq_copulaOf

attribute [blueprint "thm:hoeffding-covariance"
  (title := "Hoeffding's covariance identity")
  (statement := /-- For square-integrable $X, Y$, $\mathrm{Cov}(X,Y) = \iint \bigl(P(X \le x,
  Y \le y) - P(X \le x)P(Y \le y)\bigr)\,dx\,dy$. -/)]
  MathFin.covariance_eq_integral_cdf

-- ===== probability/analysis: Analysis and convexity =====

attribute [blueprint "thm:cone-separation"
  (title := "Separation theorem for closed convex cones")
  (statement := /-- In $\mathbb{R}^\iota$ with $\iota$ finite, if $C$ is a closed convex cone
  and $x_0 \notin C$, there is $p$ with $\langle p, v\rangle \le 0$ for all $v \in C$ and
  $\langle p, x_0\rangle > 0$. A closed convex cone disjoint from the simplex has a strictly
  positive separating functional (`exists_pos_separating_of_cone_disjoint_simplex`): the
  engine of the finite-state fundamental theorem. Finite dimension only. -/)]
  MathFin.exists_separating_of_not_mem_cone

-- ===== statistics: Statistics =====

attribute [blueprint "def:sharpe-ratio"
  (title := "Sharpe ratio")
  (statement := /-- $(\mu - r_f)/\sigma$, the excess return per unit of volatility, of given
  numbers $\mu$, $r_f$, $\sigma$. -/)]
  MathFin.sharpeRatio

attribute [blueprint "thm:empirical-cdf-strong-law"
  (title := "Strong law for the empirical distribution function")
  (statement := /-- For pairwise independent draws with a common law whose CDF is continuous,
  almost surely the empirical CDF converges to that CDF at every point. The convergence is
  pointwise; uniformity (Glivenko–Cantelli) is not proved. -/)]
  MathFin.tendsto_empiricalCDF_ae

-- ===== market: Positions and markets =====

attribute [blueprint "def:contract"
  (title := "Contract")
  (statement := /-- A contract says what is paid and when, built from payoffs by combination. -/)]
  MathFin.Contracts.Contract

attribute [blueprint "def:contract-value"
  (title := "Value of a contract")
  (statement := /-- The value of a contract is the $Q$-expectation of its discounted pathwise
  present value, against a model that turns each observation the contract makes into a random
  variable. -/)]
  MathFin.Contracts.Contract.value

attribute [blueprint "def:market"
  (title := "Market")
  (statement := /-- A market: a measurable space with a reference measure $P$ and a filtration
  $\mathcal{F}$, the adapted prices of the traded assets, and a strictly positive adapted
  numéraire. -/)]
  MathFin.Market

attribute [blueprint "def:pricing-measure"
  (title := "Pricing measure")
  (statement := /-- $Q$ prices the market up to $T$: a probability measure with the same null
  events as $P$ among the events known at $T$ (the restrictions to $\mathcal{F}_T$ are
  mutually absolutely continuous), under which every deflated asset, frozen at $T$, is an
  $\mathcal{F}$-martingale. -/)]
  MathFin.Market.IsPricingMeasure

attribute [blueprint "thm:change-of-numeraire"
  (title := "Change of numéraire")
  (statement := /-- For positive $B_T, N_T$ and $B_0 \ge 0$, $N_0 > 0$, the measure $Q^N$ with
  density $N_TB_0/(N_0B_T)$ with respect to $Q$ satisfies $N_0E^{Q^N}[X/N_T] = B_0E^Q[X/B_T]$.
  When $E^Q[N_T/B_T] = N_0/B_0$ and $B_0, N_0 > 0$, $Q^N$ is a probability measure equivalent
  to $Q$ (`numeraireMeasure_isEquivProbMeasure`). A pricing identity at one date; no dynamics. -/)]
  MathFin.changeOfNumeraire

-- ===== valuation/general: Arbitrage theory =====

attribute [blueprint "thm:continuous-ftap"
  (title := "Fundamental theorem of asset pricing in continuous time")
  (statement := /-- If $Q$ is an equivalent martingale measure on $[0,T]$ for a
  finite-dimensional price process $S$ (equivalent to $P$, with $S$ stopped at $T$ a
  martingale), then no simple strategy (piecewise constant, predictable, bounded) trading on
  $[0,T]$ is an arbitrage. Only this direction, and only for simple strategies, is proved: the
  converse and the Delbaen–Schachermayer theorem for general admissible strategies are not.
  The Black–Scholes instance is that the discounted geometric Brownian motion is a martingale
  under the risk-neutral measure (`discountedGBM_isMartingale`, straight from the Wald
  exponential) and so admits no simple arbitrage (`discountedGBM_noArbitrageSimple`). -/)]
  MathFin.ContinuousMarket.isEMM_noArbitrageSimple

attribute [blueprint "def:emm"
  (title := "Equivalent martingale measure")
  (statement := /-- $Q$ is a probability measure equivalent to $P$ under which the price $S$,
  frozen at the horizon $T$ ($t \mapsto S_{\min(t,T)}$), is a martingale for the filtration. -/)]
  MathFin.IsEMM

attribute [blueprint "thm:forward-measure"
  (title := "Forward measure")
  (statement := /-- For a positive numéraire $B_T$ with $E^Q[1/B_T] > 0$, the forward measure
  $Q^T$ prices by $E^Q[1/B_T]\cdot E^{Q^T}[X] = E^Q[X/B_T]$, that is $P(0,T)E^T[X]$ is the
  price of $X$ (`forwardMeasure_price`), the change of numéraire with the bond as numéraire.
  At the constant bank account $e^{rT}$ and $E^Q[e^{-rT}S_T] = S_0$, $E^{Q^T}[S_T] =
  S_0e^{rT}$ (`forwardMeasure_expected_spot`): the forward price is the expected spot under
  the forward measure. -/)]
  MathFin.forwardMeasure_price

attribute [blueprint "thm:put-call-parity"
  (title := "Put-call parity")
  (statement := /-- If the discounted price $D_tX_t$ is a $Q$-martingale with $D_0 = 1$ and
  $X_0 = S_0$, the value of the European call minus the European put at strike $K$ and
  maturity $T$ is $S_0 - KD_T$. In a finite-state market with non-negative state prices $q$
  summing to the discount factor $DF$ and spot $S_0 = \sum_i q_iS_i$, call minus put is $S_0 -
  K\cdot DF$ (`putCall_parity_from_no_arbitrage`). -/)]
  MathFin.Contracts.value_europeanCall_sub_put_of_martingale

attribute [blueprint "thm:first-ftap"
  (title := "First fundamental theorem of asset pricing")
  (statement := /-- On a finite probability space with $P\{\omega\} > 0$, a discrete
  filtration and a real adapted price process on $\{0, \dots, T\}$, there is no arbitrage if
  and only if there is an equivalent martingale measure (Harrison–Pliska). Finite $\Omega$
  only: one period with a finite-dimensional vector price on an arbitrary probability space is
  `ftap_one_period_vector`, an equivalent martingale measure precludes arbitrage on any space
  (`IsEMM.noArbitrage`), and the general discrete-time theorem is the frontier node
  `thm:dmw-ftap`. -/)]
  MathFin.ftap_discrete

attribute [blueprint "thm:second-ftap"
  (title := "Second fundamental theorem of asset pricing")
  (statement := /-- On a finite probability space with $P\{\omega\} > 0$, a filtration with
  $\mathcal{F}_T$ the full $\sigma$-algebra and an arbitrage-free adapted price, the market is
  complete if and only if there is exactly one equivalent martingale measure. In general,
  completeness implies that all equivalent martingale measures agree on measurable sets
  (`IsEMM.measure_eq_of_isCompleteMarket`); in the Brownian market a measure $Q \ll \mu$ that
  prices the traded Itô gains at zero agrees with $\mu$ on $\mathcal{F}^B_T$
  (`measure_eq_of_pricesGainsAtZero`), gains-neutrality being a hypothesis. The converse
  beyond finite $\Omega$ is the frontier node `thm:second-ftap-converse`. -/)]
  MathFin.ftap_two

attribute [blueprint "thm:market-ftap"
  (title := "The fundamental theorem of asset pricing for a market")
  (statement := /-- A one-asset market on a finite sample space whose reference measure charges
  every state has no arbitrage when trading at the dates of a grid (no bounded predictable
  strategy on the deflated price sampled along the grid is an arbitrage) if and only if the
  market traded on the grid has a pricing measure. A pricing measure of the market itself up to a
  horizon rules out arbitrage on every grid inside the horizon, on any space. On a general
  probability space the equivalence is proved assuming the conditional one-period theorem
  (`ConditionalOnePeriodFTAP`, not proved); unconditionally it is the frontier node
  `thm:dmw-ftap`. -/)]
  MathFin.Market.noArbitrage_iff_exists_isPricingMeasure_of_finite

-- ===== valuation/trees: Trees =====

attribute [blueprint "thm:binomial-representation"
  (title := "Martingale representation in the binomial model")
  (statement := /-- On the binomial tree every martingale is the discrete stochastic integral
  of a *predictable* hedge: $H = \Delta M/\Delta S$, fixed before the flip — completeness, the
  second pillar of the FTAP. The martingale is Mathlib's, for the natural filtration of the
  flips; the conditional expectation is the node average, so the proof is the one-period delta
  hedge, telescoped. Equivalently, under $0 < d < e^r < u$ and $S_0 \ne 0$, every payoff has a
  predictable strategy whose martingale transform against the discounted spot, added to the
  tree price, is the discounted payoff on every path (`binomialPrice_replication`). -/)]
  MathFin.binomial_martingale_representation

attribute [blueprint "thm:crr-bs-convergence"
  (title := "Cox–Ross–Rubinstein convergence to Black–Scholes")
  (statement := /-- When every $n$-step tree is arbitrage-free, the binomial call price
  converges to the Black–Scholes closed form $S_0\Phi(d_1) - Ke^{-rT}\Phi(d_2)$: charFun →
  Lévy continuity → weak convergence, with put–call parity lifting the (bounded) put's
  convergence to the call. -/)]
  MathFin.binomialPrice_call_tendsto_bs_closed

-- ===== valuation/diffusions: Black–Scholes and Bachelier =====

attribute [blueprint "thm:esscher-tilt"
  (title := "Esscher transform of a Gaussian")
  (statement := /-- Tilting the physical Gaussian by an exponential density yields an
  equivalent probability measure with shifted mean — static Girsanov, constructed, not
  assumed. -/)]
  MathFin.hasLaw_esscher_tilt

attribute [blueprint "thm:market-completeness"
  (title := "Completeness of the Brownian market")
  (statement := /-- Every square-integrable $\mathcal{F}^B_T$-claim is replicated from initial
  wealth $E_\mu[H]$ by a unique Itô-integrable strategy — the representation theorem read as a
  trading statement, the integrand *being* the hedge. The strategy class is the predictable
  $L^2$ integrands (piecewise-constant holdings could not hedge a general $L^2$ claim), and
  the traded gain is the integral against $B$ itself: the stochastic integral
  $\int\varphi\,dS$ against a general price is absent by design. -/)]
  MathFin.exists_replicating_strategy

attribute [blueprint "thm:bs-call"
  (title := "Black–Scholes call price formula")
  (statement := /-- Under `BSCallHyp`, that is $S_0, K, \sigma, T > 0$ and $S_T = S_0\exp((r -
  \tfrac12\sigma^2)T + \sigma\sqrt{T}\,Z)$ with $Z \sim N(0,1)$ under the pricing measure $Q$,
  the call price is $e^{-rT}E_Q[(S_T - K)^+] = S_0\Phi(d_1) - Ke^{-rT}\Phi(d_2)$. The pricing
  measure is a hypothesis, not derived from no arbitrage; `BSCallHyp.of_isPreBrownian` builds
  the hypothesis from a Brownian motion. -/)]
  MathFin.bs_call_formula

attribute [blueprint "thm:bs-delta"
  (title := "Black–Scholes Greeks")
  (statement := /-- $\partial V/\partial S = \Phi(d_1)$ — delta, the hedge ratio;
  representative of the five Greeks ($\delta, \gamma, \text{vega}, \theta, \rho$), each a real
  `HasDerivAt` derivation through `bs_identity`. -/)]
  MathFin.hasDerivAt_bsV_S

attribute [blueprint "thm:bs-pde"
  (title := "Black–Scholes partial differential equation")
  (statement := /-- The closed-form price satisfies $\theta + rS\delta +
  \tfrac12\sigma^2S^2\gamma - rV = 0$, verified through the Greeks and `bs_identity`. It is a
  statement about the closed form `bsV`, not about the price of a contract under a model. The
  same equation is derived independently of Itô from the heat-kernel representation
  (`bsV_satisfies_bs_pde_via_feynmanKac`), and the discounted price read along the Brownian
  state solves the backward heat equation (`discountedCallBrownian_heat_equation`); that
  $f(t,B_t)$ is then a local martingale is not proved. -/)]
  MathFin.bs_pde_holds

attribute [blueprint "thm:margrabe"
  (title := "Margrabe's exchange option formula")
  (statement := /-- For two geometric Brownian motions with correlated Gaussian drivers, the
  discounted expected exchange payoff $\mathbb E[e^{-rT}(S^1_T - S^2_T)^+]$ equals Margrabe's
  price: a Black–Scholes call on the ratio at effective volatility $\sqrt{\sigma_1^2 +
  \sigma_2^2 - 2\rho\sigma_1\sigma_2}$, by splitting off an independent residual. -/)]
  MathFin.margrabe_exchange_price

attribute [blueprint "thm:physical-measure-pricing"
  (title := "Black–Scholes pricing under the physical measure")
  (statement := /-- For the physical asset $S_u = S_0 e^{(m-\sigma^2/2)u + \sigma W_u}$ and
  the constant market price of risk $\theta = (m-r)/\sigma$, under the horizon-$H$ Girsanov
  measure every fixed-dated contract observed in $[0,H]$ has the same value on the physical
  asset as on the risk-neutral asset $S_0 e^{(r-\sigma^2/2)u + \sigma B^\theta_u}$, for any
  discount curve. So the European call with maturity $T \le H$ is worth $S_0\Phi(d_1) -
  Ke^{-rT}\Phi(d_2)$ (`value_europeanCall_physical`), and the chooser and the geometric Asian
  call their closed forms. The asset identity behind it holds almost surely at each date. The
  one-date Gaussian version: for a standard normal $W$ under $P$ and any shift $c$, the tilt
  $Q = P\,e^{cW - c^2/2}$ makes $W - c$ standard normal, and the call is worth the
  Black–Scholes closed form under $Q$ (`bs_call_formula_of_physical`). -/)]
  MathFin.Contracts.BlackScholes.value_physical_eq_riskNeutral

attribute [blueprint "thm:black-scholes-market"
  (title := "Black–Scholes is a market")
  (statement := /-- The Black–Scholes model of a pre-Brownian motion $W$ (asset $S_0e^{(m -
  \sigma^2/2)t + \sigma W_t}$, numéraire $e^{rt}$, the filtration $W$ generates) is a market,
  and for $\sigma \ne 0$ the Girsanov measure of the constant market price of risk
  $\theta = (m-r)/\sigma$ at a horizon $H$ is a pricing measure of it at every horizon $T \le
  H$: equivalent to the physical measure, with the deflated asset a martingale. Under it the
  European call is worth $S_0\Phi(d_1) - Ke^{-rT}\Phi(d_2)$ whatever the physical drift
  (`price_europeanCall_constGirsanovMeasure`). That it is the only pricing measure is not proved
  here: it is the frontier node `thm:bs-arbitrage-free-price`. -/)]
  MathFin.Contracts.BlackScholes.isPricingMeasure_constGirsanovMeasure

attribute [blueprint "thm:bs-delta-hedge"
  (title := "Black–Scholes delta hedging")
  (statement := /-- With $C(t,S) = $ `bsV` the call price and $S_t$ geometric Brownian motion,
  for every $T' < T$, almost surely and for all $t \le T'$ at once, $e^{-rt}C(t,S_t) =
  C(0,S_0) + \int_0^t \Phi(d_1)\,\sigma e^{-rs}S_s\,dB_s$: the discounted value is the initial
  price plus the gains of holding $\Delta = \Phi(d_1)$ shares. The price tends to the payoff
  as $t \to T^-$ (`tendsto_bsV_gbm_payoff`); the identity itself is stated on $[0,T']$, and
  the hedge is not packaged as a trading-strategy structure. Along the path the hedge
  satisfies the self-financing equation $V_t = V_0 + \int_0^t \Delta\,dS + \int_0^t r\psi\,ds$
  with $\psi_t = V_t - \Delta_tS_t$ in the bank (`europeanCall_selfFinancing`), as an integral
  identity and not as a trading-strategy structure. -/)]
  MathFin.bs_delta_hedge_replication

attribute [blueprint "thm:bachelier-call"
  (title := "Bachelier call price formula")
  (statement := /-- Under `BachelierHyp`, with terminal price $S_T = S_0 + \sigma\sqrt{T}\,Z$
  and $Z \sim N(0,1)$ under $Q$, $E_Q[(S_T - K)^+] = (S_0 - K)\Phi(d) +
  \sigma\sqrt{T}\,\varphi(d)$, with $d$ the standardised distance to the strike. Undiscounted,
  and the pricing measure is a hypothesis. -/)]
  MathFin.bachelier_call_formula

attribute [blueprint "thm:american-put-optimal-exercise"
  (title := "Optimal exercise of the American put")
  (statement := /-- On Wiener space with strike $1$, volatility $\sqrt2$, interest rate $k \ge
  0$ and dividend yield $h$ (the normalisation of the library's canonical American put), the
  expected discounted put payoff at the first time the stock reaches the exercise boundary
  (`brownianUsualActualContactTime`) equals the American put value `canonicalPrice` at spot
  $e^x$ and horizon $T$, the value being the supremum over stopping rules bounded by $T$
  (`brownianUsualAmericanPut`): first contact is an optimal exercise rule. For $K, \sigma >
  0$, $r > 0$ and $0 \le q \le r$ the exercise boundary tends to the strike as time to expiry
  tends to $0$ (`tendsto_brownianUsualExerciseBoundary_expiry`). Normalised parameters only;
  the early-exercise premium decomposition and the perpetual case are not proved. -/)]
  MathFin.BlackScholes.AmericanPut.Stopping.brownianUsualActualContactRule_optimal

-- ===== valuation/volatility: Volatility =====

attribute [blueprint "thm:heston-pde"
  (title := "Heston model pricing equation")
  (statement := /-- If coefficient flows $A, B$ solve the Heston Riccati system, the transform
  profile built from them satisfies the backward Heston pricing equation $\partial_t\Phi +
  L\Phi = 0$. Existence of the Riccati solutions is a hypothesis. -/)]
  MathFin.Heston.hestonProfile_pde

attribute [blueprint "thm:dupire-zero-rates"
  (title := "Dupire's local volatility formula")
  (statement := /-- For an Itô process whose local variance $\sigma_{loc}(K)^2 K^2$ is a
  continuous version of $E[\delta_t^2 \mid X_t = K]$ on a window of strikes, at every strike
  of the window with $\partial_K^2 C > 0$: $\sigma_{loc}(K)^2 = 2\,\partial_T C / (K^2
  \partial_K^2 C)$. Zero interest rate. -/)]
  MathFin.Dupire.dupire_pointwise

attribute [blueprint "thm:breeden-litzenberger"
  (title := "Breeden–Litzenberger formula")
  (statement := /-- For a price process whose time-$s$ marginal is integrable and any smooth
  compactly supported $\psi$, $\int \psi''(K)\,C(s,K)\,dK = E[\psi(X_s)]$, where $C(s,K) =
  E[(X_s - K)^+]$ is the call surface at zero rates: $\partial_K^2 C(s,\cdot)$ is the law of
  $X_s$ as a distribution. The weak form, for an arbitrary law. -/)]
  MathFin.Dupire.breedenLitzenberger_weak

attribute [blueprint "thm:time-dependent-vol-market"
  (title := "Black–Scholes with a deterministic volatility clock is a market")
  (statement := /-- For a pre-Brownian motion $W$ and a monotone clock $v$ (the total variance
  $\int_0^t\sigma^2$ of a deterministic volatility), the asset $e^{rt}S_0e^{(\theta -
  1/2)v(t) + W_{v(t)}}$ with numéraire $e^{rt}$ and the information $W$ generates up to $v(t)$
  is a market, and the Girsanov measure of the constant price of risk $\theta$ at a horizon $H$
  is a pricing measure of it at every $T$ with $v(T) \le H$. Under it the European call is worth
  the Black–Scholes formula of the total variance $v(T)$ at the strike $Ke^{-rT}$ of the
  deflated asset (`price_europeanCall_constGirsanovMeasure`). The asset is defined, not derived
  from an SDE; a general $\sigma(t,S)$ and uniqueness of the pricing measure are not proved. -/)]
  MathFin.Contracts.TimeDepVol.isPricingMeasure_constGirsanovMeasure

-- ===== valuation/jumps: Jump models =====

attribute [blueprint "thm:merton-risk-neutral-drift"
  (title := "Risk-neutral drift of a jump-diffusion")
  (statement := /-- For a jump-diffusion $X$ with drift $b$, volatility $\sigma$, jump
  intensity $\Lambda$ and a jump law $\nu$ with $\mathbb{E}[e^J] < \infty$, and $S_0 \ne 0$,
  the discounted price $e^{-rt}S_0e^{X_t}$ is a martingale if and only if $b = r - \sigma^2/2
  - \Lambda(\mathbb{E}[e^J] - 1)$. Merton's log-normal jumps have $\mathbb{E}[e^J] - 1 =
  \kappa$ (`integral_exp_mertonJump`), the compensation $r - \lambda\kappa$. -/)]
  MathFin.JumpDiffusionProcess.martingale_iff

attribute [blueprint "thm:variance-swap-jump-bias"
  (title := "Variance swap and the log contract")
  (statement := /-- At the compensated drift, the Demeterfi–Derman–Kamal–Zou log contract on
  the forward, scaled as a variance rate, has expected payoff $\sigma^2 +
  2\Lambda\,\mathbb{E}[e^J - 1 - J]$ under the jump-diffusion increment law (jump law with
  $\mathbb{E}[e^J] < \infty$ and exponential moments near $0$). Without jumps it is
  $\sigma^2$, the Black–Scholes fair strike. -/)]
  MathFin.jumpDiffusion_logContract

attribute [blueprint "thm:jump-diffusion-mixing"
  (title := "Merton's jump-diffusion formula")
  (statement := /-- For a jump-diffusion whose Poisson jump count is independent of the
  Gaussian driver and of the i.i.d. jump sizes, the discounted expected call payoff is the
  Black–Scholes price averaged over the jump part $-\kappa + \sum_{i<N} J_i$. Consequently the
  Merton call price dominates the Black–Scholes price at the diffusion volatility, for every
  intensity, mean jump size $k > -1$ and jump volatility (`bsV_le_mertonCallPrice`). -/)]
  MathFin.JumpDiffusionHyp.call_eq_integral_bsV

attribute [blueprint "thm:jump-diffusion-incompleteness"
  (title := "Incompleteness of jump-diffusion markets")
  (statement := /-- For a jump-diffusion with $\sigma \ne 0$, nontrivial jumps ($\Lambda > 0$,
  $\nu$ not the point mass at $0$) and exponential moments of the jump law, if the physical
  drift is not the compensated drift, then at every date $\tau > 0$ the Esscher law and the
  Merton law of the log return are both equivalent to the physical law and both compensated,
  and for every spot there is a strike at which the discounted call prices under them differ.
  One date: the statement is about laws of the log return, not about the processes. -/)]
  MathFin.exists_call_esscher_ne_merton

-- ===== valuation/term: Term structures =====

attribute [blueprint "thm:schwartz-commodity-futures"
  (title := "Schwartz commodity futures price")
  (statement := /-- With the log spot in its Ornstein–Uhlenbeck Wiener representation $\ln S_T
  = m_T + \sigma\int_0^T e^{-\kappa(T-s)}\,dB_s$ and $\kappa > 0$, the expected terminal spot
  is the closed form $\exp(m_T + v_T/2)$. The modelling bridge from the SDE to that
  representation is cited, not proved here. -/)]
  MathFin.schwartzFuturesPrice_eq_integral

attribute [blueprint "thm:interest-rate-parity"
  (title := "Covered interest-rate parity")
  (statement := /-- In a finite-state market pricing the domestic bond at $e^{-r_dT}$ and the
  foreign bond, in domestic currency, at $Se^{-r_fT}$, the forward priced to zero is $F =
  Se^{(r_d-r_f)T}$; under the Garman–Kohlhagen risk-neutral measure it is also the expected
  terminal spot. A statement about the pricing measure, not the physical one. -/)]
  MathFin.covered_eq_uncovered_interest_parity

attribute [blueprint "thm:key-rate-duration"
  (title := "Key-rate durations")
  (statement := /-- For a coupon bond on a curve of annually compounded key rates, at a flat
  curve $k \equiv y$ with $1 + y \ne 0$, the key-rate partial derivatives of the price sum to
  the derivative of the flat-yield price: $\sum_j \partial P/\partial k_j = dP/dy$ (dollar
  durations; divide by $-P$ for durations). -/)]
  MathFin.sum_deriv_keyRate_eq_deriv_bondPriceDisc

attribute [blueprint "def:hjm-model"
  (title := "Heath–Jarrow–Morton model")
  (statement := /-- An HJM model on $[0,H]$ over a Brownian motion $B$: forward rates $f(t,T)$
  with drift $\alpha$ and volatility $\sigma$ satisfying $f(t,T) = f(0,T) + \int_0^t
  \alpha(s,T)\,ds + \int_0^t \sigma(s,T)\,dB_s$ almost surely, for $t \le T$ and $t \le H$. -/)]
  MathFin.HJM.HJMModel

attribute [blueprint "thm:bond-immunization"
  (title := "Duration and immunization")
  (statement := /-- If the duration-weighted values of an asset and a liability bond portfolio
  agree at the rate $r$, the derivative in $r$ of their net value is zero there. -/)]
  MathFin.bondPortfolio_immunization_first_order

attribute [blueprint "thm:vasicek-bond-pde"
  (title := "Vasicek bond price")
  (statement := /-- For $\kappa \ne 0$, $u(\tau, r) = A(\tau)e^{-B(\tau)r}$ with the Vasicek
  loadings satisfies $-\partial_\tau u + \kappa(\theta - r)\partial_r u +
  \tfrac12\sigma^2\partial_r^2 u - ru = 0$. -/)]
  MathFin.vasicekBondPrice_solves_pde

attribute [blueprint "thm:black76-caplet"
  (title := "Black's caplet formula")
  (statement := /-- If the simple rate $L(T_0,T_1)$ is lognormal under the $T_1$-forward
  measure (a hypothesis, not derived from a rate model), the caplet is worth
  $P(0,T_1)\,\delta\,[F\Phi(d_1) - K\Phi(d_2)]$. -/)]
  MathFin.Contracts.value_caplet_black76

-- ===== valuation/default: Credit =====

attribute [blueprint "thm:unilateral-cva"
  (title := "Credit valuation adjustment")
  (statement := /-- With exposure $V_s = m(s) + \sigma(s)\sqrt s\,Z$, $Z \sim N(0,1)$,
  independent of a default time with continuous hazard $h \ge 0$ (no wrong-way risk), and $D$,
  $m$, $\sigma$ measurable and bounded with $\sigma > 0$: $\mathrm{CVA} = \mathrm{LGD}\int_0^T
  D(s)\,[m(s)\Phi(d_s) + \sigma(s)\sqrt s\, \varphi(d_s)]\,h(s)Q(s)\,ds$, $d_s =
  m(s)/(\sigma(s)\sqrt s)$. Only the marginal laws of the exposure enter; no exposure dynamics
  are modelled. -/)]
  MathFin.CVA.cva_gaussian

attribute [blueprint "thm:merton-structural-default"
  (title := "Merton's structural model of default")
  (statement := /-- Under the Black–Scholes lognormal hypothesis for the firm value, $V_T =
  V_0\exp((r - \tfrac12\sigma_V^2)T + \sigma_V\sqrt{T}\,Z)$, the KMV default probability
  $\Phi(-d_2)$ equals $1 - Q(V_T > F)$, one minus the risk-neutral probability that the firm
  value exceeds the debt face value $F$ at maturity; equivalently $1 - \mathrm{PD} =
  \Phi(d_2)$ (`kmv_survival_eq_Phi_d2`). Default at maturity only: first passage (Black–Cox)
  is not covered. -/)]
  MathFin.kmvPD_eq_one_sub_survival_probability

attribute [blueprint "thm:intensity-default-model"
  (title := "Intensity model of default")
  (statement := /-- For a continuous positive hazard rate $h$ with $\int_0^\infty h = \infty$
  and a unit-exponential random variable $\xi$, the default time $\tau = \Lambda^{-1}(\xi)$
  with $\Lambda(t) = \int_0^t h$ has survival probability $P(\tau > t) = e^{-\Lambda(t)}$. A
  deterministic intensity: a stochastic intensity is not covered. -/)]
  MathFin.Cox.cox_survival_timeVarying

-- ===== valuation/insurance: Life and insurance contracts =====

attribute [blueprint "def:survival-function"
  (title := "Survival function")
  (statement := /-- $S_X(t) = P(X > t)$, the probability that the age at death $X$ exceeds
  $t$. -/)]
  MathFin.SurvivalModel.survivalFunction

-- ===== valuation/mechanisms: Market mechanisms =====

attribute [blueprint "thm:impermanent-loss"
  (title := "Impermanent loss")
  (statement := /-- For a price ratio $r \ge 0$, the impermanent loss $2\sqrt r/(1+r) - 1$ of
  a fee-free constant-product position is at most $0$. -/)]
  MathFin.DeFi.impermanentLoss_nonpos

attribute [blueprint "thm:uniswap-v3-covered-call"
  (title := "A concentrated-liquidity position is dominated by a covered call")
  (statement := /-- A v3 position with liquidity $L \ge 0$ on the range $[a, b]$ is worth at
  most $x_{\max}(s^2 - \max(s^2 - ab, 0))$: long its full $X$ holding and short a call struck
  at $ab$. Under the Black–Scholes model the discounted expected value of the position is
  accordingly at most $x_{max}(S_0 - C)$, where $C$ is the Black–Scholes call struck at the
  geometric-mean price $ab$ (`integral_discounted_v3PositionValue_le`). -/)]
  MathFin.DeFi.v3PositionValue_le_coveredCall

attribute [blueprint "thm:lp-position-price"
  (title := "An AMM liquidity position is a contract")
  (statement := /-- In a market with positive price of $X$ in $Y$ at $T$, under any measure $Q$, the
  concentrated-liquidity payoff (a payoff in $\sqrt P$) paid at $T$ is worth $\int D_T\,
  v_3(\sqrt{P_T})\,dQ$ for the position value $v_3$ of Uniswap v3, and the constant-product
  payoff of invariant $x_0y_0$ is worth the discounted expectation of the rebalanced reserves
  valued at $P_T$. It is a price in the sense of a pricing measure when $Q$ is one; its closed
  form under Black--Scholes is not stated. -/)]
  MathFin.DeFi.price_lpPayoff

-- ===== valuation/model-free: Model-free =====

attribute [blueprint "thm:carr-madan"
  (title := "Carr–Madan static replication")
  (statement := /-- A payoff $f$ twice differentiable on $[L,U]$ with continuous $f''$
  decomposes, at every spot in $[L,U]$, as cash, a forward, and a static book of OTM options
  on the strikes in $[L,U]$ weighted by its convexity $f''$ — one integration by parts plus a
  positive-part case split. The unbounded-strike form is not proved. The log payoff
  specializes to the variance-swap $1/K^2$ strip. -/)]
  MathFin.carrMadan_spanning

-- ===== choice/preferences: Preferences =====

attribute [blueprint "thm:expected-utility-axioms"
  (title := "von Neumann–Morgenstern expected utility")
  (statement := /-- A preference defined by finite expected utility, $p \succeq q$ iff $\sum_i
  p_iu_i \ge \sum_i q_iu_i$, satisfies independence: if $p \succeq q$ then $\alpha p +
  (1-\alpha)r \succeq \alpha q + (1-\alpha)r$ for every weight $\alpha \ge 0$; it also
  satisfies continuity (`prefersEU_continuity`). Only this easy direction is proved: the
  representation theorem, that the axioms imply an expected-utility representation, is the
  frontier node `thm:von-neumann-morgenstern`. -/)]
  MathFin.prefersEU_independence

attribute [blueprint "def:expected-utility"
  (title := "Expected utility")
  (statement := /-- The expected utility $E_p[u] = \sum_{i \in s} p_iu_i$ of a lottery $p$
  over a finite support $s$ under the utility $u$. -/)]
  MathFin.expectedUtility

attribute [blueprint "thm:utility-state-price-density"
  (title := "Marginal utility is a state-price density")
  (statement := /-- In the finite-state market with payoff matrix $A$ and prices $\pi$, let the
  portfolio $\theta$ cost $w_0>0$, with payoff $W = A^\top\theta > 0$, probabilities $p>0$ and
  marginal utility $u'(W_\omega)>0$, and let it be stationary for $\sum_\omega p_\omega
  u(W_\omega)$ on the budget set: $\sum_\omega p_\omega u'(W_\omega) W^d_\omega = 0$ for every
  portfolio $d$ of zero cost. Then there is $\mu>0$ with $\sum_\omega p_\omega u'(W_\omega)
  A_{k\omega} = \mu\,\pi_k$ for every asset $k$: the normalised marginal utility
  $p_\omega u'(W_\omega)/\mu$ is a state-price vector (the Euler equation). A local maximum on the
  budget set is stationary, and on a finite probability space charging every state the state prices
  give an equivalent martingale measure (`exists_isEMM_of_isLocalMaxOn`). -/)]
  MathFin.exists_pos_smul_eq_of_stationary

-- ===== choice/portfolio: Portfolio choice =====

attribute [blueprint "def:portfolio-variance"
  (title := "Portfolio variance")
  (statement := /-- $\mathrm{Var}(w) = \sum_{i,j} w_i w_j \sigma_{ij}$, the variance of an
  $N$-asset portfolio with weights $w$ and covariance $\sigma$. -/)]
  MathFin.portfolioVarN

attribute [blueprint "thm:markowitz-lagrangian"
  (title := "Markowitz mean–variance optimality")
  (statement := /-- For a positive-semidefinite covariance $\Sigma$, a portfolio with $\sum
  w_i = 1$, mean return $m$ and $(\Sigma w)_i = \lambda_1 + \lambda_2\mu_i$ for every asset
  has the least variance among all portfolios with $\sum v_i = 1$ and mean return $m$. The
  same holds for square-integrable random returns (`variance_le_of_lagrangian_FOC`), and for
  two assets the closed-form weight $w^*$ minimises the variance when $D = \sigma_1^2 -
  2\rho\sigma_1\sigma_2 + \sigma_2^2 > 0$ (`portfolioVarN_minVarWeightTwo_le`). Sufficiency of
  the first-order condition only; necessity is the frontier node
  `thm:markowitz-kkt-necessity`. -/)]
  MathFin.portfolioVarN_le_of_lagrangian_FOC

attribute [blueprint "thm:risk-parity-foc"
  (title := "Risk parity")
  (statement := /-- If every asset's marginal variance equals $c / w_i$ for one constant $c$
  (the uniform-budget log-barrier first-order condition), all risk contributions are equal. -/)]
  MathFin.isRiskParity_of_uniform_log_barrier_FOC

attribute [blueprint "thm:tangent-portfolio-efficient"
  (title := "Tangent portfolio")
  (statement := /-- For positive semidefinite $\Sigma$, a fully invested portfolio with
  $\Sigma w = \lambda(\mu - r_f)$ is a tangent portfolio and has the least variance among the
  fully invested portfolios with the same expected return. -/)]
  MathFin.isTangentPortfolioN_and_portfolioVarN_le

attribute [blueprint "thm:kkt-sufficiency"
  (title := "Karush–Kuhn–Tucker sufficiency for convex quadratic programs")
  (statement := /-- For the program $\min\, c^\top x + \tfrac12 x^\top C x$ with $C$ positive
  semidefinite subject to $a_k^\top x \le b_k$, a feasible point $x_0$ with multipliers $u_k
  \ge 0$ satisfying stationarity, $c + Cx_0 = -\sum_k u_ka_k$, and complementary slackness is
  a global minimiser. Sufficiency only; uniqueness for positive definite $C$ is
  `kkt_point_unique_of_posDef`. -/)]
  MathFin.kkt_sufficient

-- ===== choice/equilibrium: Equilibrium =====

attribute [blueprint "thm:capm-equilibrium"
  (title := "Capital asset pricing model")
  (statement := /-- If the market portfolio $w_M$ meets the tangency cross-product condition
  and $w_M^\top \Sigma w_M \ne 0$, every asset's excess return is its beta times the market's:
  $\mu_i - r_f = \beta_i (\mu_M - r_f)$ with $\beta_i = (\Sigma w_M)_i / w_M^\top \Sigma w_M$.
  The tangency condition is the hypothesis: that it follows from market clearing of optimising
  investors is not proved. -/)]
  MathFin.CAPM_from_market_equilibrium

-- ===== choice/dynamic: Dynamic choice =====

attribute [blueprint "thm:kelly-criterion"
  (title := "Kelly criterion")
  (statement := /-- For win probability $p \in (0,1)$ and odds $b > 0$, the expected log
  growth of $n$ repeated bets, $f \mapsto n\,g(f)$ with $g(f) = p\log(1+fb) + (1-p)\log(1-f)$,
  has derivative zero at the Kelly fraction $f^* = (pb - q)/b$, $q = 1-p$, whatever $n$: the
  first-order condition of growth-optimal betting. First order only: global optimality and the
  continuous-time case are not proved (`thm:log-optimal-numeraire`). -/)]
  MathFin.kelly_n_periods_deriv_at_kelly

-- ===== choice/trading: Strategic trading =====

attribute [blueprint "thm:glosten-milgrom-quote"
  (title := "Glosten–Milgrom bid and ask quotes")
  (statement := /-- On a finite measure space, the conditional expectation of the asset value
  given the trade direction equals almost everywhere the ask $\int V\,d\mu[\cdot\mid B]$ on
  the buy event and the bid $\int V\,d\mu[\cdot\mid B^c]$ on the sell event. -/)]
  MathFin.Execution.condExp_payoff_eq_quote

attribute [blueprint "thm:conditional-expectation-pricing-measure"
  (title := "A conditional-expectation process is priced by its own measure")
  (statement := /-- For a probability measure $P$, a filtration $\mathcal G$ on $\mathbb N$ and
  an arbitrary value $V$, $P$ is a pricing measure, at every horizon, of the discrete market
  with unit numéraire whose asset is $n \mapsto \mathbb E_P[V \mid \mathcal G_n]$, because
  that process is a $P$-martingale and the equivalent martingale measure $P$ of it is a pricing
  measure. That the Glosten–Milgrom dealer's quotes along a sequence of trades are such
  conditional expectations is not part of this statement. -/)]
  MathFin.Execution.isPricingMeasure_toMarket_condExp

-- ===== risk/measures: Risk measures =====

attribute [blueprint "def:pricing-functional" (title := "The pricing functional")
  (statement := /-- A market is a filtered space with traded assets and a positive numéraire. A
  pricing measure up to $T$ is a probability measure equivalent to the reference measure on
  $\mathcal F_T$ under which every deflated asset, frozen at $T$, is a martingale, and the price of
  a contract under it is the expectation of its deflated cash flows. State-price pricing, the
  change of numéraire, the conditional bond price, superreplication and gains-neutral measures are
  instances. -/)]
  MathFin.Market.price

attribute [blueprint "thm:superhedging-coherent"
  (title := "The superhedging price is a coherent risk measure")
  (statement := /-- In the one-period finite-state market with a martingale probability vector, and
  for a reference measure charging every state, the superhedging price of a claim, read as a
  loss, is monotone, cash-invariant, positively homogeneous and subadditive. The equality with
  the supremum of the martingale prices is `thm:superhedging-duality`. -/)]
  MathFin.isCoherentRiskMeasure_superhedgingPrice

attribute [blueprint "thm:superhedging-duality"
  (title := "Superhedging duality")
  (statement := /-- In the one-period finite-state market with a martingale probability vector,
  the superhedging price of a claim $Y$ is the least upper bound of $\sum_n q_n Y_n$ over the
  martingale probability vectors $q$. The supremum is over all martingale probability vectors,
  which may vanish on states, and whether it is attained is not claimed. -/)]
  MathFin.superhedgingPrice_isLUB

attribute [blueprint "thm:superhedging-price-lower-bound"
  (title := "The superhedging price dominates every martingale price")
  (statement := /-- For every martingale probability vector $q$ and every claim $Y$,
  $\sum_n q_n Y_n$ is at most the superhedging price of $Y$. -/)]
  MathFin.le_superhedgingPrice

attribute [blueprint "def:convex-risk-measure"
  (title := "Convex risk measure")
  (statement := /-- A functional on the integrable losses of $(\Omega, P)$ that is monotone,
  translation invariant, $\rho(X + m) = \rho(X) + m$, and convex. Every coherent risk measure is
  one: `IsCoherentRiskMeasure` extends it. -/)]
  MathFin.IsConvexRiskMeasure

attribute [blueprint "def:coherent-risk-measure"
  (title := "Coherent risk measure")
  (statement := /-- The Artzner–Delbaen–Eber–Heath axioms for a functional on the integrable
  losses of $(\Omega, P)$: monotonicity, translation invariance, positive homogeneity and
  subadditivity. -/)]
  MathFin.IsCoherentRiskMeasure

attribute [blueprint "thm:coherent-risk-representation"
  (title := "Robust representation of coherent risk measures")
  (statement := /-- On a finite state space a coherent risk measure $\rho$ of losses is the
  least upper bound of the expected losses $\sum_i q_i L_i$ over its representing set of
  probability vectors. Finite state space only: the representation on $L^\infty(\Omega,P)$ is
  the frontier node `thm:delbaen-representation`. -/)]
  MathFin.coherentRisk_isLUB

attribute [blueprint "thm:quantile-elicitability"
  (title := "Elicitability of the quantile")
  (statement := /-- For $\alpha \in (0,1)$ the pinball loss strictly elicits the
  $\alpha$-quantile on the laws with finite mean and a unique $\alpha$-quantile: there the
  quantile is the unique minimiser of the expected pinball loss. -/)]
  MathFin.strictlyElicits_pinballLoss

attribute [blueprint "thm:expected-shortfall-not-elicitable"
  (title := "Expected shortfall is not elicitable")
  (statement := /-- For every $\alpha \in (0,1)$, no scoring function elicits
  $\mathrm{ES}_\alpha$ on a class of laws containing $\delta_0$, the witness law
  `esLevelWitness` and their mixture `esLevelMixture` (Gneiting 2011). -/)]
  MathFin.not_isElicitable_expectedShortfall

attribute [blueprint "thm:log-utility-acceptance"
  (title := "Acceptance sets from expected utility")
  (statement := /-- On a fair two-state coin at unit wealth, no coherent risk measure has the
  log-utility acceptance set: log utility accepts the Kelly bet $X = (1/2, -1/4)$ and rejects
  $3X$, so the acceptance set is not a cone. A two-state bet is acceptable under log utility
  iff its Kelly growth is nonnegative (`acceptableUnderUtility_log_iff_kellyGrowth`). -/)]
  MathFin.not_exists_isCoherentRiskMeasure_log_acceptance

attribute [blueprint "thm:entropic-risk-certainty-equivalent"
  (title := "Entropic risk is the certainty equivalent of exponential utility")
  (statement := /-- On a finite probability space with the weights $p_i = P\{i\}$, the position
  $-L$ is acceptable under the exponential utility $u(x) = -e^{-\gamma x}$ at wealth $0$ if and
  only if the entropic risk $\gamma^{-1}\log E[e^{\gamma L}]$ of the loss $L$ is at most $0$.
  The entropic risk measure is a convex risk measure on a finite probability space
  (`isConvexRiskMeasure_entropicRisk`) and is not coherent
  (`not_isCoherentRiskMeasure_entropicRisk`: positive homogeneity fails on a fair coin). -/)]
  MathFin.acceptableUnderUtility_exp_iff

-- ===== risk/law-invariant: Value at risk and expected shortfall =====

attribute [blueprint "def:law-invariant"
  (title := "Law-invariant risk functional")
  (statement := /-- A functional $\rho$ of losses on $(\Omega, P)$ such that measurable losses
  with the same law have the same risk. Value-at-risk, expected shortfall, the spectral risk
  measures, expectiles and the entropic risk measure are law invariant. -/)]
  MathFin.IsLawInvariant

attribute [blueprint "def:value-at-risk"
  (title := "Value-at-risk")
  (statement := /-- $\mathrm{VaR}_\alpha(X) = \inf\{x \mid \alpha \le P(X \le x)\}$, the
  $\alpha$-quantile of the law of the loss $X$. -/)]
  MathFin.valueAtRisk

attribute [blueprint "def:expected-shortfall"
  (title := "Expected shortfall")
  (statement := /-- $\mathrm{ES}_\alpha(X) = (1-\alpha)^{-1}\int_\alpha^1
  \mathrm{VaR}_u(X)\,du$, the average value-at-risk over the levels above $\alpha$. -/)]
  MathFin.expectedShortfall

attribute [blueprint "thm:rockafellar-uryasev"
  (title := "Rockafellar–Uryasev formula")
  (statement := /-- For an integrable loss $X$ and $\alpha \in (0,1)$, $\mathrm{ES}_\alpha(X)$
  is the least value of $c \mapsto c + (1-\alpha)^{-1}E[(X-c)^+]$. No continuity of the law is
  assumed. The same minimisation holds for a compound-Poisson loss $L = \sum_{i<N}X_i$ with $N
  \sim \mathrm{Poisson}(\lambda)$ independent of identically distributed integrable claims
  (`isLeast_rockafellarUryasev_compoundPoisson`). -/)]
  MathFin.isLeast_rockafellarUryasev

attribute [blueprint "thm:expected-shortfall-coherent"
  (title := "Expected shortfall is a law-invariant coherent risk measure")
  (statement := /-- For $\alpha \in (0,1)$, expected shortfall is a coherent risk measure on
  the integrable losses (`expectedShortfall_isCoherentRiskMeasure`) and is law invariant. Kusuoka's
  theorem, the converse, is not proved. -/)]
  MathFin.expectedShortfall_isCoherentRiskMeasure_and_isLawInvariant

attribute [blueprint "thm:expected-shortfall-dual"
  (title := "Dual representation of expected shortfall")
  (statement := /-- For an integrable loss $X$ and $\alpha \in (0,1)$, $\mathrm{ES}_\alpha(X)$
  is the greatest value of $E[DX]$ over densities $0 \le D \le (1-\alpha)^{-1}$ with $E[D]=1$.
  On a finite probability space the representing set of $\mathrm{ES}_\alpha$ in the
  Artzner–Delbaen–Eber–Heath representation is exactly the probability vectors $q$ with $q_i
  \le (1-\alpha)^{-1}P\{i\}$ (`representingSet_expectedShortfall`). -/)]
  MathFin.isGreatest_integral_mul_expectedShortfall

attribute [blueprint "thm:hedged-position-risk"
  (title := "Risk of a hedged position")
  (statement := /-- In the binomial tree under no arbitrage, a seller of a European contract
  who receives its value and follows the hedge loses $\mathrm{pathPV} - (\mathrm{value} +
  \mathrm{gains}) = 0$ on every path; so under every law $P$ of the coin flips, physical or
  not, the hedged position has zero value-at-risk and zero expected shortfall at every level
  $\alpha \in (0,1)$. -/)]
  MathFin.Contracts.Binomial.valueAtRisk_hedged_eq_zero

-- ===== risk/aggregation: Aggregation =====

attribute [blueprint "thm:gaussian-portfolio-var"
  (title := "Value-at-risk of a Gaussian portfolio")
  (statement := /-- For a Gaussian vector $X$ and $\alpha \in (0,1)$,
  $\mathrm{VaR}_\alpha(\sum_i w_i X_i) = \sum_i w_i E X_i + \sqrt{w^\top \Sigma
  w}\,\Phi^{-1}(\alpha)$ with $\Sigma$ the covariance matrix of $X$. -/)]
  MathFin.valueAtRisk_portfolio_gaussian

attribute [blueprint "thm:var-not-subadditive"
  (title := "Value-at-risk is not subadditive")
  (statement := /-- For $d$ independent Bernoulli($p$) losses $Y_i$ and $\alpha \in (0,1)$,
  $\sum_i \mathrm{VaR}_\alpha(Y_i) < \mathrm{VaR}_\alpha(\sum_i Y_i)$ if and only if $(1-p)^d
  < \alpha \le 1-p$. For independent Pareto losses with $F(x) = 1 - x^{-1/2}$ the inequality
  $\mathrm{VaR}_\alpha(L_1) + \mathrm{VaR}_\alpha(L_2) < \mathrm{VaR}_\alpha(L_1 + L_2)$ holds
  at every level (`valueAtRisk_add_gt_of_paretoHalf`). -/)]
  MathFin.valueAtRisk_sum_bernoulli_superadditive_iff

attribute [blueprint "thm:euler-allocation"
  (title := "Euler allocation of value-at-risk")
  (statement := /-- For a Gaussian vector $X$, weights $w$ with positive portfolio variance
  and $\alpha \in (0,1)$, the component VaRs $\mathrm{CVaR}_i = w_i\cdot$marginal VaR$_i$ at
  the multiplier $\Phi^{-1}(\alpha)$ sum to the portfolio VaR in excess of its mean: $\sum_i
  \mathrm{CVaR}_i = \mathrm{VaR}_\alpha(\sum_i w_iX_i) - \sum_i w_iEX_i$. Gaussian losses
  only. -/)]
  MathFin.sum_componentVaR_eq_valueAtRisk_sub

-- ===== risk/credit: Credit portfolio risk =====

attribute [blueprint "thm:tranche-leg-price"
  (title := "A CDO tranche leg is a contract")
  (statement := /-- The tranche leg, the tranche loss $((L-a)^+ - (L-d)^+)/(d-a)$ paid at $T$ as a
  contract on the portfolio loss fraction $L$, is worth on a deterministic discount curve $D$
  the discounted expected tranche loss $D_T\,\mathbb E_Q[\mathrm{tranchePayoff}(L_T)]$. The law
  of the loss fraction is not part of the statement. -/)]
  MathFin.Contracts.value_trancheLeg

attribute [blueprint "thm:aave-liquidation-kmv"
  (title := "Liquidation of a lending position is Merton default")
  (statement := /-- With lognormal collateral, liquidation threshold $LT > 0$ and debt $B + F
  > 0$, the probability that the single-collateral (v1) health factor is below $1$ at the
  horizon is the Merton–KMV default probability with barrier $(B+F)/LT$. -/)]
  MathFin.prob_healthFactorV1_lt_one_eq_kmvPD

attribute [blueprint "thm:large-portfolio-limit"
  (title := "Vasicek's large-portfolio limit")
  (statement := /-- In the one-factor model with pairwise independent standard normal
  idiosyncratic terms and $\rho < 1$, the loss fraction converges almost surely to the
  conditional default probability $p(F)$, for any systematic factor $F$. The joint default
  probability is the Gaussian factor copula's value: with $\pi \in (0,1)$ and $0 \le \rho <
  1$, the probability that every name defaults is $C(\pi, \dots, \pi)$
  (`oneFactor_measureReal_iInter_default_eq_gaussianFactorCopula`). -/)]
  MathFin.tendsto_oneFactorLossFraction_ae

-- ===== risk/exposure: Exposure =====

attribute [blueprint "thm:potential-future-exposure"
  (title := "Potential future exposure")
  (statement := /-- For $Z \sim N(0,1)$, $\sigma \ge 0$, $\alpha \in (0,1)$ and the exposure
  $V_s = m + \sigma\sqrt{s}\,Z$, $\mathrm{PFE}_\alpha(s) = \max(m +
  \sigma\sqrt{s}\,\Phi^{-1}(\alpha), 0)$. Gaussian exposure profile only: no exposure
  dynamics, netting or collateral. -/)]
  MathFin.CVA.potentialFutureExposure_gaussian
