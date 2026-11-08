/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

import MathFin.Probability.Brownian.QuadraticVariationL2
import MathFin.Probability.Brownian.Wiener.WienerIntegralL2
import MathFin.Probability.Brownian.Ito.ItoIsometryAdapted
import MathFin.Probability.Brownian.Ito.ItoIntegralCLM
import MathFin.Probability.Martingales.BracketCompensator
import MathFin.Probability.Brownian.Ito.ItoIntegralBrownian
import MathFin.Probability.Discrete.DiscreteIto
import MathFin.Probability.Brownian.Ito.ItoFormulaSquaredL2
import MathFin.Probability.Brownian.Ito.ItoFormulaCLM
import MathFin.Probability.Brownian.Ito.ItoFormulaTD
import MathFin.Probability.Brownian.Ito.ItoLemma2D
import MathFin.Probability.Gaussian.FeynmanKacHeatEquation
import MathFin.Models.BlackScholes.GaussianGirsanov
import MathFin.Models.BlackScholes.BSCallHypFromBrownian
import MathFin.Pricing.FTAP.ContinuousFTAP
import MathFin.Pricing.MarketCompleteness
import MathFin.Models.ModelFree.CarrMadan
import MathFin.Models.BlackScholes.Call
import MathFin.Models.BlackScholes.PDE
import MathFin.Models.BlackScholes.PDEFromIto
import MathFin.Models.BlackScholes.PDEFromFeynmanKac
import MathFin.Models.BlackScholes.MargrabeGrounding
import MathFin.Models.Binomial.MartingaleRepresentation
import MathFin.Models.Binomial.CRRCharFun
import MathFin.Models.Binomial.CRRClosedForm
import MathFin.Models.Jumps.MertonDominance
import MathFin.Probability.Discrete.MarkovPathMeasure
import MathFin.Probability.Brownian.Ito.ItoFormulaAdaptedProcess
import MathFin.Models.Forwards.SchwartzOneFactor
import MathFin.Models.Credit.CVA
import MathFin.Models.Forwards.FxForwardParity
import MathFin.Models.Jumps.JumpDiffusionProcess
import MathFin.Models.Jumps.JumpDiffusionVarianceSwap
import MathFin.Pricing.Numeraire
import MathFin.Probability.Discrete.SnellEnvelope
import MathFin.Probability.Dependence.MarshallOlkin
import MathFin.Models.Rates.KeyRateDuration
import MathFin.Models.BlackScholes.DeltaHedge
import MathFin.Probability.Brownian.Girsanov.GirsanovFiltered
import MathFin.Probability.Brownian.SDE.SDEExistence
import MathFin.Probability.Brownian.Ito.StochasticFubini
import MathFin.Pricing.FTAP.NoArbitrageLocal
import MathFin.Pricing.FTAP.DensityPasting
import MathFin.Models.BlackScholes.BlackScholesPhysical
import MathFin.Probability.Brownian.Ito.ItoProductRule
import MathFin.Models.BlackScholes.BlackScholesSelfFinancing
import MathFin.Probability.Gaussian.StandardNormal
import MathFin.Probability.Laws.Quantile
import MathFin.Probability.Laws.QuantileConvergence
import MathFin.Probability.Martingales.EquivMeasure
import MathFin.Pricing.EquivMartingaleMeasure
import MathFin.Probability.Discrete.MartingaleTransform
import MathFin.Probability.Dependence.GaussianCopula
import MathFin.Risk.ValueAtRisk
import MathFin.Risk.Coherent
import MathFin.Risk.ExpectedShortfall
import MathFin.Risk.Superhedging
import MathFin.Risk.AcceptanceSet
import MathFin.Risk.CompoundPoissonCVaR
import MathFin.Contracts.Core
import MathFin.Pricing.Value
import MathFin.Models.Rates.ZCB
import MathFin.Models.Rates.HJM
import MathFin.Models.Rates.Immunization
import MathFin.Models.Rates.AffineTermStructurePDE
import MathFin.Choice.Portfolio.MarkowitzNAsset
import MathFin.Choice.Portfolio.MarkowitzLagrangian
import MathFin.Choice.Portfolio.RiskParityFOC
import MathFin.Choice.Portfolio.Markowitz
import MathFin.Choice.Portfolio.CAPM
import MathFin.Choice.Utility.StatePriceDensity
import MathFin.Choice.Portfolio.TangentPortfolio
import MathFin.Choice.Performance.Ratios
import MathFin.Choice.Performance.RatiosExtended
import MathFin.Models.Binomial.Model
import MathFin.Insurance.SurvivalModel
import MathFin.Probability.Jumps.CompoundPoissonMGF
import MathFin.Markets.DeFi.UniswapMechanics
import MathFin.Markets.Microstructure.GlostenMilgromCondExp
import MathFin.Models.StochVol.Heston
import MathFin.Markets.DeFi.LiquidationAsStructuralDefault
import MathFin.Risk.Credit.VasicekIRB
import MathFin.Probability.Brownian.Ito.StochasticFubiniIto
import MathFin.Models.Rates.DeterministicCurve
import MathFin.Risk.GaussianRiskMarkowitz
import MathFin.Markets.DeFi.UniswapV3CoveredCallPrice
import MathFin.Models.Rates.Caplet
import MathFin.Models.Jumps.JumpDiffusionMixing
import MathFin.Risk.Credit.OneFactorCopula
import MathFin.Models.LocalVol.Dupire
import MathFin.Models.BlackScholes.American.Stopping.ActualBoundaryExpiryLimit
import MathFin.Choice.Portfolio.CAPMEquilibrium
import Architect

/-!
# Blueprint spine — post-hoc `@[blueprint]` tagging

Declares the blueprint nodes of the deductive spine (`docs/blueprint.md`) by
tagging existing declarations **post hoc** with LeanArchitect's
`attribute [blueprint …]`. The tags live HERE, in a leaf module nothing
imports, so the proof modules are untouched: their sources keep their
verification-ledger hashes (zero restale), and the spine's dependency edges
are *inferred from the proof terms* (`Architect.collectUsed` — a transitive
walk that stops at tagged constants, so edges pass through untagged helpers).
The graph in `docs/blueprint.md` is generated ground truth, never hand-drawn.

Regenerate after touching the spine:

  `lake build MathFin.Blueprint && lake exe blueprint_export MathFin.Blueprint`
  then `python3 tools/blueprint_render.py` (see that file's header).

Node prose lives in `(statement := …)`: one honest sentence per node — what
the mathematics says, with deferrals named, never papered over.
-/

@[expose] public section

-- ===== root: the driving noise (upstream — Mathlib) =====

attribute [blueprint "def:brownian-motion" (title := "Brownian motion (Mathlib, upstream)")
  (statement := /-- The driving noise: independent stationary Gaussian increments,
  $B_t \sim N(0,t)$ — `IsPreBrownianReal`, now in Mathlib. Rémy Degenne's
  `brownian-motion` package, on which this library also builds, supplies the
  continuous modification and the filtered versions. -/)]
  ProbabilityTheory.IsPreBrownianReal

-- ===== foundations =====

attribute [blueprint "thm:quadratic-variation" (title := "Quadratic variation: ∑(ΔB)² → T in L²")
  (statement := /-- Along the uniform partition of $[0,T]$ into $n$ pieces,
  $\sum_k (B_{t_{k+1}}-B_{t_k})^2 \to T$ in $L^2$ at rate $2T^2/n$: realized variance accumulates linearly in time at unit rate — the
  root of the "$\sigma^2 \cdot$ time" that pervades pricing. -/)]
  MathFin.QuadraticVariationL2.tendsto_qv

attribute [blueprint "thm:wiener-isometry" (title := "Wiener isometry (deterministic L²)")
  (statement := /-- For deterministic step integrands,
  $E[(\int \varphi\,dB)^2] = \int \varphi^2\,dt$: the $L^2$ geometry of a fixed
  (non-reacting) position in Brownian noise. -/)]
  MathFin.WienerIntegralL2.wiener_assembly_isometry

attribute [blueprint "thm:ito-isometry-adapted" (title := "Adapted Itô isometry")
  (statement := /-- For random *adapted* simple integrands,
  $E[(\sum_k \varphi_k \Delta B_k)^2] = \sum_k E[\varphi_k^2]\,\Delta t_k$ — the
  cross terms vanish by the weak Markov property, the exact point where Itô
  departs from Wiener. -/)]
  MathFin.ItoIsometryAdapted.ito_isometry_discrete

attribute [blueprint "def:ito-integral-clm" (title := "Continuous Itô integral (CLM on [0,T])")
  (statement := /-- The discrete isometry extended to a continuous linear isometry
  on predictable $L^2$ integrands over $[0,T]$, via density of simple processes
  (Dynkin π-λ on predictable rectangles) and `LinearMap.extendOfNorm`. -/)]
  MathFin.ItoIntegralCLM.itoIntegralCLM

attribute [blueprint "thm:ito-integral-brownian" (title := "∫₀ᵀ B dB = ½(B_T² − B₀² − T)")
  (statement := /-- The CLM's first genuine consumer: $\int_0^T B\,dB$ computed
  *through the abstract integral*, agreeing with the quadratic-variation limit —
  the clamp-truncation + isometry-Cauchy template any unbounded-coefficient
  consumer would reuse. -/)]
  MathFin.ItoIntegralBrownian.itoIntegralCLM_brownian

attribute [blueprint "thm:discrete-ito" (title := "Discrete Itô formula (pathwise)")
  (statement := /-- The exact pathwise identity
  $f(X_N) - f(X_0) = \sum f'(X_k)\Delta X_k + \tfrac12 \sum f''(X_k)(\Delta X_k)^2
  + \sum R_k$ — Itô's lemma before any limit is taken. -/)]
  MathFin.discrete_ito_formula

attribute [blueprint "thm:ito-squared-l2" (title := "Itô for x² in L²: ∑B·ΔB → ½(B_T²−B₀²−T)")
  (statement := /-- The continuous $L^2$ form for $x^2$: Riemann sums of
  $B\,dB$ converge along the uniform partition — one algebraic step from the
  discrete identity plus the $L^2$ quadratic variation. The
  $B_t^2 = 2\int B\,dB + t$ keystone behind variance-swap pricing. -/)]
  MathFin.itoSquared_L2_tendsto_div2

attribute [blueprint "thm:ito-formula-l2" (title := "Itô formula, L² (C³ bounded — Summit A)")
  (statement := /-- The continuous-time $L^2$ Itô formula
  $f(B_T) - f(B_0) = \int_0^T f'(B_s)\,dB_s + \tfrac12\int_0^T f''(B_s)\,ds$ for
  $C^3$ functions with bounded derivatives, proved from primitives (weighted QV,
  Taylor remainder, Riemann↔CLM bridge). Unbounded coefficients (e.g. GBM's
  exponential) are honestly out of scope — the named gap. -/)]
  MathFin.ito_formula_L2_bddDeriv

attribute [blueprint "thm:ito-formula-td-l2" (title := "Time-dependent Itô formula, L² (Summit A′)")
  (statement := /-- The classical $df = f_x\,dB + (f_t + \tfrac12 f_{xx})\,dt$ in
  integrated $L^2$ form: $f(T,B_T) - f(0,B_0) = \int_0^T f_x(s,B_s)\,dB_s
  + \int_0^T (f_t + \tfrac12 f_{xx})(s,B_s)\,ds$ for $C^{1,2}$ functions with bounded
  higher partials — the time-dependent extension of Summit A, with the drift Riemann
  term as the third vanishing limit and the joint continuity of $f_t$ *derived* from
  its bounded partials. Unbounded coefficients stay out of scope — the named gap. -/)]
  MathFin.ito_formula_td_L2_bddDeriv

attribute [blueprint "thm:expectation-ito" (title := "Expectation-form Itô / Feynman–Kac")
  (statement := /-- For $f$ with $f, f', f''$ bounded and $f''$ continuous,
  $E[f(B_t)] = f(0) + \tfrac12 \int_0^t E[f''(B_s)]\,ds$, proved
  via the heat equation: the $\tfrac12\sigma^2$ second-order term that drives the
  Black–Scholes PDE. -/)]
  MathFin.FeynmanKacHeatEquation.expectation_ito

attribute [blueprint "thm:gbm-sde" (title := "GBM coefficient matching (algebraic)")
  (statement := /-- $S(t,B_t)$ with $S = S_0 e^{(\mu-\sigma^2/2)t+\sigma x}$ matches
  the Itô coefficients of $dS = \mu S\,dt + \sigma S\,dB$: genuine `HasDerivAt`
  partials + the 2D Itô drift. Honestly *coefficient matching*, not a continuous
  SDE-solution theorem — the $-\sigma^2/2$ cancellation IS the Itô correction. -/)]
  MathFin.gbm_solves_sde

attribute [blueprint "thm:ito-formula-c2" (title := "Itô's formula for C² functions")
  (statement := /-- For an Itô process $X = x_0 + \int b\,ds + \int \sigma\,dB$ with adapted
  continuous coefficients (no boundedness) and $f(t,x)$ with jointly continuous $f_t$, $f_x$,
  $f_{xx}$, almost surely for every $t \in [0,T]$ at once
  $f(t,X_t) = f(0,x_0) + \int_0^t (f_t + f_x b + \tfrac12 f_{xx}\sigma^2)(s,X_s)\,ds
  + \bigl(\int f_x(\cdot,X)\,\sigma\,dB\bigr)_t$, the stochastic integral being the
  localised predictable Itô integral. The textbook $C^2$ scope, as an identity of
  processes. -/)]
  MathFin.ItoFormulaAdapted.ito_formula_adapted_unbounded_process

-- ===== change of measure — the centerpiece =====

attribute [blueprint "thm:esscher-tilt" (title := "Esscher tilt is the Gaussian Girsanov")
  (statement := /-- Tilting the physical Gaussian by an exponential density yields
  an equivalent probability measure with shifted mean — static Girsanov,
  constructed, not assumed. -/)]
  MathFin.hasLaw_esscher_tilt

attribute [blueprint "thm:girsanov-call"
  (title := "Call price under an Esscher-tilted Gaussian (static Girsanov)")
  (statement := /-- For a standard normal $W$ under $P$ and any shift $c$, the tilt
  $Q = P\,e^{cW - c^2/2}$ makes $W - c$ standard normal, so the call on
  $S_0 e^{(r-\sigma^2/2)T + \sigma\sqrt T (W - c)}$ is worth the Black–Scholes closed form
  under $Q$. One date, Gaussian shift only. With $c = (r-\mu)\sqrt T/\sigma$ the same tilt
  reprices the physical-drift asset to $S_0$ (`discounted_physical_terminal_eq_S0`); the call
  formula for the physical-drift asset is not stated separately. -/)]
  MathFin.bs_call_formula_of_physical

attribute [blueprint "thm:bscallhyp-brownian" (title := "BSCallHyp from a Brownian model")
  (statement := /-- A concrete Brownian-driven physical model produces the pricing
  hypothesis directly — the second route into `BSCallHyp`. -/)]
  MathFin.BSCallHyp.of_isPreBrownian

attribute [blueprint "thm:continuous-ftap"
  (title := "Discounted risk-neutral GBM is a martingale (EMM property)")
  (statement := /-- Under the risk-neutral measure the discounted price
  $e^{-rt}S_t$ is a continuous-time martingale, straight from the Wald
  exponential — the defining EMM property, with no stochastic-integral
  machinery. It is not a continuous-time FTAP: only "an EMM precludes arbitrage by
  simple strategies" is proved, and the converse is not. -/)]
  MathFin.discountedGBM_isMartingale

attribute [blueprint "thm:martingale-representation"
  (title := "Martingale representation (terminal form)")
  (statement := /-- Every square-integrable $\mathcal{F}^B_T$-measurable claim is its
  own mean plus an Itô integral, $F = E[F] + \int_0^T \varphi\,dB$, for a *unique*
  integrand $\varphi$. The Itô isometry's range is closed, hence orthogonally
  complemented; the remainder of the decomposition is centered and
  $\mathcal{F}^B_T$-measurable, so it is orthogonal to every step-integrand Doléans
  exponential, and Wiener-exponential totality kills it. Uniqueness is injectivity of an
  isometry. -/)]
  MathFin.exists_itoIntegral_representation

attribute [blueprint "thm:martingale-representation-process"
  (title := "Martingale representation (process form)")
  (statement := /-- Every square-integrable martingale on the Brownian filtration is its
  initial value plus an Itô integral process, $M_t = M_0 + (\varphi\cdot B)_t$ for
  $t \le T$. The terminal form supplies the integrand; the martingale property spreads it
  over the horizon, because $(\varphi\cdot B)_t$ is the $\mathcal{F}_t$-conditional
  expectation of $\int_0^T\varphi\,dB$. That $M_0$ is a.e. constant is not assumed — it is
  the representation read at $t = 0$. -/)]
  MathFin.martingale_representation

attribute [blueprint "thm:market-completeness" (title := "Completeness of the Brownian market")
  (statement := /-- Every square-integrable $\mathcal{F}^B_T$-claim is replicated from
  initial wealth $E_\mu[H]$ by a unique Itô-integrable strategy — the representation
  theorem read as a trading statement, the integrand *being* the hedge. The strategy class
  is the predictable $L^2$ integrands (piecewise-constant holdings could not hedge a
  general $L^2$ claim), and the traded gain is the integral against $B$ itself: the
  stochastic integral $\int\varphi\,dS$ against a general price is absent by design. -/)]
  MathFin.exists_replicating_strategy

attribute [blueprint "thm:pricing-measure" (title := "The pricing measure on 𝓕ᴮ_T is unique")
  (statement := /-- A probability measure $Q \ll \mu$ that prices the traded Itô gains at
  zero agrees with $\mu$ on all of $\mathcal{F}^B_T$: replicate an event's indicator, and
  only the initial wealth $\mu(A)$ survives. This is *not* the unconditional second FTAP.
  Gains-neutrality is a hypothesis, not a consequence of $Q$ being a martingale measure for
  a price $S$ — the wealth built here is an integral against $B$, and nothing in
  $\mathrm{IsEMM}\,S\,Q$ makes that a $Q$-fair game. The hypothesis is guarded: $\mu$
  satisfies it, and the textbook gains-martingale condition implies it. Only
  complete $\Rightarrow$ unique is proved; the Jacod–Yor converse is out of scope. For a
  price $S = S_0 + \int \sigma\,dB$ with $\sigma \ne 0$ a.e. and $Q$ with a square-integrable
  density, the hypothesis does follow from $S$ being a $Q$-martingale
  (`measure_eq_of_density`). -/)]
  MathFin.measure_eq_of_pricesGainsAtZero

-- ===== pricing =====

attribute [blueprint "thm:bs-call" (title := "Black–Scholes call formula")
  (statement := /-- Under `BSCallHyp`, the call price is
  $S_0\Phi(d_1) - Ke^{-rT}\Phi(d_2)$. -/)]
  MathFin.bs_call_formula

attribute [blueprint "thm:bs-identity" (title := "bs_identity: S·φ(d₁) = Ke^{−rτ}·φ(d₂)")
  (statement := /-- The algebraic collapse that cancels the pdf cross-terms —
  a self-contained root (only the $d_1/d_2$ definitions and the Gaussian
  density), feeding every clean Greek formula and the PDE. -/)]
  MathFin.bs_identity

attribute [blueprint "thm:bs-delta" (title := "Greeks (δ shown; γ vega θ ρ alongside)")
  (statement := /-- $\partial V/\partial S = \Phi(d_1)$ — delta, the hedge ratio;
  representative of the five Greeks ($\delta, \gamma, \text{vega}, \theta, \rho$),
  each a real `HasDerivAt` derivation through `bs_identity`. -/)]
  MathFin.hasDerivAt_bsV_S

attribute [blueprint "thm:bs-pde" (title := "Black–Scholes PDE (from the closed form)")
  (statement := /-- The closed-form price satisfies
  $\theta + rS\delta + \tfrac12\sigma^2S^2\gamma - rV = 0$, verified through the
  Greeks and `bs_identity`. -/)]
  MathFin.bs_pde_holds

attribute [blueprint "thm:bs-pde-brownian" (title := "BS PDE in the Brownian coordinate")
  (statement := /-- The discounted call price read along the Brownian state,
  $f(t,x) = e^{-rt}\,V(S_0 e^{(r-\sigma^2/2)t + \sigma x},\,T-t)$, solves the backward heat
  equation $\partial_t f + \tfrac12\partial_{xx} f = 0$ for $t < T$, from the Feynman–Kac
  heat-flow form of the price. That $f(t, B_t)$ is then a local martingale is not proved. -/)]
  MathFin.discountedCallBrownian_heat_equation

attribute [blueprint "thm:feynman-kac-heat-eq" (title := "Heat equation for the kernel convolution")
  (statement := /-- The convolution $u(t,x) = \int g(z)\,K(t,z-x)\,dz$ against the
  Gaussian heat kernel solves $\partial_t u = \tfrac12\partial_{xx}u$, from the
  kernel identity $\partial_t K = \tfrac12\partial_{yy}K$ and differentiation under
  the integral — `g` need only be continuous and growth-controlled, so the call's
  kink is never differentiated. -/)]
  MathFin.FeynmanKacHeatEquation.feynmanU_heat_equation

attribute [blueprint "thm:bs-pde-feynman-kac" (title := "Black–Scholes PDE (from Feynman–Kac)")
  (statement := /-- The closed-form price's actual derivatives satisfy
  $-\partial_\tau V + \tfrac12\sigma^2 S^2\partial_{SS}V + rS\partial_S V - rV = 0$,
  derived *independently of Itô* from the heat-kernel representation: the kernel's
  joint Fréchet-differentiability feeds the three Greeks, and the heat equation
  $\partial_t u = \tfrac12\partial_{xx}u$ plus exact drift cancellation assembles
  the PDE — the second, probabilistically-grounded tower closing the two-tower gap. -/)]
  MathFin.bsV_satisfies_bs_pde_via_feynmanKac

attribute [blueprint "thm:margrabe" (title := "Margrabe exchange option")
  (statement := /-- For two geometric Brownian motions with correlated Gaussian drivers, the
  discounted expected exchange payoff $\mathbb E[e^{-rT}(S^1_T - S^2_T)^+]$ equals Margrabe's
  price: a Black–Scholes call on the ratio at effective volatility
  $\sqrt{\sigma_1^2 + \sigma_2^2 - 2\rho\sigma_1\sigma_2}$, by splitting off an independent
  residual. -/)]
  MathFin.margrabe_exchange_price

attribute [blueprint "thm:carr-madan" (title := "Carr–Madan static replication")
  (statement := /-- A payoff $f$ twice differentiable on $[L,U]$ with continuous $f''$
  decomposes, at every spot in $[L,U]$, as cash, a forward, and a static book of OTM
  options on the strikes in $[L,U]$ weighted by its convexity $f''$ — one integration by
  parts plus a positive-part case split. The unbounded-strike form is not proved. The log payoff
  specializes to the variance-swap $1/K^2$ strip. -/)]
  MathFin.carrMadan_spanning

attribute [blueprint "thm:binomial-representation"
  (title := "Binomial martingale representation (completeness)")
  (statement := /-- On the binomial tree every martingale is the discrete
  stochastic integral of a *predictable* hedge: $H = \Delta M/\Delta S$, fixed
  before the flip — completeness, the second pillar of the FTAP. The martingale
  is Mathlib's, for the natural filtration of the flips; the conditional
  expectation is the node average, so the proof is the one-period delta hedge,
  telescoped. -/)]
  MathFin.binomial_martingale_representation

attribute [blueprint "thm:crr-bs-convergence" (title := "CRR → Black–Scholes convergence")
  (statement := /-- When every $n$-step tree is arbitrage-free, the binomial call price
  converges to the Black–Scholes closed form $S_0\Phi(d_1) - Ke^{-rT}\Phi(d_2)$:
  charFun → Lévy continuity → weak convergence, with put–call parity lifting the
  (bounded) put's convergence to the call. -/)]
  MathFin.binomialPrice_call_tendsto_bs_closed

attribute [blueprint "thm:merton-dominance" (title := "Merton call price dominates Black–Scholes at the diffusion vol")
  (statement := /-- The Merton (1976) jump-diffusion call price dominates the
  Black–Scholes price at the diffusion vol, for every intensity, mean jump
  size $k > -1$, and jump vol: vega prices the jump-size channel (conditional
  vols exceed $\sigma$), gamma prices the jump-count channel — spot convexity
  gives a supporting tangent at $S_0$ whose linear term integrates to zero by
  the compensation identity $E[\mathrm{spot}_N] = S_0$. -/)]
  MathFin.bsV_le_mertonCallPrice

attribute [blueprint "thm:markov-path-law" (title := "Markov path law (Ionescu–Tulcea)")
  (statement := /-- The law of a countable-state Markov chain, constructed on
  infinite trajectories by Mathlib's Ionescu–Tulcea trajectory kernels from
  kernels reading only the last history coordinate; the finite-path
  factorization $P(X_0{=}i_0,\dots,X_n{=}i_n) = \mathrm{init}(i_0)\prod_k
  P(i_k,i_{k+1})$ is derived by induction through the comp-product recursion
  of the marginals (Saporito 1.1.2). -/)]
  MathFin.markovPathMeasure_cylinder

attribute [blueprint "thm:conditional-bracket" (title := "The bracket is conditional")
  (statement := /-- For the Itô integral process $M = \varphi\bullet B$ on $[0,T]$ and
  $a \le b \le T$, the conditional second moment of an increment is the conditional
  expectation of the pathwise bracket increment,
  $\mathbb{E}[(M_b-M_a)^2 \mid \mathcal{F}_a] = \mathbb{E}[\langle M\rangle_b -
  \langle M\rangle_a \mid \mathcal{F}_a]$, with $\langle M\rangle_b - \langle M\rangle_a
  = \int_a^b \varphi_u(\omega)^2\,du$ taken $\omega$-wise. The proof is the Itô isometry
  localised on an $\mathcal{F}_a$-set: $\mathbb{1}_F$ is a bounded $\mathcal{F}_a$-measurable
  factor, so it folds back inside a single Itô integral and squaring it costs nothing. -/)]
  MathFin.PointwiseBracket.condExp_band_second_moment

attribute [blueprint "thm:bracket-compensator"
  (title := "The bracket compensates the square")
  (statement := /-- $M^2 - \langle M\rangle$ is a martingale:
  $\mathbb{E}[M_b^2 - \langle M\rangle_b \mid \mathcal{F}_a] = M_a^2 - \langle M\rangle_a$
  for $a \le b \le T$. Expanding $(M_b-M_a)^2$, the cross term collapses by the martingale
  property of $M$, and the bracket increment splits off the conditional expectation because
  $\langle M\rangle_a$ is adapted — which holds because the predictable $\sigma$-algebra,
  traced onto a band $(a,b]\times\Omega$, is $\mathcal{B}(\mathbb{R}_{\ge 0})\otimes
  \mathcal{F}_b$-measurable. -/)]
  MathFin.BracketCompensator.condExp_sq_sub_bracket

attribute [blueprint "thm:merton-risk-neutral-drift"
  (title := "Jump-diffusion risk-neutral drift")
  (statement := /-- For a jump-diffusion $X$ with drift $b$, volatility $\sigma$, jump
  intensity $\Lambda$ and a jump law $\nu$ with $\mathbb{E}[e^J] < \infty$, and
  $S_0 \ne 0$, the discounted price $e^{-rt}S_0e^{X_t}$ is a martingale if and only if
  $b = r - \sigma^2/2 - \Lambda(\mathbb{E}[e^J] - 1)$. Merton's log-normal jumps have
  $\mathbb{E}[e^J] - 1 = \kappa$ (`integral_exp_mertonJump`), the compensation
  $r - \lambda\kappa$. -/)]
  MathFin.JumpDiffusionProcess.martingale_iff

attribute [blueprint "thm:variance-swap-jump-bias" (title := "Variance-swap jump bias")
  (statement := /-- At the compensated drift, the Demeterfi–Derman–Kamal–Zou log contract on
  the forward, scaled as a variance rate, has expected payoff
  $\sigma^2 + 2\Lambda\,\mathbb{E}[e^J - 1 - J]$ under the jump-diffusion increment law
  (jump law with $\mathbb{E}[e^J] < \infty$ and exponential moments near $0$). Without
  jumps it is $\sigma^2$, the Black–Scholes fair strike. -/)]
  MathFin.jumpDiffusion_logContract

attribute [blueprint "thm:schwartz-commodity-futures" (title := "Schwartz commodity futures")
  (statement := /-- With the log spot in its Ornstein–Uhlenbeck Wiener representation
  $\ln S_T = m_T + \sigma\int_0^T e^{-\kappa(T-s)}\,dB_s$ and $\kappa > 0$, the expected
  terminal spot is the closed form $\exp(m_T + v_T/2)$. The modelling bridge from the
  SDE to that representation is cited, not proved here. -/)]
  MathFin.schwartzFuturesPrice_eq_integral

attribute [blueprint "thm:interest-rate-parity"
  (title := "Covered and uncovered interest-rate parity")
  (statement := /-- In a finite-state market pricing the domestic bond at $e^{-r_dT}$ and the
  foreign bond, in domestic currency, at $Se^{-r_fT}$, the forward priced to zero is
  $F = Se^{(r_d-r_f)T}$; under the Garman–Kohlhagen risk-neutral measure it is also the
  expected terminal spot. A statement about the pricing measure, not the physical one. -/)]
  MathFin.covered_eq_uncovered_interest_parity

attribute [blueprint "thm:unilateral-cva" (title := "Unilateral CVA, Gaussian exposure")
  (statement := /-- With exposure $V_s = m(s) + \sigma(s)\sqrt s\,Z$, $Z \sim N(0,1)$,
  independent of a default time with continuous hazard $h \ge 0$ (no wrong-way risk), and
  $D$, $m$, $\sigma$ measurable and bounded with $\sigma > 0$:
  $\mathrm{CVA} = \mathrm{LGD}\int_0^T D(s)\,[m(s)\Phi(d_s) + \sigma(s)\sqrt s\,
  \varphi(d_s)]\,h(s)Q(s)\,ds$, $d_s = m(s)/(\sigma(s)\sqrt s)$. Only the marginal laws of
  the exposure enter; no exposure dynamics are modelled. -/)]
  MathFin.CVA.cva_gaussian

attribute [blueprint "def:numeraire-measure" (title := "Numéraire measure as a Radon–Nikodym change")
  (statement := /-- $Q^N = Q$ with density $(N_T B_0)/(N_0 B_T)$. When $N_T, B_T > 0$ and
  $\mathbb{E}^Q[N_T/B_T] = N_0/B_0$ it is a probability measure equivalent to $Q$
  (`numeraireMeasure_isEquivProbMeasure`). -/)]
  MathFin.numeraireMeasure

attribute [blueprint "thm:snell-envelope" (title := "Snell envelope: the smallest dominating supermartingale")
  (statement := /-- For an integrable reward with exercise dates $X$ and horizon $N$ on a
  discrete-time filtered probability space, the Snell envelope lies almost surely below every
  supermartingale that dominates the reward at the exercise dates and at $N$: it is the
  smallest such supermartingale (it is one, and dominates the reward, by
  `snellEnvelope_supermartingale` and `snellEnvelope_dominates`). The first-contact time
  attains it in expectation (`snellContact_expected_payoff`). -/)]
  MathFin.snellEnvelope_le_supermartingale

attribute [blueprint "thm:marshall-olkin" (title := "Marshall–Olkin first-to-default")
  (statement := /-- With independent exponential clocks $T_0, T_1, T_2$ of positive rates and
  default times $\min(T_0,T_2)$, $\min(T_1,T_2)$ (a common shock $T_2$), the first default
  survives past $t \ge 0$ with probability $e^{-(\lambda_0+\lambda_1+\lambda_2)t}$. The
  default-indicator covariance is `covariance_indicator_marshallOlkin`; it is not normalised
  to a correlation. -/)]
  MathFin.marshallOlkin_firstToDefault_survival

attribute [blueprint "thm:key-rate-duration" (title := "Key-rate durations sum to the parallel shift")
  (statement := /-- For a coupon bond on a curve of annually compounded key rates, at a flat
  curve $k \equiv y$ with $1 + y \ne 0$, the key-rate partial derivatives of the price sum to
  the derivative of the flat-yield price: $\sum_j \partial P/\partial k_j = dP/dy$ (dollar
  durations; divide by $-P$ for durations). -/)]
  MathFin.sum_deriv_keyRate_eq_deriv_bondPriceDisc

attribute [blueprint "thm:girsanov-brownian-characterisation"
  (title := "Girsanov: the shifted process is a filtered Brownian motion")
  (statement := /-- For bounded predictable $\theta$ and a horizon $T$, under
  $Q = Z_T\,\mu$ with $Z_T = \exp(-\int_0^T\theta\,dB - \tfrac12\int_0^T\theta^2\,dt)$, the
  process $B^\theta$, a modification of $B + \int_0^{\cdot\wedge T}\theta\,ds$, is a pre-Brownian motion for the
  natural filtration of $B$ on all of $[0,\infty)$: $\mathcal{N}(0,t-s)$ increments independent of
  $\mathcal{F}_s$. With continuous paths for $B$ it is a Brownian motion under $Q$
  (`Btheta_isBrownianReal_predictable_of_bdd`). The measure is the horizon-$T$ one; unbounded
  $\theta$ and Novikov's condition are not covered. -/)]
  MathFin.Btheta_isFilteredPreBrownian_predictable_of_bdd

attribute [blueprint "thm:physical-measure-pricing"
  (title := "Contracts on the physical asset, priced under the Girsanov measure")
  (statement := /-- For the physical asset $S_u = S_0 e^{(m-\sigma^2/2)u + \sigma W_u}$ and the
  constant market price of risk $\theta = (m-r)/\sigma$, under the horizon-$H$ Girsanov measure
  every fixed-dated contract observed in $[0,H]$ has the same value on the physical asset as on
  the risk-neutral asset $S_0 e^{(r-\sigma^2/2)u + \sigma B^\theta_u}$, for any discount curve.
  So the European call with maturity $T \le H$ is worth $S_0\Phi(d_1) - Ke^{-rT}\Phi(d_2)$
  (`value_europeanCall_physical`), and the chooser and the geometric Asian call their closed
  forms. The asset identity behind it holds almost surely at each date. -/)]
  MathFin.Contracts.BlackScholes.value_physical_eq_riskNeutral

attribute [blueprint "thm:bs-delta-hedge" (title := "The Black–Scholes delta hedge")
  (statement := /-- With $C(t,S) = $ `bsV` the call price and $S_t$ geometric Brownian motion,
  for every $T' < T$, almost surely and for all $t \le T'$ at once,
  $e^{-rt}C(t,S_t) = C(0,S_0) + \int_0^t \Phi(d_1)\,\sigma e^{-rs}S_s\,dB_s$: the discounted
  value is the initial price plus the gains of holding $\Delta = \Phi(d_1)$ shares. The price
  tends to the payoff as $t \to T^-$ (`tendsto_bsV_gbm_payoff`); the identity itself is stated on
  $[0,T']$, and the hedge is not packaged as a trading-strategy structure. -/)]
  MathFin.bs_delta_hedge_replication

attribute [blueprint "thm:sde-strong-solution" (title := "Picard fixed point on every horizon")
  (statement := /-- For Lipschitz $b$, $\sigma$, any horizon $T$ and any initial value in the
  predictable $L^2$ space $E$ on $[0,T]$, the Picard map of $dX = b(X)dt + \sigma(X)dB$ has
  exactly one fixed point in $E$, with no smallness condition: its $n$-th iterate contracts with
  constant $(2(TL_b^2+L_\sigma^2)T)^n/n!$. The fixed point is an $L^2(dt\otimes dP)$ class; a
  continuous adapted representative on every horizon is the frontier node
  `thm:sde-continuous-solution`. -/)]
  MathFin.SDEExistence.picardMap_exists_unique_fixedPoint_any_horizon

attribute [blueprint "thm:stochastic-fubini" (title := "Stochastic Fubini (L² form)")
  (statement := /-- For a continuous linear map $I$ out of $L^2(m)$, $m$ finite, and a
  Bochner-integrable family $\varphi : A \to L^2(m)$ with jointly integrable representatives
  $\psi$, $\int I(\varphi_u)\,d\nu(u) = I(g)$ for any $g \in L^2(m)$ representing
  $x \mapsto \int \psi_u(x)\,d\nu(u)$; instances at the horizon-$T$ Itô integral and the Wiener
  integral (`stochFubini_ito`, `stochFubini_wiener`). The swap for the integral as a process in
  $t$ is the frontier node `thm:stochastic-fubini-process`. -/)]
  MathFin.StochasticFubini.stochFubini_ofCLM

attribute [blueprint "thm:no-arbitrage-local" (title := "No arbitrage is local")
  (statement := /-- For a price adapted up to a finite horizon on any filtered probability space,
  no arbitrage over bounded predictable strategies holds if and only if each one-period market,
  conditional on $\mathcal{F}_t$, admits no position with almost surely nonnegative, not almost
  surely zero gain: the reduction step of Dalang–Morton–Willinger. -/)]
  MathFin.noArbitrage_iff_noArbitrageLocal

attribute [blueprint "thm:emm-density-pasting" (title := "Pasting one-period densities into an EMM")
  (statement := /-- Bounded positive one-period densities $Z_t$, $\mathcal{F}_{t+1}$-measurable with
  $E[Z_t \mid \mathcal{F}_t] = 1$ and $E[Z_t S_{t+1} \mid \mathcal{F}_t] = S_t$, multiply to an
  equivalent martingale measure $P\,\prod_t Z_t$ for an adapted integrable price up to the horizon: the assembly
  step of Dalang–Morton–Willinger. That conditional no arbitrage produces such densities is not
  proved. -/)]
  MathFin.LocalEMMDensities.isEMM_pastedMeasure

attribute [blueprint "thm:ito-product-rule" (title := "Itô product rule")
  (statement := /-- For two Itô processes $X = x_0 + \int b\,ds + \int\sigma\,dB$ and
  $Y = y_0 + \int c\,ds + \int\tau\,dB$ driven by one Brownian motion, with continuous adapted
  coefficients and no bounds, almost surely at every $t \le T$ at once,
  $X_tY_t = x_0y_0 + \int_0^t (Xc + Yb + \sigma\tau)\,ds + \int_0^t (X\tau + Y\sigma)\,dB$:
  the cross term $\int\sigma\tau\,ds$ is derived, by polarisation from the one-process formula.
  This is Itô's formula for $f(x,y) = xy$ only. -/)]
  MathFin.ItoFormulaAdapted.ito_product_rule_process

attribute [blueprint "thm:bs-self-financing" (title := "The delta hedge satisfies the self-financing equation")
  (statement := /-- Along the Black–Scholes path, with value $V_t = C(t,S_t)$, $\Delta_t = \Phi(d_1)$
  shares and $\psi_t = V_t - \Delta_tS_t$ in the bank, for every $T' < T$, almost surely at every
  $t \le T'$: $V_t = V_0 + \int_0^t \Delta\,dS + \int_0^t r\psi\,ds$, with
  $\int\Delta\,dS = \int\Delta rS\,ds + \int\Delta\sigma S\,dB$ and $V_0$ the value of the
  European call contract. An integral identity, not a trading-strategy structure. -/)]
  MathFin.Contracts.BlackScholes.europeanCall_selfFinancing

-- ===== the program's objects: definitions the corpus is written in =====
-- A corpus entry is on the map when its proof rests on a node. Most of the corpus reaches the
-- library through its shared definitions, not through a deep theorem, so the central objects are
-- nodes too (docs/blueprint.md, "Objects and anchors").

attribute [blueprint "def:standard-normal-cdf" (title := "Standard normal CDF Φ")
  (statement := /-- $\Phi(x) = P(Z \le x)$ for $Z \sim N(0,1)$: the function the closed-form
  prices, Greeks and Gaussian risk figures of the library are written in. -/)]
  MathFin.Phi

attribute [blueprint "def:quantile" (title := "Quantile function (generalized inverse CDF)")
  (statement := /-- The quantile function of a law $\mu$ on $\mathbb{R}$,
  $q_\mu(p) = \inf\{x \mid p \le F_\mu(x)\}$, the generalized inverse of its CDF. Its values are
  meaningful for $p \in (0,1)$. -/)]
  MathFin.quantile

attribute [blueprint "def:value-at-risk" (title := "Value-at-risk")
  (statement := /-- $\mathrm{VaR}_\alpha(X) = \inf\{x \mid \alpha \le P(X \le x)\}$, the
  $\alpha$-quantile of the law of the loss $X$. -/)]
  MathFin.valueAtRisk

attribute [blueprint "def:expected-shortfall" (title := "Expected shortfall")
  (statement := /-- $\mathrm{ES}_\alpha(X) = (1-\alpha)^{-1}\int_\alpha^1 \mathrm{VaR}_u(X)\,du$,
  the average value-at-risk over the levels above $\alpha$. -/)]
  MathFin.expectedShortfall

attribute [blueprint "def:coherent-risk-measure" (title := "Coherent risk measure")
  (statement := /-- The Artzner–Delbaen–Eber–Heath axioms for a functional on the integrable
  losses of $(\Omega, P)$: monotonicity, translation invariance, positive homogeneity and
  subadditivity. -/)]
  MathFin.IsCoherentRiskMeasure

attribute [blueprint "def:equivalent-measure" (title := "Equivalent probability measure")
  (statement := /-- $Q$ is a probability measure with the same null sets as $P$ ($Q \ll P$ and
  $P \ll Q$): the prefix every equivalent-martingale-measure structure of the library extends. -/)]
  MathFin.IsEquivProbMeasure

attribute [blueprint "def:emm" (title := "Equivalent martingale measure")
  (statement := /-- $Q$ is a probability measure equivalent to $P$ under which the price $S$,
  frozen at the horizon $T$ ($t \mapsto S_{\min(t,T)}$), is a martingale for the filtration. -/)]
  MathFin.IsEMM

attribute [blueprint "def:snell-envelope" (title := "Snell envelope (the recursion)")
  (statement := /-- The Snell envelope of a reward process $Z$ on the horizon $N$ with exercise
  set $X$, defined by the backward recursion and frozen at $Z_N$ past the horizon. -/)]
  MathFin.snellEnvelope

attribute [blueprint "def:contract" (title := "The contract language")
  (statement := /-- A contract says what is paid and when, built from payoffs by combination. -/)]
  MathFin.Contracts.Contract

attribute [blueprint "def:contract-value" (title := "Value of a contract")
  (statement := /-- The value of a contract is the $Q$-expectation of its discounted pathwise
  present value, against a model that turns each observation the contract makes into a random
  variable. -/)]
  MathFin.Contracts.Contract.value

attribute [blueprint "def:zero-coupon-bond" (title := "Zero-coupon bond, constant short rate")
  (statement := /-- $P(t,T) = e^{-r(T-t)}$, the price at $t$ of one unit paid at $T$ under a
  constant short rate $r$. -/)]
  MathFin.zcb

attribute [blueprint "def:portfolio-variance" (title := "Portfolio variance")
  (statement := /-- $\mathrm{Var}(w) = \sum_{i,j} w_i w_j \sigma_{ij}$, the variance of an
  $N$-asset portfolio with weights $w$ and covariance $\sigma$. -/)]
  MathFin.portfolioVarN

attribute [blueprint "def:kelly-fraction" (title := "Kelly fraction")
  (statement := /-- $f^* = (pb - q)/b$ with $q = 1 - p$: the Kelly stake for a bet that pays $b$
  to $1$ with win probability $p$. -/)]
  MathFin.kellyFraction

attribute [blueprint "def:sharpe-ratio" (title := "Sharpe ratio")
  (statement := /-- $(\mu - r_f)/\sigma$, the excess return per unit of volatility, of given
  numbers $\mu$, $r_f$, $\sigma$. -/)]
  MathFin.sharpeRatio

attribute [blueprint "def:capm-beta" (title := "CAPM beta")
  (statement := /-- $\beta = \mathrm{Cov}(R, R_M)/\mathrm{Var}(R_M)$, defined as the ratio of a
  given covariance and variance. -/)]
  MathFin.beta

attribute [blueprint "def:two-asset-min-variance" (title := "Two-asset minimum-variance weight")
  (statement := /-- $w^* = (\sigma_2^2 - \rho\sigma_1\sigma_2)/(\sigma_1^2 - 2\rho\sigma_1\sigma_2
  + \sigma_2^2)$, the closed-form weight on the first asset of the two-asset minimum-variance
  portfolio. -/)]
  MathFin.minVarWeightTwo

attribute [blueprint "def:tangent-portfolio" (title := "Tangent portfolio (first-order condition)")
  (statement := /-- $w$ satisfies the tangency first-order condition when its marginal-variance
  vector $\Sigma w$ is parallel to the excess-return vector. -/)]
  MathFin.IsTangentPortfolioN

attribute [blueprint "def:tracking-error" (title := "Tracking error")
  (statement := /-- The squared tracking error $\sigma_p^2 - 2\,\mathrm{cov} + \sigma_b^2$ of given
  moments, the variance of the active return $R_p - R_b$
  (`trackingErrorSq_eq_variance_sub`). -/)]
  MathFin.trackingErrorSq

attribute [blueprint "def:binomial-no-arbitrage" (title := "Binomial no-arbitrage condition")
  (statement := /-- The one-period binomial model with up and down factors $u, d$ and rate $r$ is
  arbitrage-free: $0 < d < e^r < u$. -/)]
  MathFin.BinomialNoArb

attribute [blueprint "def:survival-function" (title := "Survival function of a lifetime")
  (statement := /-- $S_X(t) = P(X > t)$, the probability that the age at death $X$ exceeds $t$. -/)]
  MathFin.SurvivalModel.survivalFunction

attribute [blueprint "def:hjm-model" (title := "The HJM model")
  (statement := /-- An HJM model on $[0,H]$ over a Brownian motion $B$: forward rates $f(t,T)$
  with drift $\alpha$ and volatility $\sigma$ satisfying
  $f(t,T) = f(0,T) + \int_0^t \alpha(s,T)\,ds + \int_0^t \sigma(s,T)\,dB_s$ almost surely, for
  $t \le T$ and $t \le H$. -/)]
  MathFin.HJM.HJMModel

attribute [blueprint "def:gaussian-factor-copula" (title := "One-factor Gaussian copula")
  (statement := /-- The copula on $n$ names of the latent vector
  $X_i = \rho Z_0 + \sqrt{1-\rho^2}\,Z_i$ with independent standard normals; it is a copula for
  $\rho \in [-1,1]$. -/)]
  MathFin.gaussianFactorCopula

-- ===== area anchors: one result per area that had none on the map =====

attribute [blueprint "thm:martingale-transform" (title := "The martingale transform is a martingale")
  (statement := /-- For a martingale $M$ and a bounded predictable $A$ on a finite measure space,
  $(A \cdot M)_n = \sum_{k<n} \langle A_{k+1}, M_{k+1} - M_k \rangle$ is a martingale: the discrete
  stochastic integral, and the gains process of a trading strategy. -/)]
  MathFin.martingaleTransform_isMartingale

attribute [blueprint "thm:rockafellar-uryasev" (title := "Rockafellar–Uryasev: ES as a minimum")
  (statement := /-- For an integrable loss $X$ and $\alpha \in (0,1)$, $\mathrm{ES}_\alpha(X)$ is
  the least value of $c \mapsto c + (1-\alpha)^{-1}E[(X-c)^+]$. No continuity of the law is
  assumed. -/)]
  MathFin.isLeast_rockafellarUryasev

attribute [blueprint "thm:expected-shortfall-coherent" (title := "Expected shortfall is coherent")
  (statement := /-- For $\alpha \in (0,1)$, expected shortfall is a coherent risk measure on the
  integrable losses. -/)]
  MathFin.expectedShortfall_isCoherentRiskMeasure

attribute [blueprint "thm:expected-shortfall-dual-set"
  (title := "Expected shortfall's representing set")
  (statement := /-- On a finite probability space $(\iota, P)$ and for $\alpha \in (0,1)$, the
  representing set of $\mathrm{ES}_\alpha$ in the Artzner--Delbaen--Eber--Heath representation is
  exactly the set of probability vectors $q$ with $q_i \le (1-\alpha)^{-1} P\{i\}$, the
  probability densities bounded by $(1-\alpha)^{-1}$. -/)]
  MathFin.representingSet_expectedShortfall

attribute [blueprint "thm:coherent-risk-representation" (title := "Representation of a coherent risk measure")
  (statement := /-- On a finite state space a coherent risk measure $\rho$ of losses is the least
  upper bound of the expected losses $\sum_i q_i L_i$ over its representing set of probability
  vectors. -/)]
  MathFin.coherentRisk_isLUB

attribute [blueprint "thm:expected-shortfall-dual" (title := "Dual form of expected shortfall")
  (statement := /-- For an integrable loss $X$ and $\alpha \in (0,1)$, $\mathrm{ES}_\alpha(X)$ is
  the greatest value of $E[DX]$ over densities $0 \le D \le (1-\alpha)^{-1}$ with $E[D]=1$. -/)]
  MathFin.isGreatest_integral_mul_expectedShortfall

attribute [blueprint "thm:cvar-rockafellar-uryasev" (title := "CVaR of a compound-Poisson loss")
  (statement := /-- For $L = \sum_{i<N} X_i$ with $N \sim \mathrm{Poisson}(\lambda)$ independent of
  identically distributed integrable claims $X_i$, and $\alpha \in (0,1)$, $\mathrm{ES}_\alpha(L)$
  is the least value of $c \mapsto c + (1-\alpha)^{-1}E[(L-c)^+]$. Companion lemmas prove $L$
  integrable (`integrable_compoundPoisson`) and expand $E[(L-c)^+]$ as a Poisson mixture of the
  $n$-claim expectations (`integral_max_sub_compoundPoisson`). -/)]
  MathFin.isLeast_rockafellarUryasev_compoundPoisson

attribute [blueprint "thm:empirical-cdf-strong-law" (title := "Strong law for the empirical CDF")
  (statement := /-- For pairwise independent draws with a common law whose CDF is continuous,
  almost surely the empirical CDF converges to that CDF at every point. The convergence is
  pointwise; uniformity (Glivenko–Cantelli) is not proved. -/)]
  MathFin.tendsto_empiricalCDF_ae

attribute [blueprint "thm:compound-poisson-mgf" (title := "Compound-Poisson MGF")
  (statement := /-- For i.i.d. claims $X_i$, the MGF of the $n$-claim sum averaged over
  $n \sim \mathrm{Poisson}(\lambda)$ is $\exp(\lambda(M_X(t) - 1))$. The statement is in this
  mixture form; no claim-count process is constructed. -/)]
  MathFin.compoundPoisson_mgf

attribute [blueprint "thm:markowitz-lagrangian" (title := "Markowitz: the Lagrangian condition is sufficient")
  (statement := /-- For a positive-semidefinite covariance $\Sigma$, a portfolio with
  $\sum w_i = 1$, mean return $m$ and $(\Sigma w)_i = \lambda_1 + \lambda_2\mu_i$ for every asset
  has the least variance among all portfolios with $\sum v_i = 1$ and mean return $m$. -/)]
  MathFin.portfolioVarN_le_of_lagrangian_FOC

attribute [blueprint "thm:risk-parity-foc" (title := "Risk parity from the log-barrier condition")
  (statement := /-- If every asset's marginal variance equals $c / w_i$ for one constant $c$ (the
  uniform-budget log-barrier first-order condition), all risk contributions are equal. -/)]
  MathFin.isRiskParity_of_uniform_log_barrier_FOC

attribute [blueprint "thm:bond-immunization" (title := "First-order immunization")
  (statement := /-- If the duration-weighted values of an asset and a liability bond portfolio
  agree at the rate $r$, the derivative in $r$ of their net value is zero there. -/)]
  MathFin.bondPortfolio_immunization_first_order

attribute [blueprint "thm:vasicek-bond-pde" (title := "The Vasicek bond price solves its PDE")
  (statement := /-- For $\kappa \ne 0$, $u(\tau, r) = A(\tau)e^{-B(\tau)r}$ with the Vasicek
  loadings satisfies $-\partial_\tau u + \kappa(\theta - r)\partial_r u
  + \tfrac12\sigma^2\partial_r^2 u - ru = 0$. -/)]
  MathFin.vasicekBondPrice_solves_pde

attribute [blueprint "thm:heston-pde" (title := "Heston transform profile solves the pricing PDE")
  (statement := /-- If coefficient flows $A, B$ solve the Heston Riccati system, the transform
  profile built from them satisfies the backward Heston pricing equation
  $\partial_t\Phi + L\Phi = 0$. Existence of the Riccati solutions is a hypothesis. -/)]
  MathFin.Heston.hestonProfile_pde

attribute [blueprint "thm:impermanent-loss" (title := "Impermanent loss is never positive")
  (statement := /-- For a price ratio $r \ge 0$, the impermanent loss
  $2\sqrt r/(1+r) - 1$ of a fee-free constant-product position is at most $0$. -/)]
  MathFin.DeFi.impermanentLoss_nonpos

attribute [blueprint "thm:uniswap-v3-covered-call" (title := "A Uniswap v3 position is at most a covered call")
  (statement := /-- A v3 position with liquidity $L \ge 0$ on the range $[a, b]$ is worth at most
  $x_{\max}(s^2 - \max(s^2 - ab, 0))$: long its full $X$ holding and short a call struck at $ab$. -/)]
  MathFin.DeFi.v3PositionValue_le_coveredCall

attribute [blueprint "thm:glosten-milgrom-quote" (title := "Glosten–Milgrom: quotes are conditional expectations")
  (statement := /-- On a finite measure space, the conditional expectation of the asset value given
  the trade direction equals almost everywhere the ask $\int V\,d\mu[\cdot\mid B]$ on the buy
  event and the bid $\int V\,d\mu[\cdot\mid B^c]$ on the sell event. -/)]
  MathFin.Execution.condExp_payoff_eq_quote

attribute [blueprint "thm:aave-liquidation-kmv" (title := "Aave liquidation probability is a KMV default probability")
  (statement := /-- With lognormal collateral, liquidation threshold $LT > 0$ and debt $B + F > 0$,
  the probability that the single-collateral (v1) health factor is below $1$ at the horizon is the
  Merton–KMV default probability with barrier $(B+F)/LT$. -/)]
  MathFin.prob_healthFactorV1_lt_one_eq_kmvPD

/-! ### Shared objects and bridges

Objects the proofs already share, and theorems that already join two parts of the map. Before
these tags the proof-term graph of the blueprint fell into one main component and 34 islands:
each island was proved, but no recorded edge tied it to the rest. -/

attribute [blueprint "def:gbm" (title := "Geometric Brownian motion")
  (statement := /-- The GBM value function $S(t,x) = S_0 \exp((\mu - \tfrac12\sigma^2)t + \sigma x)$;
  at $x = B_t$ it is geometric Brownian motion. -/)]
  MathFin.gbmValue

attribute [blueprint "def:heat-feynman-kac" (title := "Heat-kernel solution $u(t,x)$")
  (statement := /-- The Feynman–Kac function of the heat equation,
  $u(t,x) = \int g(z)\,K(t, z - x)\,dz$ for the Gaussian heat kernel $K$. -/)]
  MathFin.FeynmanKacHeatEquation.feynmanU

attribute [blueprint "def:martingale-transform" (title := "Martingale transform")
  (statement := /-- The discrete stochastic integral
  $(A\cdot M)_n = \sum_{k<n} \langle A_{k+1}, M_{k+1} - M_k\rangle$. -/)]
  MathFin.martingaleTransform

attribute [blueprint "def:path-cylinder" (title := "Path cylinder")
  (statement := /-- The event that a trajectory agrees with a given path up to time $n$,
  $\{X_0 = x_0, \dots, X_n = x_n\}$. -/)]
  MathFin.pathCylinder

attribute [blueprint "def:black-scholes-model" (title := "The Black–Scholes model")
  (statement := /-- The Black–Scholes hypotheses: $S_0, K, \sigma, T > 0$ and $Z \sim N(0,1)$ under
  $Q$, for the terminal price $S_T = S_0 \exp((r - \tfrac12\sigma^2)T + \sigma\sqrt{T} Z)$. -/)]
  MathFin.BSCallHyp

attribute [blueprint "def:marginal-variance" (title := "Marginal variance $(\\Sigma w)_i$")
  (statement := /-- The marginal variance of asset $i$ in the portfolio $w$,
  $(\Sigma w)_i = \sum_k \Sigma_{ik} w_k$; the portfolio variance is $\sum_k w_k (\Sigma w)_k$. -/)]
  MathFin.marginalVariance

attribute [blueprint "thm:gbm-no-simple-arbitrage" (title := "No simple arbitrage for discounted GBM")
  (statement := /-- Under its risk-neutral measure, no simple (piecewise-constant, predictable,
  bounded) strategy trading the discounted GBM up to $T$ is an arbitrage: the forward FTAP applied
  to the discounted GBM as an EMM. -/)]
  MathFin.discountedGBM_noArbitrageSimple

attribute [blueprint "thm:numeraire-measure-equivalent" (title := "The numéraire measure is equivalent")
  (statement := /-- If $N, B > 0$ and $E^Q[N_T/B_T] = N_0/B_0$, the measure with density
  $N_T B_0 / (N_0 B_T)$ is a probability measure equivalent to $Q$. -/)]
  MathFin.numeraireMeasure_isEquivProbMeasure

attribute [blueprint "thm:stochastic-fubini-ito" (title := "Stochastic Fubini for the Itô integral")
  (statement := /-- For a Bochner-integrable family $\varphi : A \to L^2$ with jointly integrable
  representatives, $\int_A \big(\int_0^T \varphi_u\,dB\big)\,d\nu(u) = \int_0^T \big(\int_A
  \varphi_u\,d\nu(u)\big)\,dB$ in $L^2$. -/)]
  MathFin.StochasticFubini.stochFubini_ito

attribute [blueprint "thm:american-put-boundary-expiry" (title := "The American put boundary at expiry")
  (statement := /-- For $K, \sigma > 0$, $r > 0$ and $0 \le q \le r$, the exercise boundary of the
  American put in the Black–Scholes model tends to the strike as time to expiry tends to $0$. -/)]
  MathFin.BlackScholes.AmericanPut.Stopping.tendsto_brownianUsualExerciseBoundary_expiry

attribute [blueprint "thm:dupire-zero-rates" (title := "Dupire's formula, zero rates")
  (statement := /-- For an Itô process whose local variance $\sigma_{loc}(K)^2 K^2$ is a continuous
  version of $E[\delta_t^2 \mid X_t = K]$ on a window of strikes, at every strike of the window
  with $\partial_K^2 C > 0$: $\sigma_{loc}(K)^2 = 2\,\partial_T C / (K^2 \partial_K^2 C)$. Zero
  interest rate. -/)]
  MathFin.Dupire.dupire_pointwise

attribute [blueprint "thm:jump-diffusion-mixing" (title := "Jump-diffusion call as a mixture of Black–Scholes prices")
  (statement := /-- For a jump-diffusion whose Poisson jump count is independent of the Gaussian
  driver and of the i.i.d. jump sizes, the discounted expected call payoff is the Black–Scholes price averaged over the jump
  part $-\kappa + \sum_{i<N} J_i$. -/)]
  MathFin.JumpDiffusionHyp.call_eq_integral_bsV

attribute [blueprint "thm:black76-caplet" (title := "Caplet as a Black-76 call under the forward measure")
  (statement := /-- If the simple rate $L(T_0,T_1)$ is lognormal under the $T_1$-forward measure
  (a hypothesis, not derived from a rate model), the caplet is worth
  $P(0,T_1)\,\delta\,[F\Phi(d_1) - K\Phi(d_2)]$. -/)]
  MathFin.Contracts.value_caplet_black76

attribute [blueprint "thm:level-payments-annuity" (title := "Level payments are an annuity")
  (statement := /-- $n$ payments of $c$ at $\Delta t, \dots, n\Delta t$, discounted by the
  zero-coupon bond of a flat continuous curve, are worth $\sum_{i<n} c\,e^{-r(i+1)\Delta t}$. -/)]
  MathFin.Contracts.pathPV_fixedFlows_zcb

attribute [blueprint "thm:binomial-replication" (title := "The binomial price is the cost of a hedge")
  (statement := /-- Under $0 < d < e^r < u$ and $S_0 \ne 0$, every payoff has a predictable strategy
  whose martingale transform against the discounted spot, added to the tree price, is the
  discounted payoff on every path. -/)]
  MathFin.binomialPrice_replication

attribute [blueprint "thm:gaussian-portfolio-var" (title := "VaR of a Gaussian portfolio")
  (statement := /-- For a Gaussian vector $X$ and $\alpha \in (0,1)$,
  $\mathrm{VaR}_\alpha(\sum_i w_i X_i) = \sum_i w_i E X_i + \sqrt{w^\top \Sigma w}\,\Phi^{-1}(\alpha)$
  with $\Sigma$ the covariance matrix of $X$. -/)]
  MathFin.valueAtRisk_portfolio_gaussian

attribute [blueprint "thm:markowitz-random-returns" (title := "Markowitz for random returns")
  (statement := /-- For square-integrable returns, a budget- and target-feasible portfolio whose
  covariances with the assets meet the Lagrangian condition has the least variance
  $\mathrm{Var}[\sum_i w_i R_i]$ among feasible portfolios. Sufficiency only. -/)]
  MathFin.variance_le_of_lagrangian_FOC

attribute [blueprint "thm:large-portfolio-limit" (title := "The large-portfolio limit")
  (statement := /-- In the one-factor model with pairwise independent standard normal
  idiosyncratic terms and $\rho < 1$, the loss fraction converges almost surely to the conditional
  default probability $p(F)$, for any systematic factor $F$. -/)]
  MathFin.tendsto_oneFactorLossFraction_ae

attribute [blueprint "thm:one-factor-joint-default" (title := "Joint default is the Gaussian factor copula")
  (statement := /-- With $F, \varepsilon_1, \dots, \varepsilon_n$ independent standard normals,
  $\pi \in (0,1)$ and $0 \le \rho < 1$, the probability that every name defaults is
  $C(\pi, \dots, \pi)$ for the Gaussian factor copula $C$. -/)]
  MathFin.oneFactor_measureReal_iInter_default_eq_gaussianFactorCopula

attribute [blueprint "thm:uniswap-v3-bs-bound" (title := "A v3 position is worth at most a covered call")
  (statement := /-- Under the Black–Scholes model, the discounted expected value of a Uniswap v3
  position on $[a,b]$ is at most $x_{max}(S_0 - C)$, where $C$ is the Black–Scholes call struck
  at the geometric-mean price $ab$. -/)]
  MathFin.integral_discounted_v3PositionValue_le

attribute [blueprint "thm:capm-equilibrium" (title := "CAPM from market equilibrium")
  (statement := /-- If the market portfolio $w_M$ meets the tangency cross-product condition and
  $w_M^\top \Sigma w_M \ne 0$, every asset's excess return is its beta times the market's:
  $\mu_i - r_f = \beta_i (\mu_M - r_f)$ with $\beta_i = (\Sigma w_M)_i / w_M^\top \Sigma w_M$. -/)]
  MathFin.CAPM_from_market_equilibrium

attribute [blueprint "thm:tangent-portfolio-efficient" (title := "The tangent portfolio is efficient")
  (statement := /-- For positive semidefinite $\Sigma$, a fully invested portfolio with
  $\Sigma w = \lambda(\mu - r_f)$ is a tangent portfolio and has the least variance among the
  fully invested portfolios with the same expected return. -/)]
  MathFin.isTangentPortfolioN_and_portfolioVarN_le

attribute [blueprint "thm:two-asset-min-variance" (title := "The two-asset weight minimises variance")
  (statement := /-- When $D = \sigma_1^2 - 2\rho\sigma_1\sigma_2 + \sigma_2^2 > 0$, the closed-form
  weight $w^*$ gives $(w^*, 1-w^*)$ the least portfolio variance among all two-asset budgets. -/)]
  MathFin.portfolioVarN_minVarWeightTwo_le

attribute [blueprint "thm:utility-state-price-density" (title := "Marginal utility is a state-price density")
  (statement := /-- In the finite-state market with payoff matrix $A$ and prices $\pi$, let $\theta$
  be a local maximum of $\sum_\omega p_\omega u(W_\omega)$, $W = A^\top\theta$, on the budget set
  $\{\theta' : \pi\cdot\theta' = w_0\}$, with $p>0$, $w_0>0$, $W>0$ and $u'(W_\omega)>0$. Then
  $q_\omega = p_\omega u'(W_\omega)/\mu$, for some $\mu>0$, is a strictly positive state-price
  vector pricing every asset, and on a finite probability space charging every state there is an
  equivalent martingale measure for the excess returns. -/)]
  MathFin.exists_isEMM_of_isLocalMaxOn
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
  the supremum of the martingale prices is not part of this statement. -/)]
  MathFin.isCoherentRiskMeasure_superhedgingPrice

attribute [blueprint "thm:superhedging-price-lower-bound"
  (title := "The superhedging price dominates every martingale price")
  (statement := /-- For every martingale probability vector $q$ and every claim $Y$,
  $\sum_n q_n Y_n$ is at most the superhedging price of $Y$. -/)]
  MathFin.le_superhedgingPrice
