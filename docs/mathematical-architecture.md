# The mathematical architecture — the field's spine

Companion to [`architecture.md`](architecture.md), which documents the **engineering** architecture
(the three honesty tiers, the principle modules, the bridge methodology). **This** document is the
**mathematical** architecture: the unifying spine of mathematical finance, how the library's towers map
onto it, where the seams are coherent versus open, and the higher-level unification opportunities. It
exists because a top-notch formalization is not "all the theorems proved" — it is *the theorems organized
around the field's actual organizing principles, with the deep connections made load-bearing.*

Written 2026-06-29 from a whole-program architectural validation (grounded in code at every seam).

## The spine: four pillars + connective tissue

Mathematical finance is a few deep principles whose *consequences* are the models. The library has the
pillars; the question is whether the **connective tissue** that makes them one architecture is realized.

### Pillar I — No-arbitrage as convex duality (the separating hyperplane)
The FTAP: *no-arbitrage ⟺ ∃ equivalent martingale measure.* Mathematically this **is** the
separating-hyperplane theorem — the attainable-gains cone misses the positive orthant ⟺ a
strictly-positive functional (the EMM) separates them; price `= ⟨EMM, payoff⟩`.
- **Root:** `Foundations/ConvexSeparation.exists_pos_dual_of_disjoint_stdSimplex` — its own docstring:
  *"the separating hyperplane **is** the equivalent martingale measure."*
- **Instances:** `FTAPOnePeriod`/`FTAPOnePeriodVector`/`FTAPDiscrete`/`FTAPMultiState`/`FTAPTwoState`,
  `StatePrices`, `ConvexPricingFunctional` (the EMM as a convexity-preserving positive operator).

### Pillar II — Stochastic calculus (Itô semimartingales)
The engine of continuous-time models: every model is `dX = b dt + σ dB`, and Itô's formula + the
stochastic integral make functionals of `X` computable.
- **Library:** the Itô tower — `ItoIntegralCLM` (+ isometry), `QuadraticVariationL2`,
  `ItoFormulaUnrestricted` (general C³ as a continuous local martingale), `ItoFormulaGBM`.
- Since 2026-08-07 ([#183](https://github.com/formal-applied-math/formal-mathfin/issues/183)) the tower
  states the `σ` in `dX = b dt + σ dB`, not merely that some `σ` exists: every rung from
  `ito_formula_td_L2_bddDeriv` down to `discountedGBM_eq_itoIntegral` names its integrand, ending at
  `gfx =ᵐ [σ·Ŝ(·)]` for the discounted GBM. Naming the *representation's* integrand for a general
  `L²` claim — the Clark–Ocone direction, #182 — is still open.

### Pillar III — The probabilistic ⟷ analytic duality (generator / Feynman–Kac / PDE)
The same price is a risk-neutral **expectation** (probabilistic) and a **PDE solution** (analytic); the
bridge is the infinitesimal generator: Itô ⟹ Kolmogorov backward equation ⟹ Feynman–Kac.
- **Library:** `FeynmanKacHeatEquation` + `BlackScholes/PDEFromFeynmanKac` (the BS-PDE keystone, built);
  `BlackScholes/PDEFromIto` (the Itô-drift route).

### Pillar IV — Intensity & exponential families (the tractability backbone)
Closed forms come from Gaussian/lognormal/exponential structure; and a single *"exponential of an
integrated intensity"* unifies discounting, mortality, credit hazard, and the Poisson rate.
- **Library:** `StandardNormal`/`GaussianMoments` (Gaussian closed forms), `ExponentialDiscount`
  (the shared root), `Bridges/SurvivalUnification` (mortality ≡ credit hazard, *certified*),
  `GaussianGirsanov` (the Esscher exponential tilt).

## The connective tissue — what would make it ONE architecture

| Bridge | Connects | Status |
|---|---|---|
| **Girsanov / Esscher** (change of measure) | I (EMM) ↔ II (Itô) ↔ IV (exp tilt) | **PARTIALLY WIRED at I↔II (Phase 2, 2026-06-30) — the martingale side.** `Foundations/Girsanov.bs_discounted_isQMartingale` now exhibits the Black–Scholes EMM as an *explicit* Girsanov density change `Q = withDensity(exp(−θX_T − ½θ²T))` (constant market price of risk `θ = (μ−r)/σ`), under which the discounted stock is a `Q`-martingale — retiring the Wald shortcut of `discountedGBM_isMartingale` (which took `Q = P` from the start). It stands on the reusable **Bayes change-of-measure engine** `Foundations/ChangeOfMeasure.changeOfMeasure_setIntegral_eq` (`Z` and `Z·D` both `P`-martingales ⟹ `D` is a `Q`-martingale on `[0,T]` — no stochastic calculus, only conditional expectations). **The distributional side is now FULLY CLOSED for constant θ (2026-07-05):** `Foundations/GirsanovConstantTheta.Btheta_isQBrownianMotion` proves the drift-corrected `B^θ_t = X_t + θ t` is a genuine `Q`-Brownian motion — zero start, Gaussian increments `B^θ_t − B^θ_s ~ N(0, t−s)`, **and** independence of disjoint increments (corpus `gir-const-theta-qbm`, `full`; marginal law `gir-const-theta-marginal`, `full`) — from the same Bayes engine + Wald exponentials (`Wald(−θ)`, `Wald(a−θ)`) giving every `Q`-conditional MGF, Mathlib's complex-MGF machinery (`integrableExpSet_eq_of_mgf` → `eqOn_complexMGF_of_mgf` → `ext_of_complexMGF_eq`) reading off the Gaussian laws, **with no adapted-integrand Itô formula**. The increment *independence* — earlier believed blocked by a Mathlib gap ("conditional-MGF ⟹ independence" is absent; only the reverse `condExp_indep_eq` exists) — is reached WITHOUT that lemma: via `indepFun_iff_charFun_prod`, the joint characteristic function at `w = (w₁, w₂)` is the charFun-at-`1` of the Gaussian law of the linear combination `w₁·I₁ + w₂·I₂` (from the joint-MGF factorisation — a `condExp_mul_of_stronglyMeasurable_left` pull-out), so it factors into the two marginal Gaussian characteristic functions (`charFun_gaussianReal`). **Since 2026-07-06 this entire characteristic-function chain is a single reusable module** `Foundations/ExpMartingaleQBrownian.isQBrownianMotion_of_expMartingale`: any drift-corrected process that supplies its own exponential martingale (`exp(a·Y − ½a²·)` a `Q`-martingale, packaged as `IsExpQMartingale`) is a `Q`-Brownian motion by one application — const-θ instantiates it via `expBtheta_isQMartingale`, and the **simple (piecewise-constant adapted) θ** case now instantiates it too (`GirsanovSimpleTheta.Btheta_simple_isQBrownianMotion`, corpus `gir-simple-adapted`, `full`, 2026-07-06) — the general bounded-adapted-θ Girsanov for the simple case, strictly beyond constant θ, via the spine `simple_spine_ae` (`E^{−c}·exp(a·B^θ − ½a²·) =ᵐ E^{a−c}`) fed to the Bayes engine with an `L²`-Hölder mixed-time integrability, no adapted Itô. **Continuous bounded-adapted θ is now CLOSED too (2026-07-09):** `Foundations/GirsanovAdaptedTheta.Btheta_isQBrownianMotion_adapted` (corpus `gir-thm-9.1.8`, `full`) proves `B^θ_u = B_u + ∫₀ᵘθ ds` is a `Q`-Brownian motion for bounded `𝓕`-adapted path-continuous θ under `Q = μ.withDensity(exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds))` — spine-free, the simple-θ identity passed to the limit through the a.e.-subsequence set-integral engine, no adapted-integrand Itô formula and no Novikov crux; the const → simple → continuous-adapted arc is COMPLETE. Still **open**: only the strictly more general `L²`/progressive-θ under Novikov (`sc-thm-9.1.8`). The d-asset Esscher FTAP (IV) is a *discrete* Girsanov, still unlinked to the continuous one. |
| **Martingale representation** (attainability) | II (Itô) ↔ I (EMM) | **WIRED (2026-08-07) — the I↔II seam from the other side.** Girsanov wires this seam in the direction of *existence*: the equivalent martingale measure exhibited as an explicit change of measure. Martingale representation wires it in the direction of *uniqueness and attainability*, and together they close it. `Foundations/MartingaleRepresentation.itoIntegralCLM_T_surjective_onto_centered` proves the Itô isometry `φ ↦ ∫₀ᵀ φ dB` (already a `LinearIsometry` from the predictable `L²` integrands into `L²(μ)`) is **onto** the centered `𝓕ᴮ_T`-measurable part of `L²(μ)`, bundled as the `LinearIsometryEquiv` `itoIsometryEquiv`; `exists_itoIntegral_representation` is the terminal `∃!` form and `martingale_representation` the process form (corpus `gir-thm-9.3.4`, flipped `reduced_core → full`). The proof is an orthogonal decomposition against the range — closed because it is an isometry's image, hence orthogonally complemented — plus totality of the step-integrand Doléans exponentials: `DoleansStepRepresentation.stepDoleans_sub_one_mem_range` puts every such exponential minus one *inside* the range, and `WienerExponentialTotality.eq_zero_of_orthogonal_stepDoleans` kills anything orthogonal to all of them, by MGF analytic continuation on the cylinder σ-algebras of `BrownianCylinderGeneration` (`⨆ₙ cylinderSigma B T n = natFiltration`) followed by Lévy upward convergence. No Malliavin calculus, no Clark–Ocone, and no adapted-integrand Itô formula. Centering (`𝔼[∫₀ᵀ φ dB] = 0`) is proved a floor down as `ItoIntegralProcessGeneral.integral_itoIntegralCLM_T`. The finance reading is `Foundations/MarketCompleteness`: `exists_replicating_strategy` (every `L²` `𝓕ᴮ_T`-claim is `𝔼_μ[H] + ∫₀ᵀ φ dB` for a *unique* hedge) and `superReplication_eq_emm_price` (the continuous-time superreplication duality, its "EMM price" being `𝔼_μ[H]`). **Honest scope on uniqueness:** `measure_eq_of_pricesGainsAtZero` proves uniqueness of the pricing measure on `𝓕ᴮ_T` *for measures that price the traded gains at zero*, not the unconditional second FTAP. The textbook fair-game step needs the wealth process to be an integral against the price `S`; the one built here integrates against `B`, and `S` and `B` share only a filtration, so that step is the named hypothesis `PricesGainsAtZero` — step (i) of the textbook proof hypothesised, step (ii) proved. It is guarded by two proved facts, `pricesGainsAtZero_self` (`μ` satisfies it) and `pricesGainsAtZero_of_gains_martingale` (the textbook gains-martingale condition implies it); the corollary `emm_unique_of_complete` consumes only `IsEMM`'s `isProb` and `ac`. Only `complete ⟹ unique` is delivered; the converse needs Jacod–Yor extreme points. `superReplication_eq_emm_price` does **not** close the finite-state Farkas gap of `Foundations/SuperhedgingDuality` — separation there, martingale representation here. |
| **Feynman–Kac** (generator) | II ↔ III | **WIRED** (BS-PDE keystone). Not yet abstracted to a general generator / Kolmogorov-backward framework. |
| **Convex duality** (separation / Legendre–Fenchel) | I (pricing) ↔ IV (risk) | **WIRED (Phase 1, 2026-06-29).** The shared root `Foundations/ConvexDuality.exists_pos_separating_of_cone_disjoint_simplex` (cone↔simplex) + its companion `exists_separating_of_not_mem_cone` (point↔cone) now carry **both** towers: the FTAP kernel `exists_pos_dual_of_disjoint_stdSimplex` is *re-derived* from the root (pricing side), and the coherent-risk ADEH representation `RiskMeasures/AcceptanceSet.coherentRisk_isLUB` is its risk-side instance (`WorstCaseRisk.worstCase_isLUB` a concrete case). Superhedging is wired as the `SuperhedgingDuality.emm_le_superReplication` bound; the strong-duality *equality* awaits a finite-dim Farkas (Mathlib gap). |
| **The numéraire** (change of numéraire; log-optimal portfolio) | IV ↔ I (EMM) | **WIRED (2026-07-03) — both seam directions, at their achievable scope.** *(a) The change-of-numéraire law.* `Foundations/Numeraire.changeOfNumeraire`: with `Q^N = Q.withDensity((N_T·B₀)/(N₀·B_T))`, `N₀·𝔼^{Q^N}[X/N_T] = B₀·𝔼^Q[X/B_T]` for every claim `X` (a pure measure-transport identity + cancellation of `N_T` — no integrability needed), companion `numeraireMeasure_isProbabilityMeasure`. Genuinely **consumed** by two instances: `StockNumeraire.stockNumeraireMeasure_eq_numeraireMeasure` (BS stock numéraire = instance `B_T=e^{rT}`, `B₀=1`, `N=S`) and `ExchangeOption.exchangeOption_numeraire_price` (Margrabe's `S²`-numéraire valuation = instance `X=` exchange payoff, `N=S²`). (Garman's normal form is post-integration closed-form algebra — no measure — so not an instance; none was fabricated.) *(b) The numéraire-portfolio ⟹ EMM direction.* `Performance/KellyNumeraire.kellyNumeraire_isRiskNeutral`: the growth-optimal (Kelly) wealth, as deflator, turns the physical measure into the EMM (`q₊·b + q₋·(−1) = 0`), the `p`-independence being the Kelly first-order condition. **Honest remaining scope:** direction (b) is the **discrete, two-outcome** shadow of the **continuous** Long/Platen benchmark theorem (deflated prices are `P`-martingales, EMM density `∝ 1/N*`), still gated on a state-price-density / market model absent from the Itô tower. |
| **Lattice limit (CLT)** (discrete → continuous) | Binomial ↔ Black–Scholes | **WIRED** (`CRRConvergence.binomialPrice_call_tendsto_bs`), by characteristic functions and Lévy continuity. Donsker's invariance principle is **not** formalized — this is the pricing limit, not the functional CLT, and `docs/applied-areas.md` lists Donsker among the gaps. |

## Coherence verdict

Individually the towers are coherent and the *engineering* architecture is documented. **Phase 1
(2026-06-29) realized the spine's #1 unification**: the convex-duality bridge (I↔IV) is now WIRED — the
FTAP separating functional and the coherent-risk-measure representation are *proved* to be the same
Hahn–Banach root (`Foundations/ConvexDuality`), no longer split across files that never name it. Of the
bridges, Feynman–Kac (II↔III), the lattice limit (discrete↔continuous), and convex-duality (I↔IV) are WIRED;
Girsanov (I↔II) is now **wired** (Phase 2, 2026-06-30 — the EMM/change-of-measure *martingale*
side, constant θ: the risk-neutral measure is an explicit density change, built on a reusable Bayes
change-of-measure engine), with the *distributional* Girsanov now **fully closed for constant θ**
(2026-07-05, `Btheta_isQBrownianMotion`: `B^θ` is a `Q`-Brownian motion — Gaussian *and independent*
increments — via `indepFun_iff_charFun_prod` on the Gaussian joint law, no adapted Itô), and now **fully
closed for bounded adapted continuous θ** (2026-07-09, `Btheta_isQBrownianMotion_adapted`, `gir-thm-9.1.8`
`full`, via the spine-free simple → continuous limit), and finally **for bounded predictable θ**
(`Btheta_isQBrownianMotion_predictable_of_bdd`, `gir-thm-9.1.8-predictable` `full`) — note the hypothesis
is *bounded* predictable (`∀ t ω, |θ t ω| ≤ C`), which is strictly inside the integrand class:
`itoIntegralCLM_T : Lp ℝ 2 (trimMeasure_T T) →L[ℝ] Lp ℝ 2 μ` accepts every square-integrable predictable
integrand, and on a finite measure `L² ⊋ L^∞`. So the strictly more general `L²`/progressive-θ under Novikov is still open, as is Novikov's condition itself
(`gir-thm-9.1.7`, a structure spec, not a derivation); the numéraire (IV↔I) is now **wired at its achievable scope** (2026-07-03):
the change-of-numéraire *formula* (`Foundations/Numeraire.changeOfNumeraire`, consumed by the BS stock
numéraire and the Margrabe `S²`-numéraire), **and** the numéraire-*portfolio* ⟹ EMM direction in the
discrete Kelly market (`Performance/KellyNumeraire`), with only the *continuous* Long/Platen version of
the latter (needing a state-price-density model) still open. **The library's pricing↔risk spine is
realized, the continuous-time EMM is an explicit change of measure, prices are provably numéraire-invariant,
and the growth-optimal portfolio is shown to induce the EMM.**

**Martingale representation closes I↔II from the other side (2026-08-07).** Girsanov wires that seam in the
direction of *existence*: the equivalent martingale measure as an explicit change of measure. Martingale
representation wires it in the direction of *uniqueness and attainability*:
`MartingaleRepresentation.itoIntegralCLM_T_surjective_onto_centered` proves the Itô integral exhausts the
centered `𝓕ᴮ_T`-measurable part of `L²(μ)`, and `MarketCompleteness.exists_replicating_strategy` reads off a
unique hedge for every square-integrable claim. Together they close the seam. What is still open on it: the
`L²`/progressive-θ Girsanov under Novikov, and the converse `unique ⟹ complete` (Jacod–Yor extreme
points). The continuous Long/Platen numéraire-portfolio benchmark also stays open.

**The `∫ φ dS` half is closed (2026-08-16) — the chain rule.** What that sentence used to list as the
third open item is built. For a driver `φ` and `M = φ●B`, `ItoIntegralAgainstMartingale` puts the
integral against `M` on the bracket-weighted `L²(φ²·trim_T)` by composing `itoIntegralCLM_T` with the
`p = 2` multiplication isometry `ψ ↦ ψφ` (`LpMulIsometry`; Mathlib carries only `p = 1`, where density
and multiplier coincide). Both factors are isometries, so `‖∫ψ dM‖ = ‖ψ‖_{L²(⟨M⟩)}`; the chain rule
`∫ψ dM = ∫ψφ dB` is then how the object is built, and what identifies it as *the* stochastic integral
against `M` is `itoIntegralAgainst_elementary`, the Riemann–Stieltjes agreement `∫ Z·1_{(a,b]} dM =
Z·(M_b − M_a)` on a band. The finance consequence is that a hedge is a **holding in the price**
(`MarketCompletenessInPrice.exists_replicating_strategy_in_price`, needing only `σ ≠ 0` a.e. — the
weighted norm rescales, so no uniform lower bound), and that the gains-neutrality hypothesis becomes a
theorem: `PricingMeasureL2Density.measure_eq_of_density` derives `PricesGainsAtZero` from `S` being a
`Q`-martingale together with a square-integrable density, and concludes `Q = μ` on `𝓕ᴮ_T`. Still out of
scope on this seam, unchanged: the Jacod–Yor converse, a drift term in the price (additive; what HJM
needs), and the integral against a general semimartingale — `ContinuousMarket`'s meaning-2 boundary
narrows but does not close.

## A representation layer, not a fifth pillar: the reified contract (2026-08-17)

`MathFin/Contracts/` is not a new mathematical principle beside the four pillars — it is a
**representation layer that sits across them**, and is worth recording here for that reason.
Before this tower every payoff in the library was a lambda written once, inline, inside the
integral that priced it (Pillar II/III territory): the payoff and the pricing model were the same
syntactic object, so nothing could be said about the payoff independently of the model that
happened to price it. `Payoff ι` / `Contract ι` (inductives over a typed underlying index) give the
payoff its own object, prove it measurable and adapted to its own observation times — the
hypothesis a future Pillar II stochastic-integral rung will need an integrand to satisfy, not
yet consumed by anything in this round — and reduce `Contract.value` on four reified instruments
to the Black–Scholes closed forms Pillar IV's
Gaussian-moment machinery already produced (`bs_call_formula`/`bs_put_formula`/
`bs_cash_or_nothing_formula` are direct Gaussian-integral derivations; none routes through Pillar
III's Feynman–Kac/PDE keystone). `Contracts/Pricing.lean`
is deliberately thin at the Pillar I seam: `value_deliverAsset` and `value_process_martingale` are
conditional-expectation facts (`Martingale.condExp_ae_eq` + `martingale_condExp`), needing a bare
probability measure under which the price is a martingale, not `ContinuousMarket.IsEMM`'s
equivalence content — so this layer touches Pillar I's *martingale* vocabulary without yet drawing
on its *no-arbitrage* one.

Consulted as a source, not a template: Bilokon, *The Contract Is Not the Model* (2026); see
`docs/sources.md` and `docs/bridges.md` rows CT/CT.2 for what was taken and what was designed
afresh.

**Two rungs deferred, each waiting on the corpus case that forces it, not built ahead of it:**
branching contracts and the lifecycle state machine (outstanding notional, absorbing termination) —
the strongest part of the source artifact, forced by the first autocall entry; and path-dependent
instances — every instrument here observes only at maturity `T`, forced by wiring the model map to
the full GBM path rather than the terminal value, which an Asian or barrier reified instrument
needs. A third, not deferred but genuinely open: identifying `Contract.value` with the initial
wealth of a replicating strategy rather than merely a martingale value process — its dependency,
`∫ ψ dS`, is now built (`MarketCompletenessInPrice.exists_replicating_strategy_in_price`, the row
above), so this is buildable rather than blocked, and is the natural next seam between this layer
and Pillar I.

## The higher-math unification roadmap (apparently-disconnected fields that connect)

Ranked by leverage × tractability:

1. **The convex-duality unification (I↔IV) — ✅ REALIZED (Phase 1, 2026-06-29).** The shared root is
   extracted (`Foundations/ConvexDuality`: the cone↔simplex separation + the point↔cone companion, sharing
   two named atoms), and the FTAP kernel (re-derived from it), the coherent-risk ADEH representation
   (`coherentRisk_isLUB`), a concrete instance (`worstCase_isLUB`), and the superhedging bound
   (`emm_le_superReplication`) are all instances/consumers of it. **Proved: the FTAP and the
   coherent-risk-measure representation are the same Hahn–Banach theorem.** Remaining as backlog: the
   superhedging strong-duality *equality* (needs a finite-dim Farkas — a Mathlib gap), and the Gaussian
   `CVaR_α(L) = sup_{Q∈Q_α} E_Q[L]` robust form (the continuous instance, off the finite-state spine).

2. **Girsanov as the I↔II connective tissue — ✅ MARTINGALE SIDE DONE (Phase 2, 2026-06-30).** The
   continuous EMM is now *derived as an explicit change of measure*: `Girsanov.bs_discounted_isQMartingale`
   makes the Black–Scholes risk-neutral measure a Girsanov density tilt (constant θ), under which the
   discounted stock is a `Q`-martingale — retiring the Wald shortcut, standing on a reusable Bayes engine
   `ChangeOfMeasure.changeOfMeasure_setIntegral_eq`. **The distributional Girsanov is now fully closed for
   constant θ (2026-07-05):** `GirsanovConstantTheta.Btheta_isQBrownianMotion` proves drift removal →
   `Q`-Brownian (Gaussian *and independent* increments) for constant θ, with the increment independence
   reached via `indepFun_iff_charFun_prod` on the Gaussian joint law (the joint charFun factorises through
   the Gaussian law of every linear combination of the increments) — sidestepping the missing
   "conditional-MGF ⟹ independence" lemma entirely, no adapted Itô. The characteristic-function chain is
   now the reusable `ExpMartingaleQBrownian.isQBrownianMotion_of_expMartingale` (2026-07-06), instantiated
   here from `expBtheta_isQMartingale`, and then for **simple** adapted θ (`Btheta_simple_isQBrownianMotion`,
   2026-07-06) and **bounded adapted continuous** θ (`Btheta_isQBrownianMotion_adapted`, `gir-thm-9.1.8`
   `full`, 2026-07-09). The feared adapted-integrand Itô formula was **never needed**: the bounded adapted
   Doléans exponential is handled **spine-free** — the simple-θ exponential-martingale identity is passed to
   the limit through an a.e.-subsequence set-integral engine (`tendsto_setIntegral_of_subseq_ae_of_sq_bound`),
   sidestepping the pathwise quadratic variation the tower lacks. Remaining as backlog: only the strictly more
   general `L²`/progressive-θ under Novikov (`sc-thm-9.1.8`), and unifying the discrete Esscher FTAP with the
   continuous tilt. **The seam's other direction — attainability — landed 2026-08-07** (the
   martingale-representation row above): the Itô integral is onto the centered `𝓕ᴮ_T`-measurable claims, so
   the market driven by `B` is complete, and the pricing measure is pinned on that filtration among measures
   that price the traded gains at zero.

3. **The generator / Kolmogorov abstraction (II↔III).** Abstract Feynman–Kac into the infinitesimal
   generator → backward equation, of which the BS-PDE, the heat equation, and Vasicek are instances.

4. **The intensity / Cox extension (IV).** Extend the built `ExponentialDiscount`/`SurvivalUnification`
   root to *stochastic* intensity (Cox / doubly-stochastic Poisson), unifying credit, mortality, and the
   Poisson tower; the Esscher tilt = minimal-relative-entropy change ties IV back to I and to information
   theory.

5. **The numéraire / log-optimal connection (IV↔I).** The Kelly/log-optimal portfolio is the numéraire
   under which the EMM is the physical measure — connecting portfolio choice to pricing.

## What "top-notch" means at this level

Not more theorems, not polish — **realizing the architecture**: naming the shared roots and wiring the
open seams, so the library becomes a *formal theory of mathematical finance organized around its actual
spine.* That is the roadmap's elusive "tier 3": original not as a new theorem, but as a coherent formal
**architecture** of the field that no one has built.
