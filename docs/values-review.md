# Values review — the upgrade engine (not a pass/fail gate)

The mechanical gates (`tests/test_values.py`, `AxiomAudit*.lean`, the
verification ledger, the CI gates in `build.yml`) enforce everything a
machine can check. This protocol covers what a machine cannot: the eight
judgment lenses that define the repo's quality bar. Its output is **not a
pass/fail stamp** — a green "8/8 PASS" checkmark is exactly how a library
quietly settles into being a *fine* dump. The lenses are read as
**gradients**: for each, where is the work strongest (the exemplar to
propagate) and what is the next concrete **upgrade** that raises its ceiling?
Each review produces a ranked backlog of value-aligned upgrades and the
upgrades executed that session — and the session's job is to *do the top
ones*. The **pipeline enforces the cadence** (not a quality threshold):
`tests/test_values.py::test_values_review_is_current` fails when the corpus
has grown more than 12 entries past the last recorded review. A regex cannot
check "beautiful"; it can check "nobody refreshed the backlog."

Reviews before November 2026 are in [`archive/values-review-2026-05-to-10.md`](archive/values-review-2026-05-to-10.md).

## The eight lenses

1. **Inspired math quality** — each result earns its place: a structural
   fact or a clean mechanism, not bookkeeping dressed as a theorem.
2. **Mathlib / BrownianMotion (Degenne) coherence** — consume the libraries'
   machinery, never re-derive it; choose the canonical upstream API; no thin
   wrappers around single upstream lemmas.
3. **Zero slop** — no opaque discharges where a certificate-shaped proof
   exists, no ring-fallback hiding the conceptual step, no duplicated
   sub-derivations, no dead hypotheses.
4. **Architectural ingenuity** — the decomposition is the right shape: each
   lemma carries one idea, the pieces compose so future results get cheaper,
   nothing is proved at the wrong level of generality.
5. **First principles** — conclusions are derived from honest hypotheses;
   no hypothesis secretly contains the conclusion; no theorem that is its
   own definition unfolded.
6. **Mathlib / BrownianMotion idiomatic register** — naming, hypothesis
   style, namespace and `variable` discipline, statement shapes a Mathlib
   reviewer would accept.
7. **Concept clarity** — every docstring tells the honest mathematical
   story (what is proved, from what, what is *not* claimed); a strong
   probabilist reads the statement and says "yes, that is the theorem."
8. **Beautiful, elegant math** — the proof is the obviously-right argument
   once seen; the writeup neither obscures a beautiful idea nor dresses up
   a trivial one.

## Protocol

- **When**: at the close of any session that adds or changes proof content;
  at latest every 12 corpus entries (the CI ratchet's slack — one session's
  growth).
- **How**: at least three independent review agents, the lenses split among
  them, reading the work and its context (read-only; never running Lean) —
  then **adjudicated by the maintainer** against the settled doctrine (the
  wrapper taxonomy, the two-tower direction) and `grep`-confirmed usage,
  because panel agents lacking that context systematically over-escalate
  (calling a consumed rewrite-handle "slop") or under-escalate (all-green
  sycophancy). For each lens, name the current **exemplar** (the bar to
  propagate) and the next **upgrade** (the gradient). Genuine slop uncovered
  is fixed in-session; larger upgrades become ranked backlog items with
  owners (usually a future session's opening move). Each item is filed as an
  issue before the entry is recorded and ends with its outcome tag: `[#N]`,
  later `[done: <where>]` or `[retired: <why>]`
  (`tools/verify/review_backlog.py`, gated by
  `test_every_review_backlog_item_has_an_outcome`).
- **The standing first pass — read the prose against its own statement.**
  Before the lenses, for everything the session touched: does the docstring,
  the corpus `description`, or the doc paragraph claim more than the Lean
  says? This is not a hypothetical failure. On 2026-08-07 five corpus
  entries described the stochastic term as `∫₀ᵀ f_x(s,B_s) dB_s` while
  stating only `∃ gfx`; the README's landmark table rendered
  `ito_formula_unrestricted` as an integral identity when the theorem proves
  only that a residual is a continuous local martingale; and four more
  descriptions claimed a textbook theorem (`L^p` convergence, existence *and*
  uniqueness, general `σ(s)`, uniqueness of a bounded classical PDE solution)
  where the entry delivered a narrower result. Nobody wrote a false claim on
  purpose — the prose described the theorem everyone had in mind and the
  statement quietly said less.
  The mechanical half is two gates in `test_values.py`:
  `test_prose_does_not_outrun_statement` (an `∃`-statement whose witness is
  never pinned down while the prose writes the integral that would pin it
  down) and `test_reduced_core_description_discloses_scope` (a `reduced_core`
  `description` must say what the entry does not deliver). The judgment half
  stays here, and it is the larger half: `description` is published in the HF
  dataset and documented as "natural-language mathematical statement", so it
  is an outward-facing claim, not a private note. Where an entry's
  `description` states the **textbook target** rather than the delivered
  result, the delivered scope must be explicit in the same field, not left to
  `formalization_scope`.
  **Machine ordering: tried and retired.** On 2026-09-18 a TypeSafe Jev
  classifier (`tools/verify/prose_sweep.py`, now in git history) scored every
  `description` against its statements to order this pass. It earned its keep
  once, on an unread backlog: before that day's corrections, 16 of the 23
  entries it scored above 0.7 were genuine mismatches. Its blind spot was a
  conclusion assumed as a structure field, which the `reduced_core` gate now
  covers. Against the prose of two review rounds it found nothing real, and it
  was retired by its own rule at the second ("the Greeks state genuine higher
  derivatives"). Revive it only for a large unread backlog, never to read a
  change's own prose.
  **Higher derivatives are stated with `deriv`.** An entry named for a
  higher-order sensitivity states it for the price itself:
  `HasDerivAt (deriv V) …`, or `s ↦ deriv (V s) y` for a mixed partial. It does
  not state the derivative of an explicit lower-order formula such as a delta
  `Φ(d₁)` or a vega `S·ϕ(d₁)·√τ`. `hasDerivAt_deriv_of_eventually`, or
  `hasDerivAt_deriv_param_of_eventually` for a mixed partial
  (`Probability/Analysis/DerivOfDeriv.lean`), makes the formula-level result a
  statement about the price, once the formula is shown to be the lower
  derivative near the point. The Greeks family has stated genuine higher derivatives since
  2026-09-18. An entry that still differentiates a formula says so in its
  description ("stated as the S-derivative of …"). It cites the entry or lemma
  that identifies the formula with the lower-order derivative, and it never
  names the higher derivative as though one theorem stated it.
  **Names are labels, not claims.** An entry's `name` may label the result it
  targets; it may not assert a property the entry does not deliver
  ("Existence and Uniqueness" on a uniqueness entry, "Convexity" where only a
  second derivative is stated).
- **Junk values, inside the first pass.** For every price, expectation, probability or rate the
  session's prose names: does the statement carry the condition that makes the Lean term mean it
  (integrability, a non-zero denominator, `≠ ∞`, a non-null conditioning event)? Where it does not,
  the term may be Lean's totalized `0` and the prose describes nothing. The rule and the library's
  cases are in [`design.md`](design.md#2-a-junk-value-never-gets-a-financial-meaning).
- **Record**: append a review block below, headed
  `## YYYY-MM-DD — corpus <N> — <one-line title>` (the freshness test parses
  the date and the `corpus <N>` count anywhere in the heading; a
  `commit <sha>` provenance segment is optional — older entries carry it,
  working-tree entries omit it). Record (i) the **upgrades executed** this
  session, (ii) the refreshed **ranked backlog** of value-aligned upgrades,
  and (iii) the evidence/context (mechanical floor, panel findings confirmed
  or dissolved). This is a record of **direction, not a grade** — there is no
  PASS line to award; the failure mode the model guards against is a review
  that finds nothing to improve.

## Review log

## 2026-11-25 — corpus 921, modules 808 — the recorded backlog cleared: every item done, filed or retired

Scope: every ranked-backlog item recorded in this file, 326 across 57 entries. Ten workstreams
worked them in parallel on runners and merged onto `backlog/integ`. The outcome of each item is
tagged at its end, and `test_every_review_backlog_item_has_an_outcome` (with
`tools/verify/review_backlog.py`) keeps it that way:
- 179 are done, each tag naming where it landed;
- 134 point to an issue, 40 of them filed in this wave (#593–#632), each with a `Blueprint:` line;
- 13 are retired, each with its reason.

Corpus 919 → 921: the down-and-out image form split out of the BGK entry, as a reduced core, and
SSVI's tail condition, in full. Five new modules (`IndepPast`, `IdentDistribSum`, `DriftPath`,
`BarrierReflection`, `SSVI`). The `MathFin/` diff is +3.9k / −2.5k across 127 files, mostly
refactors toward one object per idea. All nine `maxHeartbeats` bumps are gone (ratchet 9 → 0).

### The standing first pass: prose against statement

- `TenorGrid.piecewiseLinear` was "linear interpolation between adjacent nodes"; only the node
  values are proved, so the docstring says the linearity is by construction (backlog 7 asks for
  the theorem).
- `integral_abs_sum_le_of_identDistrib` was titled Wald's bound. It is the triangle inequality
  plus one `L¹` norm per summand; it is now titled for what it says. The Wald step stays with
  the Poisson count in `CompoundPoissonCVaR`.
- The Markowitz diversification iff as the backlog wrote it is false: with shorting,
  `V_min < σ₁²` holds iff `ρ ≠ σ₁/σ₂`. `portfolioVarTwo_gt_min` proves the true statement, and
  the tag says so.
- `kellyMarket_numeraire_portfolio`'s "first order only" disclaimer is gone because it stopped
  being true: its stationarity now comes from `kelly_isLocalMaxOn` (Kelly's inequality), not the
  first-order formula. The statement is unchanged.
- The new entries' descriptions were read against their snippets (the image form's positivity
  hypotheses, SSVI's `θφ(1+ρ) < 4` as raw SVI's `b(1+ρ) < 2`). No overclaim.

### Upgrades executed

These were done in this wave; the per-item tags carry the declaration names.
- **One object per idea, built by the wave:**
  - independence from the past, which Girsanov and the jump-diffusion both use
    (`Probability/Dependence/IndepPast.lean`; `ExpMartingaleQBrownian` −330 lines);
  - the discrete market along a time change, with the binomial market an instance
    (`DiscreteMarket.ofTimeChange`);
  - the reflection factor of the barrier formulas (`barrierReflection`);
  - the compound sum (`compoundSum`);
  - the exponential law proved once (`ExpMin.lean`);
  - the Student-t law as `ProbabilityTheory.studentT`;
  - the in-measure lemmas of the Itô tower (`LocalisationInMeasure`);
  - the bundle `Market.IsFiniteComplete`.
- **Theorems the backlog asked for:**
  - Kelly optimality and the pricing-measure ≤ superhedging bound on `Market`;
  - key-rate durations summing to the effective duration on any tenor grid;
  - the par-strip bootstrap;
  - best affine prediction by orthogonality;
  - the compound-Poisson stop-loss recursion;
  - jump-diffusion independent increments;
  - binomial replication of path-dependent contracts;
  - the CRR put limit;
  - SSVI as raw SVI.
- **Added at merge, from the final gates:**
  - the SVI smile in a market: a market whose normalised calls are the smile satisfies
    Durrleman's condition (`durrleman_nonneg_of_isPricingMeasure`), and an SSVI slice satisfies
    `θφ(1+ρ) < 4` (`ssvi_tail_of_isPricingMeasure`), which ties both SVI entries to the trunk;
  - Kelly's inequality derived from the first-order condition (`kelly_foc` along
    `(0, y − f*)`), so the Kelly criterion stays on the tree;
  - the fourth-moment facts as `MemLp` API (`MemLp.integrable_pow_four`, `integrable_cube_mul`,
    `integrable_mul_cube`, `integrable_sq_mul_sq`, `integral_add_pow_four`), and four
    Mathlib-shaped private lemmas inlined.
- **The panel's merge fixes:**
  - The wave had added `OnePeriodVector.twoStep` beside `Market.twoStepFiltration`. Two
    reviewers found it independently. It is now one `Filtration.twoStep`, beside
    `Filtration.comp` in `Probability/Martingales/TimeChange.lean`.
  - Deriving `swap_preserves_invariant` from the constant-mean pool had added `0 < y` to an
    identity that holds for every `y`; the algebraic proof is back. The instance lemmas still
    tie the two pools together, and `hasDerivAt_swapOutput_zero` is derived.
  - The stop-loss lemmas took `AEMeasurable S` beside `Integrable S`; the redundant hypothesis
    is gone, and the lattice entry's snippet is stronger.
  - `parBootstrap_reprices` needs only its own denominator.
  - The `compoundSum_apply` docstring, a `↦`, and the LP contract's results list.
- **Integration fixes:**
  - Two workstreams had each proved `iIndepFun_of_indep_past`; the two copies are now one.
  - A golfed state-price proof met the new `vecMul` form of `portfolioCost`.
  - `KeyRateDuration`'s deprecated `if_pos`/`if_neg` and its two unused `DecidableEq`
    instances.

### Lens gradients

The panel: four independent read-only reviewers, two lenses each (1+2, 3+4 with the prose
pass, 5+6, 7+8), on the merged tree; adjudicated below.

1. **Inspired math.** Exemplar: `iIndepFun_of_indep_past`, one peel-the-maximum induction that
   replaced two bespoke independence arguments. Next: the superhedging joint as an equality in
   the complete case (backlog 1).
2. **Coherence.** Exemplar: `ProbabilityTheory.studentT` beside `gaussianReal` and
   `cauchyMeasure`, anchored by `studentT_one`. Next: the in-measure lemmas and independence
   from the past offered upstream (backlog 6, 9).
3. **Zero slop.** Exemplar: `price_pay_le_superhedgingPrice`, a three-step chain with an honest
   junk-value docstring. Next: the key-rate numéraire built from the nodes, not in a proof
   (backlog 8).
4. **Architecture.** Exemplar: `DiscreteMarket.ofTimeChange`, with `toMarket` and the binomial
   market as instances. Next: one binomial path representation; `wordWeight`/`wordSpot` beside
   `spotPath` is a third (backlog 10).
5. **First principles.** Exemplar: `mem_martingaleProbVectors`, whose deterministic start is
   exactly what it consumes. Next: the drift sums stated pathwise (backlog 5).
6. **Idiomatic register.** Exemplar: `hasIndepIncrements_of_indep_past`, a bare term with minimal
   classes. Next: the one-period names (backlog 11).
7. **Concept clarity.** Exemplar: `barrierReflection`, defined once and grep-confirmed in three
   formula families. Next: `compoundSum` where a reader would look (backlog 2).
8. **Elegance.** Most beautiful: `ssviVariance_eq_variance`, whose content is one radicand
   identity. Next: its proof as that identity alone, and the partial-time barrier forms through
   `barrierReflection` (backlog 3, 4).

Dissolved:
- "Rename the `Horizon` suffix": each suffixed object has an all-times twin with the bare name,
  and the docstrings now state the convention.
- "Remove `iSup_rpow_of_monotone`": it waits on upstream `ENNReal.rpow_iSup` (#315).
- "`exists_seq_tendsto_ae_comp` is a thin wrapper": it has five consumers.

### Ranked backlog

1. The superhedging joint as an equality in a complete finite market; `Market.IsFiniteComplete`
   beside the finite-market FTAP; `martingaleProbVectors` over any finite index (M). [#633]
2. `compoundSum` and its model-free facts in `Probability/Jumps/CompoundSum.lean` (S). [#634]
3. The partial-time barrier closed forms through `barrierReflection` (S). [#635]
4. `ssviVariance_eq_variance` as one radicand identity; the `ρ² = 1` slice in the docstring (S). [#636]
5. `tendsto_sum_mul_driftPath_sub` with its hypotheses at the fixed path (S). [#637]
6. `tendstoInMeasure_of_tendsto_integral_abs` over a normed group; both in-measure lemmas
   upstream (S). [#638]
7. `TenorGrid.piecewiseLinear`'s linearity between nodes as a theorem; shorter `rate_update` (S). [#639]
8. The key-rate deterministic numéraire defined from the nodes (S). [#640]
9. Independence from the past upstream; the Brownian conditional moments from Mathlib if it has
   them (S). [#641]
10. One binomial path representation: `wordWeight`/`wordSpot` and `spotPath` (M). [#642]
11. `isEMM_one_iff` named for what it relates; the three notions called EMM sorted in one
    sentence (S). [#643]

### Evidence

Each workstream finished on a green umbrella build (`MathFin MathFinExamples MathFinTest`) of its
own branch. Each tried every item with runner builds before filing it: an item became FILE only
after about two iterations failed to converge, and its half-done Lean was reverted. The merged
tree had one more umbrella build and the blueprint export on a runner, then the ledger sweep and
`build.yml`. Renamed declarations moved every caller, with no aliases; the release notes list
them.

## 2026-11-25 — corpus 917, modules 801 — the eleven-PR wave of 2026-11-25, brought onto the library's objects before it lands

Scope: pull requests #558 and #577–#586, merged on `integ/2026-11-25`. Eleven corpus entries
(906 → 917; full 866 → 871, reduced cores 22 → 28) and ten modules: the Ho–Lee bond price,
contango and basis convergence, the strict American put premium, the forward-start call, the
Balancer constant-mean pool and its priced position, Black–Scholes scaling invariance and the
Broadie–Glasserman–Kou discrete barrier shift, Jarrow–Yildirim and the average-strike
conditioning bound; the numéraire density as a Radon–Nikodym derivative; a security policy and
a pin-bump policy. This entry replaces the one #583 carried for its own two modules, whose
heading overstated the corpus by five.

### The standing first pass: prose against statement

- The contango module, its blueprint node and coverage said `BlackScholes/Dividends.lean`
  gives the same forward; it names none. The prose now says the commodity reading is the FX
  formula, not a separate derivation, that its continuous `δ` and `TheoryOfStorage`'s additive
  `Y` are unbridged, and (in the published `description`) that the curve is the
  deterministic-rate forward, not a futures price.
- The Balancer `description` claimed the reserves identity, which the snippet did not prove;
  the snippet now carries it as a conjunct. `price_constantMeanPayoff`'s docstring no longer
  reads as conditional: it is an unconditional unfolding.
- The American put docstring tied the general strict premium to `r > 0`; only the
  deep-in-the-money strictness needs it. A published `reference` field carried an authoring
  note about local files; removed.
- The forward-start prose called its payoff the first of its kind in the language (true today,
  aging tomorrow); dropped. The Risk column's pages are marked as Hull's citation, not checked.
- The average-strike docstring asserted, unreferenced, that the two-moment approximation is
  biased low; dropped. The Ho–Lee scope no longer says its kernel variance is proved there.

### Upgrades executed

- **One Brownian kernel.** Ho–Lee had re-defined the kernel `T − u`, its `L²` element and
  `T³/3` beside `VasicekZeroMeanReversionLimit`'s; it now uses those.
- **One total-variance step.** `bsV_eq_totalVarianceCall` is derived from the new
  `bsV_timeScale`; the Black caplet's `blackCaplet_sqrt_variance` moved from Jarrow–Yildirim
  to `Black76.lean`, beside `blackCaplet`.
- **Facts beside their object.** The six `ptDownOutCall` lemmas moved from the BGK module to
  `PartialTimeBarrierOption.lean`, where `ptDownOutCall` lives.
- **Lifts.** `scaled_increment_law` (the standardized Brownian increment is standard normal)
  in `BSCallHypFromBrownian.lean`, replacing a 15-line block of the forward-start proof; the
  American put module's thrice-written deep-in-the-money step and twice-written one-period
  continuation each became one lemma.
- **The Balancer entry** now proves the reserves identity its description claimed. Moving the
  blueprint tag onto that identity was tried and undone: the identity reaches no other node,
  and the island count rose to 1. The tag stays on `price_constantMeanPayoff` (backlog 11).
- `SECURITY.md` names every workflow that pushes with `contents: write` and says no workflow
  runs on `pull_request_target`; the pin-bump page drops a stale corpus size.

- **From the panel**: `blackCaplet_sqrt_variance` now consumes `bsd1_timeScale` and
  `bsd2_timeScale` (all three panellists who read `Black76.lean` flagged the hand re-derivation
  behind a `ring_nf`); the deep-in-the-money European closed form reuses the lifted one-period
  lemma instead of re-deriving it inline; the contango snippet states its sign facts at every
  maturity `T > 0`, as its description says, not at `T = 1`; the Balancer description says
  its price conjunct is the market's price unfolded; the contango description says the
  no-arbitrage derivation lives in `FxForwardParity.lean`; `JarrowYildirim.lean` writes `↦`.

### Lens gradients

The panel: four independent read-only reviewers, two lenses each (1+8, 2+6, 3+5, 4+7), on the
merged tree after the per-PR fixes; adjudicated below.

1. **Inspired math.** Exemplar: `expSum_pos_iff_of_root`, the single crossing of a signed
   exponential sum, which is what makes the Gaussian closed form of the conditioning bound
   possible. Thin: contango is `Real.exp` monotonicity, BGK proves a definition and a
   continuity limit, `ScalingInvariance`'s homogeneity trio is lemma-grade. Each is one corpus
   entry and says what it is. Next: the BGK shift compared with discrete monitoring on the
   binomial barrier market (backlog 7).
2. **Coherence.** Exemplar: Ho–Lee's `bondPrice_eq`, one `.trans` onto the Wiener moment lemma
   and the shared kernel; `jyZcCaplet_price` through `value_caplet_black76`. Next: the
   constant-product pool as an instance of the constant-mean one (backlog 1).
3. **Zero slop.** Exemplar: `bsV_eq_totalVarianceCall` in four lines through `bsV_timeScale`.
   Next: the American put's two near-mirror 35-line `calc` branches in
   `americanPrice_premium_mul_weight_le` (backlog 9).
4. **Architecture.** Exemplar: `ScalingInvariance` as its own module, consumed from
   `ModelFree/`, `Forwards/` and the barrier files. Next: `mf-bgk-discrete-barrier-shift`
   bundles five claims; split the `ptDownOutCall` facts from the BGK shift (backlog 8).
5. **First principles.** No `full` entry hides a reduced core; the JY `hZ` lognormal index is
   the real assumption and is disclosed; `hcond` is the defining property of a conditional
   mean, not the conclusion. Exemplar: `value_forwardStartCall`, a derivation through
   independence of the increment. Next: `hcond` from the Brownian model (backlog 6).
6. **Idiomatic register.** Exemplar: `ScalingInvariance`'s hypotheses, `c ≠ 0` or `0 < c`
   exactly where each is needed. Next: generic names in broad namespaces (`MathFin.expSum`,
   `condBoundCall`, JY's `quad2_nonneg`), the Balancer file's `variable` instances forcing nine
   `omit`s, `Real.one_le_exp` over `exp 0` rewriting (backlog 10).
7. **Concept clarity.** Exemplar: `mf-balancer-invariant`, description matching snippet clause
   by clause. Next: the JY and BGK descriptions run to 2–3k characters with a notation glossary
   in a published field; lead with the claim (backlog 8).
8. **Elegance.** Most beautiful: `americanPrice_premium_supermartingale`, three lines (the `max`
   adds a nonnegative term and the one-period price is affine). Ugliest: the 120-line double
   induction beside it, whose idea is that same step iterated along a path (backlog 9).

Dissolved: "eight contango corpus entries" and "`price_constantMeanPayoff` as an entry" (each is
one conjunct of one entry); "the numéraire lemmas have no consumer" (issue #323 asked for them
as named API for the change between two numéraire measures); retitling
`thm:futures-basis-convergence` (`F(T) → S` as time to maturity vanishes is the textbook basis
convergence on a deterministic curve, and the statement now says futures are not covered).

### Ranked backlog

1. Constant-product AMM as the `n = 2`, `w = 1/2` instance of the constant-mean pool:
   `swap_preserves_invariant`, `hasDerivAt_swapOutput_zero` derived, not re-proved (M). [done: `swapOut_two_eq_swapOutput`, `hasDerivAt_swapOutput_zero` from constant-mean; `swap_preserves_invariant` stays algebraic (true for every `y`)]
2. Jarrow–Yildirim's `quad2_nonneg`/`quad3_nonneg` stated through `Matrix.PosSemidef`, or one
   bridge to it, joining the PSD vocabulary of `Choice/Portfolio` (S). [done: `posSemidef_jyCorrMatrix`]
3. `condBoundCall_one_fixing_eq_marketPrice` restated as `S` times the price of
   `forwardStartCall 1 t T`, the payoff #585 reified, instead of a rescaled vanilla call (S). [done: `value_forwardStartCall_div` (forward-start call form)]
4. `fxForward` read as the carry forward (a carry name, or a stated generality), and a bridge
   from its continuous yield to `TheoryOfStorage`'s additive convenience yield (S–M). [done: `continuousYieldAmount`, `storageForward_continuousYield_iff`]
5. The GBM ratio decomposition `S_T = S_{t₁}·bsTerminal 1 r σ (T − t₁) …` as a lemma shared by
   the forward-start, chooser and vanilla path proofs; `pathAssets_nonneg`; the dividend-yield
   forward start (M). [done: `pathAssets_eq_mul_bsTerminal`, `value_forwardStartCall_div`]
6. The Jarrow–Yildirim SDE step (the real-rate drift shift and `V(0,T)`), `hcond` from the
   Brownian model for discrete fixings, the exact YoY caplet, a tightness statement for the
   conditioning bound (#583's backlog, carried) (L). [#605, #606]
7. The reflection step and `β = −ζ(1/2)/√(2π)` behind the BGK shift
   (`thm:barrier-lookback-closed-forms`), and its comparison with discrete monitoring on
   `Binomial/BarrierMarket` (L). [#52]
8. Split `mf-bgk-discrete-barrier-shift` into the `ptDownOutCall` image form and scaling and
   the BGK shift and limit; shorten the JY and BGK descriptions to claim first (S). [done: split: `mf-barrier-down-out-image-form` (reduced_core, scope disclosed)]
9. `americanPrice_premium_mul_weight_le` as one step lemma (weight `q` or `1 − q`) iterated on
   a path word; `BinomialNoArb.one_le_u`; a market-level deep-in-the-money corollary (M). [done: `BinomialNoArb.one_le_u`, the market corollary, `wordWeight` iteration]
10. Register pass: the Asian helpers into their own namespace, `integrable_exp_mul_gaussianPDFReal`
    via `integrable_exp_mul_gaussianReal`, the Balancer `variable` instances, the contango sign
    proofs as `mul_pos_iff_of_pos_right`/`mul_eq_zero_iff_right`, `tendsto_bgkDownBarrier` by
    `Tendsto` combinators, `absolutelyContinuous_numeraireMeasure` for the converse direction (S). [done: `MathFin.AsianAverageStrike`, `tendsto_bgkDownBarrier`]
11. A Balancer landmark with content that joins the tree: a priced statement at the pool's own
    spot price, through `eval_constantMeanPayoff_eq_reserves` and `price_constantMeanPayoff`,
    to carry the `thm:balancer-invariant` tag in place of the unfolding (S). [done: `price_constantMeanPayoff_eq_hodl`]

### Evidence

One read-only review per pull request against CLAUDE.md, all eight "ready after small fixes";
then the four-reviewer lens panel above on the fixed tree. A security pass over every diff: no
workflow, tool, script, lakefile or pin file touched; no `#eval`, `run_cmd`, `initialize`, IO,
custom syntax, `unsafe`, `extern` or new axiom in any added Lean or snippet; every added import
is MathFin or Mathlib; no bidirectional-text or zero-width characters. Ledger rows restored only
where the recorded input hash equals the merged tree's; the rest re-verified on runners. One
umbrella `lake build` and the blueprint export on a runner, then `build.yml`.

## 2026-11-19 — corpus 903, modules 790 — one concept, one object: the seven duplicates of the trunk table tied or removed

Scope: the branch `claude/inspiring-curie-fpg212`. It clears the `concept_duplicates` count of
`tools/verify/trunk.toml` (7 → 0) and gives `Contracts.bondPrice` a home in `Pricing/`. It adds no
corpus entry, and it does not touch the three counts main went red on in the 2026-11-18 merge
(`private_mathlib_shaped`, `corpus_off_blueprint`, `price_entries_off_trunk`), which are another
session's. Three read-only reviewers split the lenses: the first pass; lenses 2, 4 and 5; lenses
1, 3, 6, 7 and 8. Their findings were adjudicated against the code and the declaration index.

### The standing first pass: prose against statement

- The new `DeterministicMarket` docstring said "the library has one bond price". `HJMModel.bond`,
  `vasicekBondV` and the market's own assets are not tied to `Contracts.bondPrice`. It now says
  the bond price is canonical and names the three formulas tied to it.
- The coupon and key-rate ties were called "this bond price at a deterministic curve". They are sums
  of cash flows times it, the key-rate price with one curve per cash flow; the prose says so.
- Junk values: both ties hold for every yield or key rate, but the curve `(1 + y)^{−⌊u⌋}` is a
  discount curve only for `y > −1` (at `y = −1` it is a totalized `0` after date `0`). The docstrings keep
  the identity general and say when `P(0, tᵢ)` is a bond price.
- The survival tie wrote `ₜpₓ` with the age in the duration slot, and called a ratio a probability
  where `T < t` makes it exceed `1`. It now writes `_{T−t}p_t` for `T ≥ t`, and notes that the
  hypothesis on the law can be met only for `h₀ > 0`.
- `Caplet.lean` said, with no theorem, that the bond price at `0` is the zero curve. It is now
  `bondPrice_zero_eq_zeroCurve`.
- `SharpeFOCDerivation` lost its only pointer to what `V(w)` is when `varianceTwo` went; item 1 now
  names `portfolioVarTwo`. Its "`V > 0` regime" was a hypothesis `V ≠ 0`; it now says `V ≠ 0`.

### Upgrades executed

- **The bond price in the trunk's layer.** `Contracts.bondPrice`, `bondPrice_deflator_eq_priceAt`
  and the new `bondPrice_deterministic` (a deterministic discount `D` gives `P(t, T) = D T / D t`,
  one `condExp_const`) live in `Pricing/BondPrice.lean`, which `Caplet` imports. With them,
  `bondPrice_zero_eq_zeroCurve` and `Market.priceAt_pay_one_of_numeraire`: a deterministic numéraire
  `f` prices the unit payment at `t` at `f t / f T`.
- **`zcb` is the bond price under a constant rate** (`Rates.bondPrice_exp_eq_zcb`) and the market's
  price at `t` of one unit paid at `T` when the numéraire is `e^{rt}` (`Rates.priceAt_pay_eq_zcb`,
  an instance of the numéraire lemma). The definition stays the formula on real dates: the market
  clock is `ℝ≥0`, and seventeen corpus entries reach `zcb`, many on real dates (yields, durations,
  FRAs, DeFi accrual). Redefining it would narrow them, so `prices_off_trunk` does not move. The panel concurred; the `zcbFormula`
  rename of spec §9.2 waits for the rates limb.
- **Coupon bonds.** `bondPriceKeyRate_eq_sum_bondPrice`, and `bondPriceDisc_eq_sum_bondPrice` as its
  flat case, a term (`bondPriceKeyRate_const` is `rfl`).
- **Margrabe is the Black–Scholes call at zero rate** (`margrabePrice_eq_bsV`), with no hypotheses:
  at rate `0` the two `d₁` agree by `ring`. The first version carried two positivity hypotheses
  inherited from the Garman route; the panel caught them.
- **The SVI Black call is `bsV`** (`blackCall_eq_bsV`, formerly `blackCall_eq_bsSmile`). The old
  statement was definitionally this one through `bsSmile`, but the index reads uses from statements
  and proof terms, and `simp` had unfolded `bsV` out of both.
- **Survival.** `survivalFunction_div_eq_survivalProbability` (memorylessness: `S_τ(T) / S_τ(t)` is
  `e^{−h₀(T−t)}` for an exponential lifetime) and `survive_eq_survivalProbability` (`_{T−t}p_t`).
- **`varianceTwo` removed**, an alias of `portfolioVarTwo` with the weight first. Its lemmas are
  `portfolioVarTwo_eq_sum_mul_marginalVar` and `hasDerivAt_portfolioVarTwo`, in `portfolioVarTwo`'s
  argument order, the derivative stated of `portfolioVarTwo σ₁ σ₂ ρ` itself.

### Lens gradients

- **Inspired math.** Exemplar: `bondPrice_deterministic`, one fact that makes three formulas
  instances of the canonical price. Next: the key-rate price as a market price on one curve.
- **Coherence.** Exemplar: `Market.priceAt_pay_one_of_numeraire`, from `deflator_of_numeraire` and
  the bond price. Next: the constant-hazard ties through Mathlib's `expMeasure` (`HasLaw`) rather
  than a hand-written CDF.
- **Zero slop.** The instructive item is the Margrabe hypotheses: inherited from a general route,
  dead at the special point.
- **Architecture.** Exemplar: the bond price moved to the layer it belongs to, so the deterministic
  bond market reaches it without importing the Black-76 caplet stack. Next: the deterministic market's asset
  at every date as an instance of the numéraire lemma.
- **First principles.** Exemplar: `priceAt_pay_eq_zcb`, whose only hypothesis is the numéraire.
  Weak spot: the coupon ties quantify over a measure and information that a deterministic curve
  makes irrelevant.
- **Idiom.** The derivative is stated of the function, not of an eta-expanded lambda.
- **Concept clarity.** Next: `marginalVarOne`, `marginalVarTwo` are `marginalVariance` of `covTwo`;
  "Two" means "two assets" in one name of the file and "asset 2" in the next.
- **Beauty.** Next: `zcb_div_zcb`, the exponential ratio both the bond and the survival ties prove
  inline; `survivalProbability h` and `zcb h` are one function (#320).

### Ranked backlog

1. Re-found the rates limb (spec §5, §9): `zcb` renamed `zcbFormula`, the duration and convexity
   entries restated about the price, after the Phase 3 gate (L). [#593]
2. The key-rate price as a market price on one discount curve, under `Set.InjOn t s` (S–M). [done: `bondPriceKeyRate_eq_price_deterministicMarket`]
3. The constant-hazard survival ties stated with `HasLaw τ (expMeasure h₀) P` (S). [done: `measure_le_of_hasLaw_expMeasure`; the survival bridges take `HasLaw τ (expMeasure h₀)`]
4. One `(k, w)`-coordinates lemma, `ForwardSmile.blackForm_eq_bsV` for `0 < w`, with
   `bsCallSmile_eq` and `blackCall_eq_bsV` as instances (S). [#318]
5. `marginalVarOne`, `marginalVarTwo` as `marginalVariance` of `covTwo`, with a `[[duplicate]]` row
   for marginal variance (M). [done: `marginalVariance_covTwo_zero`, `_one`; `marginalVarOne`/`Two` removed]
6. `sharpeSqTwo_critical_iff_crossProduct_FOC` through `sharpeSqTwo_deriv_numerator_factored`
   instead of a forty-line ladder (S). [done: `sharpeSqTwo_critical_iff_crossProduct_FOC` through `HasDerivAt.unique`]
7. `zcb_div_zcb`, and `survivalProbability` routed through the one constant-rate discount (#320) (S). [#320]
8. The deterministic bond market's asset at every date from `Market.priceAt_pay_one_of_numeraire`
   (S); names `margrabe_eq_bsVGarman` → `margrabePrice_eq_bsVGarman`,
   `survive_eq_survivalFunction_ratio` → `survive_eq_survivalFunction_div` (S). [done: renames `margrabePrice_eq_bsVGarman`, `survive_eq_survivalFunction_div`]

### Evidence

`lake build` of every default target (9929 jobs) and `lake lint` green in the verify image; the
declaration index built on the branch: `concept_duplicates` 7 → 0, `chain_beyond_r3_permille`
288 → 286, both baselines lowered; no other count moved (main's three red counts are unchanged).
`decl_diff` against main: 13 added, 4 removed (the alias, its two lemmas under their old names,
`blackCall_eq_bsSmile`), 4 statements changed (the Sharpe theorems, `varianceTwo` → `portfolioVarTwo`).
The ledger rows whose inputs changed were re-verified through the lean-repl daemon. Renames for the
release notes: `SVI.blackCall_eq_bsSmile` → `SVI.blackCall_eq_bsV`, `varianceTwo_eq_w_dot_Sigma_w` →
`portfolioVarTwo_eq_sum_mul_marginalVar`, `hasDerivAt_varianceTwo` → `hasDerivAt_portfolioVarTwo`;
`varianceTwo` removed.

## 2026-11-18 — corpus 901, modules 788 — the November contributed wave, brought onto the library's objects before it lands

Scope: the branch `review/pr-wave-final`, twenty-one open pull requests reworked against the
practices before merging. Adam Kiezun's insurance, credibility, reserving, stopping, credit and
execution work (#510–#529), Yang Ye's (#502, #515, #523, #525) and #500. Two are held: #524, an
executable `Option ℚ` evaluator of the chain ladder, and #501, whose zero-maturity value at
`γ = 0` is `log(0/0)`. Three frontier nodes are delivered (`thm:life-insurance-epv`,
`thm:thiele-reserve`, `thm:buhlmann-credibility`), the life table enters `thm:survival-model`'s
core, and one landmark is new (`thm:mack-chain-ladder`). Three read-only reviewers split the lenses: the first pass;
lenses 2, 4 and 5; lenses 1, 3, 6, 7 and 8.

### The standing first pass: prose against statement

- No definite overclaim; seven borderline phrasings fixed:
  - `OvernightCompounding` and `CondExpCallJensen` stated an ordering of forward- and
    backward-looking caplets. Only `E[(E[X|m] − L)⁺] ≤ E[(X − L)⁺]` is proved; the identification of
    the fixed rate with a conditional expectation is not, and both docstrings now say so.
  - `StopLossGap` said the transform is convex and affine across the gap; the theorem is the
    identity at the two ends. The prose says that, and that expected shortfall is the objective's
    least value only for `α ∈ (0, 1)`.
  - `survive_lifeTable` lost its `0 < l x` hypothesis in the rework; its docstring now says the
    ratio is a probability when `l x > 0` and both sides are `0` otherwise.
  - The Thiele factor was "the probability of surviving" with no `μ ≥ 0`; it is a survival factor,
    a probability when `μ ≥ 0` (docstring, blueprint node, corpus description).
  - The discrete Almgren–Chriss rate "tends to `√(c/η)`": not proved, now said.
  - `sqrt_bsTerminal` gave "the mean of any square-root claim"; it is the square root of a
    lognormal terminal price.
  - `mf-smile-black-form-tail-iff`'s scope carried porting residue (issue numbers, heartbeat
    hygiene) into the published dataset; it now states the scope.
- Junk values, found in the rework rather than the panel: the reworked #501 had dropped the
  `γ ≠ 0` guard from `hestonA_at_zero`, making the terminal value at `γ = 0` hold through
  `log(0/0) = 0`. Reverted; the guard stays.

### Upgrades executed

- **Objects, not sequences.** `A = 1 − dä` was stated on a bare sequence with summability
  assumed. It is now on the survival function of a lifetime (`wholeLife_epv_eq`): term insurance is
  the CDS protection leg at recovery `0`, the pure endowment a payment on survival, and summability
  is derived. The life table goes through `Measure.ofWeights` (150 lines to 25); the two-life
  annuities through `Contract.value_payFlows_add_sub` (120 lines to 25 each); Thiele's factor is
  discount times conditional `hazardSurvival`.
- **The bridge that was there.** Bühlmann credibility is Sharpe's single-index model: the class
  mean is the factor, the shocks are uncorrelated (`covariance_latentMean_shock`), so
  `Var X̄ = a + s²/n` is `variance_singleIndex_portfolio` at equal weights, and the credibility
  premium is the least-squares predictor with slope `MathFin.beta` (`integral_sq_affine_le`,
  `Choice/Portfolio/RegressionBeta.lean`). The contributed 1340-line sum manipulation is gone; the
  layer edge Insurance → Choice is declared.
- **General statement, old one an instance.** The stop-loss recursion holds across any gap in the
  law (`integral_max_sub_add_of_gap`), the lattice and the Rockafellar–Uryasev increment are its
  instances; the derivable `S ≥ 0` hypothesis is gone. `gaussian_call_formula` sits in the Gaussian
  layer and `bachelier_call_formula` is its instance; the SVI tail condition is the Black-form
  tail condition at the SVI variance (one Mills argument, not two); the conditional-Jensen call
  bound serves calendar arbitrage and the overnight caplet.
- **A connection built, not waited for.** The chain ladder (#516, #517) was triangle algebra with
  nothing beneath it. Mack's model supplies it: with `E[C_{j+1} | 𝓕_j] = f_j C_j`, the prediction
  `(∏_{k∈[m,N)} f_k) C_m` of the ultimate is `E[C_N | 𝓕_m]`, the reference measure is an EMM of the
  prediction process (`IsMackRow.isEMM_chainPrediction`, so a pricing measure of the run-off
  market), and the claims development result has conditional mean zero (Merz–Wüthrich). The
  completion of a triangle is this prediction with the selected factors
  (`chainComplete_eq_chainPrediction`); `Insurance/ChainLadder.lean`.
- **Parallel objects removed.** `nelsonSiegelZeroRate` (the limit is now on `nssYield`), the
  `SqrtTerminal` module (into `Forward`), `thieleFactor` as a bare exponential, a forward-measure
  detour around a deterministic discount, about 40 public Almgren–Chriss helpers (the discrete
  optimum is the continuous path sampled at the discrete rate `cosh κ̃Δ = 1 + cΔ²/2η`), and about
  4000 lines of contributor tests in `MathFinTest/`, which holds the README and manual checks.
- **After the merge: the index ratchets, met by connections.** main's first `build` on the wave
  rose three index counts the branch never computed (they run only there). Each was met by a
  theorem rather than a baseline. Expected shortfall of an arithmetic loss is the least
  Rockafellar–Uryasev value on the lattice (`isLeast_rockafellarUryasev_lattice`), so the stop-loss
  recursion rests on `thm:rockafellar-uryasev`. Whole-life insurance and the annuity-due are limits
  of term `Contract.value`s (`tendsto_value_termInsurance`), which puts that entry on the trunk.
  The volatility swap is priced under the forward measure of a stochastic bank account
  (`volSwapValue_forwardMeasure`), a genuine use of `forwardMeasure_price`, unlike the
  deterministic-discount detour removed above. `chainPrediction` is a definition node
  (`def:chain-ladder-prediction`), the joint of the completion and Mack's model. The
  Nelson–Siegel–Svensson decay-limit entry left the corpus: it touched no node, and its theorem
  stays in the library. Of the six Mathlib-shaped private lemmas, two one-liners were inlined and
  four genuine facts (the product-weight sums of an iid vector, the scaled-profile boundary-value
  solution) became public under names that say what they prove.
- **The last two of the wave, landed on their neighbours.** #501's zero-maturity transform was a
  standalone module whose headline lemma dropped the `γ ≠ 0` guard through `log(0/0) = 0`. It
  now lives beside the vanishing vol-of-vol limit: `hestonTransform_terminal` needs only `γ ≠ 0`
  (it had carried the strip), and at maturity the transform is the moment of the point mass at
  the log-spot, the zero-variance member of the Black–Scholes family the limit reaches
  (`hestonTransform_terminal_eq_mgf_dirac`). #524's exact rational chain ladder sits in
  `ChainLadder.lean` with a soundness theorem that needs no hypothesis (a returned value is the
  real completion, and on unobserved cells Mack's prediction by the selected factors), and a
  worked reserve in `MathFinExamples` evaluates a triangle in the kernel and certifies it in `ℝ`.

### Lens gradients

- **Inspired math.** Exemplar: the discrete Almgren–Chriss path as the continuous one at a modified
  rate. Next: the cost as a quadratic form, so "cross terms vanish iff stationary" is polarisation.
- **Coherence.** Exemplar: `CondExpCallJensen`, an instance of `ConvexOn.map_condExp_le` consumed
  twice. Next: Bühlmann's draws as `Measure.pi` with the mixture as a kernel, replacing the
  hand-rolled `Fin n → Ξ` sums.
- **Zero slop.** The instructive item is the junk value the rework itself introduced at `γ = 0`.
- **Architecture.** Exemplar: the spread call reduced to the one-name Gaussian call through
  `hasLaw_linear_gaussianPair`. Next: `value_payFlows_add_sub` from `value_payFlows_sub`.
- **First principles.** Exemplar: the credibility factor as a regression slope. Next: the
  best-affine-predictor proof as Pythagoras (the residual is uncorrelated with `X`).
- **Idiom.** The surface is clean; the debt is structural: the Thiele proof is a 25-step have
  ladder, and `OvernightCompounding` computes a power integral inline.
- **Concept clarity.** Exemplar: the `StopLossGap` docstring after the first pass. Next:
  `SampledRules`' stopping proof inside a structure field.
- **Beauty.** Exemplar: `ae_notMem_Ioo_of_lattice`, one `filter_upwards`.

### Ranked backlog

1. The integrating-factor reserve lemma: `u ↦ (∫ᵤᵀ G + c)/exp(−∫₀ᵘ λ)` has derivative
   `λV − G/S`; Thiele becomes an instance (M). [done: `hasDerivAt_integral_div_exp_neg_integral`; `hasDerivAt_thieleReserve` its instance]
2. Bühlmann on `Measure.pi` and a kernel mixture, independence from Mathlib (M). [#601]
3. Thiele's discrete recursion (#84) on the same factor (S–M). [#84]
4. Mack's other two assumptions: independent accident years make `f̂_j` unbiased given the
   past columns, and the variance assumption gives the standard error of the reserve (M–L). [#594]
5. `∫₀ᵃ (u/L)^p = a^{p+1}/(L^p (p+1))` lifted out of `OvernightCompounding` (S). [done: `integral_div_rpow`]
6. `value_payFlows_add_sub` as a corollary of `value_payFlows_sub` (S). [done: `Contract.value_payFlows_add`]
7. A compound-Poisson instance of the stop-loss recursion with lattice severities, joining
   `CompoundPoissonCVaR` (S–M). [done: `integral_max_sub_succ_mul_compoundPoisson`, `isLeast_rockafellarUryasev_compoundPoisson_lattice`]
8. The best affine predictor by orthogonality (S); `SampledRules`' stopping set as a named lemma (S). [done: `integral_residual_mul_affine`, `integral_sq_affine_eq_add`; the stopping set is `le_sampleTimes_iff`]

### Evidence

`pytest` green on the branch apart from the blueprint export, the ledger rows and this review
before it was written; architecture and the host-side ratchets green (no layer violation, no
module unused). The index ratchets were not computed on the branch, and main went red on three of
them; see the last upgrade above.
`lean-build` of the default targets with the blueprint export and the runner ledger sweep of the
stale rows are the branch's CI; every reworked module and new corpus entry was built and checked
locally first, one Lean process at a time.

## 2026-11-16 — corpus 883, modules 779 — the RiO panel's second reading, and the wave it asked for

Scope: #506 and #507 (merged 2026-11-15 and 16) and the branch `feat/rio-panel-2` that answers the
panel. The panel: three read-only reviewers in the roles of a researcher in arbitrage theory, one
in volatility and numerics, and one in risk and decision theory. They read the program tree
regenerated from main's declaration index after #507, judged it fresh, then compared it with their
2026-11-15 reports item by item. That is lenses 1, 2, 4 and 7 read from outside; the first pass
and lenses 3, 5, 6 and 8 on the new Lean were the session's own.

### The standing first pass: prose against statement

- Titles that said more than the statement, fixed: `thm:vasicek-bond-pde` ("Vasicek bond price"
  for a check that `A·e^{−Br}` solves the PDE), `thm:fissler-ziegel` (one member of the family is
  proved strictly consistent, not the characterisation), `thm:euler-allocation` (Gaussian only),
  `thm:kelly-criterion` (a first-order condition), `thm:risk-parity-foc` (assumes the condition).
- A title that said less: `thm:dmw-ftap` read "(one asset)" for a theorem on a general probability
  space with no integrability hypothesis.
- `thm:cone-separation` claimed the simplex-separation root as its own; that root now sits under
  `thm:stiemke`, the node whose declaration the first FTAP actually uses.
- `thm:market-call-surface` said Dupire's equation is not restated for a market. It is now
  (`thm:market-dupire`), and the sentence is gone.
- New prose read against its statements: the market Carr–Madan node and entry say "expectation"
  for the left side (the payoff language has no general `f(S_T)` contract), a bounded strike
  range holding `S_T` almost surely, and zero rates; the market Dupire node says "under a
  probability measure" (no pricing measure is assumed) and that the price-surface derivatives are
  hypotheses; the Heston node now states the explicit transform and that no market link is proved.

### Upgrades executed

- **The fundamental theorems on the trunk.** The equivalent martingale measure, the FTAP family,
  the no-arbitrage core and the discrete and continuous market adapters moved from the
  `valuation/general` branch to the trunk (`docs/taxonomy.toml`); the branch is now *arbitrage
  pricing*: state prices, replication and completeness, superhedging duality, parity, the American
  price. The trees family no longer claims `Pricing.FTAP`. Three FTAP frontier nodes moved with
  them.
- **Distinct FTAP edges, from proofs.** `ftap_two` takes its measure from `ftap_discrete`, so the
  second theorem uses the first; `exists_pos_dual_of_disjoint_stdSimplex` is tagged as Stiemke's
  lemma, which the first theorem uses. The three FTAP nodes no longer share one use list.
- **Superhedging duality** sits in arbitrage pricing (its module is placed there), with the joint
  to risk kept: its proof runs through the coherent representation.
- **Carr–Madan as prices.** `Market.IsPricingMeasure.integral_eq_carrMadan`: under a pricing
  measure of a unit-numéraire market, `𝔼_Q[f(S_T)]` is cash, the forward and the market's put and
  call prices weighted by `f''`, by Fubini on a bounded strike range. The pathwise identity is
  drawn among the analysis tools (`tools/verify/tree_map.toml`); the variance-swap and semistatic
  frontier nodes now build on the market statement.
- **Dupire for a market.** `Market.dupire_price_europeanCall` states Dupire's formula for the
  market's own call prices when its asset is an Itô process under `Q`.
- **Heston.** `thm:heston-pde` now tags the explicit transform (`hestonTransform_pde`, no
  Riccati hypothesis) instead of the hypothesis version.
- **Joints.** Dropped `thm:log-utility-acceptance` (a counterexample) and
  `thm:hedged-position-risk` (a perfect hedge carries no risk); added `thm:esscher-premium-is-price`,
  a premium principle that is a price.
- **Tower summit.** A `[[tower]]` may name its summit; the American put tower shows
  `thm:bs-american-market`, not the dominance bound that won the old alphabetical tie-break.

### Panel verdicts, second reading

| | fixed since 11-15 | still standing |
|---|---|---|
| arbitrage | scoped FTAP and superhedging titles; the semimartingale gap labelled | EMM and FTAPs off the trunk, superhedging under risk, identical FTAP edges (all three addressed above); Black–Scholes formula nodes do not touch the EMM; tool vocabulary |
| volatility | American and smile branches; forwards split from rates; scoped Black–Scholes, Heston, Dupire, Black-76 titles | Heston, Dupire, Carr–Madan not markets (the last two addressed above); Heston CF, SABR, general Dupire, HJM drift on the frontier; no numerics |
| risk | scoped titles; Fissler–Ziegel proved; vocabulary of the risk branches | Kusuoka, Delbaen, von Neumann–Morgenstern, Lundberg, comonotonic additivity on the frontier; collective risk theory has no proved node; weak joints (addressed above) |

All three judged the tree clearly better and more honest than on 11-15; none judged it a map of
their whole field yet.

### Lens gradients

- **Inspired math.** Exemplar: the market Carr–Madan, a pathwise Taylor identity becoming a
  statement about prices by one Fubini. Next: the unbounded strip with the moment conditions of
  Carr and Lee.
- **Coherence.** Exemplar: the second FTAP now consumes the first. Next: the Black–Scholes call
  formula through `Market.price` under the Girsanov measure, so `thm:bs-call` uses the EMM.
- **Zero slop.** The integrability lemma that two files would have needed is one public lemma
  (`Market.IsPricingMeasure.integrable_asset`), not a second private copy.
- **Architecture.** The trunk now carries the theorems that justify it, not only its objects.
- **First principles.** Exemplar: Stiemke's lemma as the named engine of Harrison–Pliska.
- **Idiom.** The Fubini step is a local `have` generic in the strike measure and the option
  payoff, used for the put and the call alike.
- **Concept clarity.** Next: the reading guide and the vocabulary (socket, joint, island, R3), held
  until the organization pass is exhausted, by the maintainer's order.
- **Beauty.** Exemplar: the domination `|φ(y, K)| ≤ |y| + |K|` that serves both legs.

### Ranked backlog

1. A Heston market: the CIR variance process and the two-dimensional Itô formula, then the price
   of `e^{u log S_T}` as the transform (L; blocks `thm:heston-cf` as a market statement). [#99]
2. `thm:bs-call` and `thm:margrabe` through the EMM (M). [#291]
3. A first proved node in collective risk theory: premium principles or Cramér–Lundberg (M). [done: #459]
4. Kusuoka, Föllmer–Schied on `L^∞`, von Neumann–Morgenstern, Lundberg (L each). [#78]
5. Kyle's equilibrium (M). [#106]
6. Frontier nodes for numerics: Monte Carlo pricing, finite differences, Longstaff–Schwartz (S). [#614, #615, #616]
7. Comonotonic additivity and the distortion representation (M). [#75]
8. The reading guide, the vocabulary and the 3,798-theorems-versus-entries count (M; last). [done: `docs/glossary.md`, `docs/onboarding.md`]

### Evidence

- `lean-build.yml` run 43814075174 (with the blueprint export): the whole library green. The run
  before it caught a missing `Mathlib.MeasureTheory.Integral.Prod` import in
  `CarrMadanMarket.lean` and an `ω` binder that `open scoped ContDiff` makes a token.
- The ledger sweep re-verified the changed entries and `mf-carr-madan-market`.
- The first PR builds caught a long line and a chain-reach rise, 290 → 291 per mille. Nothing had
  moved away from the spine. Moving the FTAP family onto the trunk took 19 theorems that were
  within three hops out of the denominator. The fix was a real connection, not a baseline change:
  `premiumLeg_const_intensity` and `protectionLeg_const_intensity` state the time-varying CDS legs
  at constant intensity in terms of the risky annuity. This brings five constant-intensity Cox
  theorems within three hops (back to 290). `corpus_off_blueprint` fell 295 → 294.

## 2026-11-12 — corpus 870, modules 769 — one-asset DMW, Black–Scholes uniqueness and ten contributed modules, read before they land

Scope: the integration branch `v2/integrate-2026-11-12`. Two frontier nodes delivered:
`thm:dmw-ftap` for one asset (`Pricing/FTAP/OneAssetDMW.lean`, on a rewritten
`Pricing/FTAP/DensityPasting.lean`) and `thm:bs-arbitrage-free-price`
(`Probability/Brownian/MartingaleMeasureUniqueness.lean`, `Models/BlackScholes/PricingMeasureUnique.lean`).
Ten pull requests from Yang Ye (#432–#467): trinomial and willow lattices, piecewise-linear and
natural-spline interpolation, FX smile quotes, SABR chain-rule Greeks, the continuous lookback, the
shout floor, Marchenko–Pastur edges and concentrated-liquidity VaR. Each was reviewed against the
practices before merging, then joined to the library. 17 corpus entries are new and 9 changed.
Three read-only reviewers split the lenses: the first pass; lenses 2, 4 and 5; lenses 1, 3, 6, 7
and 8.

### The standing first pass: prose against statement

- Faithful as written: the DMW, uniqueness, willow, FX, lookback and quotes-to-market entries.
- Fixed:
  - `mf-natural-cubic-spline-exists-unique` and its module bullet said the glued spline is C². The
    theorem gives slope matching at the interior pillars (C¹) and natural ends; no glued function
    and no `ContDiff` statement. Its sibling entry already said so.
  - The shout-floor docstrings gave the market's ATM put price as `e^{qτ}·g(τ)`; it is `g(τ)`.
  - The uniqueness module title and the blueprint node said "every pricing measure"; the theorem
    covers densities square-integrable under the Girsanov measure (and bounded ones against μ), and
    only the restriction to 𝓕_T is identified. The README says the same now.
  - "Equivalent to μ" where `IsPricingMeasure` (mutual absolute continuity on 𝓕_T) is meant.
  - The trinomial node and entry said "if and only if" for the "if" direction; the converse is now
    in the snippet and named in the node.
  - `mf-piecewise-linear-arbitrage-free-interpolation` still said nothing extends the interpolant;
    it now points to `mf-quotes-market-realisation`.
  - The Marchenko–Pastur entry called a conjunction a bridge; the link that exists is the average
    eigenvalue theorem, and the entry says so.
  - README counts and the reduced-core list (21, with the interpolation and the lookback).
- The branch's own merge damage, found by the first pass: a union merge of `Blueprint.lean` brought
  back two tags the reviewers had deleted (`thm:willow-beta-identity`, `thm:cubic-spline-moments-unique`).
  Union resolution is now limited to append-only files.

### Upgrades executed

- **One pasting trunk.** `ConditionalOnePeriodFTAP` asked for a bounded one-period density with
  conditional mean one, which an arbitrage-free market need not have (`ΔS = ±1` with
  `P(ΔS = 1 | 𝓕ₜ) = u` forces `1/(2u)`). `IsOnePeriodDensity` is now the unnormalised weight in
  `[0, 1]` that is fair against bounded 𝓕ₜ-measurable variables under the already-weighted measure;
  `DensityPasting` composes such weights backwards and normalises once
  (`exists_isEMM_of_onePeriodDensities`). One asset supplies the weight
  (`OneAsset.exists_onePeriodDensity`), so `Market.noArbitrage_iff_exists_isPricingMeasure` holds
  with no hypothesis; for `d` assets the hypothesis is now true as stated.
- **Contributed modules joined to the trunk**: arbitrage-free quotes are a market's call prices
  (`exists_market_of_isArbitrageFreeQuotes`, via Roper's converse); the trinomial law is a pricing
  measure of the one-date market iff its exponential moment is `s₀e^{rτ}`; the willow chain has the
  second and cross moments of a pre-Brownian motion; the SABR Greeks are derivatives of the
  Black–Scholes market price; concentrated-liquidity VaR is the VaR of contract revaluations. The
  ratchet `price_entries_off_trunk` had risen by three; it is back at its baseline.
- **Duplicates folded**: the put price by parity from the call (the parallel physical-measure proof
  is gone); `bsd1_eq_dpl` once in `ForwardSmile` for three sites; the generic Black–Scholes chain
  rules moved to `HigherGreeks` with `DifferentiableAt` signatures.
- **Lifted**: the balancing weight (`balanceWeight`), `NoArbitrageAt.of_absolutelyContinuous`,
  `exists_memLp_two_withDensity_of_bdd` (a bounded density is an L² density against `Z·μ` when
  `1/Z` is integrable), `processToLpPredictable_neg`, `Measure.ofWeights_absolutelyContinuous_of_pos`.
- **Junk value**: the lookback bound held at `r = 0` only through a division by zero; it now assumes
  `r ≠ 0`.
- **Slop**: junk Mathlib imports in four contributed files, gratuitous `classical`, hand-rolled
  `obtain … rfl` and duplicated arguments in the DMW proof, essays in docstrings, four unguarded
  `#print axioms` lines.

### Lens gradients

- **Inspired math.** Exemplar: the one-asset DMW, which found that the textbook conditional step is
  stronger than the theorem and that unnormalised weights are the primitive. Next: the `d`-asset
  weight by measurable selection.
- **Coherence.** Exemplar: the uniqueness pair consumes martingale representation, the isometry and
  the π-λ theorem without reproving any of them. Next: `integral_mul_condExp` upstream.
- **Zero slop.** The merge-induced resurrection above is the instructive one: a gate-green tree that
  had silently undone a review.
- **Architecture.** Exemplar: the pasting trunk serving both theorems. Next: the knot-based APIs
  (spline, interpolant, quotes) share no interface.
- **First principles.** Exemplar: `lattice_variance_lower_bound` (`n(n−1) ≥ 0` gives the variance
  floor). Next: the trinomial step as an extension of the CRR tree.
- **Idiom.** The contributed files now follow the checklist; the willow marginals still reimplement
  `Matrix.vecMul` entrywise.
- **Concept clarity.** Exemplar: the DMW and uniqueness module docstrings (counterexample, plan,
  scope). Next: `bsV_eq_closedForm` keeps its name though the premise of its docstring was false.
- **Beauty.** Exemplar: `exists_integrable_equivalent`, the `exp(−Σ‖Sₙ‖)` reweighting.

### Ranked backlog

1. Bachelier and time-dependent volatility uniqueness from `trim_eq_of_martingale_withDensity` (S–M). [#624]
2. Black–Scholes uniqueness for an arbitrary equivalent density by localisation (L). [#607]
3. The `d`-asset conditional weight, closing `thm:dmw-ftap` in general (#313, L). [#313]
4. A shared knot interface for `CubicSplineSmile`, `CallPriceInterpolation` and the quotes (M). [#619]
5. Willow marginals through `Matrix.vecMul`; the willow step law as a bivariate normal coupling (M). [#620]
6. The Marchenko–Pastur law as a measure with the edges as its support (L), or a narrower module. [#608]
7. The v3 VaR at the empirical price quantile (full revaluation through monotonicity) (M). [#629]
8. A shout-option `Contract` on the American stopping substrate (L). [#609]
9. `bsV_eq_closedForm` retired in favour of unfolding `bsV` at its three users (S). [retired: `bsV_eq_closedForm` no longer exists]

### Evidence

`lake build` of every default target, the blueprint export and the declaration index green
(the umbrella build caught one name clash, `balance`, now `balanceWeight`); `pytest` green apart
from the ledger rows, which the runner sweep re-verified (388 entries whose imports changed);
ratchets lowered: chain beyond three hops 389 → 382 ‰, corpus off the blueprint 298 → 297; prices
off the trunk back at 171; two private Mathlib-shaped spline helpers made public under the names of
what they prove (`sum_fin_ite_const_le`, `sum_fin_ite_val_eq`).

### Backlog executed the next day (on main)

- **1, in part.** Bachelier: a pricing measure with a nonnegative density in `L²(μ)` agrees with
  `μ` on `𝓕_T` and prices the call at the Bachelier formula
  (`Bachelier.trim_eq_of_isPricingMeasure_withDensity`, `mf-bachelier-pricing-measure-unique-l2`).
  The increment of `S₀ + σW` is the Itô integral of the constant `σ`, now a lemma of its own
  (`exists_itoIntegral_const`, the case `f(t, x) = σx` of the time-dependent Itô formula).
  Time-dependent volatility is left: the clocked market's martingale property holds only at the
  clock times `v(t)`, and the uniqueness argument needs every time in `[0, v(T)]`. That needs a
  continuous clock with `v(0) = 0`, and the hypothesis is not decoration. A clock that jumps
  reveals a one-period lognormal step at once, and that step has many pricing measures.
- **9.** `bsV_eq_closedForm` is gone; its three users unfold `bsV`, and the prose that cited it
  says so.

## 2026-11-11 — corpus 849, modules 755 — the wave's sockets and connectors, read before they land

Scope: the v2 wave of 2026-11-11 (`v2/wave-2026-11-11`), seven workstreams integrated on one branch
and verified once. Sockets (a family theorem whose statement names `Market.IsPricingMeasure`) for
rates (`Models/Rates/DeterministicMarket.lean`), volatility
(`Models/LocalVol/TimeDependentVol.lean`), jumps (`Models/Jumps/Market.lean`), credit (`Models/Credit/MertonMarket.lean`) and insurance
(`Insurance/EsscherPremium.lean`, `Insurance/AnnuityValue.lean`), on the new one-date market
(`Pricing/OneDateMarket.lean`). Bachelier as a market. The American summit
(`Models/Binomial/AmericanSnell.lean`, `Models/BlackScholes/American/Summit.lean`). The model-free
connector (`Models/ModelFree/MarketCallPrice.lean`, `SVI/MarketRealisation.lean`). The choice
connectors: the market's stochastic discount factor, Hansen–Jagannathan and CAPM from it, and
marginal utility as an sdf (`Choice/Portfolio/MarketSDF.lean`,
`Choice/Portfolio/StochasticDiscountFactor.lean`, `Choice/Utility/MarketMarginalUtility.lean`).
`Probability/Laws/FiniteWeights.lean` replaces `finiteLaw`. 23 corpus entries are new or changed.
Three read-only reviewers split the lenses:
- the first pass;
- lenses 2, 4 and 5;
- lenses 1, 3, 6, 7 and 8.

### The standing first pass: prose against statement

- Twenty of the twenty-three entries are faithful, each with its narrowing in the same field
  (Bachelier "μ itself, not constructed", the binomial Snell envelope as the recursion only, the
  Esscher market "built to quote the loss at that premium").
- Fixed:
  - `Models/Jumps/Market.lean` said "the market is incomplete". It proves two pricing measures
    that price a call differently. It now says that, and that non-replicability is not proved. The
    tag "incomplete market" is gone.
  - `Choice/Utility/MarketMarginalUtility.lean` and the blueprint node
    `thm:log-optimal-numeraire-one-period` said "log-optimal" and "growth-optimal" for a portfolio
    that is only stationary, and called the sdf "the density of the pricing measure" (it is the
    density times the deflator). Both are fixed, and the entry `mf-log-optimal-sdf-numeraire` is
    renamed "A Stationary Log Portfolio Is the Numéraire Portfolio in One Period".
  - `mf-expected-utility-integral` and its blueprint node claimed the finite-measure form, which
    is a sibling lemma the snippet does not state.
  - `mf-deterministic-bond-market-pricing-measure` said "under any probability measure" where the
    snippet states the reference measure. The post-maturity convention moved to the scope.
  - `mf-bond-portfolio-value-is-market-price` and `DeterministicMarket.lean` said the immunization
    and key-rate formulas "are values of contracts". It is the values they differentiate.
  - The four market-sdf entries did not say that the numéraire at time 0 is a constant (a
    hypothesis of every statement).
  - `mf-esscher-premium-is-price` now marks `esscherPremium_eq_price` as not restated.
- Disclosed: the one-date socket is a calibration. A measure prices `Market.oneDate` when it is
  equivalent to `P` and has mean `s₀ e^{rτ}`, so a family's socket there certifies routing, and
  its content is the family's own moment identity. `OneDateMarket.lean` now says so.

### Upgrades executed

- `Market.deflator_of_numeraire` and `Market.deflator_of_numeraire_exp` (`Pricing/Market.lean`):
  a deterministic numéraire gives the deflator `f 0 / f t`, and `e^{rt}` gives `e^{−rt}`. The
  Black–Scholes, clocked-volatility and one-date `deflator_*` lemmas are now one-line instances
  instead of three copies of the same `simp only` chain.
- The four `try` hedges in `OneDateMarket.lean` and `EsscherPremium.lean` are gone. The two
  filtration lemmas rewrite through `twoStepFiltration_zero`/`_one`, and the `smul_eq_mul` step
  fires because Mathlib's `integral_tilted` and `integrable_tilted_iff` are stated with `•`.
- The prose corrections above.

### Lens gradients

- **Inspired math.** The exemplar is `esscherPremium_eq_price` with
  `isPricingMeasure_insuredMarket_tilted`: the actuary's premium principle is the arbitrage price
  under Mathlib's `tilted`. The next upgrade is to state the Esscher result without the
  calibration: the Esscher parameter is the only tilt for which the quote equals the premium.
- **Coherence.** The exemplar is `Measure.integral_ofWeights`: one lemma under expected utility,
  state-price pricing and discrete VaR, built from Mathlib's `integral_finsetSum_measure` and
  `sum_smul_dirac`. The next upgrade is the bridge `M.sdf Q T ω = M.statePrice Q T ω / P{ω}` on
  a finite space, so the finite Euler equation and the market sdf are one statement.
- **Zero slop.** The exemplar is the four-line core of
  `capm_from_market_equilibrium_of_discountFactor`. The next upgrade covers the hand-rolled
  `MemLp`/integrability blocks in `BachelierMarket.lean` and `MertonMarket.lean`, replaced by
  `MemLp.pos_part` and one `IsPricingMeasure.integrable_deflator_mul_of_le`.
- **Architectural ingenuity.** The exemplar is `Market.oneDate`: the two-step filtration
  time-changed along the date, so one construction serves jumps and insurance. The next upgrade is
  one constructor for a market with a deterministic numéraire, of which `oneDate`,
  `Bachelier.market`, `TimeDepVol.market` and `deterministicMarket` are instances.
- **First principles.** The exemplar is `JumpDiffusion.exists_isPricingMeasure_price_call_ne`:
  two pricing measures, two prices, a socket doing real work. The next upgrade is to say which of
  the sockets are calibrations in every family docstring, not only in `OneDateMarket.lean`.
- **Idiomatic register.** The exemplar is `IsNormalizedCallPrice.of_eqOn` in structure-`where`
  form. The next upgrade is a `variable` bundle (or a structure) for the finite one-period market
  hypotheses that `MarketMarginalUtility.lean` repeats verbatim in four theorems, and
  `abbrev Market.terminalPayoff`.
- **Concept clarity.** The exemplar is the `OneDateMarket.lean` header (what the model is, what
  the initial price is, what the families supply). The next upgrade is to split `merton_market`,
  a four-conjunct statement with the Girsanov measure retyped twenty times, into named lemmas.
- **Beautiful math.** The exemplar is `expectedUtility_univ_real_eq_integral`: expected utility
  is the integral against the lottery, from one two-line lemma. The next upgrade is
  `price_oneDate_eq_integral` for any payoff of the asset at `τ`, so that the call and the claim
  on the asset are instances.

### Ranked backlog

1. A deterministic-numéraire `Market` constructor, with `price_pay_of_numeraire`. The Merton and
   `bondPortfolioValue_eq_price` deflator blocks and `price_europeanCall_of_numeraire_eq_one` (a
   pricing fact in `ModelFree/`) become instances. [done: `Market.lean`]
2. Move `stronglyMeasurable_deflator` to `Pricing/Market.lean`. Lift the `trim`/`withDensity` core
   shared by `IsPricingMeasure.integral_rnDeriv_mul` (`MarketSDF.lean`) and
   `exists_isEquivProbMeasure_trim_eq` (`EquivMeasure.lean`) into one change-of-measure lemma on a
   sub-σ-algebra. [done: `Market.lean`]
3. The bridge from `sdf` to `statePrice` on a finite space (Coherence above). [done: `MarketSDF.lean`]
4. Integrability: `MemLp.pos_part` in Bachelier and one integrability lemma under a pricing
   measure for Merton and the market sdf. [done: `Market.IsPricingMeasure.integrable_deflator_mul_asset`]
5. Split `merton_market` and `bondPortfolioValue_eq_price` into named lemmas. [done: `merton_market` from four named lemmas]
6. The hypothesis bundle in `MarketMarginalUtility.lean`. [done: `Market.IsFiniteComplete`]
7. Move Glosten–Milgrom's hand-written finite law onto `Measure.ofWeights`. Decide whether
   `ofWeights` stays in Mathlib's `MeasureTheory.Measure` namespace or is upstreamed. [done: `gmMeasure` as `Measure.ofWeights`]
8. Fold `americanPrice_eq_snellEnvelope`, a one-line wrapper, into the binomial Snell module, and
   rename `American/Summit.lean` after its content. [done: `Summit.lean`]
9. The Esscher uniqueness statement (Inspired math above). [done: `esscherPremium_strictMonoOn`, `isPricingMeasure_insuredMarket_tilted_iff_eq`]

### Backlog executed the same day (`v2/backlog-2026-11-11`)

1. In part. `Market.price_eq_value_of_numeraire`, and `price_europeanCall_of_numeraire_eq_one`
   moved to `Pricing/Market.lean`; the bond-portfolio deflator blocks are instances. The
   constructor was not built: redefining the four markets through it would rewrite their `simp`
   proofs for no new content. Merton's numéraire is not deterministic, so its blocks stay.
2. Done. `trim_withDensity_rnDeriv_trim` and `integral_rnDeriv_trim_mul` (`EquivMeasure.lean`)
   carry both former proofs; `stronglyMeasurable_deflator` is in `Pricing/Market.lean`.
3. Done. `IsPricingMeasure.sdf_mul_real_singleton`: `sdf(ω) P{ω}` is the state price of `ω`
   when the singletons are known at `T`.
4. In part. Bachelier's `MemLp` block is one `MemLp.pos_part` chain; Merton's integrability is
   not lifted.
5. Done. `merton_market` and `bondPortfolioValue_eq_price` are conjunctions of named lemmas.
6. Done as a `variable` block. The `terminalPayoff` abbreviation was tried and dropped: goals in
   the abbreviation and lemmas in `portfolioPayoff` defeat `rw`.
7. Done. Glosten–Milgrom's law is `Measure.ofWeights`; `ofWeights` stays in Mathlib's namespace
   as an upstream candidate.
8. Done. `americanPrice_eq_snellEnvelope` is in `Binomial/American.lean` (the Snell module would
   close an import cycle); `Summit.lean` is `AmericanPutMarketBound.lean`.
9. In part. `isPricingMeasure_insuredMarket_tilted_iff`: for `T > 0`, the `h'`-tilt prices the
   insured market exactly when its premium is the quote, from the new converse
   `Market.integral_eq_of_isPricingMeasure_oneDate`. Uniqueness of the parameter (strict
   monotonicity of the premium) is not proved.
## 2026-11-10 — corpus 830, modules 740 — the layered-trunk merge into the SABR chain-rule-Greeks branch

Scope: no new proof content. The branch merged the layered trunk (origin/main through the
tree-measured phase) and was brought back over the corpus gates: the module re-placed in its
layer, the audit pin and formalization counts regenerated, docstrings re-checked against the doc
standard, the benchmark citations resolved against the shared bibliography. The corpus delta past
the last recorded review (817) is the trunk's own 13 entries, covered by the trunk-side reviews of
2026-11-08; the branch's own two entries below were re-read now.

### The standing first pass: prose against statement

- `mf-sabr-atm-chain-rule-delta`: the description says the chain rule for the Black call with
  strike held fixed at `K = f`, spot `s` moving, the vol re-marked along the ATM backbone —
  exactly the theorem's `HasDerivAt (fun s ↦ bsV f 0 (sabrATMVol s ⋯) s tex)` shape, and the
  module docstring explicitly says this is *not* eq. 3.9 restricted to `K = f` (the fixed-strike
  smile derivative, whose `0/0` ATM factor is unresolved here). Faithful.
- `mf-sabr-atm-chain-rule-vega`: the companion statement differentiated in `α` only; the
  description matches, including the note that this case needs no smile-fix.
- The module docstring's "what is proved and what is not" block stays the exemplar for scope
  disclosure: it names the unresolved `x''(0)`, names the convention the proved quantity follows,
  and says the two curves' slopes differ at `f = K`.

### Evidence

pytest green after the merge except the ledger rows the trunk move restaled (a stale-scope sweep
re-verifies them on this branch); doc-standard hard problems zero; ratchet at baseline; audit pin
regenerated (990 guards).

## 2026-11-08 — corpus 817, modules 731 — the one trunk, phases 0–2, read before it lands

Scope: the one-trunk work since the RiO review (#450, #451; branches `v2/phase2c-horizon` and
`v2/phase2d-black-scholes`). `Market`, `IsPricingMeasure` (equivalence on `𝓕 T` only), `price` and
`priceAt` (`Pricing/Market.lean`) and `Contract.value` with a stochastic deflator
(`Pricing/Value.lean`). Three markets on it: discrete (`Pricing/DiscreteMarket.lean`), binomial
(`Models/Binomial/Market.lean`) and Black–Scholes (`Models/BlackScholes/Market.lean`).
Superreplication and gains-neutral measures as instances (`Pricing/MarketCompleteness.lean`). The
support lemmas: `MartingaleFrozen`, `EquivMeasure`'s gluing lemma and `TimeChange`. 13 new corpus
entries. Three read-only reviewers split the lenses:
- the first pass with lenses 7 and 8;
- lenses 2, 3 and 6;
- lenses 1, 4 and 5.

### The standing first pass: prose against statement

- Twelve of the thirteen entries are faithful. `gir-market-superreplication-price` named
  `M.price Q c` for a merely gains-neutral `Q`, never shown to be a pricing measure of `M`, and
  its description said the market was "driven additively by `B`", which nothing in the statement
  says. This is the junk-value case. The theorem now takes `M.𝓕 T = 𝓕ᴮ_T` and
  `M.IsPricingMeasure T μ` and concludes `M.IsPricingMeasure T Q` alongside the price identity. The
  description says when the hypothesis on `μ` holds (a Bachelier-type market, not Black–Scholes
  under its physical measure).
- Module docstrings, fixed:
  - `Market.lean` said the change of numéraire "changes the pricing measure". Only the price
    identity is proved, and the docstring now says that `Q^N` being a pricing measure is not proved.
  - `Market.lean` said "a measure equivalent everywhere is one" without the martingale condition.
  - `Binomial/Market.lean` led with "the pricing measure is unique". It is unique on the
    information at the horizon, and the lead now says so.
  - `MarketCompleteness.lean` did not say that "the market driven by `B`" means its deflated asset
    is `B`.
  - `BlackScholes/Market.lean` said "Brownian motion" for a pre-Brownian hypothesis.
  - `DiscreteMarket.lean` had a stale title and a stale model count.
  - `Value.lean` said `value` integrates against "a pricing measure".
- Dissolved on adjudication:
  - the claim that the Black–Scholes pricing-measure proof re-proves `deflated_market` inline (it
    rewrites through `B^θ`, not `W`, so the lemma does not apply);
  - the claim that `Value.lean`'s "no theorem here needs `IsEMM`" is stale (it is true);
  - the claim that the Wald exponential has no Itô representation in the library
    (`discountedGBM_eq_itoIntegral`, `constDoleans_sub_one_mem_range`).

### Upgrades executed

- `Market.superReplicationPrice_eq_price` restated with a genuine pricing measure (above).
- `Martingale.congr_ae` (an adapted a.e.-equal copy of a martingale is one) and
  `Market.stronglyAdapted_deflated`, the general lemmas the Black–Scholes pricing measure needed, in
  the general modules rather than inline.
- The seven docstring corrections above.

### Lens gradients

- **Inspired math.** The exemplar is `IsPricingMeasure` with `of_trim_eq` and
  `exists_isEquivProbMeasure`: the Föllmer–Schied notion, lossless in both directions. The next
  upgrade is a trunk notion of strategy: `Market.NoArbitrage` with self-financing gains, so that the
  three FTAPs are statements about a `Market` rather than about raw data or a parameter condition.
- **Coherence.** The exemplar is `martingale_min_iff` and `martingale_min_of_trim_eq`, general and
  consumed thinly by the trunk. The next upgrade is one `Martingale.integral_eq` lemma replacing the
  seven re-derivations of "a martingale has constant mean".
- **Zero slop.** The exemplar is the module docstrings' "not proved" disclosures. The next upgrade
  covers the duplicated blocks in `Binomial/Market.lean` (the two `map_flips` bullets, the two
  `crrUpProb` casts, `hgrid`/`hfl`), the duplicated `hS₀` shim and the `D ≡ 1` residue in
  `DiscreteMarket.lean`.
- **Architectural ingenuity.** The exemplar is the time change: the discrete market and the tree
  become markets on `ℝ≥0` by `Filtration.comp`. The next upgrade is one `Market.ofDiscrete` along a
  step `h` with a numéraire, of which `toMarket` and `Binomial.market` are both instances.
- **First principles.** The exemplar is the Black–Scholes uniqueness gap, stated as a gap. The next
  upgrade is `exists_isEquivProbMeasure` under `SigmaFinite (P.trim _)` instead of
  `IsFiniteMeasure P`.
- **Idiomatic register.** The exemplar is `exists_isEquivProbMeasure` as a two-line term. The next
  upgrade is `trim_eq_trim_iff` and `isProbabilityMeasure_of_trim_eq`, replacing four hand-rolled
  `Measure.ext`/`trim_measurableSet_eq` blocks.
- **Concept clarity.** The exemplar is `Market.lean`'s header (definition, then why `𝓕 T`, then
  when the total `price` is a price). The next upgrade is to state `IsPricingMeasure` through
  `IsEquivProbMeasure (P.trim _) (Q.trim _)` instead of a bare `ac`/`ac'` pair.
- **Beautiful math.** The exemplar is the gluing lemma `exists_isEquivProbMeasure_trim_eq` (weight
  `P` by `d(Q|m)/d(P|m)`). The next upgrade is the Black–Scholes keystone itself (#452).

### Ranked backlog

1. Black–Scholes uniqueness among pricing measures with an `L²` density (#452, phase 3). The route:
   under the Girsanov measure the deflated asset is `S₀ + ∫ σS dB^θ`
   (`discountedGBM_eq_itoIntegral`), so `pricesGainsAtZero_of_density` applies. The filtration of
   `B^θ` against that of `W` is the step to settle first. The `L¹`-density case (localisation) stays
   on the frontier. [done: `trim_eq_of_isPricingMeasure_withDensity`]
2. `Market.NoArbitrage` / self-financing gains on the trunk, with the discrete, binomial and
   Black–Scholes FTAPs as instances (phase 5 or after v2.0). [done: `Market.NoArbitrage` with the finite-space and one-asset FTAPs (`MarketFTAP.lean`)]
3. `Market.ofDiscrete` with a numéraire and a step, merging `toMarket` and `Binomial.market`. This
   also opens the short-rate limb: `Market.ofShortRate`, with `value_fixedFlows_vasicek`/`hullWhite`/
   `gsr` restated as `Market.price` (#453). [#598]
4. `bondPrice` and `HasBondPrice` over a `Market` (`priceAt`), retiring the parallel definition
   (#453). [done: `BondPrice.lean`]
5. `Martingale.integral_eq`, `trim_eq_trim_iff` and `isProbabilityMeasure_of_trim_eq`, with their
   callers migrated, as upstream candidates alongside `Martingale.congr_ae`, `Filtration.comp` /
   `Martingale.comp` / `of_comp` and `exists_isEquivProbMeasure_trim_eq`. [retired: the three lemmas were never kept; `Market.IsPricingMeasure.of_trim_eq` covers the use]
6. Binomial API friction: derive `hq` from `hna`, use `T = N h` as the single grid hypothesis, and
   derive `BinomialNoArb` from `hQ` in `trim_eq_of_isPricingMeasure`. [#630]
7. `Market.superPrice` over the set of pricing measures, convex and monotone, for the risk,
   insurance and incomplete jump limbs (#454, #456, #459). [#599]
8. A Mathlib-style home for `integral_abs_sum_le_of_identDistrib` (`Risk/CompoundPoissonCVaR.lean`),
   and the mean-based domination there in place of `2ⁿ`.


Entries from 2026-06-29 (corpus 302, the whole-repo review below) onward use the **upgrade-driven model**
(per-lens exemplar → next upgrade; upgrades executed + ranked backlog). Earlier entries are historical
PASS / PASS-WITH-NOTES verdicts, kept as-is — the transition itself was an upgrade to lens 4 (the review
should *generate work*, not certify "OK"). [done: `Probability/Analysis/IdentDistribSum.lean`, mean-based domination]

## 2026-11-08 — corpus 817, modules 732 — the trunk's first sockets and three dualities, read before they land

Scope: `v2/choice-utility-state-prices` (#473) with what it brings from main besides #474,
whose trunk review is recorded separately (#470, #472, #476). There are 13 new corpus entries,
from these modules:
- `Pricing/Market` (the price system and the `𝓕 T` glue);
- `Models/Binomial/Market` (the first socket);
- `Pricing/DiscreteMarket`;
- `Choice/Utility/StatePriceDensity` and `Choice/Performance/KellyNumeraire`;
- `Risk/Superhedging`, `Risk/ExpectedShortfall` (the representing set);
- `Risk/CompoundPoissonCVaR`.

Two read-only reviewers split the lenses: the first pass with lenses 1–4, and lenses 5–8.

### The standing first pass: prose against statement

Five overclaims, all fixed in this session:
- **The ES representing-set description** went on, "hence ES is the least upper bound, and by
  the dual representation the greatest value, of ∑ qᵢLᵢ over that set". The entry proves the set
  equality only. The least-upper-bound is `expectedShortfall_isLUB_representingSet`, and the
  greatest value is taken over densities, not over these `q`. The sentence is gone.
- **`Pricing/Market`, two dropped qualifiers.**
  - "the price in every market with that law" holds for fixed-dated contracts, which is all
    that `price_eq_of_map_observation_eq` covers.
  - "nothing is lost" needs a finite `P` (`exists_isEquivProbMeasure`).
- **Superhedging.** "implied by no arbitrage" needs at least one state (`[NeZero N]`).
- **Kelly.**
  - The fair-odds probabilities were called "unique", which is not stated.
  - The module said the state-price form is absent, but `kelly_statePrices` in the same file
    gives it.

The panel also showed that one *scope disclosure* overstated an obstruction. `Superhedging` and
two corpus scopes said the duality needs Minkowski–Weyl, which is absent from the pinned
Mathlib. It does not:
- `coherentRisk_isLUB` (`AcceptanceSet`) represents any coherent risk measure on a finite space
  with no closedness hypothesis;
- the superhedging price is coherent;
- its representing set is exactly the martingale probability vectors. Trading gains `±θ·z` are
  acceptable at zero cost, and a vector that prices them at zero is a martingale vector.

The duality is being proved on `v2/risk-convex` (backlog 1), and that branch corrects the
prose.

### Lenses: exemplar, then the next upgrade

1. **Inspired math.**
   - Exemplar: the horizon glue (`IsPricingMeasure` on `𝓕 T`, with `exists_isEquivProbMeasure`
     and `of_trim_eq`).
   - Next: the superhedging duality above, and the ES representing set stated in Mathlib's
     measure order (`Q ≤ (1−α)⁻¹ • P`), which removes the null-atom case split and extends
     beyond finite spaces.
2. **Coherence.**
   - Exemplar: `Binomial/Market` consumes `Martingale.comp`/`of_comp`, `Filtration.comp` and
     `integral_trim`.
   - Next: `portfolioPayoff`, `SuperReplicates` and their `Finset.sum_comm` swaps are
     `Matrix.vecMul` (`add_vecMul`, `smul_vecMul`, `dotProduct_vecMul`).
   - `integral_abs_sum_le_of_identDistrib` is a general `IdentDistrib` lemma living in a Risk
     file, and belongs in `Probability/`.
3. **Zero slop.**
   - Exemplar: `Superhedging`, where every lemma is used and the `sInf` junk value is documented.
   - Next:
     - `DiscreteMarket` repeats the floor-zero block in `value_forward` and
       `value_europeanCall_sub_put` (extract `discreteAssets_zero`);
     - `∑ i ∈ range (N ω), X i ω` is written ten times across `CompoundPoissonCVaR` and
       `CompoundPoissonMGF` (a shared `compoundSum`).
4. **Architecture (one trunk).**
   - Exemplar: `DiscreteMarket.toMarket` with `isPricingMeasure_toMarket_iff`, which puts the
     finite FTAP on the trunk.
   - Next:
     - `Binomial.market` builds a floor filtration by hand and repeats the `of_comp` argument.
       Generalise `toMarket` to a step and a numéraire, and make the binomial market an instance.
     - The superhedging and utility theorems never mention `Market`. Their joints are
       `M.price Q c ≤ superhedgingPrice` (risk × valuation) and "marginal utility weighted by
       `p` is a pricing measure of a finite `Market`" (choice × valuation). These are K4 and K6
       of the chain design.
5. **First principles.**
   - Exemplar: `StatePriceDensity` derives the density from Fermat on the budget set, with no
     concavity assumed.
   - Next: `kelly_statePrices` takes the Kelly first-order condition from the closed form.
     Proving `f*` is a local maximum of `portfolioUtility` for `log` (concavity) and calling
     `exists_statePrices_of_isLocalMaxOn` makes it "the log-optimal portfolio has density p/W",
     which is K5.
6. **Idiomatic register.**
   - Exemplar: the `SuperReplicates.mono/add_const/smul/add` dot-notation transport lemmas.
   - Next, the golf list from the panel:
     - `hθ ▸ hw₀.ne'` for a nested `have`;
     - `fin_cases ω <;> simp` for three duplicated blocks;
     - a redundant `ℝ` cast;
     - shadowed anonymous `have`s in `of_trim_eq`;
     - `portfolioCost` as `portfolioPayoff` of one row.
7. **Concept clarity.**
   - Exemplar: `Superhedging`'s docstring opens with its non-claims.
   - Next: the hypothesis list of the stationary-point theorems is retyped four times. An
     `IsStationary` bundle would show that the first-order condition is the only analytic
     input.
8. **Elegance.**
   - Exemplar: each coherence axiom of the superhedging price is a two-line transport through
     `sInf`.
   - Next:
     - cash invariance, homogeneity and subadditivity are one fact (`SuperReplicates` is a convex
       cone in `(Y, x, θ)`), not three `linarith` proofs;
     - in `exists_eq_smul_of_forall_cost_eq_zero`, "a functional vanishing on `ker cost` is a
       multiple of `cost`" is `LinearMap.ker_le_ker_iff`-shaped, with no `k₀`.

### Ranked backlog

1. **The superhedging duality** by `coherentRisk_isLUB`, with no Minkowski–Weyl (on
   `v2/risk-convex`). [done: `AcceptanceSet.lean`]
2. **The joints over `Market`**:
   - K4: utility state prices are a pricing measure;
   - K6: price ≤ superhedging price;
   - K5: Kelly from optimality, not from the formula.

   These are the choice workstream after #473. [done: `kelly_log_le`, `kelly_isLocalMaxOn`, `Market.IsPricingMeasure.price_pay_le_superhedgingPrice`]
3. **One discrete market.** `Binomial.market` as an instance of a stepped `toMarket`. [done: `DiscreteMarket.ofTimeChange`; `Binomial.market` an instance]
4. **`Matrix.vecMul`** for portfolio payoffs, and `compoundSum`. [#625]
5. **The golf list** of lens 6, and the `discreteAssets_zero` extraction. [done: `discreteAssets_zero`, `kellyWeights_pos`, the golf list]

## 2026-11-07 — corpus 804, modules 725 — the RiO foundations, read before they land

Scope: `feat/rio-foundations`, six foundation results, each with a seam into the contracts
layer:
- the Black–Scholes delta hedge (`DeltaHedge`, `BlackScholesHedge`, `BlackScholesSelfFinancing`);
- the SDE Picard fixed point on every horizon (`SDEExistence`, `BlackScholesSDE`);
- Girsanov for the filtration with bounded predictable `θ` (`GirsanovFiltered`,
  `BlackScholesPhysical`);
- stochastic Fubini and the HJM bundle (`StochasticFubini`, `StochasticFubiniIto`, `HJM`,
  `HJMBond`);
- the Dalang–Morton–Willinger reduction and pasting (`NoArbitrageLocal`, `DensityPasting`,
  `DalangMortonWillinger`, `DiscreteMarket`);
- the Itô product rule (`ItoProductRule`).

There are 23 new corpus entries. Three read-only reviewers split the lenses:
- the first pass with lenses 7 and 8;
- lenses 2, 3 and 6;
- lenses 1, 4 and 5.

### The standing first pass: prose against statement

Most of the new prose states its hypotheses where it should: `ConditionalOnePeriodFTAP`,
`hprice`, `T' < T`, `t ≤ H`, and "almost sure per date, not pathwise". The pass found three
patterns of overclaim.

- **Names that promise what the scope retracts.**
  - "The delta hedge is self-financing" (entry name, blueprint title, module title): the entry
    states the self-financing *equation* as an integral identity, with no strategy predicate.
  - "SDE strong solution: existence and uniqueness": the entry proves a unique fixed point of the
    Picard map in `L²`, with no continuous adapted representative.
  - "the hedge pays the call": what is proved is that the call price formula tends to the payoff.

  All are renamed to what they deliver. `DeltaHedge` loses the "self-financing strategy" tag.
- **Quantifier order.** `exists_isEMM_parity` bound the strike and the maturity before `∃ Q`,
  while its prose read "one `Q` for every strike and maturity". The Lean statement is now the
  stronger `∃ Q, IsEMM … ∧ ∀ K τ, …`, which the proof already gave, so the prose is true.
- **Dropped qualifiers.**
  - The Girsanov landmark and README wrote `B_t + ∫₀ᵗ θ` for what is an adapted modification of
    `B_t + ∫₀^{t∧T} θ`.
  - The HJM sentences omitted the deterministic time-0 curve (`hdet`).
  - `GirsanovFiltered` promised continuous paths without the continuity hypothesis.
  - `StochasticFubini` listed the Lévy integral beside the two instances that exist.
  - The DMW descriptions said "inner-product space F" without noting that the hypothesis is the
    conditional FTAP only for `F = ℝ^d`.
  - The density-pasting node omitted the adapted integrable price.

  All are restated.

**Taxonomy.** `mf-hjm-fixed-flows` was `full` while assuming `E[D(tᵢ)] = P(0,tᵢ)`, the identity
the HJM drift condition is for. Given it, the theorem is the model-agnostic zero-curve valuation.
It is now `reduced_core`, like the two entries that assume the conditional one-period FTAP.

Junk values: `HJMModel.bankAccount` and `discount` integrate the short rate `f(s,s)`, which the
bundle did not assume integrable. A non-integrable short rate made the discount factor
`exp 0 = 1`. The bundle now carries `shortRate_integrable` (design.md §2).

### Upgrades executed

- **One physical-value theorem for every contract.**
  - New: `value_physical_eq_riskNeutral`. Under the Girsanov measure of `(m − r)/σ`, any
    fixed-dated contract observed in `[0, H]` has, on the physical asset, its value on the
    risk-neutral asset of `B^θ`.
  - The call, chooser and geometric-Asian theorems were three copies of one `value_congr_ae`
    spine; they are now its instances.
  - It is the blueprint node `thm:physical-measure-pricing` and a corpus entry
    (`mf-bs-physical-contract-value`).
- **No advertised dependency that is not used.** `BlackScholesSelfFinancing` imported
  `ItoProductRule` and its docstring called the proof "the product rule". The proof is Itô's
  formula for `e^{rt}x`. The import is gone and the docstring says what the proof does.
- **The coherence findings, executed on a branch before landing:**
  - `Payoff.obsTimes` was the same recursion as the new `Payoff.obsList`, so there is one
    primitive.
  - `HasOnePeriodDensity` and `LocalEMMDensities` stated the same five per-period conditions
    twice; they now share `IsOnePeriodDensity`.
  - Predictability of time, of the Brownian path and of constants was re-derived at four sites;
    one Foundations lemma each now covers them.
  - `HJMModel.integratedRate` replaces three copies of the integrated short rate.
  - `eval_congr`'s six identical cases are one or-pattern.
  - The redundant `hρa`/`hρc` hypotheses of the product-rule additivity lemmas are gone.
  - The moved `timeMeasure_Ioc_eq_interval` is in house style.

### Ranked backlog

1. **Consumers for three foundations.** The product rule, stochastic Fubini and the
   any-horizon fixed point are each used only by their corpus entries.
   - Derive the self-financing equation from `ito_product_rule_process` with the
     finite-variation factor `e^{rt}`, which removes the second `timeCap` bookkeeping, or the
     discounted-stock representation `e^{−rt}S_t = S₀ + ∫ σ e^{−rs}S_s dB_s`.
   - `pathAssets_eq_picardSolution`: GBM is the unique Picard fixed point. Then the contract
     model is the SDE's solution, not a convention.
   - `HJMModel.expected_discount_eq_bond_zero` from the drift condition `α = σ σ*` via
     `stochFubini_ito`, which retires `hprice`. [#603, #604]
2. **`IsSelfFinancing` as a predicate.** A structure on `(Δ, ψ)`: predictable, value
   `ΔS + ψ`, and the self-financing equation. Then `europeanCall_hedge_isSelfFinancing`
   instantiates it, the hedge value equals `C(t, S_t)` as a corollary, and the physical and HJM
   seams can reuse it. Link it to `ContinuousMarket.SimpleStrategy`. [#597]
3. **`conditionalOnePeriodFTAP_of_finite_filtration`.** For `𝓕 t` generated by finitely many
   atoms of positive mass, apply `ftap_one_period_vector` per atom and paste. This makes
   `exists_isEMM_of_noArbitrage` unconditional on countable `Ω`, and gives `DiscreteMarket` an
   unconditional instance. Also connect the CRR tree as a `discreteAssets` model with its EMM,
   since the DiscreteMarket seam is the weakest of the six. [#313]
4. **The delta hedge beyond the call.**
   - `heat_solution_itoIntegral_rep`: `f(t, B_t) = f(0,0) + ∫ f_x dB` for `f_t + ½f_xx = 0`, of
     which the call hedge is an instance.
   - The put hedge by parity.
   - The identity up to `T` by localisation at `τ_n ↑ T` in place of `timeCap`. [#623]
5. **Random physical drift.** `value_europeanCall_physical` with a predictable drift `m_t`. It
   is the case the predictable-`θ` Girsanov theorem exists for and that the constant-`θ` seam
   does not exercise. It needs a `pathAssets` with drift integral. [#600]
6. **Unify the two constant-`θ` Girsanov measures.** `ZTpred` of a constant is
   `exp(−θB_T − ½θ²T)`; prove it, and `GirsanovConstantTheta` becomes an instance. [done: `ae_ZTconst_eq_wald`, `constGirsanovMeasure_eq_withDensity_wald`]
7. **Name checks for scope words.** Extend `test_prose_does_not_outrun_statement` to entry
   names: "self-financing", "strong solution", "existence and uniqueness", "replicat" beside a
   "Not proved" clause naming the same notion. [done: `test_scope_words_in_names_are_not_disclaimed`]

## 2026-11-06 — corpus 779, modules 710 — library practices (#439), read before it lands

Scope: #439, the library-practices program (`docs/specs/2026-11-05-library-practices-design.md`):
the declaration index, one ratchet, one host-side library model, one doc standard on every module,
one bibliography, `MathFin/Init.lean`, the blueprint ↔ issues link, and the debt the index found.
Three read-only reviewers: the lemmas this branch made public (lenses 2, 3, 6), the Lean structure
it changed (`IsEMM`, the twelve removed duplicates, the `pricing` set, the renames; lenses 1, 4,
5), and 85 rewritten module docstrings against their statements (lenses 7, 8 and the first pass).
Their findings were adjudicated against the code, executed, and built before the branch landed.

### The standing first pass: prose against statement

The doc standard put a `## Main results` list in every module, about 170 of them written this
session, which is a great deal of new prose to read against statements. Seven bullets said more
than the theorem: a balance equation over abstract reals read as a hazard-model theorem
(`cdsFairSpread_TV_cash_flow_balance`); a conditional-expectation identity as "is a martingale"
(`condExp_itoProcessCLM_min`); the binomial representation without its second martingale's
nondegeneracy and `0 < q < 1`; the jump-diffusion martingale criterion without `S₀ ≠ 0` and
integrable `e^J`, and its MGF without `∫ e^{θx} dν < ∞` (the junk-value case); a consistency
witness read as a nontrivial density, where it is `Q = μ`; and a one-period zero-mean identity as
a martingale. All are restated. One flagged bullet was dismissed: the Glosten–Milgrom average does
go through `integral_condExp`. Seven modules still had bare name lists under Main results (`Cox`,
`HullWhiteCalibration`, `Bootstrapping`, `CMS`, `UniswapMechanics`, `MarshallOlkin`,
`ConvexDuality`); they are bullets now, hypotheses included. Beyond the bullets:
`martingale_comp_monotone` claimed to be the sampling bridge of the forward FTAP, which uses
`IsEMM.sampled`, and the `pricing` set promised discounting and forward-price lemmas it never held.

### Upgrades executed

- **One-liners inline, upstream by name.** The index's count of Mathlib-shaped private lemmas went
  193 → 0, but the first resolution made every one public, and the coherence panel found 52 thin
  wrappers, 9 upstream copies and 4 duplicates among them. Publishing a one-liner trades a hidden
  helper for a public wrapper. 26 are gone: 23 written inline (`by positivity`, `fun_prop`,
  `rw [abs_div, abs_two]`, `.pos_part`, …), `hasDerivAt_const_mul` and
  `intervalIntegral.continuous_primitive` called by name, and `absolutelyContinuous_of_pos`
  folded into `eq_empty_of_pos_singleton`. 34 stay, each for a stated reason (a rewrite handle in
  `rw` lists, an upstream lemma outside the file's imports, an ascription longer than the lemma).
  The spec and `decl_index.mathlib_shaped_private` now name the three resolutions.
- **One `L²` increment.** `memLp_increment` (`GaussianMoments`, beside `hasLaw_increment`): for
  any two times, `B t − B s ∈ L²(μ)`. It replaces `WienerIntegralL2.memLp_increment_two` (on a
  `StepIndex`) and `PointwiseBracket.memLp_increment` (with an order hypothesis it never used).
- **The `pricing` set holds what grind can use.** `mertonTerm_parity` and `margrabe_parity` were
  tagged with no example. Pinned, both failed: each is stated as a difference (`call − put = …`),
  so grind's only pattern is that difference, which a rearranged goal never contains. Both are
  untagged, and the set's description now says what it holds (parity on the closed forms, the
  trees' risk-neutral probabilities).
- **Renames finished.** `memLp_uncurry_trim_T` → `memLp_uncurry_trimMeasure`,
  `assembly_isometry_T` → `norm_itoAssemblyHorizon` (their objects were renamed in this branch);
  `max_zero_sub_eq_self` (a Mathlib alias) → `max_zero_sub_max_neg_zero_eq_self`, the name the
  rest of the library uses.

Confirmed and fine: the one `IsEMM` over `[LinearOrder ι]` (no restated ℕ or ℝ≥0 lemma survives),
the twelve duplicates went to the copies every user imports, the `PointwiseBracket` increment
merge, and the `TwoState`/`MultiState`/`Horizon` renames.

### Ranked backlog

1. **The Brownian increment kernels at `IsFilteredPreBrownian`.** Mean zero and variance of an
   increment given `𝓕_s` are derived inline in `squareSubTime_isMartingale`, again in
   `PointwiseBracket.condExp_increment_eq_zero`/`_sq`, and a third time in
   `integral_sq_increment`. State `IsFilteredPreBrownian.condExp_increment_eq_zero` and `_sq`
   once, and make the others instances. [done: `condExp_increment_eq_zero`, `condExp_increment_sq`]
2. **The exponential survival function, once.** `expMeasure_real_Ioi` (`MarshallOlkin`),
   `expMeasure_Ioi` (`ExpMin`, its `ofReal` form) and `expClock_Ioi`/`_Iic` (`Cox`, at rate 1)
   state it three times; the survivor belongs in a module the other two import. [done: `expMeasure_real_Ioi`, `expMeasure_Iic` in `ExpMin.lean`; Cox's clocks are corollaries]
3. **The kept wrappers.** The six chain-rule shims in `WeakForwardUniqueness` are
   `HasDerivAt.cos`/`.sin` of `hasDerivAt_const_mul` plus `congr_deriv (by ring)`;
   `martingale_norm_submartingale` and `iSup_rpow_of_monotone` are BrownianMotion's
   `Martingale.submartingale_norm` and `ENNReal.rpow_iSup` once `DoobLpMaximalInequality` imports
   it; the four `Lp.const` helpers in `MartingaleRepresentation` vanish if constants are written
   `Lp.const 2 μ c`; `convexOn_inv_shift` is `convexOn_zpow (-1)` after a translation. Each needs
   Lean in the loop. [done: `hf.submartingale_norm`, `convexOn_zpow`; `iSup_rpow_of_monotone` waits on `ENNReal.rpow_iSup` upstream (#315)]
4. **`IsEMM.sampled` and `sampledFiltration` at a monotone `t : κ → ι`**, beside the already
   general `IsEMM.increment`; and the vector, general-`Ω` form of `isEMM_one_iff_onePeriod`, which
   retires the hand-built two-step filtration in `noArbitrage_of_isEMM`. [done: `sampledFiltration` over monotone times; `OnePeriodVector.isEMM_one_iff`; `OnePeriodVector.twoStep`]
5. **First principles.** `emm_unique_of_complete` uses only `IsEquivProbMeasure` of its `IsEMM`
   argument; state it there. [retired: `IsEMM` kept as the argument type, recorded in `MarketCompleteness.lean`]
6. **Names.** `OnePeriodVector.IsEMM` shadows the unified `IsEMM` inside its namespace; the
   `Horizon` suffix next to unsuffixed `trimMeasure`/`itoIsometry` hides which objects are the
   horizon ones; `band_overlap_real`, `min_gt_iInter` and `upperPartialMoment_sub` say nothing
   about their statements; the MatrixSignature `toQuadraticForm'` lemmas are upstream candidates
   that will collide when Mathlib adds them. [done: five renames (`OnePeriodVector.IsCentringMeasure`, …)]
7. **Merton and Margrabe parity in price form.** `bsP_eq_bsV` states the put as a function of the
   call, which gives grind a pattern; restate `mertonTerm_parity` and `margrabe_parity` the same
   way and tag them, with a pinned example each. [done: `mertonTerm_parity`, `margrabe_parity` in price form in the `pricing` grind set, pinned]
8. **The nine heartbeat bumps** (89 to 614 lines each): one lemma per idea, with Lean in the loop. [done: all nine `maxHeartbeats` bumps gone (ratchet 0)]

## 2026-11-05 — corpus 779, modules 709 — the backlog closed on main, read before it lands

Scope: #418, the CDS half of #367 and the backlogs of the two 2026-11-04 entries, in four areas
(pricing and FTAP, fixed income, the Itô stack, risk and the American put) worked in parallel and
merged into one tree. Two read-only reviewers read the merged diff; their findings were executed
before it reached main, each change built, the final no-argument build and lint green.

### The standing first pass: prose against statement

A new corpus description cited `mf-ftap-discrete-complete` (existence of an EMM) as the discrete
instance of "replication pins the pricing measure", whose instance is `mf-ftap-two-discrete`; the
Brownian half named no entry. The tree-Snell entry called the general envelope "the smallest
supermartingale above the payoff", which the Lean proves only at the exercise times and the horizon.
The CDS protection contract was "the contract whose value is `Cox.protectionLeg`", true under the
Cox default time at a flat rate; the general value is an identity of Bochner integrals, which now says
both sides are `0` off integrability. In the Itô stack, ten docstrings still named the threaded
hypotheses the bundle replaced (`hMeq`, `hMadap`) or narrated stage layouts that had moved, and one
"stated once" was false (a third `lp_two_norm_sq` sat in `WienerIntegralL2`). All restated; three
bridges rows had their new sentences in the status column (and one an unescaped `|` that split the
table since 2026-11-04), repaired.

### Upgrades executed

- **Replication pins the measure, once.** `ReplicationPricing.measure_eq_of_replicates`: two
  gains-neutral measures agree on every event whose indicator is replicated. The finite market's
  `IsEMM.measure_eq_of_isCompleteMarket` and the Brownian `measure_eq_of_pricesGainsAtZero` are its
  instances (2026-11-04 backlog 7), and the private copies in `MarketCompleteness` are gone.
- **The hedge is priced by the contract.** `exists_hedge_eq_value`: in the complete tree the capital
  of the replication of a European contract is its `Contract.value` (lens 1 of 2026-11-04).
- **The tree's Snell envelope is a Mathlib `Supermartingale`**, frozen at the horizon (lens 2).
- **A payment at a random time.** `Contract.payAtHit` pays at Mathlib's `hittingAfter` on the
  observed path, so CDS protection is a contract paying at default: worth `(1 − R)·𝔼[D(τ)1{τ ≤ T}]`,
  `Cox.protectionLeg` under the Cox time, the limit of the grid legs (#367). `Contract.FixedDated`
  carries the one restriction a random date brings: integrability is proved for fixed-date contracts.
- **The forward measure in Foundations**, the Wiener forward-measure law beside the Wiener integral,
  so the GSR bond price no longer imports a timing-adjustment file; the GSR put at `σ₁ = σ₂` is the
  Vasicek put (`valueDisc_bondPut_gsr_self`).
- **The drift stack's hypotheses as two structures.** `IsAdaptedIntegrand` (δ adapted, continuous,
  bounded) and `IsAdaptedItoDrift` extending it with the version `M`, with a named integrand; five
  arguments threaded through about 25 theorems and their callers become one. `clm_band_energy` sits
  beside `itoProcessCLM_norm_sq` and is Pythagoras for the martingale; the two-band split is one
  `setIntegral_Ioc_prod_add`; `lp_two_norm_sq` is stated once; `stepSum_pow4_le` is its own module.
- **Risk.** Covariance Cauchy–Schwarz from the library's Hölder lemma, in Foundations; Gaussian VaR
  subadditivity a corollary, a third discriminant derivation deleted. `DiscreteVaR` takes a
  `StdSimplex`, built with a new `StdSimplex.prod` (absent from Mathlib, an upstream candidate).

Closed as already done, the boxes stale: the freeze lemma, `SimpleStrategy.toDiscrete`,
`bond_mul_capletPayoff`, `SwapModel` through `HasBondPrice`, the CDS mesh limit,
`martingale_iff_setIntegral_eq` at a σ-finite filtration (Mathlib still has only the ℕ-indexed form).
Declined with reason: the `itoProcessCLM` density proofs (the engine's own is irreducible, the
corollary already one line); a C² preamble bundle (its files carry different hypothesis subsets);
the classical track's `Coe` (`Tangency` needs it) and canonical restatements (inlining them
re-threads the parameter list).

### Ranked backlog

1. `stepSum_pow4_le`: 500 lines at `maxHeartbeats 1600000`, now in its own module but still one
   proof; one lemma per idea (the Young dominations as a Hölder `MemLp.integrable_mul` step, `hY4mem`)
   should drop the heartbeat bump. [done: `stepSum_pow4_le` split into one lemma per idea]
2. The CDS premium leg as a contract: the tower has no continuous payment stream. [done: `Credit.lean`]
3. `snellAux_supermartingale`'s pathwise clause, kept because `bermudanPrice_snell_minimal` and a
   benchmark state pathwise hypotheses; restate them a.e. and drop it. [#631]
4. `Probability/Analysis/FiniteMeasureCauchySchwarz` now also holds covariance lemmas under
   `IsProbabilityMeasure`; `StdSimplex.prod` and `lp_two_norm_sq` are upstream candidates. [#315]

## 2026-11-04 — corpus 773, modules 703 — the pin bump (BrownianMotion 497e5e2, Mathlib e91b128), read before it lands

Scope: the port to Lean v4.35.0, Mathlib e91b128 and BrownianMotion 497e5e2. One read-only
reviewer read the whole diff against the new upstream API; nothing blocked. Its findings were
executed before the push, each change built, the final no-argument build green.

### Upgrades executed

- **Upstream absorbs the library's copies.** `HasLaw.integrable`, `.memLp` and
  `.integrable_fun_comp` replace five Gaussian, Student-t and Rademacher integrability lemmas and the
  private map-form `integrable_exp_mul_of_map_eq_gaussianReal`; `isLocalMartingale_congr_ae` replaces
  the American put's own path-congruence lemma; `List.signVariations` replaces `signVariationsList`;
  the upstream instance replaces `isProbabilityMeasure_map_const_mul`; `gaussianReal_const_mul` and
  `gaussianReal_map_neg` replace hand-built scalings in `BernoulliMixture` and `BivariateNormalCDF`.
- **The predictable-`L²`-is-product-`L²` block, once** (2026-11-04 wave backlog, item 6). Eleven
  hand-rolled `eLpNorm_trim` rewrites are Mathlib's `memLp_of_memLp_trim`; the six `Lp` cases are one
  `ItoIntegralCLM.memLp_prod_of_lp`, and `PointwiseBracket`'s private copy is gone.
- **Probability vectors, one spelling.** The convex-separation roots take "no nonnegative `v` with
  `∑ v = 1` lies in `C`", so FTAP I's two proofs lose their `generalize` ritual; `Convexity.StdSimplex`
  stays where a statement ranges over the simplex (`representingSet_worstCase`).
- **Indistinguishability stated as such.** `brownianInteriorRule_ito_representation` concludes `≡ᵐ` in
  the orientation its caller needs, and the manual flips in `StochasticIntegralCharacterisation`
  are `.symm`.

### Ranked backlog

1. `DiscreteVaR`: bundle the probability vector so `hq₀ hq₁` stop being threaded. Skipped in the
   port: `StdSimplex` has no product constructor for `jointQ`, and `PMF` would put every explicit
   cdf lemma behind `ENNReal.toReal`. The right move is probably a small product lemma for
   `StdSimplex`, upstreamable. [done: `DiscreteVaR.lean`]
2. `MarkovPathMeasure` keeps `unfold; infer_instance`, because `inferInstanceAs` times out in `whnf`
   there. The definition wants an `instance` lemma of its own, as `referenceIntensity` now has. [done: `instance : IsProbabilityMeasure`]

## 2026-11-04 — corpus 773, modules 703 — the backlog wave, read before it lands

Scope: the four maintainer branches that close the 2026-10-31 backlog, merged with the five
contributor PRs into one integration branch so the corpus is swept once: `feat/snell-ftap2` (one
Snell envelope, FTAP II for the finite market and the tree), `feat/aput-coherence` (the American-put
grid and sampling layer), `feat/ito-stack-c2` (the 4000-line `ItoFormulaAdaptedDrift` split by stage,
the Itô-isometry files on one kernel, the American-put Itô chain at C²) and `feat/gsr-bond-put` (#367's
GSR bond put as a contract value). Three read-only reviewers, one per area; their findings were
executed before the merge, not backlogged, by two fixers and the maintainer, each change built.

### The standing first pass: prose against statement

The overclaims were of two kinds. Dropped hypotheses: FTAP II stated as "complete iff the EMM is
unique" without `𝓕 T = ⊤`, which the completeness-to-uniqueness direction needs; the tree's Snell
envelope "the discounted Bermudan price at every time" for a statement at `k ≤ N`, almost surely; the
README's FTAP bullet without its hypotheses; "and both hold" attached to an iff it does not belong to.
Prose that outlived a refactor: the split Itô modules kept the monolith's stage headers, each
narrating an assembly that now lives elsewhere (`ItoDriftMartingaleKill` described the whole proof
and proved one lemma); "the one envelope of the library" while the tree's `snell` keeps its own
recursion, tied to the general envelope only almost surely; a bridges row naming the deleted
`FiniteBellman`; a roadmap naming a branch and calling CMS "next" after #419. All restated to what is
proved; `aeStoppingValue` (a bare `sSup`) gained the junk-value sentence `stoppingValue` carries.

### Upgrades executed

- **Duplicates of Mathlib and of the library, deleted.** In the Itô stack:
  `integral_abs_mul_le_L2L2` was `integral_abs_mul_le_sqrt_mul_sqrt`; `pow3_add_le` was `add_pow_le`;
  the private `1/(n+1)` null sequence was `tendsto_one_div_add_atTop_nhds_zero_nat`; the hand-rolled
  `L²` triangle inequalities and `sqIntegral_of_Lp` went to the `Lp` norm; `continuous_of_dominated`,
  `Even.pow_abs`, `sq_le_sq'`, `Set.Disjoint.set_prod_left` replace their re-proofs; the
  independence step "compose with a power, integrate the product" is one `IndepFun.integral_mul_comp`,
  used by the moment bounds and the quadratic-variation and Poisson isometry files;
  `expectation_pathIntegral_eq` is stated almost surely, absorbing its `_of_ae` twin.
- **A module that was a corollary, dissolved.** `ItoDriftMartingaleKill` proved the martingale
  congruence three times; the hypothesised `M` is now a Mathlib `Martingale` once (`martingale_M`),
  and the kill lemma is `integral_inner_sub_eq_zero` at `F = ℝ`.
- **The Gaussian bond put, once.** `valueDisc_bondPut_wiener` carries the plumbing for any
  integrated short rate in Wiener representation `R T = M T + c T·∫ g_T dB` (integrable discount
  factor, forward measure a probability measure, the put by `valueDisc_bondPut_gaussian`); the
  Hull–White and GSR puts, which repeated 25 lines of it, are now its instances, and Vasicek is
  Hull–White at constant forcing. `vasicekBondB_pos` replaces two inline proofs. The Hull–White caplet
  gets the corpus entry its Vasicek and GSR siblings had.
- **Snell and FTAP.** The tree's Snell envelope agrees with the general one
  (`snell_ae_eq_snellEnvelope`, now a corpus entry and a bridges row); the Doob decomposition of the
  envelope moves to `Probability/Discrete/SnellDoobDecomposition` in namespace `MathFin` (it never needed the
  American put); the `*_bellman` lemma names follow the object they are about (`snellEnvelope`);
  FTAP II's 45-line `by_contra` ladder is two lemmas in `ConvexSeparation` (a nonzero annihilator of a
  proper subspace, on Mathlib's `Submodule.exists_le_ker_of_lt_top`; a positive perturbation); one
  `BinomialNoArb.exists_nnreal_crrUpProb` in `Models/Binomial/Model` replaces a repeated block; `gridTime_mono`
  replaces three cast inequalities; implicit `hq` arguments that every caller named became explicit.

### Lens gradients

1. Inspired math. Exemplar: `isCompleteMarket_of_unique`. Next: `isCompleteMarket_horizonSpot` names no
   hedge; tie its `(x, φ)` to `pathPV_eq_value_add_gains`, so `x` is a `Contract.value`.
2. Coherence. Exemplar: `snell_ae_eq_snellEnvelope`. Next: the tree's `snell` as a Mathlib
   `Supermartingale` under `coinFlipMeasure`, dropping its pathwise clause where a.e. suffices.
4. Architecture. Exemplar: `valueDisc_bondPut_wiener`. Next: `stepSum_pow4_le` (500 lines, run at
   `maxHeartbeats 1600000`) as its own module, "the fourth moment of a bounded adapted Brownian sum".
6. Idiomatic register. Exemplar: the stage modules without their `omit` lists. Next: one
   `IsAdaptedItoDrift` bundle for the seven hypotheses every drift-stack lemma re-threads.
8. Beauty. Exemplar: the kill lemma as a one-line corollary. Next: the GSR put at `σ₁ = σ₂` is the
   Vasicek put (`gsrShortRateV_self`), stated and proved as such.

### Ranked backlog

1. The CDS half of #367: a pay-at-a-stopping-time combinator and the mesh limit of the grid legs. [done: `Core.lean`]
2. `isCompleteMarket_horizonSpot`'s hedge as a contract value (lens 1). [done: `BinomialCompleteMarket.lean`]
3. `stepSum_pow4_le` in its own module; the `IsAdaptedItoDrift` bundle (lenses 4, 6). [done: `ItoStepSumFourthMoment.lean`]
4. `hasLaw_forwardMeasure_wienerIntegralLp` beside the Wiener integral, so `GSRBondPriceAt` stops
   importing a timing-adjustment file for a Wiener fact; the GSR–Vasicek bridge (lens 8). [done: `WienerIntegralForwardMeasure.lean`]
5. `lp_two_norm_sq` stated twice (`PoissonCompensatedIntegralOperator`, `ItoIntegralL2`); the band
   split argument still repeated between `ItoDriftIncrementEnergy` and `ItoDriftWeightedIsometry`. [done: `LpMulIsometry.lean`]
6. The predictable-`L²`-is-product-`L²` block, four times across the Girsanov and drift-process files
   (found by the pin-bump port). [done: `ItoIntegralCLM.memLp_prod_of_lp`]
7. Unjoined twins: `measure_eq_of_pricesGainsAtZero` (Brownian market) and
   `measureReal_eq_of_replicates` (finite market) are one argument without a theorem linking them.

Closed from earlier backlogs: one Snell envelope (2026-10-31, item 2); FTAP II for the tree (item 7);
the split of `ItoFormulaAdaptedDrift` (item 8); the C³ chain at C² (item 4); #423's two squeeze
scaffolds as one lemma (2026-11-04, item 4). [done: `ReplicationPricing.lean`]

## 2026-11-04 — corpus 756, modules 687 — five contributor PRs, read at the raised merge bar

Scope: Yang Ye's five open PRs (#325 Haug barriers, #423 Vasicek κ → 0, #427 American exercise
approximations at their degenerate boundary, #428 removable singularities in Heston and SABR, #429
weak uniqueness for the constant-coefficient forward equation), read by three independent reviewers
and then by the maintainer. The bar since v1.8.0 is coherence, integration and elegance, not only
honest prose: a contribution consumes the objects the library already has, connects to them through
a proved theorem (an instrument with a price is a `Contract` whose `value` is that price), and leaves
no parallel scaffolding behind. Each PR carried a self-review entry written to clear the cadence
gate; those are replaced by this one.

### The standing first pass: prose against statement

Every PR had sentences stronger than its Lean, all in the same direction: a transcribed closed form
described as a price or as "the standard" object. #325: the binary vanilla leg called "a genuine
price" by a theorem that only multiplied `bboB1_eq_Phi_bsd2` by `e^{−rT}`; "the closed-form instance
of `knockIn_add_knockOut_eq_vanilla`" for an identity not derived from it; "the standard down-and-out
closed form" for an expression with no Lean name. #423: the κ → 0 limit's description named the
driftless model the separate cross-check entry identifies. #427: a hypothesis said to "fail" for puts
where Lean proves only that the r = 0 equation has no positive root; "divides by zero" and "jointly
necessary" asserted without proof. #428: integral identities stated for closed forms that never
mention an integral; a Riccati-profile limit described as the Heston expectation. #429: the same
hypothesis-difference sentence repeated in six places.

### Upgrades executed

- **#325, integration through the contracts tower.** `value_digitalCall_eq_bboB1`: the Black–Scholes
  value of `Contracts.digitalCall K T` is the binary parity's vanilla leg `e^{−rT}·B₁`, through
  `Contracts.BlackScholes.value_digitalCall`; it replaces the restating theorem. `ptDownOutCall`
  names the full-life down-and-out closed form, so both partial-time theorems state against one
  object instead of a four-line expression written four times; `e₁`/`e₂` are `bsd1`/`bsd2`. Prose
  says "counterpart", not "instance", and the README's limitation paragraph shrank to what is proved.
- The other four PRs get their reviewers' blocking and coherence findings in their own maintainer
  commits before merge: #428 drops `integral_vasicekDeterministic` and its entry for
  `HullWhiteCalibration.integratedMean_const`; #427 consumes `continuous_gaussianPDFReal` instead of
  five inline re-proofs and drops its release-metadata edits; #429 replaces `IsWeakForwardFlow` and
  the inline `hgate` block of `gyongy_mimicry_gated` by one predicate, so the Gyöngy theorem consumes
  what the uniqueness theorem is about, and the module is renamed for what it proves.

### Lens gradients

2. Coherence. Exemplar: #428's Heston limit, which writes `hestonA` as an integral through
   `hasDerivAt_hestonA` and avoids the 2κθ/ξ² cancellation entirely. Next: the reflection factor
   `(H/S)^{2μ}` is defined twice (`bboHS2mu`, `ptHSmu`) and once more implicitly in Heynen–Kat.
4. Architecture. Exemplar after the rework: Gyöngy consuming the weak-forward predicate. Next: a
   non-vacuity witness — the Gaussian flow `s ↦ N(bs, vs)` satisfies the predicate — which is the
   bridge from the Itô side.
8. Beauty. Exemplar: #423's `abs_vasicekBondV_sub_le`. Next: #429's cos/sin Volterra pair is the real
   and imaginary part of one complex linear ODE; solving it identifies the flow, `ρ_s = ρ_0 ∗ N(bs, vs)`,
   a stronger theorem with a shorter proof.

### Ranked backlog

1. The barriers as contracts: a payoff on a path event, so the transcribed knock-out closed forms can
   be stated as values once the reflection principle is derived rather than assumed. [#52]
2. #429's flow identification through one complex ODE (lens 8 above). [#613]
3. One reflection factor `(H/S)^{2μ}` for the binary, partial-time and Heynen–Kat barriers. [done: `barrierReflection` (`BarrierReflection.lean`)]
4. #423's two squeeze scaffolds as one lemma ("`|f κ − L| ≤ C|κ|` near 0⁺ gives the limit"). [done: `tendsto_nhdsGT_zero_of_abs_sub_le`]
