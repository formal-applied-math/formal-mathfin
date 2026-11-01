# Roadmap — strategy

This file states where the library is going and why. It is kept short and current. The phase log
of how it got here, from May 2026 on, is [`archive/roadmap-history.md`](archive/roadmap-history.md);
the live backlog is the issue tracker, indexed in [`status.md`](status.md).

## What the library is for

One formalization of mathematical finance, organised around the field's own principles, on Mathlib
and Degenne's BrownianMotion and nothing else. The principles are the four pillars of
[`mathematical-architecture.md`](mathematical-architecture.md): no-arbitrage as convex duality,
stochastic calculus, the probabilistic–analytic duality (Feynman–Kac), and the Gaussian and
exponential families. The models are their consequences. A result is worth adding when it makes
one of those consequences a theorem, or when it connects two parts of the library that were
apart.

What the library is not trying to be: the largest theorem count, or a catalogue of closed forms.

## Depth before breadth

The leverage is on the spine: Itô's formula, Girsanov's theorem, the fundamental theorems of asset
pricing, martingale representation. Results there compound. Each one turns hypotheses elsewhere
into theorems: `BSCallHyp` stopped being an axiom when the risk-neutral measure was constructed,
and a hedge became a holding in the price once the integral against the price existed. A new
closed form on its own does not move the library, and the review panel reads a run of them as
drift. Breadth is still welcome, but only on the terms below.

## How breadth is admitted

Since the coherence pass of 2026-10-21, every module connects to the library
(`tests/test_architecture.py`):

* It stands on the library's objects. There is one normal law (`Phi`, `PhiInv`, `quantile`), one
  `valueAtRisk`, one Black–Scholes price `bsV`, one numéraire, one bond lemma. Where a new area has
  its own encoding of an existing object, the two are proved equal.
* A formula the library can derive is derived, not posited. A cost-of-carry forward comes from
  `forward_price_from_no_arbitrage`; a bond price comes from a pricing measure the library
  constructs.
* A module is imported by another module or cited by a corpus entry. A result that nothing uses
  and nothing cites is a claim nobody checks.
* `Foundations/` imports only `Foundations/`. A module that joins a foundation to a model lives in
  `Bridges/`.

Satellites such as market making, DeFi mechanics and the machine-learning utilities of López de
Prado are integrated by bridges, not fenced off. A satellite that cannot be bridged honestly is a
sign it does not belong yet. That is a conversation with the maintainer, not a module.

## Direction

The concrete next rungs, each tracked by an issue. The coherence wave (#357–#368) folded about sixty
parallel developments into instances of one object each; what it left open is below.

* **Rates and credit under a measure the library constructs.** Vasicek and Hull–White bond prices at
  t > 0 and the Jamshidian bond put are done (#410, #413). Next comes GSR, which needs a kernel
  identity for piecewise volatility, then CMS through a swap-rate model bundle, and CDS legs as the
  mesh limit of the grid legs ([#367](https://github.com/formal-applied-math/formal-mathfin/issues/367)). The CMS convexity adjustment ([#303](https://github.com/formal-applied-math/formal-mathfin/issues/303)) follows from that.
  Then the HJM program ([#138](https://github.com/formal-applied-math/formal-mathfin/issues/138)), through the stochastic Fubini theorems
  ([#141](https://github.com/formal-applied-math/formal-mathfin/issues/141)–[#145](https://github.com/formal-applied-math/formal-mathfin/issues/145)).
* **The spine's open seams.** The multi-dimensional martingale representation ([#180](https://github.com/formal-applied-math/formal-mathfin/issues/180)), the
  converse of the second FTAP ([#181](https://github.com/formal-applied-math/formal-mathfin/issues/181)) together with FTAP II for the tree ([#415](https://github.com/formal-applied-math/formal-mathfin/issues/415)), Clark–Ocone
  ([#182](https://github.com/formal-applied-math/formal-mathfin/issues/182)), and the Wiener ↔ Itô bridges ([#366](https://github.com/formal-applied-math/formal-mathfin/issues/366), which is partly blocked on Doob–Meyer
  upstream).
* **One object per concept, continued.**
  * One Snell envelope for the tree and for the foundations ([#415](https://github.com/formal-applied-math/formal-mathfin/issues/415)).
  * One sampled filtration for the American put's grids, and its leftover canonical parameters
    ([#414](https://github.com/formal-applied-math/formal-mathfin/issues/414)).
  * The Itô stack at C² ([#416](https://github.com/formal-applied-math/formal-mathfin/issues/416)).
  * The accepted elegance rewrites from the lens-8 review ([#418](https://github.com/formal-applied-math/formal-mathfin/issues/418)).
* **Jumps.** The Itô–Lévy formula ([#132](https://github.com/formal-applied-math/formal-mathfin/issues/132)) and the PIDE ([#133](https://github.com/formal-applied-math/formal-mathfin/issues/133)). Before them comes the
  jump-diffusion process itself, which the library so far constructs only without jumps ([#305](https://github.com/formal-applied-math/formal-mathfin/issues/305)).

## What stays out

Results that need mathematics Mathlib or BrownianMotion does not yet have, and that the library
should not build for itself, are labelled `status:blocked-upstream` (CEV, Kou, Black–Cox among
them). [`upstreaming.md`](upstreaming.md) logs what the library contributes back. The library
depends on Mathlib and BrownianMotion only. A third dependency is a decision for the maintainer,
not a convenience.
