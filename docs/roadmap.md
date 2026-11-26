# Roadmap — strategy

This file states where the library is going and why. It is kept short and current. The phase log
of how it got here, from May 2026 on, is [`archive/roadmap-history.md`](archive/roadmap-history.md);
the live backlog is the issue tracker, indexed in [`status.md`](status.md).

## What the library is for

A place to learn, use and extend mathematical finance in Lean, on Mathlib and Degenne's
BrownianMotion and nothing else, organized as the field organizes itself
([`organization.md`](organization.md)): one object, a price system; three questions asked of it,
valuation, risk and choice; the model families as a second axis; probability and statistics as
the tools. A result is worth adding when it turns a hypothesis somewhere in the library into a
theorem, or when it connects two parts of the library that were apart.

What the library is not trying to be: the largest theorem count, or a catalogue of closed forms.

## Depth before breadth

The leverage is on the spine: Itô's formula, Girsanov's theorem, the fundamental theorems of asset
pricing, martingale representation. Results there compound. Each one turns hypotheses elsewhere
into theorems: `BSCallHyp` stopped being an axiom when the risk-neutral measure was constructed,
and a hedge became a holding in the price once the integral against the price existed. A new
closed form on its own does not move the library, and the review panel reads a run of them as
drift. Breadth is still welcome, but only on the terms below.

## How breadth is admitted

Every module connects to the library (`tests/test_architecture.py`):

* It stands on the library's objects. There is one normal law (`Phi`, `PhiInv`, `quantile`), one
  `valueAtRisk`, one Black–Scholes price `bsV`, one numéraire, one bond lemma. Where a new area has
  its own encoding of an existing object, the two are proved equal.
* A formula the library can derive is derived, not posited. A cost-of-carry forward comes from
  `forward_price_from_no_arbitrage`; a bond price comes from a pricing measure the library
  constructs.
* A module is imported by another module or cited by a corpus entry. A result that nothing uses
  and nothing cites is a claim nobody checks.
* Imports follow the layers of [`architecture.md`](architecture.md), and a join lives in the module
  that consumes it.

Satellites such as market making, DeFi mechanics and the machine-learning utilities of López de
Prado are integrated by bridges, not fenced off. A satellite that cannot be bridged honestly is a
sign it does not belong yet. That is a conversation with the maintainer, not a module.

## Direction

The next rungs, each carried by an open issue; the blueprint's
[frontier](glossary.md#frontier) states them as results.

* **The spine's open seams.** The multi-dimensional martingale representation ([#180](https://github.com/formal-applied-math/formal-mathfin/issues/180)), the
  converse of the second fundamental theorem in continuous time ([#181](https://github.com/formal-applied-math/formal-mathfin/issues/181)), Clark–Ocone ([#182](https://github.com/formal-applied-math/formal-mathfin/issues/182)),
  and the bridges between the Wiener and Itô integrals ([#366](https://github.com/formal-applied-math/formal-mathfin/issues/366), partly blocked on Doob–Meyer
  upstream).
* **Interest rates.** The CMS convexity adjustment under the payment-date forward measure
  ([#303](https://github.com/formal-applied-math/formal-mathfin/issues/303)), then the Heath–Jarrow–Morton drift condition through the stochastic Fubini theorems
  ([#138](https://github.com/formal-applied-math/formal-mathfin/issues/138), [#142](https://github.com/formal-applied-math/formal-mathfin/issues/142)–[#145](https://github.com/formal-applied-math/formal-mathfin/issues/145); [`hjm-program.md`](hjm-program.md)).
* **Jumps.** A jump-diffusion with jumps, built from the compound Poisson law ([#305](https://github.com/formal-applied-math/formal-mathfin/issues/305)), then the
  Itô–Lévy formula ([#132](https://github.com/formal-applied-math/formal-mathfin/issues/132)) and the pricing PIDE ([#133](https://github.com/formal-applied-math/formal-mathfin/issues/133)).
* **Every price through the pricing functional** ([#450](https://github.com/formal-applied-math/formal-mathfin/issues/450)): the model families priced as markets.

## What the literature says (2026-11-26)

The [literature atlas](specs/2026-11-25-literature-atlas-design.md) placed 21,915 of 24,505 corpus
papers in the taxonomy's cells, then compared each cell's share of the field with its share of the
library's corpus entries. The program tree's Literature layer draws it; `docs/atlas.json` holds the
numbers. The three largest gaps are below. The classifier finds 75–86% of each cell's labelled
papers, so these three are well measured.

* **Collective risk theory** (`risk/insurance`): 9.7% of the field, 0.5% of the library (4
  entries, no proved node). The field rests on ruin theory: Gerber's *Introduction to
  Mathematical Risk Theory*, the Gerber–Shiu *time value of ruin*, Grandell and Rolski et al.
* **Dynamic choice** (`choice/dynamic`): 8.3% of the field, 0.9% of the library (8 entries, one
  proved node). It rests on Merton's continuous-time portfolio problem (1969, 1971),
  Kramkov–Schachermayer's utility maximisation in incomplete markets, and Fleming–Soner's
  controlled Markov processes.
* **Market microstructure** (`choice/trading`): 6.4% of the field, 1.2% of the library (11
  entries, three proved nodes). It rests on Almgren–Chriss optimal execution, Kyle's insider
  trading model and Avellaneda–Stoikov market making.

These are candidates, not commitments: depth before breadth still decides. All three meet the
spine at known points. Ruin theory would build on the compound Poisson law (the jumps rung
above), Merton's problem on Itô's formula through a verification theorem, and optimal execution on
discrete-time control over the library's `Market`. A cell can also be dense for empirical work
the library does not formalise. The next step is a literature trail per cell (milestone 4 of the
spec), before any issue is opened.

## What stays out

Results that need mathematics Mathlib or BrownianMotion does not yet have, and that the library
should not build for itself, are labelled `status:blocked-upstream` (CEV, Kou, Black–Cox among
them). [`upstreaming.md`](upstreaming.md) logs what the library contributes back. The library
depends on Mathlib and BrownianMotion only. A third dependency is a decision for the maintainer,
not a convenience.
