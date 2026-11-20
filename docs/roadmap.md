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

## What stays out

Results that need mathematics Mathlib or BrownianMotion does not yet have, and that the library
should not build for itself, are labelled `status:blocked-upstream` (CEV, Kou, Black–Cox among
them). [`upstreaming.md`](upstreaming.md) logs what the library contributes back. The library
depends on Mathlib and BrownianMotion only. A third dependency is a decision for the maintainer,
not a convenience.
