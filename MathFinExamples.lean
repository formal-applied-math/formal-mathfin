/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFinExamples.Applications.BinomialTree
public import MathFinExamples.Applications.Bootstrapping
public import MathFinExamples.Applications.ChainLadderReserve
public import MathFinExamples.Applications.CappedCall
public import MathFinExamples.Applications.CreditCorrelation
public import MathFinExamples.Applications.GaussianRiskReport
public import MathFinExamples.Applications.MinimumVariance
public import MathFinExamples.Applications.Provenance
public import MathFinExamples.Applications.PutCallParity
public import MathFinExamples.Tour

/-!
# Worked examples

Demonstrations of the library's public API, built by default with `lake build`. Each file imports
only the umbrella `MathFin`, as a downstream project would. Nothing in `MathFin/` imports them.
Each application states what the library supplies and what it does not.

* `Tour`: five representative theorems (Black–Scholes delta, minimum variance, Gaussian VaR,
  Kelly, variance swap) restated in a few lines each.
* `Applications.BinomialTree`: a binomial tree checked for no-arbitrage, hedge, put–call parity
  and the Cox–Ross–Rubinstein limit.
* `Applications.BlackScholesMarket`: a concrete Black–Scholes market on Brownian motion, its
  pricing measure and the price of a call.
* `Applications.Bootstrapping`: a discount curve solved from par bonds, repricing every input.
* `Applications.CappedCall`: a term sheet written in the payoff language and priced in a
  Black–Scholes market, with static bounds.
* `Applications.ChainLadderReserve`: a chain-ladder reserve computed exactly over `ℚ` and
  certified against the real chain ladder.
* `Applications.CreditCorrelation`: default probabilities and default correlation in a one-factor
  Gaussian threshold pool.
* `Applications.GaussianRiskReport`: VaR, expected shortfall and the diversification benefit of a
  two-position Gaussian book.
* `Applications.MinimumVariance`: the minimum-variance split between two assets.
* `Applications.Provenance`: the shared record of where an example's inputs come from and what it
  does not model.
* `Applications.PutCallParity`: put–call parity as a check on a pair of quoted prices.
-/
