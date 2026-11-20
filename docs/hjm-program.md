# The Heath–Jarrow–Morton drift condition

Status of one open program: the HJM drift condition, with the bond dynamics derived from a
stochastic Fubini theorem. The umbrella issue is
[#138](https://github.com/formal-applied-math/formal-mathfin/issues/138). The program sits in the
term-structure [model family](organization.md#kinds-of-randomness-the-model-families); its
frontier nodes are in [`blueprint_frontier.toml`](blueprint_frontier.toml)
(`thm:hjm-log-bond-dynamics`, `thm:hjm-bond-dynamics`, `thm:hjm-drift-condition`,
`thm:hjm-affine-models`, `thm:hjm-short-rate`, `thm:hjm-musiela`).

## The goal

Let `W` be a Brownian motion under the pricing measure. The state is the forward-rate curve
`f(t,T)`, `t ≤ T`, an Itô process in `t` for each maturity `T`:
`df(t,T) = α(t,T) dt + σ(t,T) dW_t`. With the bond `P(t,T) = exp(−∫_t^T f(t,u) du)`, the short
rate `r(t) = f(t,t)` and the bank account `B(t) = exp(∫₀ᵗ r)`, the Heath–Jarrow–Morton drift
condition says that the discounted bonds `P(·,T)/B` are martingales for every `T` exactly when

```
α(t,T) = σ(t,T) · ∫_t^T σ(t,u) du .
```

The target is this equivalence with the bond dynamics derived rather than assumed. The route has
five identities. Writing `α*` and `σ*` for the integrals of `α` and `σ` over `[t,T]`:

1. The log-bond has `dY = (r − α*) dt − σ* dW`, where `Y = log P`. The interchange of
   `∫_t^T (σ(t,u) dW_t) du` with `(∫_t^T σ(t,u) du) dW_t` is the stochastic Fubini theorem, and
   the moving lower limit contributes the term `r(t) dt`.
2. Itô's formula for the exponential gives `dP/P = (r − α* + ½σ*²) dt − σ* dW`.
3. Dividing by the bank account gives `dZ/Z = (−α* + ½σ*²) dt − σ* dW` for `Z = P/B`.
4. `Z` is a local martingale exactly when its drift vanishes, `α* = ½σ*²`.
5. Differentiating in `T` gives `α = σσ*`; integrating from `t` to `T` using `σ*(t,t) = 0` gives
   the converse.

The martingale statement needs an integrability condition beyond the local-martingale form; the
first target is the local-martingale equivalence.

## The shared primitive

An Itô, Wiener or compensated-Poisson integral is a continuous linear map out of an `L²` space, and
a continuous linear map commutes with a Bochner integral
(`ContinuousLinearMap.integral_comp_comm`). The stochastic Fubini theorem is that commutation plus
one analytic fact, the pointwise representative of an `L²`-valued Bochner integral. It is proved
once for any continuous linear map, and each integral is an instance.

## What is proved

* `StochasticFubini.coeFn_integral_ae_eq` and `StochasticFubini.stochFubini_ofCLM`
  (`Probability/Brownian/Ito/StochasticFubini.lean`): for a continuous linear
  `I : Lp ℝ 2 m →L[ℝ] F` and a Bochner-integrable family `φ : A → Lp ℝ 2 m` with jointly
  integrable representatives `ψ`, `∫ u, I (φ u) ∂ν = I g` for any `g` representing
  `x ↦ ∫ u, ψ u x ∂ν`. Corpus entry `sc-stochastic-fubini-clm`.
* `StochasticFubini.stochFubini_ito` and `StochasticFubini.stochFubini_wiener`
  (`Probability/Brownian/Ito/StochasticFubiniIto.lean`): the instances at the Itô isometry on
  `[0,T]` and at `wienerIntegralLp`. Corpus entries `sc-stochastic-fubini-ito` and
  `sc-stochastic-fubini-wiener`.
* `HJM.HJMModel` and its derived objects `bond`, `shortRate`, `integratedRate`, `bankAccount`,
  `discountedBond`, `starDrift`, `starVol` (`Models/Rates/HJM.lean`), with `bond_self`,
  `bond_pos`, `bankAccount_pos`, `discountedBond_pos`, and `bond_of_flat` (on a flat curve the bond
  is `zcb r t T`).
* `value_fixedFlows_hjm` and `value_fixedFlows_hjm_flat` (`Models/Rates/HJMBond.lean`): a schedule
  of fixed cash flows is worth `∑ P(0, tᵢ) cᵢ` given the pricing hypothesis `𝔼[D tᵢ] = P(0, tᵢ)`,
  and unconditionally on a flat deterministic curve. The hypothesis is what the drift condition
  would deliver, so the first of these is a `reduced_core` entry (`mf-hjm-fixed-flows`; the flat
  case is `mf-hjm-flat-curve-fixed-flows`).

## What is open

* The Lévy instance of stochastic Fubini, through `itoLevyIntegralL2`. No declaration exists yet.
* The pathwise lift of Fubini to all times `t` on the Itô integral process (a continuous
  modification), which the bond dynamics need.
* The refactor of the integrated-rate step of the Vasicek bond price onto the Wiener instance.
* The log-bond dynamics, the bond and discounted-bond dynamics, and the drift condition in
  integrated, pointwise and converse form. None of these is stated in Lean yet.
* The consequences: the short-rate model induced by `r(t) = f(t,t)`, Ho–Lee (constant volatility
  gives `α(t,T) = σ²(T − t)`), the Vasicek and Hull–White affine term structure
  (`vasicekBondPrice_affine`, which the bridge must land on, not re-derive), and the Musiela
  parametrization `r(t,x) = f(t,t+x)`, a stochastic PDE in its own right.

## Open issues

| issue | content |
|---|---|
| [#138](https://github.com/formal-applied-math/formal-mathfin/issues/138) | umbrella |
| [#142](https://github.com/formal-applied-math/formal-mathfin/issues/142) | Stochastic Fubini, Itô, terminal |
| [#143](https://github.com/formal-applied-math/formal-mathfin/issues/143) | Stochastic Fubini, Itô, process |
| [#144](https://github.com/formal-applied-math/formal-mathfin/issues/144) | Stochastic Fubini, Wiener, and the Vasicek refactor |
| [#145](https://github.com/formal-applied-math/formal-mathfin/issues/145) | Stochastic Fubini, Lévy (also unblocks #132, #133) |
| [#146](https://github.com/formal-applied-math/formal-mathfin/issues/146), [#147](https://github.com/formal-applied-math/formal-mathfin/issues/147), [#148](https://github.com/formal-applied-math/formal-mathfin/issues/148) | log-bond dynamics: fixed lower limit, moving-boundary term, assembly |
| [#149](https://github.com/formal-applied-math/formal-mathfin/issues/149), [#150](https://github.com/formal-applied-math/formal-mathfin/issues/150) | bond and discounted-bond dynamics |
| [#151](https://github.com/formal-applied-math/formal-mathfin/issues/151), [#152](https://github.com/formal-applied-math/formal-mathfin/issues/152), [#153](https://github.com/formal-applied-math/formal-mathfin/issues/153), [#154](https://github.com/formal-applied-math/formal-mathfin/issues/154) | drift condition: integrated, pointwise, converse, equivalence |
| [#155](https://github.com/formal-applied-math/formal-mathfin/issues/155), [#156](https://github.com/formal-applied-math/formal-mathfin/issues/156), [#157](https://github.com/formal-applied-math/formal-mathfin/issues/157), [#158](https://github.com/formal-applied-math/formal-mathfin/issues/158) | short rate, Ho–Lee, Vasicek and Hull–White, Musiela |

The Itô-jump consumers of the Lévy instance are
[#132](https://github.com/formal-applied-math/formal-mathfin/issues/132) (the Itô–Lévy formula)
and [#133](https://github.com/formal-applied-math/formal-mathfin/issues/133) (the Merton PIDE).
The model bundle (#139) and the tower-agnostic primitive (#141) are closed.

## References

* Heath, Jarrow, Morton (1992), *Bond pricing and the term structure of interest rates*,
  Econometrica 60(1).
* Björk, *Arbitrage Theory in Continuous Time*, 3rd ed., ch. 23–25.
* Filipović, *Term-Structure Models: A Graduate Course*.
* Veraar (2012), *The stochastic Fubini theorem revisited*, Thm 2.2.
