/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import MathFin.Contracts.Instruments.Options

/-!
# A static-hedge compiler for piecewise-linear payoffs

A European payoff that is a continuous piecewise-linear function of the terminal price is a
*static portfolio*: an amount of zero-coupon bond, an amount of the underlying, and finitely many
calls, one at each kink of the payoff, weighted by the change of slope there. This file proves
that, for the payoffs written in the payoff language of `Contracts/Core.lean`, and compiles them.

The fragment `Payoff.IsPiecewiseLinear T` is what the language builds from constants, the
observation `obs () T`, `add`, `sub`, `max`, `min` and the product with a constant. The portfolio
`StaticHedge` is data: a bond amount, a forward amount and a list of `(strike, weight)` pairs.
`Payoff.staticHedge` sends a payoff to its portfolio, and `StaticHedge.contract` reads the
portfolio back as a `Contract Unit` built from `pay T (const 1)`, `pay T (obs () T)` and
`europeanCall K T`.

The correctness theorem is pathwise and holds for every discount function: along any scenario
with a nonnegative observation at `T`, the compiled contract has the same present value as
`pay T e` (`Payoff.IsPiecewiseLinear.pathPV_staticHedge`). The restriction to nonnegative
observations is the true condition: below zero a call at a nonnegative strike pays nothing, and
the identity `e S = a + b S + ∑ wⱼ (S − Kⱼ)⁺` is an identity of functions on `S ≥ 0`. The values
of the two contracts in every model, and the prices of the pieces by the call price function of a
market, are in `Pricing/StaticHedge.lean` and `Models/ModelFree/StaticHedgeMarket.lean`.

## Implementation notes

`Payoff.staticHedge` is defined by choice: the existence of a portfolio is the theorem
(`Payoff.IsPiecewiseLinear.exists_hedge`), and the definition picks one. It is therefore not an
algorithm, and nothing here says which portfolio it picks, only that every portfolio it can pick
reproduces the payoff on `S ≥ 0`. Outside the fragment the definition returns the empty
portfolio, and no theorem about it applies.

The existence proof runs through the class `IsCallSpanned` of real functions that equal
`a + b S + ∑ wⱼ (S − Kⱼ)⁺` on `S ≥ 0`. It contains the constants and the identity and is closed
under sums, scalings, `max` and `min`. Closure under `max` is the one step with content: it
reduces to the positive part `h⁺` of a member `h`, which is shown to belong to the class by
induction on the number of kinks of `h`, splitting at the smallest kink `K`. Left of `K` the
function `h` is affine, right of `K` it is a member with one kink fewer, and the two positive
parts are glued at `K` (`IsCallSpanned.glue`).

## Main definitions

* `callSum`: the sum `∑ⱼ wⱼ (S − Kⱼ)⁺` of a list of `(Kⱼ, wⱼ)`.
* `IsCallSpanned`: a function that is `a + b S + callSum L S` on `S ≥ 0`.
* `Payoff.IsPiecewiseLinear`: the payoffs of one terminal observation built from constants,
  `obs () T`, `add`, `sub`, `max`, `min` and the product with a constant.
* `StaticHedge`: a bond amount, a forward amount and a list of `(strike, weight)` calls, with its
  `eval` as a function of the terminal price and its `contract` at a date `T`.
* `Payoff.staticHedge`: the compiler, a portfolio for each payoff.

## Main results

* `IsCallSpanned.max`, `IsCallSpanned.min`: the class is closed under `max` and `min`.
* `Payoff.IsPiecewiseLinear.exists_hedge`: every payoff of the fragment equals the value of some
  portfolio at the terminal price, for every scenario with nonnegative terminal observation.
* `StaticHedge.pathPV_contract`: the present value of the compiled contract along a scenario is
  the discount factor times the portfolio's value at the terminal price.
* `Payoff.IsPiecewiseLinear.pathPV_staticHedge`: the compiled contract and `pay T e` have the same
  present value along every scenario with nonnegative terminal observation, for every discount
  function.

## References

* [P. Carr and D. Madan, *Towards a theory of volatility trading*][CarrMadan1998]
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [S. Peyton Jones, J. M. Eber and J. Seward, *Composing contracts*][PeytonJonesEberSeward2000]

## Tags

static hedge, static replication, piecewise linear payoff, spanning by calls, contract compiler,
payoff language, MSC 91G20, JEL G13
-/

@[expose] public section

open scoped NNReal

namespace MathFin.Contracts

/-! ### Call sums and the class they span -/

/-- The sum `∑ⱼ wⱼ (S − Kⱼ)⁺` over a list of `(Kⱼ, wⱼ)`: the payoff, at the price `S`, of calls
at the strikes `Kⱼ` held in the amounts `wⱼ`. -/
noncomputable def callSum (L : List (ℝ × ℝ)) (S : ℝ) : ℝ :=
  (L.map fun p ↦ p.2 * max (S - p.1) 0).sum

/-- An empty call sum is zero. -/
@[simp] theorem callSum_nil (S : ℝ) : callSum [] S = 0 := by simp [callSum]

/-- A call sum splits off its first call. -/
@[simp] theorem callSum_cons (p : ℝ × ℝ) (L : List (ℝ × ℝ)) (S : ℝ) :
    callSum (p :: L) S = p.2 * max (S - p.1) 0 + callSum L S := by simp [callSum]

/-- A call sum over two lists is the sum of the two call sums. -/
theorem callSum_append (L L' : List (ℝ × ℝ)) (S : ℝ) :
    callSum (L ++ L') S = callSum L S + callSum L' S := by simp [callSum]

/-- Scaling every weight of a call sum scales the sum. -/
theorem callSum_smul (c : ℝ) (L : List (ℝ × ℝ)) (S : ℝ) :
    callSum (L.map fun p ↦ (p.1, c * p.2)) S = c * callSum L S := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, callSum_cons, ih]
    ring

/-- A call sum does not depend on the order of its calls. -/
theorem callSum_perm {L L' : List (ℝ × ℝ)} (h : L.Perm L') (S : ℝ) :
    callSum L S = callSum L' S := by
  unfold callSum
  exact (h.map _).sum_eq

/-- Calls struck at or above `K` pay nothing at any price `S ≤ K`. -/
theorem callSum_eq_zero_of_le {K S : ℝ} (hS : S ≤ K) {R : List (ℝ × ℝ)}
    (h : ∀ q ∈ R, K ≤ q.1) : callSum R S = 0 := by
  induction R with
  | nil => simp
  | cons q R ih =>
    have h1 : max (S - q.1) 0 = 0 := max_eq_right (by linarith [h q List.mem_cons_self])
    rw [callSum_cons, h1, ih fun r hr ↦ h r (List.mem_cons_of_mem _ hr)]
    ring

/-- A real function **spanned by calls** on the nonnegative reals: on `S ≥ 0` it equals a constant,
plus a multiple of `S`, plus a call sum. The values at negative `S` are not constrained, since a
price is not negative. -/
def IsCallSpanned (f : ℝ → ℝ) : Prop :=
  ∃ (a b : ℝ) (L : List (ℝ × ℝ)), ∀ S, 0 ≤ S → f S = a + b * S + callSum L S

/-- A function that agrees on `S ≥ 0` with a spanned one is spanned. -/
theorem IsCallSpanned.congr {f g : ℝ → ℝ} (hg : IsCallSpanned g)
    (h : ∀ S, 0 ≤ S → f S = g S) : IsCallSpanned f := by
  obtain ⟨a, b, L, hL⟩ := hg
  exact ⟨a, b, L, fun S hS ↦ (h S hS).trans (hL S hS)⟩

/-- A constant is spanned by calls. -/
theorem isCallSpanned_const (c : ℝ) : IsCallSpanned fun _ ↦ c :=
  ⟨c, 0, [], fun S _ ↦ by simp⟩

/-- The identity is spanned by calls: it is the forward. -/
theorem isCallSpanned_id : IsCallSpanned fun S ↦ S :=
  ⟨0, 1, [], fun S _ ↦ by simp⟩

/-- Spanned functions are closed under sums. -/
theorem IsCallSpanned.add {f g : ℝ → ℝ} (hf : IsCallSpanned f) (hg : IsCallSpanned g) :
    IsCallSpanned fun S ↦ f S + g S := by
  obtain ⟨a, b, L, hL⟩ := hf
  obtain ⟨a', b', L', hL'⟩ := hg
  exact ⟨a + a', b + b', L ++ L', fun S hS ↦ by
    rw [hL S hS, hL' S hS, callSum_append]
    ring⟩

/-- Spanned functions are closed under scaling. -/
theorem IsCallSpanned.smul {f : ℝ → ℝ} (c : ℝ) (hf : IsCallSpanned f) :
    IsCallSpanned fun S ↦ c * f S := by
  obtain ⟨a, b, L, hL⟩ := hf
  exact ⟨c * a, c * b, L.map fun p ↦ (p.1, c * p.2), fun S hS ↦ by
    rw [hL S hS, callSum_smul]
    ring⟩

/-- Spanned functions are closed under differences. -/
theorem IsCallSpanned.sub {f g : ℝ → ℝ} (hf : IsCallSpanned f) (hg : IsCallSpanned g) :
    IsCallSpanned fun S ↦ f S - g S :=
  (hf.add (hg.smul (-1))).congr fun S _ ↦ by
    show f S - g S = f S + -1 * g S
    ring

/-! ### The positive part of a spanned function is spanned -/

/-- The positive part of an affine function is spanned: with root `r`, it is `b (S − r)⁺` for
`b > 0` and `(a + b S) + (−b)(S − r)⁺` for `b < 0`. -/
theorem isCallSpanned_max_affine (a b : ℝ) : IsCallSpanned fun S ↦ max (a + b * S) 0 := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · obtain ⟨r, hr⟩ : ∃ r, b * r = -a := ⟨-a / b, mul_div_cancel₀ _ hb.ne⟩
    refine ⟨a, b, [(r, -b)], fun S _ ↦ ?_⟩
    have e : a + b * S = b * (S - r) := by linear_combination hr
    simp only [callSum_cons, callSum_nil, add_zero, e]
    rcases le_total (S - r) 0 with h | h
    · rw [max_eq_left (by nlinarith : 0 ≤ b * (S - r)), max_eq_right h]
      ring
    · rw [max_eq_right (by nlinarith : b * (S - r) ≤ 0), max_eq_left h]
      ring
  · exact ⟨max a 0, 0, [], fun S _ ↦ by simp⟩
  · obtain ⟨r, hr⟩ : ∃ r, b * r = -a := ⟨-a / b, mul_div_cancel₀ _ hb.ne'⟩
    refine ⟨0, 0, [(r, b)], fun S _ ↦ ?_⟩
    have e : a + b * S = b * (S - r) := by linear_combination hr
    simp only [callSum_cons, callSum_nil, add_zero, zero_add, zero_mul, e]
    rcases le_total (S - r) 0 with h | h
    · rw [max_eq_right (by nlinarith : b * (S - r) ≤ 0), max_eq_right h]
      ring
    · rw [max_eq_left (by nlinarith : 0 ≤ b * (S - r)), max_eq_left h]

/-- Splitting a call sum at a level `K`, on `S ≥ K`: the calls struck below `K` are affine in `S`
there, and the calls struck at or above `K` are kept, the others carrying weight zero. -/
theorem callSum_split (K : ℝ) (L : List (ℝ × ℝ)) (S : ℝ) (hS : K ≤ S) :
    callSum L S = (L.map fun p ↦ if p.1 < K then p.2 else 0).sum * S
      - (L.map fun p ↦ if p.1 < K then p.2 * p.1 else 0).sum
      + callSum (L.map fun p ↦ (p.1, if p.1 < K then 0 else p.2)) S := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, callSum_cons, ih]
    by_cases hp : p.1 < K
    · have h1 : max (S - p.1) 0 = S - p.1 := max_eq_left (by linarith)
      simp only [if_pos hp, h1]
      ring
    · simp only [if_neg hp]
      ring

/-- The calls kept by `callSum_split` pay nothing at any price `S ≤ K`. -/
theorem callSum_split_eq_zero (K : ℝ) (L : List (ℝ × ℝ)) (S : ℝ) (hS : S ≤ K) :
    callSum (L.map fun p ↦ (p.1, if p.1 < K then 0 else p.2)) S = 0 := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, callSum_cons, ih]
    by_cases hp : p.1 < K
    · simp [if_pos hp]
    · have h1 : max (S - p.1) 0 = 0 := max_eq_right (by linarith [not_lt.1 hp])
      simp [if_neg hp, h1]

/-- **A spanned function that vanishes at `K ≥ 0`, cut off below `K`, is spanned.** Right of `K`
the function is a call sum plus an affine function that vanishes at `K`, that is `β (S − K)`, a
call at `K`; the calls struck below `K` are absorbed into `β`. -/
theorem IsCallSpanned.tail {d : ℝ → ℝ} {K : ℝ} (hd : IsCallSpanned d) (hK : 0 ≤ K)
    (h0 : d K = 0) : IsCallSpanned fun S ↦ if S < K then 0 else d S := by
  obtain ⟨a, b, L, hL⟩ := hd
  refine ⟨0, 0, (K, b + (L.map fun p ↦ if p.1 < K then p.2 else 0).sum) ::
      L.map (fun p ↦ (p.1, if p.1 < K then 0 else p.2)), fun S hS ↦ ?_⟩
  have hK0 := hL K hK
  rw [h0, callSum_split K L K le_rfl, callSum_split_eq_zero K L K le_rfl] at hK0
  by_cases hlt : S < K
  · have h1 : max (S - K) 0 = 0 := max_eq_right (by linarith)
    simp only [if_pos hlt, callSum_cons, h1, callSum_split_eq_zero K L S hlt.le]
    ring
  · have hKS : K ≤ S := not_lt.1 hlt
    have h1 : max (S - K) 0 = S - K := max_eq_left (by linarith)
    simp only [if_neg hlt, callSum_cons, h1]
    rw [hL S hS, callSum_split K L S hKS]
    linear_combination (-1 : ℝ) * hK0

/-- **Gluing two spanned functions at a point where they agree.** If `u` and `v` are spanned and
agree at `K ≥ 0`, the function that is `u` left of `K` and `v` from `K` on is spanned. -/
theorem IsCallSpanned.glue {u v : ℝ → ℝ} {K : ℝ} (hu : IsCallSpanned u) (hv : IsCallSpanned v)
    (hK : 0 ≤ K) (huv : u K = v K) : IsCallSpanned fun S ↦ if S < K then u S else v S :=
  (hu.add ((hv.sub hu).tail hK (sub_eq_zero.2 huv.symm))).congr fun S _ ↦ by
    show (if S < K then u S else v S) = u S + (if S < K then 0 else v S - u S)
    split_ifs <;> ring

/-- The positive part of a call-sum function with `n` calls is spanned, by induction on `n`. -/
theorem isCallSpanned_max_zero_aux (n : ℕ) :
    ∀ (a b : ℝ) (L : List (ℝ × ℝ)), L.length = n →
      IsCallSpanned fun S ↦ max (a + b * S + callSum L S) 0 := by
  induction n with
  | zero =>
    intro a b L hL
    cases L with
    | nil => simpa using isCallSpanned_max_affine a b
    | cons p L => exact absurd hL (Nat.succ_ne_zero _)
  | succ n ih =>
    intro a b L hL
    obtain ⟨p0, hp0⟩ : ∃ p, p ∈ L := by
      cases L with
      | nil => exact absurd hL.symm (Nat.succ_ne_zero n)
      | cons p L => exact ⟨p, List.mem_cons_self⟩
    -- the smallest strike `K`, with weight `w`
    obtain ⟨⟨K, w⟩, hpL, hmin⟩ :=
      Finset.exists_min_image L.toFinset Prod.fst ⟨p0, List.mem_toFinset.2 hp0⟩
    obtain ⟨R, hperm⟩ : ∃ R, L.Perm ((K, w) :: R) :=
      ⟨_, List.perm_cons_erase (List.mem_toFinset.1 hpL)⟩
    have hlen : R.length = n := by
      have := hperm.length_eq
      simp only [List.length_cons] at this
      omega
    have hK : ∀ q ∈ R, K ≤ q.1 := fun q hq ↦
      hmin q (List.mem_toFinset.2 (hperm.mem_iff.2 (List.mem_cons_of_mem _ hq)))
    have hcs (S : ℝ) : callSum L S = w * max (S - K) 0 + callSum R S := by
      simp only [callSum_perm hperm, callSum_cons]
    rcases lt_or_ge K 0 with hK0 | hK0
    · -- a kink left of `0` is affine on `S ≥ 0`: fold it into the affine part
      refine (ih (a - w * K) (b + w) R hlen).congr fun S hS ↦ ?_
      have h1 : max (S - K) 0 = S - K := max_eq_left (by linarith)
      simp only [hcs, h1]
      congr 1
      ring
    · -- left of `K` the function is `a + b S`, right of `K` it has one kink fewer
      have hu := isCallSpanned_max_affine a b
      have hv := ih (a - w * K) (b + w) R hlen
      have huv : max (a + b * K) 0 = max (a - w * K + (b + w) * K + callSum R K) 0 := by
        rw [callSum_eq_zero_of_le le_rfl hK]
        congr 1
        ring
      refine (hu.glue hv hK0 huv).congr fun S hS ↦ ?_
      show max (a + b * S + callSum L S) 0 = if S < K then max (a + b * S) 0
        else max (a - w * K + (b + w) * S + callSum R S) 0
      rw [hcs]
      split_ifs with hlt
      · have h1 : max (S - K) 0 = 0 := max_eq_right (by linarith)
        rw [callSum_eq_zero_of_le hlt.le hK, h1]
        simp
      · have h1 : max (S - K) 0 = S - K := max_eq_left (by linarith [not_lt.1 hlt])
        rw [h1]
        congr 1
        ring

/-- **The positive part of a spanned function is spanned.** -/
theorem IsCallSpanned.max_zero {f : ℝ → ℝ} (hf : IsCallSpanned f) :
    IsCallSpanned fun S ↦ max (f S) 0 := by
  obtain ⟨a, b, L, hL⟩ := hf
  refine (isCallSpanned_max_zero_aux _ a b L rfl).congr fun S hS ↦ ?_
  show max (f S) 0 = max (a + b * S + callSum L S) 0
  rw [hL S hS]

/-- **Spanned functions are closed under `max`**: `max f g = f + (g − f)⁺`. -/
theorem IsCallSpanned.max {f g : ℝ → ℝ} (hf : IsCallSpanned f) (hg : IsCallSpanned g) :
    IsCallSpanned fun S ↦ max (f S) (g S) :=
  (hf.add (hg.sub hf).max_zero).congr fun S _ ↦ by
    show max (f S) (g S) = f S + max (g S - f S) 0
    rcases le_total (f S) (g S) with h | h
    · rw [max_eq_right h, max_eq_left (sub_nonneg.2 h)]
      ring
    · rw [max_eq_left h, max_eq_right (sub_nonpos.2 h)]
      ring

/-- **Spanned functions are closed under `min`**: `min f g = f + g − max f g`. -/
theorem IsCallSpanned.min {f g : ℝ → ℝ} (hf : IsCallSpanned f) (hg : IsCallSpanned g) :
    IsCallSpanned fun S ↦ min (f S) (g S) :=
  ((hf.add hg).sub (hf.max hg)).congr fun S _ ↦ by
    show min (f S) (g S) = f S + g S - max (f S) (g S)
    rcases le_total (f S) (g S) with h | h
    · rw [min_eq_left h, max_eq_right h]
      ring
    · rw [min_eq_right h, max_eq_left h]
      ring

/-! ### The fragment and its compiler -/

/-- **The piecewise-linear fragment** of the payoff language, at the observation `obs () T`: the
payoffs built from constants, the observation at `T` alone, sums, differences, `max`, `min` and
the product with a constant, on either side. Every one of them is a continuous piecewise-linear
function of `S_T` with finitely many kinks; `mul` of two non-constant payoffs, `indicatorLt` and
`rpow` are not in the fragment. -/
inductive Payoff.IsPiecewiseLinear (T : ℝ≥0) : Payoff Unit → Prop
  | const (c : ℝ) : IsPiecewiseLinear T (.const c)
  | obs : IsPiecewiseLinear T (.obs () T)
  | add {a b : Payoff Unit} :
      IsPiecewiseLinear T a → IsPiecewiseLinear T b → IsPiecewiseLinear T (.add a b)
  | sub {a b : Payoff Unit} :
      IsPiecewiseLinear T a → IsPiecewiseLinear T b → IsPiecewiseLinear T (.sub a b)
  | max {a b : Payoff Unit} :
      IsPiecewiseLinear T a → IsPiecewiseLinear T b → IsPiecewiseLinear T (.max a b)
  | min {a b : Payoff Unit} :
      IsPiecewiseLinear T a → IsPiecewiseLinear T b → IsPiecewiseLinear T (.min a b)
  | constMul (c : ℝ) {a : Payoff Unit} :
      IsPiecewiseLinear T a → IsPiecewiseLinear T (.mul (.const c) a)
  | mulConst {a : Payoff Unit} (c : ℝ) :
      IsPiecewiseLinear T a → IsPiecewiseLinear T (.mul a (.const c))

/-- **A static hedge**: an amount of the zero-coupon bond paying `1` at the date, an amount of the
underlying delivered at the date, and calls at the date, each a pair `(strike, weight)`. -/
structure StaticHedge where
  /-- The amount of the bond paying `1`. -/
  bondAmount : ℝ
  /-- The amount of the underlying delivered. -/
  forwardAmount : ℝ
  /-- The calls, as `(strike, weight)` pairs. -/
  calls : List (ℝ × ℝ)

/-- The value of the portfolio at the terminal price `S`: `a + b S + ∑ⱼ wⱼ (S − Kⱼ)⁺`. -/
noncomputable def StaticHedge.eval (H : StaticHedge) (S : ℝ) : ℝ :=
  H.bondAmount + H.forwardAmount * S + callSum H.calls S

/-- The contract holding the calls `(Kⱼ, wⱼ)` at the date `T`: the weighted `europeanCall Kⱼ T`
combined with `both`. -/
noncomputable def callPortfolio (T : ℝ≥0) : List (ℝ × ℝ) → Contract Unit
  | [] => .zero
  | p :: L => .both (.scale p.2 (europeanCall p.1 T)) (callPortfolio T L)

/-- **The compiled contract** of a static hedge at the date `T`: the bond amount of
`pay T (const 1)`, the forward amount of `pay T (obs () T)`, and the calls. -/
noncomputable def StaticHedge.contract (H : StaticHedge) (T : ℝ≥0) : Contract Unit :=
  .both (.scale H.bondAmount (.pay T (.const 1)))
    (.both (.scale H.forwardAmount (.pay T (.obs () T))) (callPortfolio T H.calls))

/-- **Every payoff of the fragment is spanned by calls**: a function of the terminal price that is
spanned by calls on `S ≥ 0` and evaluates the payoff on every scenario. -/
theorem Payoff.IsPiecewiseLinear.exists_eval {T : ℝ≥0} {e : Payoff Unit}
    (h : e.IsPiecewiseLinear T) :
    ∃ f : ℝ → ℝ, IsCallSpanned f ∧ ∀ s : Scenario Unit, e.eval s = f (s () T) := by
  induction h with
  | const c => exact ⟨fun _ ↦ c, isCallSpanned_const c, fun s ↦ rfl⟩
  | obs => exact ⟨fun S ↦ S, isCallSpanned_id, fun s ↦ rfl⟩
  | add _ _ iha ihb =>
    obtain ⟨f, hf, hfe⟩ := iha
    obtain ⟨g, hg, hge⟩ := ihb
    exact ⟨_, hf.add hg, fun s ↦ by simp only [Payoff.eval, hfe, hge]⟩
  | sub _ _ iha ihb =>
    obtain ⟨f, hf, hfe⟩ := iha
    obtain ⟨g, hg, hge⟩ := ihb
    exact ⟨_, hf.sub hg, fun s ↦ by simp only [Payoff.eval, hfe, hge]⟩
  | max _ _ iha ihb =>
    obtain ⟨f, hf, hfe⟩ := iha
    obtain ⟨g, hg, hge⟩ := ihb
    exact ⟨_, hf.max hg, fun s ↦ by simp only [Payoff.eval, hfe, hge]⟩
  | min _ _ iha ihb =>
    obtain ⟨f, hf, hfe⟩ := iha
    obtain ⟨g, hg, hge⟩ := ihb
    exact ⟨_, hf.min hg, fun s ↦ by simp only [Payoff.eval, hfe, hge]⟩
  | constMul c _ iha =>
    obtain ⟨f, hf, hfe⟩ := iha
    exact ⟨_, hf.smul c, fun s ↦ by simp only [Payoff.eval, hfe]⟩
  | mulConst c _ iha =>
    obtain ⟨f, hf, hfe⟩ := iha
    exact ⟨fun S ↦ f S * c, (hf.smul c).congr fun S _ ↦ mul_comm _ _,
      fun s ↦ by simp only [Payoff.eval, hfe]⟩

/-- **A portfolio exists for every payoff of the fragment**: its value at the terminal price is the
payoff, on every scenario with nonnegative terminal observation. -/
theorem Payoff.IsPiecewiseLinear.exists_hedge {T : ℝ≥0} {e : Payoff Unit}
    (h : e.IsPiecewiseLinear T) :
    ∃ H : StaticHedge, ∀ s : Scenario Unit, 0 ≤ s () T → e.eval s = H.eval (s () T) := by
  obtain ⟨f, ⟨a, b, L, hL⟩, hfe⟩ := h.exists_eval
  exact ⟨⟨a, b, L⟩, fun s hs ↦ (hfe s).trans (hL _ hs)⟩

open scoped Classical in
/-- **The static-hedge compiler**: a portfolio for each payoff, chosen among those that reproduce
the payoff on the nonnegative reals when the payoff is in the fragment
(`Payoff.IsPiecewiseLinear.exists_hedge`), and the empty portfolio otherwise. The choice is not
constructive, and the correctness theorems carry the hypothesis that the payoff is in the
fragment, which the definition does not need. -/
noncomputable def Payoff.staticHedge (T : ℝ≥0) (e : Payoff Unit) : StaticHedge :=
  if h : e.IsPiecewiseLinear T then h.exists_hedge.choose else ⟨0, 0, []⟩

/-- **The compiler is correct on the fragment**: the payoff is the value of its portfolio at the
terminal price, on every scenario with nonnegative terminal observation. -/
theorem Payoff.IsPiecewiseLinear.eval_staticHedge {T : ℝ≥0} {e : Payoff Unit}
    (h : e.IsPiecewiseLinear T) (s : Scenario Unit) (hs : 0 ≤ s () T) :
    e.eval s = (e.staticHedge T).eval (s () T) := by
  unfold Payoff.staticHedge
  rw [dif_pos h]
  exact h.exists_hedge.choose_spec s hs

/-! ### What the compiled contract pays -/

/-- The present value of a single payment is the discount factor times the payoff. -/
theorem Contract.pathPV_pay {ι : Type*} (D : ℝ≥0 → ℝ) (s : Scenario ι) (t : ℝ≥0)
    (a : Payoff ι) : (Contract.pay t a).pathPV D s = D t * a.eval s := by
  simp [Contract.pathPV, Contract.cashflows]

/-- The present value of the call along a scenario: the discount factor at maturity times the call
payoff of the observation. -/
theorem pathPV_europeanCall (D : ℝ≥0 → ℝ) (s : Scenario Unit) (K : ℝ) (T : ℝ≥0) :
    (europeanCall K T).pathPV D s = D T * max (s () T - K) 0 := by
  simp [europeanCall, europeanCallPayoff, Contract.pathPV_pay, Payoff.eval]

/-- The present value of a portfolio of calls: the discount factor times its call sum at the
terminal observation. -/
theorem pathPV_callPortfolio (D : ℝ≥0 → ℝ) (s : Scenario Unit) (T : ℝ≥0)
    (L : List (ℝ × ℝ)) :
    (callPortfolio T L).pathPV D s = D T * callSum L (s () T) := by
  induction L with
  | nil => simp [callPortfolio, Contract.pathPV, Contract.cashflows]
  | cons p L ih =>
    rw [callPortfolio, Contract.pathPV_both, Contract.pathPV_scale, pathPV_europeanCall, ih,
      callSum_cons]
    ring

/-- **The compiled contract pays the portfolio's value**: along any scenario, for any discount
function, its present value is `D T` times the value of the portfolio at the terminal price. -/
theorem StaticHedge.pathPV_contract (H : StaticHedge) (D : ℝ≥0 → ℝ) (s : Scenario Unit)
    (T : ℝ≥0) : (H.contract T).pathPV D s = D T * H.eval (s () T) := by
  simp only [StaticHedge.contract, Contract.pathPV_both, Contract.pathPV_scale,
    Contract.pathPV_pay, pathPV_callPortfolio, StaticHedge.eval, Payoff.eval]
  ring

/-- **The static hedge of a piecewise-linear payoff replicates it, pathwise.** Along every
scenario with nonnegative terminal observation and for every discount function, the compiled
contract (a bond, a forward and calls) has the present value of `pay T e`. Nothing is assumed of a
model: in any model whose underlying is nonnegative at `T`, the two contracts have equal values
(`Contract.value_pay_eq_value_staticHedge`). -/
theorem Payoff.IsPiecewiseLinear.pathPV_staticHedge {T : ℝ≥0} {e : Payoff Unit}
    (h : e.IsPiecewiseLinear T) (D : ℝ≥0 → ℝ) (s : Scenario Unit) (hs : 0 ≤ s () T) :
    ((e.staticHedge T).contract T).pathPV D s = (Contract.pay T e).pathPV D s := by
  rw [StaticHedge.pathPV_contract, Contract.pathPV_pay, h.eval_staticHedge s hs]

end MathFin.Contracts
