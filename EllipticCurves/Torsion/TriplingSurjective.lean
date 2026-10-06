/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.Torsion.DoublingSurjective
import Mathlib.Algebra.Field.ZMod

/-!
# Multiplication by `3` is surjective on `E(F̄)`

For an elliptic curve `W : Affine F` over an **algebraically closed** field `F` with `(2 : F) ≠ 0`,
every point of `W` is three times another point:

```
∀ Q : W.Point, ∃ P : W.Point, 3 • P = Q.
```

This is the `n = 3` analogue of `EllipticCurves.Torsion.DoublingSurjective`'s
`nsmul_two_surjective`, which was the *only* surjectivity result for the group law in this tree.
Like it, the proof is elementary and one-dimensional: it solves the tripling equation for the
`x`-coordinate directly, and is independent of Ward's theorem, of the elliptic-net recurrence, and
of the general multiplication-by-`n` coordinate formula.

## Which characteristic hypotheses are load-bearing

**Only `(2 : F) ≠ 0`.  `(3 : F) ≠ 0` is *not* needed**, and is deliberately absent.

* `h2` is used in exactly **two** places, and ⚠️ **neither is the tripling formula**:
  `exists_equation` (finding a point above a given `x` means solving a quadratic in `y`) and
  `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`.
* ⚠️ **This bullet used to name a third place — *"the `2` in the denominator of the tangent slope,
  which is what makes `addX_add_self_mul_ΨSq_three_eval` fail in characteristic `2`"* — and both
  halves of it were false.**  The tangent slope's denominator is `s = 2y + a₁x + a₃`, and what
  guards it is `two_mul_add_ne_zero_of_Y_ne` (`EllipticCurves.Torsion.ThreeTorsion`), which binds
  **no** characteristic hypothesis: `s ≠ 0` follows from `y ≠ negY x y` alone, in every
  characteristic.  `addX_add_self_mul_ΨSq_three_eval` now carries no characteristic hypothesis at
  all, and the `Nonvacuity` section below exhibits a point of a curve over `ZMod 2` satisfying its
  three hypotheses.
* A `(3 : F) ≠ 0` would be needed to know `deg Ψ₃ = 4`, but nothing here needs that: the degree
  input is `deg Φ₃ = 9` with leading coefficient `1` (Mathlib's `natDegree_Φ` / `coeff_Φ`, valid
  over
  any nontrivial ring) against `deg ΨSq₃ ≤ 8` (`natDegree_ΨSq_le`, unconditional).  In
  characteristic `3` the polynomial `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` degenerates to
  `b₂X³ + b₈`, and every statement below still holds.

This is stronger than expected — issue `#690` predicted `h3` would be inherited from the tripling
formula — and it is the right answer: `[n]` is surjective on `E(F̄)` for every `n ≥ 1` and every
characteristic.

## The mechanism

Write `p = Ψ₂Sq(x)`, `T = Ψ₃(x)`, `Q = preΨ₄(x)` for an affine point `P = (x, y)`.

* **The tripling formula with denominators cleared**, `addX_add_self_mul_ΨSq_three_eval`:
  for `y ≠ negY x y` and `T ≠ 0`,

  ```
  x(3P) · ΨSq₃(x) = Φ₃(x).
  ```

  This is the only substantial computation.  It is the affine-point mirror of
  `EllipticCurves.FunctionField.GenericTripling`'s `addX_gen_eq_mulByThree`, which proves the same
  identity at the generic point of `F(W)`; that statement cannot be specialised to an `F`-point
  (there is no ring map `F(W) → F`), so the computation is redone here, in the same shape.  The
  route: `x(2P) − x = −T/p` (`addX_self_sub`, merged) and `y(2P) − y = −(ℓ + a₁)(x(2P) − x) − s`
  — a rearrangement of `addY`, `negY` and `negAddY` that introduces no denominator — give
  `(L + ℓ + a₁)(x(2P) − x) = −s` for the secant slope `L` through `2P` and `P`.  Clearing
  `x(2P) − x` against the first relation turns that into `(L + ℓ + a₁)·T = s³`, and substituting
  into `addX` closes the identity after cancelling `s²` alone.

  ⚠️ **The old route went through `y(2P) − y = (Q − p² + a₁Ts)/(2ps)` and the secant slope
  `(p² − Q − a₁Ts)/(2sT)`, and its final cancellation was by `4s²` rather than `s²` — which is
  where the theorem's `(2 : F) ≠ 0` came from, and the only place it ever came from.**  The `2`s in
  that route are an artefact of pinning `L` through `hYkey` rather than through `x(2P) − x ≠ 0`,
  which `Ψ₃(x) ≠ 0` already supplies.  ⚠️ **The new route also does not use `tripling_core` at
  all**; that relation stays in this file because `Φ_three_eval_ne_zero_of_Ψ₃` still consumes it.

* **`Φ₃` and `Ψ₃` have no common root**, `Φ_three_eval_ne_zero_of_Ψ₃`.  At a root of `Ψ₃` the core
  relation collapses to `(p² + Q)² = 0`, so `Q = −p²` and therefore `Φ₃(x) = x·0 − Q·p = p³`, which
  is nonzero because a root of `Ψ₃` is never a root of `Ψ₂Sq` (`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`,
  merged).  **No resultant computation and no Bézout certificate for `(Φ₃, Ψ₃)` is needed** — the
  `n = 3` mirror of the same economy in `DoublingSurjective`.  ⚠️ **It used to need
  `[IsAlgClosed F]` and it no longer does**: `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃` lost its closure in
  `#2104`, and this lemma's was inherited from it and from nowhere else.  `(2 : F) ≠ 0` remains,
  and it is still not the route input (2) takes; see *"The hypotheses of input (2)"* below.

⚠️ **Those two inputs are the whole of what is `n`-specific here, and the argument that consumes
them is not in this file.**  `EllipticCurves.Torsion.NsmulSurjective` runs it once at general `n`:
the degree count on `Φₙ − x₀·ΨSqₙ`, the root extraction over `F̄`, the point above the root and the
absorption of the sign ambiguity `nP = ±Q`.  This file packages the two inputs as
`hasXCoordFormula_three` and `eval_Φ_three_ne_zero_of_root_ΨSq`.

⚠️ **The point above the root may be `2`-torsion, and that case is not degenerate — it is a second,
genuine branch of `hasXCoordFormula_three`.**  `Ψ₂Sq(x) = 0` is not excluded (only `Ψ₃(x) ≠ 0` is),
and there `2P = O`, so the secant construction of `3P = 2P + P` does not apply.  But then
`Φ₃(x) = x·T²` and `ΨSq₃(x) = T²`, so `Φ₃(x)/ΨSq₃(x) = x` and `3P = P` already has the right
`x`-coordinate.

## Main statements

* `WeierstrassCurve.Affine.preΨ₄_eq` / `preΨ₄_eval` — `preΨ₄ = Ψ₃·(6X² + b₂X + b₄) − Ψ₂Sq²`, an
  identity of division polynomials that needs the `b`-relation and is what makes the `y`-coordinate
  of `2P` computable in closed form;
* `WeierstrassCurve.Affine.tripling_core` — the core relation
  `(p² − Q)² + 4T³ − (b₂ + 12x)·p·T² + 4Qp² = 0`;
* `WeierstrassCurve.Affine.Φ_three_eval_ne_zero_of_Ψ₃` — `Φ₃` and `Ψ₃` have no common root, over
  any field of characteristic `≠ 2` with `Δ` a unit, and
  `WeierstrassCurve.Affine.eval_Φ_three_ne_zero_of_root_ΨSq` — the same fact in the form the engine
  consumes, input (2) at `n = 3`, over any field with `Δ` a unit;
* `WeierstrassCurve.Affine.addX_add_self_mul_ΨSq_three_eval` — the tripling formula
  `x(3P)·ΨSq₃(x) = Φ₃(x)`, ⚠️ **over an arbitrary field and with no characteristic hypothesis**,
  certified non-vacuous in characteristic `2` in the `Nonvacuity` section below; and
  `WeierstrassCurve.Affine.hasXCoordFormula_three` — the same formula in the form the engine
  consumes, input (1) at `n = 3`, ⚠️ **also with no characteristic hypothesis** — the retained
  vacuous `_h2` that `#2242` left there is gone, with the whole cascade behind it (`#2245`; see
  that declaration's docstring for the wave table and for why it terminates);
* `WeierstrassCurve.Affine.exists_nsmul_three_some` — every `x₀` is the `x`-coordinate of a tripled
  point;
* **`WeierstrassCurve.Affine.exists_nsmul_three_eq`** and
  **`WeierstrassCurve.Affine.nsmul_three_surjective`** — the headline;
* `WeierstrassCurve.Affine.exists_nsmul_three_eq_some_of_root` — the finite-level companion of the
  headline: a named affine point is three times another point given one root of `Φ₃ − x₀·Ψ₃²` with
  a point of `W` above it, **over an arbitrary field**, with no algebraic closure.

## Scope

Nothing here is about `#E[3] = 9`
(`Torsion/ThreeTorsionStructure.lean` has that), about the Weil pairing, or about general `[n]`:
the classical route to `[n]`-surjectivity is Silverman III.4.10 through `deg [n] = n²`, which is
rung-8 territory and a different piece of work.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ## Division-polynomial identities -/

/-- **`preΨ₄ = Ψ₃·(6X² + b₂X + b₄) − Ψ₂Sq²`.**

The `b`'s are not algebraically independent, and this identity is one of the places where that
matters: its `X²` coefficient is `10b₈` on the left and `6b₈ + b₂b₆ − b₄²` on the right, so the
`b`-relation `4b₈ = b₂b₆ − b₄²` is exactly what closes it.  A bare `ring` will not prove it.

Its role below: `2·(3x² + 2a₂x + a₄ − a₁y) + a₁·(2y + a₁x + a₃) = 6x² + b₂x + b₄` is `y`-free, so
this identity is what turns the `y`-coordinate of the doubled point into a function of `x` alone. -/
lemma preΨ₄_eq :
    W.preΨ₄ = W.Ψ₃ * (6 * X ^ 2 + C W.b₂ * X + C W.b₄) - W.Ψ₂Sq ^ 2 := by
  rw [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq]
  simp only [map_ofNat, C_sub, C_mul, C_pow]
  linear_combination (norm := ring1) (X : F[X]) ^ 2 * W.C_b_relation

/-- `preΨ₄_eq`, evaluated. -/
lemma preΨ₄_eval (x : F) :
    W.preΨ₄.eval x = W.Ψ₃.eval x * (6 * x ^ 2 + W.b₂ * x + W.b₄) - W.Ψ₂Sq.eval x ^ 2 := by
  rw [preΨ₄_eq]; simp

/-- Mathlib's `Φ_three : Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq`, evaluated. -/
lemma Φ_three_eval (x : F) :
    (W.Φ 3).eval x = x * W.Ψ₃.eval x ^ 2 - W.preΨ₄.eval x * W.Ψ₂Sq.eval x := by
  rw [WeierstrassCurve.Φ_three]; simp

/-- Mathlib's `ΨSq_three : ΨSq₃ = Ψ₃²`, evaluated. -/
lemma ΨSq_three_eval (x : F) : (W.ΨSq 3).eval x = W.Ψ₃.eval x ^ 2 := by
  rw [WeierstrassCurve.ΨSq_three]; simp

/-- **The core division-polynomial relation.**  Writing `p = Ψ₂Sq(x)`, `T = Ψ₃(x)`,
`Q = preΨ₄(x)`,

```
(p² − Q)² + 4T³ − (b₂ + 12x)·p·T² + 4Qp² = 0.
```

It is the identity the tripling formula reduces to once the doubling denominators are cleared, and
it is also what shows `Φ₃` and `Ψ₃` have no common root.  Like `preΨ₄_eq` it is closed off the
`b`-relation.  (The same relation, at the generic point, is the `hcore` step of
`EllipticCurves.FunctionField.GenericTripling`; the `linear_combination` witness is shared.) -/
lemma tripling_core (x : F) :
    (W.Ψ₂Sq.eval x ^ 2 - W.preΨ₄.eval x) ^ 2 + 4 * W.Ψ₃.eval x ^ 3
        - (W.b₂ + 12 * x) * W.Ψ₂Sq.eval x * W.Ψ₃.eval x ^ 2
        + 4 * W.preΨ₄.eval x * W.Ψ₂Sq.eval x ^ 2 = 0 := by
  rw [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
  linear_combination (W.b₈ ^ 2 + 6 * x * W.b₆ * W.b₈ + 9 * x ^ 2 * W.b₆ ^ 2 +
      8 * x ^ 2 * W.b₄ * W.b₈ + 24 * x ^ 3 * W.b₄ * W.b₆ + 4 * x ^ 3 * W.b₂ * W.b₈ +
      22 * x ^ 4 * W.b₈ + 16 * x ^ 4 * W.b₄ ^ 2 + 11 * x ^ 4 * W.b₂ * W.b₆ +
      54 * x ^ 5 * W.b₆ + 14 * x ^ 5 * W.b₂ * W.b₄ + 60 * x ^ 6 * W.b₄ +
      3 * x ^ 6 * W.b₂ ^ 2 + 24 * x ^ 7 * W.b₂ + 45 * x ^ 8) * W.b_relation

/-! ## `Φ₃` and `Ψ₃` have no common root -/

/-- At a root of `Ψ₃` the core relation collapses to `(p² + Q)² = 0`, so `Q = −p²`. -/
lemma preΨ₄_eval_of_Ψ₃ {x : F} (hT : W.Ψ₃.eval x = 0) :
    W.preΨ₄.eval x = -W.Ψ₂Sq.eval x ^ 2 := by
  have hcore := tripling_core (W := W) x
  rw [hT] at hcore
  have hsq : (W.Ψ₂Sq.eval x ^ 2 + W.preΨ₄.eval x) ^ 2 = 0 := by linear_combination hcore
  have h0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  linear_combination h0

/-- At a root of `Ψ₃` one has `Φ₃(x) = Ψ₂Sq(x)³`. -/
lemma Φ_three_eval_of_Ψ₃ {x : F} (hT : W.Ψ₃.eval x = 0) :
    (W.Φ 3).eval x = W.Ψ₂Sq.eval x ^ 3 := by
  rw [Φ_three_eval, hT, preΨ₄_eval_of_Ψ₃ hT]; ring

/-- **`Φ₃` and `Ψ₃` have no common root.**  A root of `Ψ₃` is never a root of `Ψ₂Sq`
(`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`, merged), and there `Φ₃(x) = Ψ₂Sq(x)³`.  No Bézout certificate for
the pair `(Φ₃, Ψ₃)` is needed.

⚠️ **This used to take `[IsAlgClosed F]` and it does not**: the instance was inherited from
`Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`, which dropped it in `#2104` once the point above `x` was taken to
be `twoTorsionY` rather than produced by `exists_equation`.  Nothing else in the proof ever used
it, and `lake lint`'s `unusedArguments` is what said so. -/
lemma Φ_three_eval_ne_zero_of_Ψ₃ [W.IsElliptic] (h2 : (2 : F) ≠ 0) {x : F}
    (hT : W.Ψ₃.eval x = 0) : (W.Φ 3).eval x ≠ 0 := by
  rw [Φ_three_eval_of_Ψ₃ hT]
  exact pow_ne_zero 3 (Ψ₂Sq_eval_ne_zero_of_root_Ψ₃ h2 hT)

/-! ## Solving the tripling equation for the `x`-coordinate -/

/-! ### The hypotheses of input (2)

⚠️ **`eval_Φ_three_ne_zero_of_root_ΨSq` used to carry `[IsAlgClosed F]` and `(2 : F) ≠ 0`, and it no
longer does.**  Its docstring used to read *"`ΨSq₃ = Ψ₃²`, so a root of `ΨSq₃` is a root of `Ψ₃`,
and `Φ_three_eval_ne_zero_of_Ψ₃` is the statement that `Φ₃` does not vanish there"*, which is where
both hypotheses came from: `Φ_three_eval_ne_zero_of_Ψ₃` ends in `Ψ₂Sq_eval_ne_zero_of_root_Ψ₃`, a
statement about the points above an `x`.

The trade is the `n = 3` mirror of `DoublingSurjective`'s and it is not free in both directions:

* what is gained — the statement is about polynomials over a field with `Δ` a unit and nothing
  else, matching the `hroot` argument of `exists_nsmul_eq_of_hasXCoordFormula`;
* what is paid — the general route runs through `isCoprime_preΨ₄_Ψ₃` and `isCoprime_Ψ₃_Ψ₂Sq`, both
  of which **are** proved from `Δ`-certificates in `EllipticCurves.DivisionPolynomial.Coprime`, so
  *"no resultant computation and no Bézout certificate for `(Φ₃, Ψ₃)` is needed"* survives only in
  its literal reading: no certificate for the pair `(Φ₃, Ψ₃)`, and two for other pairs.

⚠️ **Neither route is discarded**: the retired proof is kept verbatim as a compiled `example`
below, which is now the only use of `Φ_three_eval_ne_zero_of_Ψ₃` anywhere in this tree.  ⚠️ An
`example` adds no constant to the environment, so a census of *named* consumers reports that lemma
as unconsumed; it is not, and this paragraph is where that is recorded. -/

/-- **`Φ₃` and `ΨSq₃` have no common root**, over any field over which `W` is elliptic — with **no
algebraic closure and no hypothesis on `(2 : F)`**.

`ΨSq₄ = preΨ₄²·Ψ₂Sq` and `ΨSq₂ = Ψ₂Sq` are the factors adjacent to `ΨSq₃ = Ψ₃²`, so this is the
`n = 3` instance of `eval_Φ_ne_zero_of_eval_ΨSq_ne_zero`
(`EllipticCurves.DivisionPolynomial.Coprime`) and its inputs are `isCoprime_preΨ₄_Ψ₃` and
`isCoprime_Ψ₃_Ψ₂Sq` read at a root — the same two inputs the hand proof of
`isCoprime_Φ_three_ΨSq_three` uses, one point at a time.  Reading a coprimality at a root is
`Polynomial.eval_ne_zero_of_isCoprime`, in the same file.  ⚠️ **The proof below used to open with a
local `have key : ∀ {a b : F[X]}, IsCoprime a b → b.eval x = 0 → a.eval x ≠ 0`**, which was that
lemma restated inside a proof because it was `private` where it lived; `#1255` made it public and
the local copy is gone.

This is the `hroot` hypothesis of `exists_nsmul_eq_of_hasXCoordFormula` at `n = 3`.  ⚠️ The degree
count and the root extraction that used to stand here are `n`-independent and are now
`natDegree_Φ_sub_C_mul_ΨSq` and `exists_eval_Φ_eq` in
`EllipticCurves.Torsion.NsmulSurjective`. -/
theorem eval_Φ_three_ne_zero_of_root_ΨSq [W.IsElliptic] (x : F)
    (hx : (W.ΨSq 3).eval x = 0) : (W.Φ 3).eval x ≠ 0 := by
  have h3 : W.Ψ₃.eval x = 0 := by
    refine pow_eq_zero_iff two_ne_zero |>.mp ?_
    rw [← eval_pow, ← ΨSq_three]
    exact hx
  refine eval_Φ_ne_zero_of_eval_ΨSq_ne_zero hx ?_ ?_
  · rw [show (3 : ℤ) + 1 = 4 from rfl, ΨSq_four, eval_mul, eval_pow]
    exact mul_ne_zero
      (pow_ne_zero _ (Polynomial.eval_ne_zero_of_isCoprime W.isCoprime_preΨ₄_Ψ₃ h3))
      (Polynomial.eval_ne_zero_of_isCoprime W.isCoprime_Ψ₃_Ψ₂Sq.symm h3)
  · rw [show (3 : ℤ) - 1 = 2 from rfl, ΨSq_two]
    exact Polynomial.eval_ne_zero_of_isCoprime W.isCoprime_Ψ₃_Ψ₂Sq.symm h3

/-- **The geometric route to input (2), retained.**  This is the proof
`eval_Φ_three_ne_zero_of_root_ΨSq` used to carry, verbatim, under the two hypotheses it used to
carry, and it is the only remaining use of `Φ_three_eval_ne_zero_of_Ψ₃`.

⚠️ It is an `example` and not a theorem because its conclusion **is**
`eval_Φ_three_ne_zero_of_root_ΨSq`'s, under strictly more hypotheses; a second name on a weaker
form of the same statement is the worse outcome.  It is kept because the route through the core
relation is the only one in this tree that reaches input (2) at `n = 3` with no Bézout certificate
at all. -/
example [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) (x : F)
    (hx : (W.ΨSq 3).eval x = 0) : (W.Φ 3).eval x ≠ 0 := by
  rw [ΨSq_three_eval] at hx
  exact Φ_three_eval_ne_zero_of_Ψ₃ h2 (pow_eq_zero_iff two_ne_zero |>.mp hx)


/-! ## The tripling formula `x(3P) = Φ₃(x) / ΨSq₃(x)` -/

section Point

variable [DecidableEq F]

set_option maxHeartbeats 4000000 in
-- The tripling identity clears the doubling denominators into a large division-polynomial relation;
-- its `linear_combination`/`ring1` normalisation exceeds both the default heartbeat limit and the
-- default recursion depth.  The same computation at the generic point (`GenericTripling.lean`) also
-- runs with a raised heartbeat limit.
set_option maxRecDepth 100000 in
/-- **The tripling formula at an affine point, with the denominator cleared.**  For an affine point
`P = (x, y)` of `W` not fixed by negation and with `Ψ₃(x) ≠ 0` — equivalently, with `2P ≠ ±P`, so
that `3P = 2P + P` takes the secant branch — the `x`-coordinate of `3P` satisfies

```
x(3P) · ΨSq₃(x) = Φ₃(x).
```

This is the `n = 3` instance of the multiplication-by-`n` coordinate formula
`x(nP) = Φₙ(x)/ΨSqₙ(x)`, in a form that needs no division.  ⚠️ This docstring used to add *"the
general case is not available in this tree"*, and that is false:
`hasXCoordFormula_of_two_ne_zero` (`EllipticCurves.Torsion.NsmulOrder`) proves it at every index
with `(2 : F) ≠ 0`.  The division-free shape below is still worth having on its own terms, and is
what this file's consumers take.  The mirror statement at the generic point of `F(W)` is
`EllipticCurves.FunctionField.GenericTripling.addX_gen_eq_mulByThree`; it cannot be specialised to
an `F`-point, so the computation is redone here.

⚠️ **No characteristic hypothesis at all.**  This docstring used to close *"characteristic `2` is
excluded (`h2`), through the tangent slope"*, and the reason was wrong as well as the exclusion: the
tangent slope's denominator `s = 2y + a₁x + a₃` is guarded by `two_mul_add_ne_zero_of_Y_ne`, which
binds no characteristic, and `s` is not identically zero in characteristic `2` — there it reads
`a₁x + a₃`, and `a₁ = a₃ = 0` forces `Δ = 0`.  The `h2` was consumed by one step and one only: the
final cancellation of a factor `4`.  Pinning the secant slope through `x(2P) − x ≠ 0` instead of
through the `y`-difference cancels `s²` there, and `s ≠ 0` needs only `hy`.  Nothing needs
`(3 : F) ≠ 0` either. -/
theorem addX_add_self_mul_ΨSq_three_eval {x y : F} (h : W.Equation x y)
    (hy : y ≠ W.negY x y) (hT : W.Ψ₃.eval x ≠ 0) :
    W.addX (W.addX x x (W.slope x x y y)) x
        (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y)
        * (W.ΨSq 3).eval x = (W.Φ 3).eval x := by
  set ℓ := W.slope x x y y with hℓ
  set x₂ := W.addX x x ℓ with hx₂
  set y₂ := W.addY x x y ℓ with hy₂def
  set s := 2 * y + W.a₁ * x + W.a₃ with hsdef
  set T := W.Ψ₃.eval x with hTdef
  set Q := W.preΨ₄.eval x with hQdef
  have hsne : s ≠ 0 := two_mul_add_ne_zero_of_Y_ne hy
  have hs : W.Ψ₂Sq.eval x = s ^ 2 := Ψ₂Sq_eval_eq_sq h
  have hXsub : (x₂ - x) * s ^ 2 = -T := by
    rw [hx₂, hℓ, addX_self_sub h hy, div_mul_cancel₀ _ (pow_ne_zero 2 hsne)]
  have hx₂ne : x₂ - x ≠ 0 := by
    intro hcon
    rw [hcon, zero_mul, eq_comm, neg_eq_zero] at hXsub
    exact hT hXsub
  have hx₂eq : x₂ = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x - x := by
    rw [hx₂, WeierstrassCurve.Affine.addX]
  have hslope_self : ℓ * s = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := slope_self_mul hy
  have hQeq : Q = T * (6 * x ^ 2 + (W.a₁ ^ 2 + 4 * W.a₂) * x + (2 * W.a₄ + W.a₁ * W.a₃))
      - (s ^ 2) ^ 2 := by
    rw [hQdef, hTdef, preΨ₄_eval, hs, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  -- The difference of `y`-coordinates, with the tangent slope kept as `ℓ`.  ⚠️ This is the step the
  -- old proof took in the form `(y₂ − y)·2s³ = Q − (s²)² + a₁Ts`, whose leading `2` is what forced
  -- `h2` on the whole theorem.  Here the `2` is confined to `s = 2y + a₁x + a₃` itself, which is
  -- nonzero by `hy` alone in every characteristic.
  have hy₂sub : y₂ - y = -(ℓ + W.a₁) * (x₂ - x) - s := by
    rw [hy₂def, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, ← hx₂]
    linear_combination hsdef
  set L := W.slope x₂ x y₂ y with hLdef
  have hsl : L * (x₂ - x) = y₂ - y := by
    rw [hLdef, slope_of_X_ne (fun hcon => hx₂ne (by rw [hcon, sub_self])), div_mul_cancel₀ _ hx₂ne]
  -- The secant slope is pinned by `x₂ − x ≠ 0`, not by `2 ≠ 0`: `(L + ℓ + a₁)·(x₂ − x) = −s`.
  have hR1 : (L + ℓ + W.a₁) * (x₂ - x) = -s := by linear_combination hsl + hy₂sub
  -- Clearing `x₂ − x` against `hXsub` gives the characteristic-free replacement for `hslope2`.
  have hLkey : (L + ℓ + W.a₁) * T = s ^ 3 := by
    linear_combination (L + ℓ + W.a₁) * hXsub + (-(s ^ 2)) * hR1
  have main : (W.addX x₂ x L * T ^ 2 - (x * T ^ 2 - Q * s ^ 2)) * s ^ 2 = 0 := by
    simp only [WeierstrassCurve.Affine.addX]
    linear_combination (s * (L * s * T + (s ^ 2) ^ 2 - ℓ * s * T)) * hLkey
      + (s ^ 2) ^ 2 * hQeq - (2 * (s ^ 2) ^ 2 * T) * hslope_self
      - (W.a₁ * (s ^ 2) ^ 2 * T) * hsdef - (s ^ 2 * T ^ 2) * hx₂eq
  rw [ΨSq_three_eval, Φ_three_eval, ← hTdef, ← hQdef, hs]
  have hz := (mul_eq_zero.mp main).resolve_right (pow_ne_zero 2 hsne)
  linear_combination hz

/-- **The coordinate formula at `n = 3`.**  Since `ΨSq₃ = Ψ₃²`, the hypothesis is `Ψ₃(x) ≠ 0`.

⚠️ **Both branches are genuine.**  `Ψ₂Sq(x) = 0` is *not* excluded, and there `2P = O`, so the
secant construction of `3P = 2P + P` does not apply; but then `Φ₃(x) = x·Ψ₃(x)²` and
`ΨSq₃(x) = Ψ₃(x)²`, so `3P = P` already has `x`-coordinate `Φ₃(x)/ΨSq₃(x)`.  Otherwise
`addX_add_self_mul_ΨSq_three_eval` computes it.  This file's module docstring records the same
warning.

⚠️ **NO CHARACTERISTIC HYPOTHESIS AT ALL.**  Both branches of the proof below are
characteristic-free: the `2`-torsion branch never used one, and the secant branch calls
`addX_add_self_mul_ΨSq_three_eval`, which stopped taking one at `#2242`.  So `HasXCoordFormula W 3`
holds over **any** field, and the `Nonvacuity` section below instantiates it over `ZMod 2`.

⚠️ **`#2242` left a retained vacuous binder `_h2` here rather than delete it**, because `--wfail`
turns an unreferenced binder into a build *error*, so deleting it starts a cascade that leaves this
file — and `#2242`'s scope forbade going there.  **`#2245` ran that cascade to exhaustion and took
it.**  Each wave was produced by deleting the previous wave's binders, running a **full
`lake build`**, and reading `is not explicitly referenced` out of the log — measured, not predicted:

* **wave 0** — this declaration.
* **wave 1** — `exists_nsmul_three_eq_some_of_root` (below) and `xCoord_two_sub_xCoord_three`
  (`EllipticCurves.Torsion.XDifferencePoint`).
* **wave 2** — `exists_nsmul_three_eq_triplingField` and
  `exists_nsmul_three_eq_of_roots_baseChange` (`EllipticCurves.Torsion.TriplingGaloisTower`).
* **wave 3** — `exists_nsmul_three_eq_triplingGaloisField` (same file).
* ⚠️ **wave 4 — EMPTY.  The cascade terminates**, at **six** declarations in **four** files.

⚠️ **It terminates for a reason worth naming, and the reason is not that nothing consumes wave 3.**
`exists_nsmul_three_eq_triplingGaloisField` has **two** code consumers.  One binds nothing at all
and so has no binder to lose — `exists_nsmul_three_eq_triplingGaloisField_y2AddYEqX3`, `private` in
`EllipticCurves.Torsion.TriplingGaloisTower`.  The other is
`exists_nsmul_divisor_eq_divisor_mulByThreeEndo_general`
(`EllipticCurves.FunctionField.PullbackPrincipalityThreeGeneral`), whose own `h2` occurs **in its
own statement** — the conclusion names `mulByThreeEndo h2 h3 f` — and ⚠️ **a hypothesis the
conclusion mentions can never become unreferenced.**  **The cascade stops at a statement-level
occurrence and not at a proof-level one**, so the `hprin` front is reached as a call site to fix and
is not weakened by a single binder. -/
theorem hasXCoordFormula_three : HasXCoordFormula W 3 := by
  intro x y h hne
  simp only [Nat.cast_ofNat] at hne ⊢
  have hyeq : W.Equation x y := h.1
  have hT : W.Ψ₃.eval x ≠ 0 := fun h0 => hne (by rw [ΨSq_three_eval, h0]; ring)
  have h3P : (3 : ℕ) • Point.some x y h
      = Point.some x y h + Point.some x y h + Point.some x y h := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, add_smul, two_nsmul, one_nsmul]
  by_cases hyeqn : y = W.negY x y
  · -- `P` is `2`-torsion: `3 • P = P`, and `Φ₃(x)/ΨSq₃(x) = x`
    have hs0 : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      have h' := hyeqn
      rw [WeierstrassCurve.Affine.negY] at h'
      linear_combination h'
    have hp : W.Ψ₂Sq.eval x = 0 := by rw [Ψ₂Sq_eval_eq_sq hyeq, hs0]; ring
    have hxx : (W.Φ 3).eval x / (W.ΨSq 3).eval x = x := by
      rw [Φ_three_eval, hp, mul_zero, sub_zero, ΨSq_three_eval, mul_div_assoc,
        div_self (pow_ne_zero 2 hT), mul_one]
    have hns₃ : W.Nonsingular ((W.Φ 3).eval x / (W.ΨSq 3).eval x) y := by rw [hxx]; exact h
    refine ⟨y, hns₃, ?_⟩
    rw [h3P, Point.add_self_of_Y_eq hyeqn, zero_add]
    simp only [Point.some.injEq, and_true]
    exact hxx.symm
  · -- the secant branch: `3 • P = 2 • P + P`
    have hx₂ne : W.addX x x (W.slope x x y y) ≠ x := by
      rw [Ne, addX_self_eq_iff hyeq hyeqn]
      exact hT
    have hX : W.addX (W.addX x x (W.slope x x y y)) x
        (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y)
        = (W.Φ 3).eval x / (W.ΨSq 3).eval x := by
      rw [eq_div_iff hne]
      exact addX_add_self_mul_ΨSq_three_eval hyeq hyeqn hT
    have hns₃ : W.Nonsingular ((W.Φ 3).eval x / (W.ΨSq 3).eval x)
        (W.addY (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y))
          (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y)) := by
      rw [← hX]
      exact nonsingular_add (nonsingular_add h h fun hxy => hyeqn hxy.right) h
        fun hxy => hx₂ne hxy.left
    refine ⟨W.addY (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y))
        (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y),
      hns₃, ?_⟩
    rw [h3P, Point.add_self_of_Y_ne hyeqn, Point.add_of_X_ne hx₂ne]
    simp only [Point.some.injEq, and_true]
    exact hX

/-- **Every `x`-coordinate is the `x`-coordinate of a tripled point.**  Over an algebraically closed
field — ⚠️ **in every characteristic**, since `#2253` — for every `x₀` there is a point `P` with
`3 • P` affine of `x`-coordinate `x₀`.

The two inputs above, fed to `exists_nsmul_some_of_hasXCoordFormula`. -/
theorem exists_nsmul_three_some [IsAlgClosed F] [W.IsElliptic] (x₀ : F) :
    ∃ (P : W.Point) (y' : F) (h' : W.Nonsingular x₀ y'), (3 : ℕ) • P = Point.some x₀ y' h' :=
  exists_nsmul_some_of_hasXCoordFormula (by norm_num)
    (by simp only [Nat.cast_ofNat]; exact eval_Φ_three_ne_zero_of_root_ΨSq)
    hasXCoordFormula_three x₀

/-- **Multiplication by `3` is surjective on `E(F̄)`.**  Over an algebraically closed field —
⚠️ **in every characteristic**, since `#2253` — every point of an elliptic curve is three times
another point.

The two inputs above, fed to `exists_nsmul_eq_of_hasXCoordFormula`.  There the point at infinity is
`3 • 0`, an affine `Q` is matched by `exists_nsmul_some_of_hasXCoordFormula`, which pins the
`x`-coordinate, and the sign ambiguity `3P = ±Q` that `Point.X_eq_iff` leaves is absorbed by
`−P`. -/
theorem exists_nsmul_three_eq [IsAlgClosed F] [W.IsElliptic] (Q : W.Point) :
    ∃ P : W.Point, (3 : ℕ) • P = Q :=
  exists_nsmul_eq_of_hasXCoordFormula (by norm_num)
    (by simp only [Nat.cast_ofNat]; exact eval_Φ_three_ne_zero_of_root_ΨSq)
    hasXCoordFormula_three Q

/-- **Multiplication by `3` is surjective on `E(F̄)`**, stated as `Function.Surjective` — the
`n = 3` analogue of `nsmul_two_surjective`, and the form `Torsion/Divisible.lean`'s
`torsionSmulHom_surjective` consumes. -/
theorem nsmul_three_surjective [IsAlgClosed F] [W.IsElliptic] :
    Function.Surjective fun P : W.Point => (3 : ℕ) • P :=
  exists_nsmul_three_eq

/-! ## Tripling a named point over an arbitrary field -/

/-- **A named affine point is three times another point**, as soon as `Φ₃ − x₀·Ψ₃²` has a root
carrying a point of `W` above it — over an **arbitrary field**, with no algebraic closure.

⚠️ **This headline read *"is three times another point with `(2 : F) ≠ 0`"* until `#2245`, which is
the binder this statement no longer has**: it is wave 1 of the `hasXCoordFormula_three` cascade
tabulated above.

This is `exists_nsmul_eq_some_of_hasXCoordFormula_of_root`
(`EllipticCurves.Torsion.NsmulSurjective`) at `n = 3`, and the `n = 3` companion of
`exists_nsmul_two_eq_some_of_root` (`EllipticCurves.Torsion.DoublingSurjective`).  Those two are
the engine's finite-level layer's only instances anywhere in this tree.  ⚠️ **The reason recorded
here used to be `#251`, and that reason is gone**: `hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`) supplies the coordinate formula at every index with
`(2 : F) ≠ 0`, and the general-`n` surjectivity it feeds is `nsmul_surjective_of_two_ne_zero`
(`EllipticCurves.Torsion.TwoTorsionOrder`).  ⚠️ Both are **downstream** of this file, so the two
instances below are still the only ones reachable *here*; what is no longer true is that anything
stands between this tree and a general `n`.

⚠️ **`h2` survived here until `#2245` and does not now, and the recorded reason for the asymmetry
with `n = 2` was FALSE before it was removed.**  Both existence steps of the merged
`exists_nsmul_three_eq` — the root extraction and the point above the root — are promoted to
arguments here, so `[IsAlgClosed F]` and `n ≠ 0` have no
consumer left, exactly as at `n = 2`.  This paragraph used to continue: *"what survives is input
(1): `hasXCoordFormula_two` needs nothing at all, while `hasXCoordFormula_three` needs `(2 : F) ≠ 0`
for the secant construction of `3P = 2P + P`.  That is a hypothesis of the tripling formula, not of
the closure, and no promotion of an existence step can remove it."*  ⚠️ **Every clause of that is
now wrong**: the secant construction needs no characteristic hypothesis
(`addX_add_self_mul_ΨSq_three_eval` carries none), it was never a hypothesis of the tripling formula
in the sense meant, and what removes it is not a promotion but a change of route.  ⚠️ **`#2242`
left `h2` standing here as a retained vacuous binder and `#2245` removed it**, together with the
rest of the cascade `hasXCoordFormula_three`'s docstring tabulates.  ⚠️ **So there is no asymmetry
with `n = 2` left to explain**: neither `hasXCoordFormula_two` nor `hasXCoordFormula_three` binds a
characteristic hypothesis, and neither does this statement.

⚠️ The hypothesis is stated on `W.Ψ₃.eval x ^ 2`, not on `(W.ΨSq 3).eval x`.  `ΨSq_three_eval`
bridges them inside the proof, and `Ψ₃` is the name every consumer in this tree computes with — a
hypothesis a caller has to restate before it can discharge it is a hypothesis nobody discharges.
This is `exists_nsmul_two_eq_some_of_root`'s `Ψ₂Sq`-not-`ΨSq 2` decision at the next index.

⚠️ Existence of a third part is genuinely a *hypothesis-shaped* statement over a field that is not
algebraically closed — `exists_nsmul_three_eq` above is stated over `F̄` for a reason.  What this
lemma buys is that the obstruction is entirely visible in one polynomial root, and the `Nonvacuity`
section below discharges that root over `ℚ`. -/
theorem exists_nsmul_three_eq_some_of_root [W.IsElliptic] {x₀ y₀ : F}
    (hQ : W.Nonsingular x₀ y₀) {x y : F} (hxy : W.Equation x y)
    (hx : (W.Φ 3).eval x = x₀ * W.Ψ₃.eval x ^ 2) :
    ∃ P : W.Point, (3 : ℕ) • P = Point.some x₀ y₀ hQ :=
  exists_nsmul_eq_some_of_hasXCoordFormula_of_root
    (by simp only [Nat.cast_ofNat]; exact eval_Φ_three_ne_zero_of_root_ΨSq)
    hasXCoordFormula_three hQ hxy
    (by simpa only [Nat.cast_ofNat, ΨSq_three_eval] using hx)

/-! ### Non-vacuity

The tripling formula carries three hypotheses at once — the point is on the curve, is not fixed by
negation, and has `Ψ₃(x) ≠ 0` — so it is worth exhibiting a point satisfying all three.  On
`y² = x³ + 1` over `ℚ` the point `(2, 3)` does: `negY 2 3 = −3 ≠ 3`, and
`Ψ₃(2) = 3·16 + 3·4·2 = 72`.

⚠️ **The three surjectivity statements above still need an algebraically closed base field, and no
committed instantiation of them is attempted here** — as with the merged `nsmul_two_surjective`.
What *is* instantiated below, on this same curve and this same `x = 2`, is
`exists_nsmul_three_eq_some_of_root`, which needs no closure: the value that makes the tripling
formula apply, `Ψ₃(2) = 72 ≠ 0`, sits at a root of `Φ₃ − (−1)·Ψ₃²`, and that one root makes
`(−1, 0)` three times a **rational** point of `y² = x³ + 1`.

⚠️ **A certificate over an algebraically closed field would certify `exists_nsmul_three_eq`
instead**, and nothing the finite-level lemma adds; this is why the block is over `ℚ`.  It is the
same rule `EllipticCurves.Torsion.DoublingSurjective`'s `ℚ` block states at `n = 2`.

The arithmetic, from `b₂ = 0`, `b₄ = 0`, `b₆ = 4`, `b₈ = 0`:

```
Ψ₃    = 3X⁴ + 12X          Ψ₃(2)    = 48 + 24  = 72
Ψ₂Sq  = 4X³ + 4            Ψ₂Sq(2)  = 32 + 4   = 36
preΨ₄ = 2X⁶ + 40X³ − 16    preΨ₄(2) = 128 + 320 − 16 = 432
Φ₃(2) = 2·72² − 432·36 = 10368 − 15552 = −5184 = (−1)·72².
```

⚠️ `Φ₃(2)` is read off `Φ_three_eval`, `Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq`, rather than by unfolding
`(y2EqX3AddOne ℚ).Φ 3`, whose definition is a recursion. -/

section Nonvacuity

/-! The certificate curve is the shared `EllipticCurves.Fixture.y2EqX3AddOne` at `R = ℚ`:
`y² = x³ + 1`, of discriminant `−432`.  ⚠️ It is the curve here because it carries the rational
pair the tripling formula needs — `(2, 3)` is on it, is not fixed by negation, and has
`Ψ₃(2) = 72 ≠ 0` — over a base that is **not** algebraically closed; the shared docstring records
the same constraint.  `(y2EqX3AddOne ℚ).IsElliptic` comes from the single `[CharZero F]` instance
in `Fixtures`. -/

open EllipticCurves.Fixture

/-- The tripling point `P = (2, 3)` lies on the curve: `8 + 1 = 9 = 3²`. -/
private lemma equation_y2EqX3AddOne_two : (y2EqX3AddOne ℚ).Equation 2 3 := by
  rw [Affine.equation_iff]; norm_num [y2EqX3AddOne]

/-- The tripled point `Q = (−1, 0)` lies on the curve: `−1 + 1 = 0 = 0²`.  It is the point of order
`2`, being fixed by negation. -/
private lemma equation_y2EqX3AddOne_neg_one : (y2EqX3AddOne ℚ).Equation (-1) 0 := by
  rw [Affine.equation_iff]; norm_num [y2EqX3AddOne]

/-- The three hypotheses of the tripling formula at `(2, 3)`, exhibited together.

⚠️ Deliberately anonymous, and deliberately not folded into the certificate below: it is about
`addX_add_self_mul_ΨSq_three_eval`'s hypotheses — on the curve, **not fixed by negation**, and
`Ψ₃(x) ≠ 0` — which is a different job from being a root of `Φ₃ − x₀·Ψ₃²`.  Its first conjunct is
`equation_y2EqX3AddOne_two` rather than a second copy of that proof. -/
example : (y2EqX3AddOne ℚ).Equation 2 3 ∧ (3 : ℚ) ≠ (y2EqX3AddOne ℚ).negY 2 3
    ∧ (y2EqX3AddOne ℚ).Ψ₃.eval 2 ≠ 0 := by
  refine ⟨equation_y2EqX3AddOne_two, ?_, ?_⟩
  · norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.negY]
  · norm_num [y2EqX3AddOne, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **The root that does the work**: `Φ₃(2) = −5184 = (−1) · Ψ₃(2)²`.

Through `Φ_three_eval`, `Φ₃ = X·Ψ₃² − preΨ₄·Ψ₂Sq`, giving `2·5184 − 432·36 = −5184`, rather than by
unfolding `(y2EqX3AddOne ℚ).Φ 3`, whose definition is a recursion. -/
private lemma eval_Φ_three_y2EqX3AddOne :
    ((y2EqX3AddOne ℚ).Φ 3).eval 2 = (-1 : ℚ) * (y2EqX3AddOne ℚ).Ψ₃.eval 2 ^ 2 := by
  rw [Φ_three_eval]
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    y2EqX3AddOne]
  norm_num

/-- **`(−1, 0)` is three times a rational point of `y² = x³ + 1` over `ℚ`**, with no hypothesis on
the base field beyond `(2 : ℚ) ≠ 0`.

The witness the engine returns is `±(2, 3)`: `exists_nsmul_three_eq_some_of_root` hands back the
point above the root, up to the sign `Point.X_eq_iff` leaves.  ⚠️ What makes this a certificate for
the finite-level lemma rather than for `exists_nsmul_three_eq` is that `ℚ` is **not** algebraically
closed — the whole content is that one root of `Φ₃ − x₀·Ψ₃²` is enough. -/
private theorem exists_nsmul_three_eq_y2EqX3AddOne :
    ∃ P : (y2EqX3AddOne ℚ).Point,
      (3 : ℕ) • P =
        Point.some (-1) 0 (equation_iff_nonsingular.mp equation_y2EqX3AddOne_neg_one) :=
  exists_nsmul_three_eq_some_of_root _ equation_y2EqX3AddOne_two
    eval_Φ_three_y2EqX3AddOne

/-! ### Non-vacuity in characteristic `2`

⚠️ `addX_add_self_mul_ΨSq_three_eval` carries **no** characteristic hypothesis, and a removed
hypothesis is worth exactly as much as the widened statement is non-vacuous.  The certificate below
exhibits a point of a curve over a field of characteristic `2` satisfying all three of the
hypotheses that remain — on the curve, not fixed by negation, and `Ψ₃(x) ≠ 0` — so the theorem is
not merely *stated* over such a field but has content there.

⚠️ **The obvious point does not work, and that is why the certificate names a point rather than a
curve.**  On `y² + xy = x³ + 1` over `ZMod 2` the point `(0, 1)` is fixed by negation
(`negY 0 1 = −1 − 0 − 0 = 1`), so it fails `hy`; `(1, 0)` and `(1, 1)` are the two points that pass.
**`Ψ₃ = X⁴ + X³ + 1` there**, which is nonzero at both.

⚠️⚠️ **The curve below is `EllipticCurves.Fixture`'s own, by CITATION rather than by
coincidence**: it is `y2AddXYEqX3AddC (ZMod 2) 1`, the shared `a₁ ≠ 0` family, so the literal
survives in this block's prose and nowhere in this file's code (`#2345` stage 2).

⛔ **Retired, from this paragraph's own earlier text, and the clause was false rather than
partial** — it is a universal negative over the curves `EllipticCurves.Fixtures` serves and one of
them falsifies it, so `### Retired claims` binds and a qualification in place would not have done:
*"`EllipticCurves.Fixture` was checked first and declines: it serves no curve over a finite field,
and says why in terms"*, together with the import comparison that sentence went on to price.
⚠️ **And the paraphrase is wrong independently of this round, which is worth naming rather than
quietly correcting**: what that file declines is the finite-field *certificates*, in its own words,
and not the *curves* — all of its base curves are polymorphic in `[CommRing R]`, and
`y2AddYEqX3 (ZMod 2)` is served to `EllipticCurves.Torsion.TwoTorsionCharTwo` and to
`EllipticCurves.FunctionField.FunctionFieldGaloisDescent`.

⚠️ **`import Mathlib.Algebra.Field.ZMod` is left in place and is no longer justified here**, which
this paragraph says rather than leaving a reader to wonder: no curve is **written out** here any
more, the one below being `Fixtures`' by citation and still declared here, and
this file elaborates with that `import` deleted — at this head and at the base — its transitive
closure being the **same set** with and without it.  ⚠️ **No module count is given here on
purpose**: the one this paragraph carried was read at a base long retired, a closure count moves
under every landing, and whether to delete that `import` is a separate job and not this one's. -/

/-- `y² + xy = x³ + 1` over `ZMod 2` — ⚠️ **`EllipticCurves.Fixture`'s `y2AddXYEqX3AddC` at
`c = 1`, and no longer a separate spelling of the tuple `⟨1, 0, 0, 0, 1⟩`** (`#2345` stage 2), on
the **ordinary** branch (`a₁ ≠ 0`), with `b₂ = 1`, `b₄ = 0`, `b₆ = 0`, `b₈ = 1` and `Δ = 1` — the
general form of that last being `Δ_y2AddXYEqX3AddC_of_two_eq_zero`, which proves `Δ = c` wherever
`2 = 0`.  ⚠️ **No count is given here on purpose**: the population moves under this row, and a
numeral here is one step out of date in the hunk that writes it.

⚠️ The local name is kept because the lemmas below read better with it, and ⚠️ **no `_eq` pin is
added, deliberately**: there is no `IsElliptic` instance and no `Δ` lemma here for a `rfl` of that
shape to protect, and an unreferenced `private` helper is what
`EllipticCurves.Torsion.NsmulSmoothSurjective`'s own `#2253` paragraph argues against.

⚠️⚠️ **It is a `def` and not an `abbrev`, and unlike in `NsmulSmoothSurjective` that is NOT
load-bearing here — measured in both directions.**  That file's alias must stay opaque so that
instance search cannot reach its private `IsElliptic` through the family's head symbol; **this file
declares no `IsElliptic` at all**, so `inferInstance` at `y2AddXYEqX3AddC (ZMod 2) 1` fails under
`def` **and** under `abbrev`, and what `Fixtures`' module docstring says of that family — ⚠️ **in a
bold sentence, whose emphasis is named here rather than reproduced inside the quotation** —
*"carries NO `IsElliptic` instance anywhere in the tree"* is untouched by this file either way.
`def` is kept for consistency with the other aliases. -/
private def curveChar2 : WeierstrassCurve.Affine (ZMod 2) := y2AddXYEqX3AddC (ZMod 2) 1

/-- The base field really is of characteristic `2`. -/
private lemma two_eq_zero_zmod_two : (2 : ZMod 2) = 0 := by decide

/-- `(1, 0)` lies on `curveChar2`: `0 + 0 + 0 = 1 + 0 + 0 + 1 = 0`. -/
private lemma equation_curveChar2 : curveChar2.Equation 1 0 := by
  rw [Affine.equation_iff]; decide +kernel

/-- `(1, 0)` is **not** fixed by negation: `negY 1 0 = −0 − 1·1 − 0 = 1 ≠ 0`.  ⚠️ This is the
hypothesis that replaces `h2`: it is what makes `s = 2y + a₁x + a₃` nonzero, and in characteristic
`2` that reads `s = a₁x + a₃ = 1`. -/
private lemma negY_ne_curveChar2 : (0 : ZMod 2) ≠ curveChar2.negY 1 0 := by
  rw [Affine.negY]; decide +kernel

/-- `Ψ₃ = X⁴ + X³ + 1` on `curveChar2`, so `Ψ₃(1) = 1 ≠ 0`. -/
private lemma Ψ₃_eval_ne_zero_curveChar2 : curveChar2.Ψ₃.eval 1 ≠ 0 := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, curveChar2]
  decide +kernel

/-- **The tripling formula, instantiated over a field of characteristic `2`.**

⚠️ This is the whole content of dropping `h2`: the statement below could not be *written* before,
because the theorem demanded `(2 : F) ≠ 0` and `two_eq_zero_zmod_two` says the opposite holds
here. -/
private theorem addX_add_self_mul_ΨSq_three_eval_curveChar2 :
    curveChar2.addX (curveChar2.addX 1 1 (curveChar2.slope 1 1 0 0)) 1
        (curveChar2.slope (curveChar2.addX 1 1 (curveChar2.slope 1 1 0 0)) 1
          (curveChar2.addY 1 1 0 (curveChar2.slope 1 1 0 0)) 0)
        * (curveChar2.ΨSq 3).eval 1 = (curveChar2.Φ 3).eval 1 :=
  addX_add_self_mul_ΨSq_three_eval equation_curveChar2 negY_ne_curveChar2
    Ψ₃_eval_ne_zero_curveChar2

/-- **`HasXCoordFormula` at `n = 3` over a field of characteristic `2`** — the engine's input (1),
instantiated where it could not be instantiated before.

⚠️ **This is the statement `#2242` could not write, and it is the whole point of `#2245`.**  At
`#2242`'s head `hasXCoordFormula_three` still carried the vacuous binder `_h2 : (2 : F) ≠ 0`, so
naming this instance would have required a proof of `(2 : ZMod 2) ≠ 0`, which is **false**.
⚠️ **Deleting a vacuous binder is therefore not cosmetic: a hypothesis nobody can discharge makes a
true statement unusable over exactly the fields it silently excludes, and the linter that reports
it as unreferenced says nothing about that.** -/
private theorem hasXCoordFormula_three_curveChar2 : HasXCoordFormula curveChar2 3 :=
  hasXCoordFormula_three

end Nonvacuity

end Point

end WeierstrassCurve.Affine
