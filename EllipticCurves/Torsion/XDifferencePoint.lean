/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.TriplingSurjective
import EllipticCurves.Torsion.XDifference

/-!
# The `x`-difference identity at the two indices where it is a statement about points

`EllipticCurves.Torsion.XDifference` proves the `x`-difference identity

```
Φ_q(x)/ΨSq_q(x) − Φ_p(x)/ΨSq_p(x) = ψ_{p+q}(x, y)·ψ_{p−q}(x, y)/(ΨSq_p(x)·ΨSq_q(x))
```

for every pair of integer indices, as a statement about the *polynomials* `Φ` and `ΨSq`.  Reading
`Φₙ/ΨSqₙ` as `x(n • P)` needs the multiplication-by-`n` coordinate formula
`WeierstrassCurve.Affine.HasXCoordFormula`, which is issue `#251`.

⚠️ **It holds at every `n`** over a field of characteristic `≠ 2` —
`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`.  That module and this one
are **import-incomparable**: neither imports the other, so the general form is not reachable here
without adding an import, and the two instances that are reachable are `hasXCoordFormula_two`
(`…DoublingSurjective`) and `hasXCoordFormula_three` (`…TriplingSurjective`).

This file does the reading at the one pair of those two, `(p, q) = (3, 2)`.
Because `ψ_{3−2} = ψ₁ = 1`, the identity collapses to

```
x(2 • P) − x(3 • P) = ψ₅(x, y)/(ΨSq₃(x)·ΨSq₂(x)),
```

`WeierstrassCurve.Affine.xCoord_two_sub_xCoord_three` below.

## ⚠️ What this file is for

It is the **witness that the identity in `XDifference` is about points**, not a step towards `#251`.
A polynomial identity between `Φ` and `ΨSq` is compatible with `Φₙ/ΨSqₙ` never being anybody's
`x`-coordinate; exhibiting one pair of indices at which it *is* rules that out.  ⚠️ It is no longer
the only thing in this tree that can — `hasXCoordFormula_of_two_ne_zero` rules it out at every
index — but it is the only one **at this point in the import order**.  Nothing here is used by
`XDifference`.  Generalising the statement below is now a matter of importing that module and
substituting for the two hypotheses; it is not done here, and no consumer has asked for it.

## Main statements

* `WeierstrassCurve.Affine.xCoord_sub_xCoord_of_hasXCoordFormula` : the point-level `x`-difference
  identity at any pair of indices at which the coordinate formula is available, stated as a
  hypothesis.
* `WeierstrassCurve.Affine.xCoord_two_sub_xCoord_three` : its unconditional instance at `(3, 2)`,
  over a field of characteristic `≠ 2`.
* `WeierstrassCurve.Affine.evalEval_ψ_five_y2EqX3AddOne` : the certificate — on `y² = x³ + 1` over
  `ℚ` at `(2, 3)` the identity **computes** `ψ₅(2, 3) = 186624`, from univariate data only, and the
  value is not zero.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {x y : F}

/-- **The `x`-difference identity as a statement about points**, at any pair of indices `p q : ℕ`
carrying the multiplication-by-`n` coordinate formula:

```
x(q • P) − x(p • P) = ψ_{p+q}(x, y)·ψ_{p−q}(x, y)/(ΨSq_p(x)·ΨSq_q(x)).
```

The `x`-coordinates are produced by `hp`/`hq` rather than by a coordinate function on `W.Point`,
which is why they appear existentially. -/
theorem xCoord_sub_xCoord_of_hasXCoordFormula {p q : ℕ}
    (hp : HasXCoordFormula W p) (hq : HasXCoordFormula W q) (h : W.Nonsingular x y)
    (hp0 : (W.ΨSq p).eval x ≠ 0) (hq0 : (W.ΨSq q).eval x ≠ 0) :
    ∃ (xp yp xq yq : F) (hP : W.Nonsingular xp yp) (hQ : W.Nonsingular xq yq),
      p • Point.some x y h = Point.some xp yp hP ∧ q • Point.some x y h = Point.some xq yq hQ ∧
        xq - xp = (W.ψ (p + q : ℤ)).evalEval x y * (W.ψ (p - q : ℤ)).evalEval x y
          / ((W.ΨSq (p : ℤ)).eval x * (W.ΨSq (q : ℤ)).eval x) := by
  obtain ⟨yp, hP, hPeq⟩ := hp h hp0
  obtain ⟨yq, hQ, hQeq⟩ := hq h hq0
  exact ⟨_, yp, _, yq, hP, hQ, hPeq, hQeq, Φ_div_ΨSq_sub_Φ_div_ΨSq h.1 hp0 hq0⟩

/-- **`x(2 • P) − x(3 • P) = ψ₅(x, y)/(ΨSq₃(x)·ΨSq₂(x))`**, over a field of characteristic `≠ 2`,
at a point of `W` at which neither `ΨSq₂` nor `ΨSq₃` vanishes.

This is `xCoord_sub_xCoord_of_hasXCoordFormula` at `(p, q) = (3, 2)`, where `ψ_{p−q} = ψ₁ = 1`.  It
is the only unconditional point-level instance of the `x`-difference identity this tree admits, and
it exists to witness that the identity of `EllipticCurves.Torsion.XDifference` has point-level
content.  ⚠️ It does not generalise *here*: `HasXCoordFormula W n` holds at every index
(`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`), but that module and this
one are import-incomparable, and the hypotheses substituted below are the two instances reachable
from here. -/
theorem xCoord_two_sub_xCoord_three (h2 : (2 : F) ≠ 0) (h : W.Nonsingular x y)
    (h3 : (W.ΨSq 3).eval x ≠ 0) (h2' : (W.ΨSq 2).eval x ≠ 0) :
    ∃ (x₃ y₃ x₂ y₂ : F) (h₃ : W.Nonsingular x₃ y₃) (h₂ : W.Nonsingular x₂ y₂),
      (3 : ℕ) • Point.some x y h = Point.some x₃ y₃ h₃ ∧
        (2 : ℕ) • Point.some x y h = Point.some x₂ y₂ h₂ ∧
          x₂ - x₃ = (W.ψ 5).evalEval x y / ((W.ΨSq 3).eval x * (W.ΨSq 2).eval x) := by
  have H := xCoord_sub_xCoord_of_hasXCoordFormula (p := 3) (q := 2) (hasXCoordFormula_three h2)
    hasXCoordFormula_two h (by simpa using h3) (by simpa using h2')
  obtain ⟨x₃, y₃, x₂, y₂, h₃, h₂, e₃, e₂, hx⟩ := H
  refine ⟨x₃, y₃, x₂, y₂, h₃, h₂, e₃, e₂, ?_⟩
  rw [hx]
  norm_num

/-! ## A rational certificate: the identity computes `ψ₅` at a point, and the value is nonzero

⚠️ Every statement above is an *equation*, so each is compatible with both of its sides being `0` at
every point one can name.  This block rules that out on a committed curve and a committed point.

The certificate curve is the shared `EllipticCurves.Fixture.y2EqX3AddOne` at `R = ℚ`, `y² = x³ + 1`,
with `b₂ = b₄ = b₈ = 0` and `b₆ = 4`; the point is `(2, 3)`, which `8 + 1 = 9` puts on it and which
`EllipticCurves.Torsion.TriplingSurjective` already uses for the tripling formula.  There

```
Φ₂  = X⁴ − b₄X² − 2b₆X − b₈ = X⁴ − 8X       Φ₂(2)   = 16 − 16 = 0
ΨSq₂ = Ψ₂Sq = 4X³ + 4                       ΨSq₂(2) = 36
Φ₃(2)   = −5184                             ΨSq₃(2) = Ψ₃(2)² = 72² = 5184
```

and `ψ_add_mul_ψ_sub_evalEval` at `(p, q) = (3, 2)` reads `ψ₅(2, 3)·ψ₁(2, 3) = Φ₂(2)·ΨSq₃(2) −
Φ₃(2)·ΨSq₂(2) = 0 + 5184·36 = 186624`.  ⚠️ The `ψ₅` value is **derived from the identity**, not
computed by unfolding `normEDS` — which is the point: the identity is what turns univariate data at
one `x` into a bivariate value at `(x, y)`. -/

section Nonvacuity

open EllipticCurves.Fixture

/-- The point `(2, 3)` lies on `y² = x³ + 1`: `8 + 1 = 9 = 3²`. -/
private lemma equation_y2EqX3AddOne_two_three : (y2EqX3AddOne ℚ).Equation 2 3 := by
  rw [Affine.equation_iff]; norm_num [y2EqX3AddOne]

/-- `ΨSq₂(2) = 36` on `y² = x³ + 1`. -/
private lemma eval_ΨSq_two_y2EqX3AddOne : ((y2EqX3AddOne ℚ).ΨSq 2).eval 2 = 36 := by
  rw [WeierstrassCurve.ΨSq_two]
  norm_num [y2EqX3AddOne, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]

/-- `ΨSq₃(2) = 72² = 5184` on `y² = x³ + 1`. -/
private lemma eval_ΨSq_three_y2EqX3AddOne : ((y2EqX3AddOne ℚ).ΨSq 3).eval 2 = 5184 := by
  rw [ΨSq_three_eval]
  norm_num [y2EqX3AddOne, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `Φ₂(2) = 0` on `y² = x³ + 1`: the point `(2, 3)` doubles to `(0, 1)`. -/
private lemma eval_Φ_two_y2EqX3AddOne : ((y2EqX3AddOne ℚ).Φ 2).eval 2 = 0 := by
  rw [WeierstrassCurve.Φ_two]
  norm_num [y2EqX3AddOne, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `Φ₃(2) = −5184` on `y² = x³ + 1`, through `Φ_three_eval` rather than by unfolding the
recursion that defines `Φ 3`. -/
private lemma eval_Φ_three_y2EqX3AddOne : ((y2EqX3AddOne ℚ).Φ 3).eval 2 = -5184 := by
  rw [Φ_three_eval]
  norm_num [y2EqX3AddOne, WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **The certificate.**  On `y² = x³ + 1` over `ℚ`, the `x`-difference identity at
`(p, q) = (3, 2)` evaluates `ψ₅` at the rational point `(2, 3)`:

```
ψ₅(2, 3) = Φ₂(2)·ΨSq₃(2) − Φ₃(2)·ΨSq₂(2) = 0 − (−5184)·36 = 186624.
```

⚠️ It is the **nonzero** value that is the content.  Both sides of every statement in this file are
now known to be nonzero somewhere, so none of them is a disguised `0 = 0`. -/
theorem evalEval_ψ_five_y2EqX3AddOne :
    ((y2EqX3AddOne ℚ).ψ 5).evalEval 2 3 = 186624 := by
  have h := ψ_add_mul_ψ_sub_evalEval equation_y2EqX3AddOne_two_three 3 2
  rw [show (3 : ℤ) + 2 = 5 from rfl, show (3 : ℤ) - 2 = 1 from rfl, WeierstrassCurve.ψ_one,
    Polynomial.evalEval_one, mul_one, eval_Φ_two_y2EqX3AddOne, eval_Φ_three_y2EqX3AddOne,
    eval_ΨSq_two_y2EqX3AddOne, eval_ΨSq_three_y2EqX3AddOne] at h
  rw [h]; norm_num

/-- The hypotheses of `xCoord_two_sub_xCoord_three` are satisfiable: `(2, 3)` on `y² = x³ + 1` over
`ℚ` meets all of them, and `ℚ` is not algebraically closed. -/
example : (2 : ℚ) ≠ 0 ∧ ((y2EqX3AddOne ℚ).ΨSq 3).eval 2 ≠ 0
    ∧ ((y2EqX3AddOne ℚ).ΨSq 2).eval 2 ≠ 0 :=
  ⟨two_ne_zero, by rw [eval_ΨSq_three_y2EqX3AddOne]; norm_num,
    by rw [eval_ΨSq_two_y2EqX3AddOne]; norm_num⟩

end Nonvacuity

end WeierstrassCurve.Affine
