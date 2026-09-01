/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OmegaOnCurve

/-!
# The `2`-division `y`-coordinate and the doubling map is on the curve

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` develops the
`x`-coordinate division polynomials (`ψ₂, Ψ₂Sq, Ψ₃, preΨ₄, ΨSq, Ψ, Φ, ψ, φ`) but explicitly leaves
the *`y`-coordinate* division polynomials `ωₙ` as a `TODO`. Consequently there is, on the current
pin, no statement that the multiplication-by-`n` point `[n]P = (Φₙ/ΨSqₙ, ωₙ/ψₙ³)` actually lies on
the curve — the *on-curve identity* that the function-field pullback `[n]∗ : F(W) → F(W)` consumes.

This file supplies the crux for the **duplication map** `n = 2` (Silverman AEC, Exercise 3.7).

The heavy algebra collapses to a single **univariate** division-polynomial identity
`preΨ₄² = 4Φ₂³ + b₂Φ₂²Ψ₂Sq + 2b₄Φ₂Ψ₂Sq² + b₆Ψ₂Sq³` (`WeierstrassCurve.preΨ₄_sq`, in
`EllipticCurves.Torsion.OmegaDivisionPolynomial`), a polynomial identity in `R[X]` proved by
unfolding the definitions and `ring`. That is exactly `WeierstrassCurve.HasPreΩSq 2`, so the
on-curve identity for the doubled point is the `n = 2` case of the engine
`WeierstrassCurve.Affine.equation_of_hasPreΩSq` of `EllipticCurves.Torsion.OmegaOnCurve`, and the
theorem below is that engine applied and the `n = 2` names unfolded: over a field of characteristic
`≠ 2`, for a point `(x, y)` on `W` with `ψ₂(x, y) ≠ 0` (i.e. `P` is not `2`-torsion), the point
`(Φ₂(x)/Ψ₂Sq(x), ω₂(x,y)/ψ₂(x,y)³)` lies on `W`, where `ω₂(x,y) := (preΨ₄(x) - ψ₂(x,y)·(a₁Φ₂(x) +
a₃Ψ₂Sq(x)))/2` is the value of the `2`-division `y`-coordinate polynomial.

Note that this is a purely *algebraic* on-curve identity for the classical division-polynomial
doubling coordinates; identifying `(Φ₂/Ψ₂Sq, ω₂/ψ₂³)` with the group-law double `2 • P` (which then
makes the on-curve property automatic) is a separate, harder statement not proved here — but it
**is** proved, in `EllipticCurves.Torsion.DoublingCoords`, as `addX_self_eq_div` and
`addY_self_eq_div` (the second over a field of characteristic `≠ 2`; the first needs no such
hypothesis). ⚠️ Both are **forward references**: that module imports this one directly and is not
in this file's import closure, so neither is nameable here and nothing below uses either.
⚠️ `EllipticCurves.Torsion.OmegaThree` carries the twin of this sentence at `n = 3` and already
names its discharger, `EllipticCurves.Torsion.TriplingCoords`; this one had not caught up.

## Main statements

* `WeierstrassCurve.Affine.doubling_equation`: the division-polynomial doubling point lies on the
  curve.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **The doubling point lies on the curve.** For a point `(x, y)` on `W` over a field of
characteristic `≠ 2`, with `ψ₂(x, y) ≠ 0` (i.e. `(x, y)` is not `2`-torsion), the point
`[2](x, y) = (Φ₂(x)/Ψ₂Sq(x), ω₂(x,y)/ψ₂(x,y)³)` satisfies the Weierstrass equation, where the
`2`-division `y`-coordinate value is `ω₂(x,y) = (preΨ₄(x) - ψ₂(x,y)·(a₁Φ₂(x) + a₃Ψ₂Sq(x)))/2`.

This is the crux on-curve identity consumed by the multiplication-by-`2` function-field pullback. -/
theorem doubling_equation (h : W.Equation x y) (h2 : (2 : F) ≠ 0)
    (hψ : (W.ψ 2).evalEval x y ≠ 0) :
    W.Equation ((W.Φ 2).eval x / W.Ψ₂Sq.eval x)
      ((W.preΨ₄.eval x -
          (W.ψ 2).evalEval x y * (W.a₁ * (W.Φ 2).eval x + W.a₃ * W.Ψ₂Sq.eval x)) /
        (2 * (W.ψ 2).evalEval x y ^ 3)) := by
  have H := equation_of_hasPreΩSq (W := W) (n := 2) W.hasPreΩSq_two h h2 hψ
  rwa [if_pos (even_two (α := ℤ)), one_mul, preΩ_two, ΨSq_two] at H

end Affine

end WeierstrassCurve
