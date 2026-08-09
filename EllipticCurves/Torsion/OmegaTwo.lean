/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.DivisionPolynomialEval

/-!
# The `2`-division `y`-coordinate and the doubling map is on the curve

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` develops the
`x`-coordinate division polynomials (`ψ₂, Ψ₂Sq, Ψ₃, preΨ₄, ΨSq, Ψ, Φ, ψ, φ`) but explicitly leaves
the *`y`-coordinate* division polynomials `ωₙ` as a `TODO`. Consequently there is, on the current
pin, no statement that the multiplication-by-`n` point `[n]P = (Φₙ/ΨSqₙ, ωₙ/ψₙ³)` actually lies on
the curve — the *on-curve identity* that the function-field pullback `[n]∗ : F(W) → F(W)` consumes.

This file supplies the crux for the **duplication map** `n = 2` (Silverman AEC, Exercise 3.7).

The heavy algebra collapses to a single **univariate** division-polynomial identity
`preΨ₄² = 4Φ₂³ + b₂Φ₂²Ψ₂Sq + 2b₄Φ₂Ψ₂Sq² + b₆Ψ₂Sq³` (`WeierstrassCurve.preΨ₄_sq`), a polynomial
identity in `R[X]` proved by unfolding the definitions and `ring`. Feeding it the point-evaluation
`ψ₂(x,y)² = Ψ₂Sq(x)` (`ψ_sq_evalEval`) and clearing denominators, the full on-curve identity for the
doubled point follows: over a field of characteristic `≠ 2`, for a point `(x, y)` on `W` with
`ψ₂(x, y) ≠ 0` (i.e. `P` is not `2`-torsion), the point
`(Φ₂(x)/Ψ₂Sq(x), ω₂(x,y)/ψ₂(x,y)³)` lies on `W`, where `ω₂(x,y) := (preΨ₄(x) - ψ₂(x,y)·(a₁Φ₂(x) +
a₃Ψ₂Sq(x)))/2` is the value of the `2`-division `y`-coordinate polynomial.

Note that this is a purely *algebraic* on-curve identity for the classical division-polynomial
doubling coordinates; identifying `(Φ₂/Ψ₂Sq, ω₂/ψ₂³)` with the group-law double `2 • P` (which then
makes the on-curve property automatic) is a separate, harder statement not proved here.

## Main statements

* `WeierstrassCurve.preΨ₄_sq`: the univariate identity relating `preΨ₄`, `Φ₂` and `Ψ₂Sq`.
* `WeierstrassCurve.Affine.doubling_equation`: the division-polynomial doubling point lies on the
  curve.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The key univariate division-polynomial identity underlying the duplication formula: the square
of `preΨ₄` is the cubic in `Φ₂` and `Ψ₂Sq` with the `bᵢ` as coefficients. Equivalently, this is the
statement that `(Φ₂/Ψ₂Sq, preΨ₄/(2 ψ₂³))` — up to the linear correction absorbed into `ω₂` — solves
the Weierstrass equation after clearing the `ψ₂²`-denominators. -/
lemma preΨ₄_sq : W.preΨ₄ ^ 2 =
    4 * W.Φ 2 ^ 3 + C W.b₂ * W.Φ 2 ^ 2 * W.Ψ₂Sq + 2 * C W.b₄ * W.Φ 2 * W.Ψ₂Sq ^ 2 +
      C W.b₆ * W.Ψ₂Sq ^ 3 := by
  rw [Φ_two, preΨ₄, Ψ₂Sq, b₂, b₄, b₆, b₈]
  C_simp
  ring1

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
  rw [equation_iff]
  set s := (W.ψ 2).evalEval x y with hsdef
  set Φv := (W.Φ 2).eval x with hΦdef
  set Ψv := W.Ψ₂Sq.eval x with hΨdef
  set Pv := W.preΨ₄.eval x with hPdef
  have hs : s ^ 2 = Ψv := by rw [hsdef, hΨdef, ← ΨSq_two]; exact ψ_sq_evalEval h 2
  have hΨne : Ψv ≠ 0 := by rw [← hs]; exact pow_ne_zero 2 hψ
  have hd : Pv ^ 2 = 4 * Φv ^ 3 + W.b₂ * Φv ^ 2 * Ψv + 2 * W.b₄ * Φv * Ψv ^ 2 + W.b₆ * Ψv ^ 3 := by
    have H := congrArg (eval x) W.preΨ₄_sq
    simpa only [hΦdef, hΨdef, hPdef, eval_mul, eval_pow, eval_add, eval_C, eval_ofNat] using H
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hd
  field_simp
  linear_combination ((-4) * Ψv ^ 5 * W.a₆ + (-1) * Ψv ^ 5 * W.a₃ ^ 2 + (-4) * Φv * Ψv ^ 4 * W.a₄ +
    (-2) * Φv * Ψv ^ 4 * W.a₁ * W.a₃ + (-4) * Φv ^ 2 * Ψv ^ 3 * W.a₂ +
    (-1) * Φv ^ 2 * Ψv ^ 3 * W.a₁ ^ 2 + (-4) * Φv ^ 3 * Ψv ^ 2 + 2 * s * Ψv ^ 3 * Pv * W.a₃ +
    2 * s * Φv * Ψv ^ 2 * Pv * W.a₁ + (-4) * s ^ 2 * Ψv ^ 4 * W.a₆ +
    (-2) * s ^ 2 * Ψv ^ 4 * W.a₃ ^ 2 + (-4) * s ^ 2 * Φv * Ψv ^ 3 * W.a₄ +
    (-4) * s ^ 2 * Φv * Ψv ^ 3 * W.a₁ * W.a₃ + (-4) * s ^ 2 * Φv ^ 2 * Ψv ^ 2 * W.a₂ +
    (-2) * s ^ 2 * Φv ^ 2 * Ψv ^ 2 * W.a₁ ^ 2 + (-4) * s ^ 2 * Φv ^ 3 * Ψv +
    (-4) * s ^ 4 * Ψv ^ 3 * W.a₆ + (-4) * s ^ 4 * Φv * Ψv ^ 2 * W.a₄ +
    (-4) * s ^ 4 * Φv ^ 2 * Ψv * W.a₂ + (-4) * s ^ 4 * Φv ^ 3) * hs + Ψv ^ 3 * hd

end Affine

end WeierstrassCurve
