/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.Localization.AtPrime.Basic
import EllipticCurves.FunctionField.PointClosedPoint

/-!
# The first-order (Taylor) expansion of `W.polynomial` and the cotangent relation (normality crux)

This file supplies the **Taylor / first-order expansion** brick of the normality crux (issue #396
Part A / milestone #469).  It is the exact polynomial identity expressing the Weierstrass polynomial
`W(X, Y)` as its first-order part around a point `(x, y)` plus a remainder lying in the square
of the ideal `⟨X - x, Y - y⟩`, together with the resulting **cotangent-space relation** in the
ring `F[W]`.

## The mathematics

For any `(x, y)` (no on-curve hypothesis needed for the polynomial identity), Taylor's theorem for
the quadratic-in-`Y`, cubic-in-`X` polynomial `W(X, Y)` reads
```
W(X, Y) = W(x, y)
        + W_X(x, y)·(X - x) + W_Y(x, y)·(Y - y)
        + [ (Y - y)² + a₁·(X - x)·(Y - y) − (3x + a₂)·(X - x)² − (X - x)³ ],
```
where `W_X, W_Y` are the two partial derivatives `polynomialX`, `polynomialY` and the bracketed
remainder manifestly lies in `⟨X - x, Y - y⟩²` (every monomial is a product of at least two of
`X - x`, `Y - y`).  This is `polynomial_taylor` below (an identity in `R[X][Y]` over a `CommRing`).

Passing to the coordinate ring `F[W] = R[X][Y] ⧸ (W.polynomial)`, where `mk W W.polynomial = 0`,
and using that `(x, y)` lies on `W` (so `W(x, y) = 0`), the first-order part must itself lie in
`⟨X - x, Y - y⟩²`:
```
W_X(x, y)·[X - x] + W_Y(x, y)·[Y - y]  ∈  ⟨X - x, Y - y⟩².
```
This is `taylor_cotangent_mem_sq` — precisely the linear relation in the cotangent space
`m/m²` (with scalar coefficients `W_X(x, y)`, `W_Y(x, y)`) that the Nakayama step of `#469` uses:
combined with the unit fact `isUnit_mk_polynomial{X,Y}_of_nonsingular` (`LocalRingUnit.lean`, #185),
it collapses the two generators of the maximal ideal to a single uniformizer.

## Main statements

* `polynomial_taylor` — the exact first-order expansion of `W.polynomial` in `R[X][Y]`.
* `taylor_cotangent_mem_sq` — the cotangent relation
  `W_X(x,y)·XClass + W_Y(x,y)·YClass ∈ (XYIdeal W x (C y))²` at an on-curve point.

## Out of scope (the remaining #469 work)

* The **Nakayama** step producing the single uniformizer from this relation plus the unit fact of
  `LocalRingUnit.lean`, and hence `(maximalIdeal (Localization.AtPrime (XYIdeal …))).IsPrincipal`.
* The passage `principal ⇒ IsIntegrallyClosed ⇒ IsDedekindDomain` and the `F` vs `F̄`
  classification / integral descent (see `#469`).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.1–II.3, III.8.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {R : Type*} [CommRing R] {W : Affine R} {x y : R}

/-- **The first-order (Taylor) expansion of the Weierstrass polynomial around `(x, y)`.**

An exact identity in `R[X][Y]`: `W(X, Y)` equals the constant value `W(x, y)`, plus its first-order
part `W_X(x, y)·(X - x) + W_Y(x, y)·(Y - y)` (with the two partial derivatives evaluated at
`(x, y)`), plus a remainder every monomial of which is a product of at least two of `X - x`,
`Y - y` — hence lies in `⟨X - x, Y - y⟩²`. -/
theorem polynomial_taylor (x y : R) :
    W.polynomial =
      C (C (W.polynomialX.evalEval x y)) * C (X - C x)
        + C (C (W.polynomialY.evalEval x y)) * (Y - C (C y))
        + C (C (W.polynomial.evalEval x y))
        + ((Y - C (C y)) ^ 2 + C (C W.a₁) * C (X - C x) * (Y - C (C y))
            - C (C (3 * x + W.a₂)) * C (X - C x) ^ 2 - C (X - C x) ^ 3) := by
  rw [evalEval_polynomialX, evalEval_polynomialY, evalEval_polynomial]
  simp only [polynomial, map_ofNat, C_add, C_sub, C_mul, C_pow]
  ring1

/-- **The cotangent-space relation at an on-curve point.**

For `(x, y)` on `W` (`h : W.Equation x y`), the first-order part of the Taylor expansion of the
Weierstrass polynomial lies in the square of the closed-point ideal `⟨X - x, Y - y⟩`:
```
W_X(x, y)·[X - x] + W_Y(x, y)·[Y - y]  ∈  ⟨X - x, Y - y⟩².
```
Indeed, applying the quotient map `mk W` to `polynomial_taylor` kills `W.polynomial` (its own root)
and, since `W(x, y) = 0`, the constant term, leaving the first-order part equal to minus the
image of the Taylor remainder — every monomial a product of at least two of `XClass`, `YClass`,
hence lies in `⟨X - x, Y - y⟩²`.  This is the linear relation among the two generators of the
maximal ideal in the cotangent space `m/m²`; combined with the unit fact
`isUnit_mk_polynomial{X,Y}_of_nonsingular` it drives the Nakayama step producing a single
uniformizer (`#469`). -/
theorem taylor_cotangent_mem_sq {W : Affine R} {x y : R} (h : W.Equation x y) :
    mk W (C (C (W.polynomialX.evalEval x y))) * XClass W x
        + mk W (C (C (W.polynomialY.evalEval x y))) * YClass W (C y)
      ∈ (XYIdeal W x (C y)) ^ 2 := by
  -- Generators of the closed-point ideal.
  have hX : XClass W x ∈ XYIdeal W x (C y) := Ideal.subset_span (Set.mem_insert _ _)
  have hY : YClass W (C y) ∈ XYIdeal W x (C y) :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  -- Apply the quotient map to the Taylor identity: `W.polynomial` is its own root, and on the curve
  -- the constant term `W(x, y)` vanishes.
  have hmk := congrArg (mk W) (polynomial_taylor (W := W) x y)
  rw [AdjoinRoot.mk_self, show W.polynomial.evalEval x y = 0 from h] at hmk
  -- Make the leaf polynomials opaque so distributing `mk W` does not split the constants `C`
  -- through the inner subtractions of `X - x` and `Y - y` (folds inside `hmk` too).
  set u : R[X][Y] := C (X - C x) with hu
  set v : R[X][Y] := Y - C (C y) with hv
  set c2 : R := 3 * x + W.a₂ with hc2
  -- `mk W u = XClass W x`, `mk W v = YClass W (C y)` by definition.
  have bX : XClass W x = mk W u := rfl
  have bY : YClass W (C y) = mk W v := rfl
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, add_zero] at hmk
  -- From `0 = firstOrder + remainder`, read off `firstOrder = -remainder`.
  have key : mk W (C (C (W.polynomialX.evalEval x y))) * XClass W x
      + mk W (C (C (W.polynomialY.evalEval x y))) * YClass W (C y)
      = -(YClass W (C y) ^ 2
          + mk W (C (C W.a₁)) * XClass W x * YClass W (C y)
          - mk W (C (C c2)) * XClass W x ^ 2 - XClass W x ^ 3) := by
    rw [bX, bY, eq_neg_iff_add_eq_zero]; linear_combination -hmk
  rw [key, pow_two]
  -- Every monomial of the remainder is a product of two of `XClass`, `YClass`.
  refine neg_mem (Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_) ?_)
  · -- `YClass ^ 2 = YClass * YClass`
    rw [pow_two]; exact Ideal.mul_mem_mul hY hY
  · -- `c₁ * XClass * YClass = c₁ * (XClass * YClass)`
    rw [mul_assoc]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hX hY)
  · -- `c₂ * XClass ^ 2`
    rw [pow_two]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hX hX)
  · -- `XClass ^ 3 = XClass * (XClass * XClass)`
    have h3 : XClass W x ^ 3 = XClass W x * (XClass W x * XClass W x) := by ring
    rw [h3]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hX hX)

end CoordinateRing

end WeierstrassCurve.Affine
