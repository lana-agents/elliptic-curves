/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.Localization.AtPrime.Basic
import EllipticCurves.FunctionField.PointClosedPoint

/-!
# Nonsingularity ⇒ a partial derivative is a unit in the local ring (normality crux, first brick)

This file supplies the first algebraic brick of the **normality crux** (issue #396 Part A /
milestone #469): that the localization of the affine coordinate ring `F[W]` at the closed point
`⟨X - x, Y - y⟩` of a nonsingular point `(x, y)` is a discrete valuation ring, hence
`F[W]` is integrally closed, hence Dedekind.

The milestone `#469` reduces to the single Jacobian–uniformizer lemma
`(maximalIdeal (Localization.AtPrime (XYIdeal W x (C y)))).IsPrincipal`, whose hand-built heart is a
first-order (Taylor) expansion of `W.polynomial` around `(x, y)` inside `AdjoinRoot W.polynomial`
plus a Nakayama argument.  That argument needs, as its very first input, the fact that **one of the
two partial derivatives** `W_X = W.polynomialX` and `W_Y = W.polynomialY` — the one that is nonzero
at `(x, y)` by nonsingularity — becomes a **unit** in the localization `Localization.AtPrime …`.
This file delivers exactly that input, unconditionally (no Ward, no normality, no Dedekind
hypothesis).

## Main statements

* `isUnit_mk_polynomialX_of_localization` — if `W_X(x, y) ≠ 0` then the class of `W_X` in any
  localization of `F[W]` at the prime `⟨X - x, Y - y⟩` is a unit.
* `isUnit_mk_polynomialY_of_localization` — the same for `W_Y`, from `W_Y(x, y) ≠ 0`.
* `isUnit_mk_polynomial_of_nonsingular` — the packaged disjunction: at a nonsingular point at least
  one of the two partial-derivative classes is a unit in the localization.

## Route

The class `mk W g ∈ F[W]` of a bivariate polynomial `g` maps to `g.evalEval x y` under the
evaluation homomorphism `evalEvalHom h : F[W] → F` (`evalEvalHom_mk`), whose kernel is precisely the
closed-point ideal `⟨X - x, Y - y⟩ = XYIdeal W x (C y)` (`ker_evalEvalHom`).  Hence `mk W g` lies
**outside** that prime iff `g.evalEval x y ≠ 0`, and an element outside the prime becomes a unit in
the localization at it (`IsLocalization.AtPrime.isUnit_to_map_iff`).  Applying this to
`g = W.polynomialX` / `W.polynomialY`, whose evaluations are the partial derivatives
`W_X(x, y)` / `W_Y(x, y)` (`evalEval_polynomialX` / `evalEval_polynomialY`), gives the unit facts,
and the disjunction defining `W.Nonsingular x y` packages them.

## Out of scope (the remaining #469 work)

* The **Taylor / first-order expansion** of `W.polynomial` inside `AdjoinRoot`
  (`0 = W.polynomial ≡ W_X·(X - x) + W_Y·(Y - y)` mod `(X - x, Y - y)²`) and the **Nakayama** step
  producing the single uniformizer — the mathematical heart of `#469`, still to be built.
* The passage `principal maximal ideal ⇒ IsIntegrallyClosed ⇒ IsDedekindDomain` and the
  `of_localization_maximal` assembly — mechanical once the milestone lands (see `#469`).
* The `F` vs `F̄` closed-point classification / integral descent — a separate follow-on (`#469`).

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.1–II.3, III.8.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **A nonzero-at-`(x, y)` polynomial class is a unit in the local ring at the closed point.**

If a bivariate polynomial `g` does not vanish at the point `(x, y)` on `W` (`hg : g.evalEval x y ≠
0`), then its class `mk W g` in the coordinate ring `F[W]` lies outside the closed-point prime
`⟨X - x, Y - y⟩ = XYIdeal W x (C y)` (the kernel of the evaluation map `evalEvalHom h`), and hence
becomes a **unit** in any localization `S` of `F[W]` at that prime. -/
theorem isUnit_mk_of_evalEval_ne_zero (h : W.Equation x y) {g : F[X][Y]}
    (hg : g.evalEval x y ≠ 0) {S : Type*} [CommRing S] [Algebra W.CoordinateRing S]
    [(XYIdeal W x (C y)).IsPrime] [IsLocalization.AtPrime S (XYIdeal W x (C y))] :
    IsUnit (algebraMap W.CoordinateRing S (mk W g)) := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff S (XYIdeal W x (C y)), Ideal.mem_primeCompl_iff]
  -- `mk W g ∉ XYIdeal` because its image under `evalEvalHom h` is `g.evalEval x y ≠ 0`.
  rw [← ker_evalEvalHom h, RingHom.mem_ker, evalEvalHom_mk]
  exact hg

/-- **The `X`-partial derivative `W_X` is a unit in the local ring at a point where it is nonzero.**
A special case of `isUnit_mk_of_evalEval_ne_zero` at `g = W.polynomialX`, whose evaluation is the
partial derivative `W_X(x, y)` (`evalEval_polynomialX`). -/
theorem isUnit_mk_polynomialX_of_localization (h : W.Equation x y)
    (hX : W.polynomialX.evalEval x y ≠ 0) {S : Type*} [CommRing S] [Algebra W.CoordinateRing S]
    [(XYIdeal W x (C y)).IsPrime] [IsLocalization.AtPrime S (XYIdeal W x (C y))] :
    IsUnit (algebraMap W.CoordinateRing S (mk W W.polynomialX)) :=
  isUnit_mk_of_evalEval_ne_zero h hX

/-- **The `Y`-partial derivative `W_Y` is a unit in the local ring at a point where it is nonzero.**
A special case of `isUnit_mk_of_evalEval_ne_zero` at `g = W.polynomialY`, whose evaluation is the
partial derivative `W_Y(x, y)` (`evalEval_polynomialY`). -/
theorem isUnit_mk_polynomialY_of_localization (h : W.Equation x y)
    (hY : W.polynomialY.evalEval x y ≠ 0) {S : Type*} [CommRing S] [Algebra W.CoordinateRing S]
    [(XYIdeal W x (C y)).IsPrime] [IsLocalization.AtPrime S (XYIdeal W x (C y))] :
    IsUnit (algebraMap W.CoordinateRing S (mk W W.polynomialY)) :=
  isUnit_mk_of_evalEval_ne_zero h hY

/-- **At a nonsingular point, one of the two partial derivatives is a unit in the local ring.**

By definition `W.Nonsingular x y` is `W.Equation x y ∧ (W_X(x, y) ≠ 0 ∨ W_Y(x, y) ≠ 0)`, so at
least one of `mk W W.polynomialX`, `mk W W.polynomialY` avoids the closed-point prime and is a unit
in the localization.  This is the disjunctive input consumed by the Nakayama step that produces the
single uniformizer of the maximal ideal (`#469`). -/
theorem isUnit_mk_polynomial_of_nonsingular (h : W.Nonsingular x y)
    {S : Type*} [CommRing S] [Algebra W.CoordinateRing S]
    [(XYIdeal W x (C y)).IsPrime] [IsLocalization.AtPrime S (XYIdeal W x (C y))] :
    IsUnit (algebraMap W.CoordinateRing S (mk W W.polynomialX)) ∨
      IsUnit (algebraMap W.CoordinateRing S (mk W W.polynomialY)) :=
  h.2.imp (fun hX => isUnit_mk_polynomialX_of_localization h.1 hX)
    (fun hY => isUnit_mk_polynomialY_of_localization h.1 hY)

end CoordinateRing

end WeierstrassCurve.Affine
