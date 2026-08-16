/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import EllipticCurves.FunctionField.LocalRingUnit
import EllipticCurves.Torsion.CoordinateRingDedekind

/-!
# First-order (Taylor) expansion of the Weierstrass polynomial at a point (normality crux)

This file supplies the next algebraic brick of the **normality crux** (issue #396 Part A /
milestone #469): the first-order Taylor expansion of the Weierstrass polynomial `W(X, Y)` around an
affine point `(x, y)`, and the resulting **cotangent relation** in the coordinate ring `F[W]`.

The milestone `#469` — `(maximalIdeal (Localization.AtPrime (XYIdeal W x (C y)))).IsPrincipal`
at a nonsingular point — is proved by a Nakayama argument whose load-bearing input is exactly this
expansion: writing `u = X - x`, `v = Y - y`, one has the *exact* polynomial identity
```
W(X, Y) = W(x, y) + W_X(x, y)·u + W_Y(x, y)·v + r,   r ∈ (u, v)²,
```
with the explicit quadratic remainder `r = v² + a₁·u·v - (3x + a₂)·u² - u³`.  On the curve
(`W(x, y) = 0`) and after passing to `F[W]` (where `W(X, Y) = 0`), this becomes the cotangent
relation
```
W_X(x, y)·(X - x) + W_Y(x, y)·(Y - y) + r(X - x, Y - y) = 0     in F[W],
```
whose remainder `r(X - x, Y - y)` lies in `(XYIdeal)²`.  Localising at the closed point and using
that the nonzero partial derivative is a unit there (`isUnit_mk_polynomial_of_nonsingular`, #469's
first brick), the class of `Y - y` (resp. `X - x`) is expressible through `X - x` (resp. `Y - y`)
modulo the square of the maximal ideal, which is precisely the Nakayama premise.

## Main statements

* `polynomial_taylor` — the exact bivariate Taylor identity in `F[X][Y]`.
* `mk_polynomial_taylor` — its image in `F[W]`: the cotangent relation
  `W_X·XClass + W_Y·YClass + r = 0`, valid for any affine point `(x, y)` on `W`.
* `maximalIdeal_isPrincipal_of_span_pair` — the ring-level Nakayama step: a Noetherian local ring
  whose maximal ideal is `⟨a, b⟩` with `b ∈ ⟨a⟩ + m²` has principal maximal ideal.
* `maximalIdeal_isPrincipal_of_nonsingular` — **the `#469` milestone**: at a nonsingular point the
  maximal ideal of `Localization.AtPrime ⟨X - x, Y - y⟩` is principal (the Jacobian–uniformizer
  lemma).

## Out of scope (the remaining #469 work)

* `principal maximal ideal ⇒ IsIntegrallyClosed ⇒ IsDedekindDomain` and the
  `of_localization_maximal` assembly; the `F` vs `F̄` closed-point classification.  See `#469`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.1–II.3, III.8.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] (W : Affine F) (x y : F)

/-- **First-order (Taylor) expansion of the Weierstrass polynomial at `(x, y)`.**

Writing `u := X - x` and `v := Y - y` (as elements `C X - CC x` and `Y - CC y` of `F[X][Y]`), the
Weierstrass polynomial `W(X, Y)` decomposes exactly as its value at `(x, y)`, plus the linear part
`W_X(x, y)·u + W_Y(x, y)·v` (with `W_X`, `W_Y` the two partial derivatives), plus an explicit
quadratic remainder `r = v² + a₁·u·v - (3x + a₂)·u² - u³ ∈ (u, v)²`.

This is a pure polynomial identity (no hypothesis on `(x, y)`); on the curve the value `W(x, y)`
vanishes, and passing to `F[W]` gives the cotangent relation `mk_polynomial_taylor`. -/
theorem polynomial_taylor :
    W.polynomial =
      CC (W.polynomial.evalEval x y)
      + CC (W.polynomialX.evalEval x y) * (C X - CC x)
      + CC (W.polynomialY.evalEval x y) * (Y - CC y)
      + ((Y - CC y) ^ 2 + CC W.a₁ * (C X - CC x) * (Y - CC y)
          - CC (3 * x + W.a₂) * (C X - CC x) ^ 2 - (C X - CC x) ^ 3) := by
  rw [evalEval_polynomial, evalEval_polynomialX, evalEval_polynomialY]
  simp only [polynomial, CC, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring1

/-- **The cotangent relation in `F[W]`.**

Passing the Taylor expansion `polynomial_taylor` through the quotient map `mk W : F[X][Y] → F[W]`
(which kills `W.polynomial`) and using that `(x, y)` lies on the curve (`W(x, y) = 0`) yields the
linear-plus-quadratic relation between the closed-point generators `XClass W x = X - x` and
`YClass W (C y) = Y - y`:
```
W_X(x, y)·(X - x) + W_Y(x, y)·(Y - y) + r = 0,
```
where `W_X`, `W_Y` are the partial derivatives evaluated at `(x, y)` and `r` is the image of the
quadratic remainder.  Localised at the closed point, the summand `r` lies in the square of the
maximal ideal, and — once the partial derivative that is nonzero is inverted — this expresses one
generator through the other modulo `m²`, the Nakayama premise for `#469`. -/
theorem mk_polynomial_taylor (h : W.Equation x y) :
    mk W (CC (W.polynomialX.evalEval x y)) * XClass W x
      + mk W (CC (W.polynomialY.evalEval x y)) * YClass W (C y)
      + (YClass W (C y) ^ 2 + mk W (CC W.a₁) * XClass W x * YClass W (C y)
          - mk W (CC (3 * x + W.a₂)) * XClass W x ^ 2 - XClass W x ^ 3) = 0 := by
  have hpoly :
      CC (W.polynomialX.evalEval x y) * (C X - CC x)
        + CC (W.polynomialY.evalEval x y) * (Y - CC y)
        + ((Y - CC y) ^ 2 + CC W.a₁ * (C X - CC x) * (Y - CC y)
            - CC (3 * x + W.a₂) * (C X - CC x) ^ 2 - (C X - CC x) ^ 3)
        = W.polynomial - CC (W.polynomial.evalEval x y) := by
    nth_rewrite 1 [polynomial_taylor W x y]; ring
  have key :
      mk W (CC (W.polynomialX.evalEval x y) * (C X - CC x)
        + CC (W.polynomialY.evalEval x y) * (Y - CC y)
        + ((Y - CC y) ^ 2 + CC W.a₁ * (C X - CC x) * (Y - CC y)
            - CC (3 * x + W.a₂) * (C X - CC x) ^ 2 - (C X - CC x) ^ 3)) = 0 := by
    rw [hpoly, map_sub, AdjoinRoot.mk_self, show W.polynomial.evalEval x y = 0 from h]
    simp [CC]
  simp only [map_add, map_sub, map_mul, map_pow, XClass, YClass, CC] at key ⊢
  linear_combination key

/-- **Nakayama uniformizer criterion.**  In a Noetherian local ring `R`, if the maximal ideal is
generated by two elements `a`, `b` and the second lies in `⟨a⟩ + m²`, then the maximal ideal is
principal (generated by `a`).  This is the ring-level Nakayama step that turns the localised
cotangent relation into principality. -/
theorem maximalIdeal_isPrincipal_of_span_pair {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {a b : R}
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {a, b})
    (hb : b ∈ Ideal.span {a} ⊔
        IsLocalRing.maximalIdeal R * IsLocalRing.maximalIdeal R) :
    (IsLocalRing.maximalIdeal R).IsPrincipal := by
  have ha : a ∈ IsLocalRing.maximalIdeal R :=
    hm ▸ Ideal.subset_span (Set.mem_insert _ _)
  refine ⟨a, le_antisymm ?_ ?_⟩
  · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal R)
      (IsNoetherian.noetherian _) ?_ ?_
    · exact le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).symm
    · conv_lhs => rw [hm]
      rw [Ideal.smul_eq_mul, Ideal.span_insert]
      exact sup_le le_sup_left (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact ha

/-- **A nonzero constant is a unit in the coordinate ring.**  For `c ≠ 0` in the field `F`, the
class `mk W (CC c)` (`= algebraMap F F[W] c`) is a unit. -/
theorem isUnit_mk_CC {c : F} (hc : c ≠ 0) : IsUnit (mk W (CC c)) := by
  have h1 : mk W (CC c) * mk W (CC c⁻¹) = 1 := by
    simp only [CC, ← map_mul, mul_inv_cancel₀ hc, map_one]
  exact (Units.mkOfMulEqOne _ _ h1).isUnit

/-- **The Jacobian–uniformizer lemma (`#469` milestone).**  At a nonsingular affine point `(x, y)`
of `W`, the maximal ideal of the local ring `Localization.AtPrime ⟨X - x, Y - y⟩` is **principal**.

The proof localises the cotangent relation `mk_polynomial_taylor`: the maximal ideal `m` is
generated by the images `X - x`, `Y - y`; the quadratic remainder lands in `m²`; and the nonzero
partial
derivative — a nonzero constant, hence a unit — lets one generator be solved for in terms of the
other modulo `m²`, so Nakayama (`maximalIdeal_isPrincipal_of_span_pair`) collapses `m` to a single
uniformizer.  This is the local-normality input for `IsIntegrallyClosed W.CoordinateRing` (over an
algebraically closed base, via `IsIntegrallyClosed.of_localization_maximal`) and hence for
`IsDedekindDomain W.CoordinateRing` (`#396` Part A). -/
theorem maximalIdeal_isPrincipal_of_nonsingular (h : W.Nonsingular x y)
    [(XYIdeal W x (C y)).IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime (XYIdeal W x (C y)))).IsPrincipal := by
  set Rp := Localization.AtPrime (XYIdeal W x (C y)) with hRp
  set φ := algebraMap W.CoordinateRing Rp with hφ
  set X' := φ (XClass W x) with hX'
  set Y' := φ (YClass W (C y)) with hY'
  set m := IsLocalRing.maximalIdeal Rp with hm
  -- (1) the maximal ideal is the span of the two generator images
  have hmap : Ideal.map φ (XYIdeal W x (C y)) = m :=
    Localization.AtPrime.map_eq_maximalIdeal
  have hmspan : m = Ideal.span {X', Y'} := by
    rw [← hmap]
    change Ideal.map φ (Ideal.span {XClass W x, YClass W (C y)}) = Ideal.span {X', Y'}
    rw [Ideal.map_span, Set.image_pair]
  have hXm : X' ∈ m := by rw [hmspan]; exact Ideal.subset_span (by simp)
  have hYm : Y' ∈ m := by rw [hmspan]; exact Ideal.subset_span (by simp)
  -- (2) the localised cotangent relation
  have hrel : φ (mk W (CC (W.polynomialX.evalEval x y))) * X'
      + φ (mk W (CC (W.polynomialY.evalEval x y))) * Y'
      + (Y' ^ 2 + φ (mk W (CC W.a₁)) * X' * Y'
          - φ (mk W (CC (3 * x + W.a₂))) * X' ^ 2 - X' ^ 3) = 0 := by
    have H := congrArg φ (mk_polynomial_taylor W x y h.1)
    simpa only [map_zero, map_add, map_mul, map_pow, map_sub, ← hX', ← hY'] using H
  -- (3) the quadratic remainder lies in m²
  set Q := Y' ^ 2 + φ (mk W (CC W.a₁)) * X' * Y'
      - φ (mk W (CC (3 * x + W.a₂))) * X' ^ 2 - X' ^ 3 with hQdef
  have hXX : X' * X' ∈ m * m := Ideal.mul_mem_mul hXm hXm
  have hXY : X' * Y' ∈ m * m := Ideal.mul_mem_mul hXm hYm
  have hYY : Y' * Y' ∈ m * m := Ideal.mul_mem_mul hYm hYm
  have hQ : Q ∈ m * m := by
    have hQ' : Q = Y' * Y' + φ (mk W (CC W.a₁)) * (X' * Y')
        - φ (mk W (CC (3 * x + W.a₂))) * (X' * X') - X' * (X' * X') := by rw [hQdef]; ring
    rw [hQ']
    exact Ideal.sub_mem _ (Ideal.sub_mem _
      (Ideal.add_mem _ hYY (Ideal.mul_mem_left _ _ hXY))
      (Ideal.mul_mem_left _ _ hXX)) (Ideal.mul_mem_left _ _ hXX)
  -- (4) case split on which partial derivative is nonzero
  rcases h.2 with hX0 | hY0
  · -- `W_X(x, y) ≠ 0`: solve `X'` through `Y'` mod `m²`; uniformizer `Y'`
    have hu : IsUnit (φ (mk W (CC (W.polynomialX.evalEval x y)))) :=
      (isUnit_mk_CC W hX0).map φ
    have hmem : X' ∈ Ideal.span {Y'} ⊔ m * m := by
      have hin : φ (mk W (CC (W.polynomialX.evalEval x y))) * X'
          ∈ Ideal.span {Y'} ⊔ m * m := by
        have he : φ (mk W (CC (W.polynomialX.evalEval x y))) * X'
            = -(φ (mk W (CC (W.polynomialY.evalEval x y))) * Y') - Q := by
          linear_combination hrel
        rw [he]
        exact Ideal.sub_mem _
          (Ideal.mem_sup_left (neg_mem
            (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))))
          (Ideal.mem_sup_right hQ)
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hin
    exact maximalIdeal_isPrincipal_of_span_pair
      (hmspan.trans (congrArg _ (Set.pair_comm _ _))) hmem
  · -- `W_Y(x, y) ≠ 0`: solve `Y'` through `X'` mod `m²`; uniformizer `X'`
    have hu : IsUnit (φ (mk W (CC (W.polynomialY.evalEval x y)))) :=
      (isUnit_mk_CC W hY0).map φ
    have hmem : Y' ∈ Ideal.span {X'} ⊔ m * m := by
      have hin : φ (mk W (CC (W.polynomialY.evalEval x y))) * Y'
          ∈ Ideal.span {X'} ⊔ m * m := by
        have he : φ (mk W (CC (W.polynomialY.evalEval x y))) * Y'
            = -(φ (mk W (CC (W.polynomialX.evalEval x y))) * X') - Q := by
          linear_combination hrel
        rw [he]
        exact Ideal.sub_mem _
          (Ideal.mem_sup_left (neg_mem
            (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))))
          (Ideal.mem_sup_right hQ)
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hin
    exact maximalIdeal_isPrincipal_of_span_pair hmspan hmem

end CoordinateRing

end WeierstrassCurve.Affine
