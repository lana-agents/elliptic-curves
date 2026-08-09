/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import EllipticCurves.Torsion.DivisionPolynomialEval

/-!
# Closed points of an affine Weierstrass curve from its affine points

For a Weierstrass curve `W` over a field `F`, an affine point `(x, y)` lying on `W`
(`h : W.Equation x y`) cuts out the ideal `⟨X - x, Y - y⟩` of the affine coordinate ring `F[W]`.
Mathlib already knows this ideal — `WeierstrassCurve.Affine.CoordinateRing.XYIdeal W x (C y)` — and
that the quotient of `F[W]` by it is the base field `F`
(`WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv`). Hence the ideal is **maximal**,
in particular a nonzero prime, i.e. a **closed point** of the affine curve.

This file records those facts and packages the closed point as an element of the height-one prime
spectrum `IsDedekindDomain.HeightOneSpectrum F[W]` — the point-to-closed-point bridge that the
order-of-vanishing / divisor calculus (`EllipticCurves.FunctionField.Divisors`) and the eventual
divisor-theoretic Weil pairing (issue #244) consume. Composing with the order-of-vanishing map `ord`
of that file, `ord (pointClosedPoint h) f` is the order of vanishing of a rational function `f` at
the affine point `(x, y)`, and the divisor `f_P` with `div f_P = n·(P) − n·(O)` becomes expressible.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal` : `⟨X - x, Y - y⟩` is maximal.
* `WeierstrassCurve.Affine.CoordinateRing.ker_evalEvalHom` : it is the kernel of the
  evaluation-at-`(x, y)` homomorphism `evalEvalHom h : F[W] → F` — the concrete description of the
  closed point "as the locus where `evalEvalHom` vanishes".
* `WeierstrassCurve.Affine.CoordinateRing.pointClosedPoint` : the closed point of `F[W]` (an
  `IsDedekindDomain.HeightOneSpectrum`) attached to an affine point `(x, y)` on `W`.

## Design / the Dedekind hypothesis

Maximality of `⟨X - x, Y - y⟩` needs only that `F` is a field; the closed-point *packaging*
`pointClosedPoint` additionally carries `[IsDedekindDomain W.CoordinateRing]`, since
`HeightOneSpectrum` is defined for a Dedekind domain. On a nonsingular curve this holds (see
`EllipticCurves.Torsion.CoordinateRingDedekind`, modulo the normality input); keeping it as a
hypothesis decouples the bridge from that discharge, exactly as the order calculus in
`EllipticCurves.FunctionField.Divisors` does.

## References

Silverman, *The Arithmetic of Elliptic Curves*, II.2 (points and maximal ideals), III.8 (the Weil
pairing).
-/

open Polynomial IsDedekindDomain
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} {x y : F}

/-- For an affine point `(x, y)` on `W`, the quotient of the coordinate ring by `⟨X - x, Y - y⟩` is
the base field `F` (`quotientXYIdealEquiv`), so the ideal is **maximal**. -/
theorem XYIdeal_isMaximal (h : W.Equation x y) : (XYIdeal W x (C y)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    (quotientXYIdealEquiv (y := C y) h).toRingEquiv.toMulEquiv.isField (Field.toIsField F)

/-- `⟨X - x, Y - y⟩` is a prime ideal of `F[W]` for an affine point `(x, y)` on `W`. -/
theorem XYIdeal_isPrime (h : W.Equation x y) : (XYIdeal W x (C y)).IsPrime :=
  (XYIdeal_isMaximal h).isPrime

/-- `⟨X - x, Y - y⟩` is nonzero: it contains `X - x ≠ 0` (this needs no hypothesis on `(x, y)`). -/
theorem XYIdeal_ne_bot : XYIdeal W x (C y) ≠ ⊥ := by
  intro hbot
  have hmem : XClass W x ∈ XYIdeal W x (C y) :=
    Ideal.subset_span (Set.mem_insert _ _)
  rw [hbot, Ideal.mem_bot] at hmem
  exact XClass_ne_zero x hmem

lemma evalEvalHom_XClass (h : W.Equation x y) : evalEvalHom h (XClass W x) = 0 := by
  change evalEvalHom h (mk W (C (X - C x))) = 0
  rw [evalEvalHom_mk, evalEval_C]
  simp

lemma evalEvalHom_YClass (h : W.Equation x y) : evalEvalHom h (YClass W (C y)) = 0 := by
  change evalEvalHom h (mk W (Y - C (C y))) = 0
  rw [evalEvalHom_mk]
  simp [Polynomial.evalEval]

/-- The closed point `⟨X - x, Y - y⟩` is exactly the kernel of the evaluation-at-`(x, y)`
homomorphism `evalEvalHom h : F[W] → F`: it is the locus of functions vanishing at `(x, y)`. -/
theorem ker_evalEvalHom (h : W.Equation x y) :
    RingHom.ker (evalEvalHom h) = XYIdeal W x (C y) := by
  refine ((XYIdeal_isMaximal h).eq_of_le ?_ ?_).symm
  · -- the kernel is proper: `evalEvalHom h 1 = 1 ≠ 0`
    rw [Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
    exact one_ne_zero
  · -- `⟨X - x, Y - y⟩ ⊆ ker`, since the two generators vanish at `(x, y)`
    rw [XYIdeal, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨RingHom.mem_ker.mpr (evalEvalHom_XClass h),
      RingHom.mem_ker.mpr (evalEvalHom_YClass h)⟩

variable [IsDedekindDomain W.CoordinateRing]

/-- The **closed point** (height-one prime of `F[W]`) of the affine curve cut out by an affine point
`(x, y)` lying on `W`. Its underlying ideal is `⟨X - x, Y - y⟩ = ker (evalEvalHom h)`. -/
noncomputable def pointClosedPoint (h : W.Equation x y) : HeightOneSpectrum W.CoordinateRing where
  asIdeal := XYIdeal W x (C y)
  isPrime := XYIdeal_isPrime h
  ne_bot := XYIdeal_ne_bot

omit [IsDedekindDomain W.CoordinateRing] in
@[simp]
lemma pointClosedPoint_asIdeal (h : W.Equation x y) :
    (pointClosedPoint h).asIdeal = XYIdeal W x (C y) :=
  rfl

end WeierstrassCurve.Affine.CoordinateRing
