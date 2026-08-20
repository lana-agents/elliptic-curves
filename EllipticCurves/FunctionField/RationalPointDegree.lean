/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.DivisorDegree
import EllipticCurves.FunctionField.PrincipalDivisorOfPoint

/-!
# Rational points have degree one, and `div f_P = n·(P) − n·(O)`

`EllipticCurves.FunctionField.DivisorDegree` attaches a degree `degPt v` to every affine closed
point and proves the degree-zero theorem `degDiv (div f) + ordInfty f = 0`.  This file computes
`degPt` at the closed point of an `F`-**rational** point and draws the conclusion the
Weil-pairing rungs have been writing around.

## The affine-chart caveat, closed

`EllipticCurves.FunctionField.PrincipalDivisorOfPoint` (`#409`) produces, for an `n`-torsion point
`P`, a function `f_P` with `divisor W f_P = n·(P)` — and its module docstring has to explain that
the classical divisor is `n·(P) − n·(O)` but that *"the `−n·(O)` term lives off this chart and is
invisible to `divisor W`"*.  With `ordInfty` (`#637`) and the degree-zero theorem (`#642`) that
term is no longer invisible: `ordInfty f_P = −n`, which is exactly `−n·(O)`.

## Main results

* `degPt_pointClosedPoint` — an `F`-rational point is a closed point of **degree one**;
* `ordInfty_of_divisor_eq_single` — a function whose affine divisor is `n·(P)` for a rational `P`
  has a pole of order exactly `n` at infinity;
* `exists_generator_divisor_eq_of_torsion'` — the full **`div f_P = n·(P) − n·(O)`** for the
  torsion generator of `#409`.

## Route

No residue-field computation and no ramification theory is needed, and in particular no case split
on whether `P` is `2`-torsion.  Mathlib's `XYIdeal_neg_mul` says
`⟨X − x, Y − ȳ⟩ · ⟨X − x, Y − y⟩ = ⟨X − x⟩`, i.e. `v_{−P} · v_P = (x − x₀)`.  Applying the
multiplicative `Ideal.relNorm F[X]` and taking degrees turns this into

```
degPt v_{−P} + degPt v_P = deg ((X − x₀)²) = 2,
```

and `degPt_pos` forces both summands to be `1`.  When `P` is `2`-torsion the two points coincide
and the same equation reads `2 · degPt v_P = 2`; the argument does not care.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.3, III.8.
-/

open Polynomial Polynomial.Bivariate IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open FractionalIdeal WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing] {x y : F}

omit [IsDedekindDomain W.CoordinateRing] in
/-- The norm of the coordinate function `x − x₀` is `(X − x₀)²`: it has a double pole at infinity,
matching its two affine zeros `P` and `−P`. -/
lemma norm_XClass (x : F) :
    Algebra.norm F[X] (CoordinateRing.XClass W x) = (X - C x) ^ 2 := by
  have h : CoordinateRing.XClass W x
      = (X - C x) • (1 : W.CoordinateRing) + (0 : F[X]) • CoordinateRing.mk W Y := by
    rw [zero_smul, add_zero, CoordinateRing.smul, mul_one]
    rfl
  rw [h, norm_smul_basis]
  ring

/-- **An `F`-rational point is a closed point of degree one.**

The two closed points `v_P` and `v_{−P}` satisfy `v_{−P} · v_P = ⟨x − x₀⟩` (Mathlib's
`XYIdeal_neg_mul`), whose relative norm is `⟨(X − x₀)²⟩` of degree `2`.  Since `degPt` is additive
along the product and positive at every point, both degrees are `1`.  For `2`-torsion `P` the two
points coincide and the equation reads `2 · degPt v_P = 2` instead; no case split is needed. -/
theorem degPt_pointClosedPoint (h : W.Nonsingular x y) :
    degPt (CoordinateRing.pointClosedPoint h.left) = 1 := by
  have hneg : W.Nonsingular x (W.negY x y) := (nonsingular_neg ..).mpr h
  set v := CoordinateRing.pointClosedPoint h.left with hv
  set v' := CoordinateRing.pointClosedPoint hneg.left with hv'
  have hmul : v'.asIdeal * v.asIdeal = Ideal.span {CoordinateRing.XClass W x} :=
    CoordinateRing.XYIdeal_neg_mul h
  have hnorm := congrArg (Ideal.relNorm F[X]) hmul
  rw [map_mul, Ideal.relNorm_singleton, Algebra.intNorm_eq_norm, norm_XClass] at hnorm
  have hne : ∀ w : HeightOneSpectrum W.CoordinateRing, Ideal.relNorm F[X] w.asIdeal ≠ 0 :=
    fun w => by simpa using (Ideal.relNorm_eq_bot_iff (R := F[X])).not.mpr w.ne_bot
  have hdeg := congrArg Ideal.natDegreeGenerator hnorm
  rw [Ideal.natDegreeGenerator_mul (hne v') (hne v), Ideal.natDegreeGenerator_span,
    natDegree_pow, natDegree_X_sub_C] at hdeg
  have hsum : degPt v' + degPt v = 2 := hdeg
  have h1 := degPt_pos v
  have h2 := degPt_pos v'
  omega

/-- A function whose affine divisor is `n·(P)` for an `F`-rational point `P` has a pole of order
exactly `n` at infinity. -/
theorem ordInfty_of_divisor_eq_single {f : W.FunctionField} (hf : f ≠ 0) (h : W.Nonsingular x y)
    (n : ℤ) (hd : divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.left) n) :
    ordInfty W f = -n := by
  have hz := degDiv_divisor_add_ordInfty hf
  rw [hd, degDiv_single, degPt_pointClosedPoint h] at hz
  omega

/-- **`div f_P = n·(P) − n·(O)`.**  The torsion generator of `#409`, whose affine divisor is
`n·(P)`, has a pole of order exactly `n` at the point at infinity — the classical statement, with
the term that the affine chart could not see now supplied by `ordInfty`. -/
theorem exists_generator_divisor_eq_of_torsion' [DecidableEq F] (h : W.Nonsingular x y) {n : ℕ}
    (hP : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.left) (n : ℤ) ∧
      ordInfty W f = -n := by
  obtain ⟨f, hf, hd⟩ := exists_generator_divisor_eq_of_torsion h hP
  exact ⟨f, hf, hd, ordInfty_of_divisor_eq_single hf h _ hd⟩

end WeierstrassCurve.Affine
