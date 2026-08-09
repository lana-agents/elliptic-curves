/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.Divisors
import EllipticCurves.FunctionField.PointClosedPoint
import EllipticCurves.FunctionField.PrincipalDivisor

/-!
# The affine divisor of the principal function `f_S` is `n·(S)`

For a Weierstrass curve `W` over a field `F` whose coordinate ring `F[W]` is a Dedekind domain, and
a nonzero `n`-torsion point `P = (x, y) ∈ E[n] = W.torsion n`, this file computes the **divisor** of
the rung-1 principal function `f_P` (project issue #401): on the affine chart it is exactly `n·(P)`,
concentrated at the closed point `v₀ = pointClosedPoint` cut out by `P`.

Concretely there is a nonzero `f ∈ F(W)` with

```
divisor W f = Finsupp.single (pointClosedPoint h.1) (n : ℤ)
```

i.e. `ord v f = n` at `v₀` and `0` at every other height-one prime. This is the starting datum the
divisor-theoretic Weil pairing `e_n(S, T) = g_S(X + T) / g_S(X)` consumes (project issue #244).

## The affine-chart caveat

The classical divisor of `f_P` is `n·(P) − n·(O)`. The point at infinity `O` is **not** a closed
point of the *affine* coordinate ring `F[W]` — the height-one primes `HeightOneSpectrum F[W]` are
precisely the affine closed points — so the `−n·(O)` term lives off this chart and is invisible to
`divisor W`. The affine divisor is therefore exactly `n·(P)`, as proved here. This is the same
affine/projective phenomenon documented in `EllipticCurves.FunctionField.Divisors` (the identity
`deg (div f) = 0` is a statement about the projective completion, deliberately not developed there).

## Route

The rung-1 statement `exists_generator_XYIdeal'_pow_of_torsion` (issue #401) produces a nonzero
generator `f` with `↑(XYIdeal' h ^ n) = ⟨f⟩` as fractional ideals. Mathlib's `XYIdeal'_eq`
identifies `↑(XYIdeal' h)` with the coeIdeal of `(pointClosedPoint).asIdeal`, so
`⟨f⟩ = (v₀.asIdeal)^n`. The order `ord v f = FractionalIdeal.count v ⟨f⟩` is then read off from the
count of a prime power (`count v (v₀.asIdeal ^ n) = n · [v = v₀]`) via `count_pow_self` and
`count_maximal_coprime`.

## Design — Ward- and normality-independent

Everything carries `[IsDedekindDomain W.CoordinateRing]` as an explicit hypothesis, exactly as
`Divisors.lean` / `PointClosedPoint.lean` / `DivisorInjective.lean` do, decoupling this rung from
the research-blocked Part A normality discharge of issue #396. It uses neither the elliptic-net
(Ward) recurrence nor the torsion count `#E[n] = n²`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, II.3 (divisors on curves) and III.8 (the Weil
pairing; the functions `f_P` with `div f_P = n·(P) − n·(O)`).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-- **The order of vanishing of a generator of `(XYIdeal' h)^n` at every closed point.** If `f`
generates the principal fractional ideal `(XYIdeal' h)^n` (the rung-1 generator `f_P` for an
`n`-torsion point, issue #401), then `f` vanishes to order `n` at the closed point
`v₀ = pointClosedPoint` of `(x, y)` and to order `0` everywhere else. Phrased as a value of the
divisor `n·(v₀) = Finsupp.single v₀ n`. -/
theorem ord_generator_eq {x y : F} (h : W.Nonsingular x y) {n : ℕ}
    (f : W.FunctionField)
    (hgen : (↑(CoordinateRing.XYIdeal' (W := W) h ^ n) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      FractionalIdeal.spanSingleton W.CoordinateRing⁰ f)
    (v : HeightOneSpectrum W.CoordinateRing) :
    ord v f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (n : ℤ) v := by
  -- `⟨f⟩ = (v₀.asIdeal)^n` as fractional ideals.
  have hspan : spanSingleton W.CoordinateRing⁰ f =
      ((CoordinateRing.pointClosedPoint h.1).asIdeal :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) ^ n := by
    rw [← hgen, Units.val_pow_eq_pow_val, CoordinateRing.XYIdeal'_eq,
      CoordinateRing.pointClosedPoint_asIdeal]
  rw [ord, hspan]
  by_cases hv : v = CoordinateRing.pointClosedPoint h.1
  · rw [hv, count_pow_self, Finsupp.single_eq_same]
  · have hne : CoordinateRing.pointClosedPoint h.1 ≠ v := fun hc => hv hc.symm
    rw [count_pow, count_maximal_coprime W.FunctionField v hne, mul_zero]
    exact (Finsupp.single_eq_of_ne (b := (n : ℤ)) hv).symm

/-- **The affine divisor of the principal function `f_P` is `n·(P)`.** For a nonzero `n`-torsion
point `P = (x, y) ∈ E[n]`, there is a nonzero rational function `f ∈ F(W)` (the rung-1 generator
`f_P`) whose divisor on the affine chart is `n` times the closed point `v₀ = pointClosedPoint` cut
out by `P`:

`divisor W f = Finsupp.single (pointClosedPoint h.1) (n : ℤ)`.

The classical `−n·(O)` term lives at the point at infinity, off this affine chart (see the module
docstring). This is the starting datum of the divisor-theoretic Weil pairing (issue #244). -/
theorem exists_generator_divisor_eq_of_torsion [DecidableEq F] {x y : F} (h : W.Nonsingular x y)
    {n : ℕ} (hP : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (n : ℤ) := by
  obtain ⟨f, hf, hgen⟩ := exists_generator_XYIdeal'_pow_of_torsion h hP
  refine ⟨f, hf, ?_⟩
  ext v
  rw [divisor_apply, ord_generator_eq h f hgen v]

end WeierstrassCurve.Affine
