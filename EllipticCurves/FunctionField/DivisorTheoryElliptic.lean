/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral
import EllipticCurves.FunctionField.DivisorClassGroup
import EllipticCurves.FunctionField.DivisorInjective
import EllipticCurves.FunctionField.PrincipalDivisorOfPoint

/-!
# The affine divisor theory of an elliptic curve, unconditionally

The core divisor-theoretic results on the affine coordinate ring `F[W]` — that a rational function
is determined up to a unit by its divisor (Abel's theorem, Silverman II.3), that every principal
divisor is trivial in the class group, and that a torsion point cuts out a principal divisor
`n·(P)` — are all developed under an **explicit** hypothesis `[IsDedekindDomain W.CoordinateRing]`
in `DivisorInjective.lean`, `DivisorClassGroup.lean` and `PrincipalDivisorOfPoint.lean`, because at
the time they were written the normality of `F[W]` was not yet available over a general field.

That hypothesis is now discharged: `CoordinateRingNormalGeneral.lean` (issues #476/#479, faithfully-
flat descent from the algebraic closure) registers

```
instance : IsIntegrallyClosed W.CoordinateRing   -- for [W.IsElliptic]
instance : IsDedekindDomain  W.CoordinateRing   -- for [W.IsElliptic]
```

as global instances for **every elliptic curve over an arbitrary field**. This file re-exposes the
headline divisor-theoretic facts with that hypothesis removed — the natural, unconditional public
API for the affine Picard theory of elliptic curves, and the entry point that downstream
Weil-pairing / Picard-group code should consume. Each statement simply delegates to its conditional
counterpart, with `[W.IsElliptic]` firing the normality instance in place of the dropped hypothesis.

## Main results (for `[Field F] {W : Affine F} [W.IsElliptic]`)

* `WeierstrassCurve.Affine.Elliptic.exists_unit_of_ord_eq`
* `WeierstrassCurve.Affine.Elliptic.exists_unit_of_divisor_eq`
* `WeierstrassCurve.Affine.Elliptic.classGroup_mk_toPrincipalIdeal`
* `WeierstrassCurve.Affine.Elliptic.exists_generator_divisor_eq_of_torsion`

## References

Silverman, *The Arithmetic of Elliptic Curves*, II.3 (a rational function is determined up to an
`F*`-scalar by its divisor; the Picard group) and III.8 (the Weil pairing).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal

open scoped nonZeroDivisors

namespace WeierstrassCurve.Affine.Elliptic

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The divisor determines a rational function up to a unit** (order form), for an elliptic curve
over an arbitrary field. If nonzero `f, g ∈ F(W)` have the same order of vanishing at every closed
point, they differ by a unit of the coordinate ring `F[W]`. The
`[IsDedekindDomain W.CoordinateRing]` hypothesis of
`WeierstrassCurve.Affine.exists_unit_of_ord_eq` is discharged by the normality instance
for `[W.IsElliptic]`. -/
theorem exists_unit_of_ord_eq {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ v, ord v f = ord v g) :
    ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • f = g :=
  WeierstrassCurve.Affine.exists_unit_of_ord_eq hf hg h

/-- **The divisor determines a rational function up to a unit** (divisor form), for an elliptic
curve over an arbitrary field. If nonzero `f, g ∈ F(W)` have the same divisor, they differ by a
unit of `F[W]` — Abel's theorem on the affine chart (Silverman II.3). Unconditional in
`[W.IsElliptic]`. -/
theorem exists_unit_of_divisor_eq {f g : W.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : divisor W f = divisor W g) :
    ∃ u : W.CoordinateRingˣ, (u : W.CoordinateRing) • f = g :=
  WeierstrassCurve.Affine.exists_unit_of_divisor_eq hf hg h

/-- **Every principal divisor is class-trivial**, for an elliptic curve over an arbitrary field: the
principal fractional ideal `⟨x⟩` of any nonzero rational function has trivial class in
`ClassGroup F[W]`. Unconditional in `[W.IsElliptic]`. -/
theorem classGroup_mk_toPrincipalIdeal (x : W.FunctionFieldˣ) :
    ClassGroup.mk W.FunctionField
      (toPrincipalIdeal W.CoordinateRing W.FunctionField x) = 1 :=
  WeierstrassCurve.Affine.classGroup_mk_toPrincipalIdeal x

/-- **A nonzero torsion point cuts out a principal divisor `n·(P)`**, for an elliptic curve over an
arbitrary field. For a nonzero `n`-torsion point `P = (x, y) ∈ E[n]` there is a nonzero rational
function `f ∈ F(W)` whose affine divisor is `n` times the closed point cut out by `P`. This is the
starting datum of the divisor-theoretic Weil pairing (issue #244); the classical `−n·(O)` term
lives at the point at infinity, off this affine chart. Unconditional in `[W.IsElliptic]`. -/
theorem exists_generator_divisor_eq_of_torsion [DecidableEq F] {x y : F} (h : W.Nonsingular x y)
    {n : ℕ} (hP : Point.some x y h ∈ W.torsion n) :
    ∃ f : W.FunctionField, f ≠ 0 ∧
      divisor W f = Finsupp.single (CoordinateRing.pointClosedPoint h.1) (n : ℤ) :=
  WeierstrassCurve.Affine.exists_generator_divisor_eq_of_torsion h hP

end WeierstrassCurve.Affine.Elliptic
