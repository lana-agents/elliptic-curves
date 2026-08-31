/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Certificate curves: the shared fixtures the non-vacuity blocks run on

Almost every file in this development ends in a `section Nonvacuity` block whose job is to show
that the results above it are not vacuous — that the hypotheses can be met on a curve that exists.
Those blocks all need the same handful of objects, and until now each one built its own `private`
copy: **164** `IsElliptic` instances across 119 files, of which **142 have a byte-identical
four-line proof** naming `Δ`, `b₂`, `b₄`, `b₆`, `b₈`; **143** curve definitions over **five**
distinct curves; and **72** copies of `AlgebraicClosure ℚ` under six different names.

This module holds the shared layer. ⚠️ **Its declarations exist only to make non-vacuity
certificates non-vacuous. They are not part of the mathematical API**, and no result about
Weierstrass curves in general should be stated in terms of them.

## The design, and the two decisions in it

**The curves are polymorphic in the base ring.** The same five literals occur in the tree both over
`ℚ` and over `AlgebraicClosure ℚ` (and, at three sites, over a finite field), so a definition taking
`[CommRing R]` serves every base at once and one definition replaces a whole column of copies.

**One `IsElliptic` instance per curve, over `[Field F] [CharZero F]`.** Each of the five
discriminants — `64`, `−27`, `−432`, `2304`, `−4096` — is a nonzero integer, so characteristic zero
is the exact hypothesis, and it covers the `ℚ` and `AlgebraicClosure ℚ` sites with a single
instance rather than one per base type.

⚠️ **The finite-field certificates are deliberately NOT served here.**
`EllipticCurves.FunctionField.NegYGaloisGroup` certifies over `ZMod 2` on purpose — its curve
docstring records that `negYAlgEquiv_ne_one` is exactly what would fail for `y² = x³ + …` in
characteristic `2` — and `EllipticCurves.FunctionField.NegYInvolution` and
`EllipticCurves.FunctionField.MulByNDegreeTower` do the same over `ZMod 2` and `ZMod 5`. Those
bases are not of characteristic zero, so the instances below do not apply, and the missing piece is
an import: `Mathlib.FieldTheory.Finite.Basic` is what supplies `Field (ZMod p)` and makes their
`decide +kernel` proofs go through (checked, both directions). It is **not** imported here, because
this module is imported across the library and pulling a finite-field file into every one of those
import closures to serve three certificates is the wrong trade. **Those three keep their local
fixtures**, and a later sweep should not "finish the job" by deleting them: they are the only
positive-characteristic non-vacuity evidence on the `negY` front.

## Characteristic side-conditions

The `#916` blocks also carry **67** copies of `(2 : F) ≠ 0` and **54** of `(3 : F) ≠ 0`, all proved
`by norm_num`. Only one of the two needs anything here:

* `(2 : F) ≠ 0` is **already** Mathlib's `two_ne_zero` in a field of characteristic zero — nothing
  is added below for it, and a call site should use Mathlib's lemma directly.
* `(3 : F) ≠ 0` is not: `three_ne_zero` asks for a `NeZero 3` instance that is not found here, so
  `three_ne_zero_of_charZero` below supplies it.

## Naming

The curves are named after their Weierstrass equations rather than after the roles they play, since
several of them serve more than one role. What each is *for* is recorded in its own docstring; that
information came from the per-file docstrings this module replaces and must not be lost — in
particular `y2EqX3Add5X2Add4X` is the one with split rational `2`-torsion, and `y2AddYEqX3` is the
`n = 3` curve precisely because `y2EqX3SubX` has no rational `3`-torsion point.
-/

namespace EllipticCurves.Fixture

open WeierstrassCurve

/-- An algebraically closed field of characteristic zero, the base of most of the certificates in
this development. -/
abbrev AlgClosedQ : Type := AlgebraicClosure ℚ

/-- `y² = x³ − x = x(x − 1)(x + 1)`, of discriminant `64`.

This tree's standard `n = 2` certificate curve: its `2`-torsion is split and rational, so the
points `(0, 0)`, `(1, 0)`, `(−1, 0)` can be named over any base. ⚠️ It does **not** serve at
`n = 3` — `Ψ₃ = 3X⁴ − 6X² − 1` has no rational root, so none of its nine `3`-torsion points can be
named; `y2AddYEqX3` is the curve for that. -/
def y2EqX3SubX (R : Type*) [CommRing R] : Affine R := ⟨0, 0, 0, -1, 0⟩

/-- `y² + y = x³`, of discriminant `−27`.

This tree's standard `n = 3` certificate curve: `Ψ₃ = 3X⁴ + 3b₆X = 3X(X³ + 1)` factors, so `(0, 0)`
is a rational `3`-torsion point — which is exactly what `y2EqX3SubX` lacks. Over `ZMod 2` the same
equation is supersingular and has `a₁ = 0`, `a₃ = 1`, so `y ↦ −y − a₁x − a₃` is `y ↦ y + 1` and is
not the identity; that is the char-`2` certificate described in the module docstring, and it is not
served here. -/
def y2AddYEqX3 (R : Type*) [CommRing R] : Affine R := ⟨0, 0, 1, 0, 0⟩

/-- `y² = x³ + 1`, of discriminant `−432`.

The certificate curve for the composite-index statements, which need a rational point `P` whose
double is also affine and rational: `(2, 3)` has order `6` and `[2](2, 3) = (0, 1)`. `y2EqX3SubX`
supplies no such pair, which is why `EllipticCurves.FunctionField.WeilPairingAlternatingConsumerN`
says of its own copy *"deliberately not `y² = x³ − x`"*. -/
def y2EqX3AddOne (R : Type*) [CommRing R] : Affine R := ⟨0, 0, 0, 0, 1⟩

/-- `y² = x³ + 5x² + 4x = x(x + 1)(x + 4)`, of discriminant `2304`.

⚠️ Chosen for **split rational `2`-torsion**: the cubic factors over `ℚ` with three distinct roots
`0`, `−1`, `−4`, so all three nontrivial `2`-torsion points are rational. That is the entire content
of the four certificates that use it (`Torsion.TwoTorsion`, `Torsion.DoublingSurjective`,
`FunctionField.WeilPairingAlternatingTwoRational`,
`FunctionField.PullbackPrincipalityTwoRationalTorsion`), and substituting another curve there would
leave them green and vacuous. -/
def y2EqX3Add5X2Add4X (R : Type*) [CommRing R] : Affine R := ⟨0, 5, 0, 4, 0⟩

/-- `y² = x³ + 4x`, of discriminant `−4096`.

Chosen for the shape of its `Φ₂`: `b₂ = 0`, `b₄ = 8`, `b₆ = 0`, `b₈ = −16` give
`Φ₂ = X⁴ − 8X² + 16 = (X² − 4)²`, which vanishes at `x = 2` while the `2`-torsion point `T = (0, 0)`
has `x(T) = 0` — the root that discharges a halving from a polynomial identity in
`EllipticCurves.FunctionField.WeilPairingAlternatingAssemblyN`. ⚠️ It shares `b₄`, `b₆`, `b₈` and
hence `Φ₂` with `y2EqX3Add5X2Add4X`, but **not** `Ψ₂Sq` (`4X³ + 16X` against `4X³ + 20X² + 16X`), so
`Ψ₃` and every evaluation differ; that file's docstring says the same and it is worth repeating
here, because the two curves look interchangeable and are not. -/
def y2EqX3Add4X (R : Type*) [CommRing R] : Affine R := ⟨0, 0, 0, 4, 0⟩

section CharZero

variable (F : Type*) [Field F] [CharZero F]

/-- `(3 : F) ≠ 0` in a field of characteristic zero. Mathlib's `three_ne_zero` asks for a `NeZero 3`
instance that is not available here; the `2` case needs nothing, being Mathlib's `two_ne_zero`. -/
lemma three_ne_zero_of_charZero : (3 : F) ≠ 0 := by norm_num

/-- `Δ = 64 ≠ 0`. -/
instance : (y2EqX3SubX F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [y2EqX3SubX, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `Δ = −27 ≠ 0`. -/
instance : (y2AddYEqX3 F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [y2AddYEqX3, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `Δ = −432 ≠ 0`. -/
instance : (y2EqX3AddOne F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [y2EqX3AddOne, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `Δ = 2304 ≠ 0`. -/
instance : (y2EqX3Add5X2Add4X F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [y2EqX3Add5X2Add4X, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `Δ = −4096 ≠ 0`. -/
instance : (y2EqX3Add4X F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [y2EqX3Add4X, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

end CharZero

end EllipticCurves.Fixture
