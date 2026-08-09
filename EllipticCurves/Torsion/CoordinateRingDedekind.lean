/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Dedekind-domain pillars of the affine coordinate ring of a Weierstrass curve

For a Weierstrass curve `W` over a field `F`, its affine coordinate ring
`F[W] = AdjoinRoot W.polynomial` (Mathlib `WeierstrassCurve.Affine.CoordinateRing`) is a rank-two
free module over `F[X]` with basis `{1, Y}`. This file records the *ring-theoretic* consequences of
that finiteness that are needed to build the divisor / order-of-vanishing calculus on `F(W)` (the
foundation for a divisor-theoretic Weil pairing, project issue #244): namely that `F[W]` satisfies
two of the three defining conditions of a Dedekind domain, and that the third reduces to a single
normality statement.

Recall (`Mathlib/RingTheory/DedekindDomain/Basic.lean`) that a domain is a **Dedekind domain**
iff it is

1. Noetherian,
2. of Krull dimension `≤ 1`, and
3. integrally closed in its fraction field.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.instModuleFinite` /
  `WeierstrassCurve.Affine.CoordinateRing.instModuleFree`: `F[W]` is a finite, free `F[X]`-module
  (from `Polynomial.Monic.finite_adjoinRoot`/`free_adjoinRoot` applied to `monic_polynomial`).
* `WeierstrassCurve.Affine.CoordinateRing.instIsNoetherianRing`: pillar 1 — `F[W]` is Noetherian,
  being module-finite over the Noetherian ring `F[X]`.
* `WeierstrassCurve.Affine.CoordinateRing.instDimensionLEOne`: pillar 2 — `F[W]` has Krull
  dimension `≤ 1`, being integral over the dimension-one ring `F[X]` (a PID).
* `WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain`: pillar 3 supplies the rest —
  **assuming `F[W]` is integrally closed**, it is a Dedekind domain. This isolates the full
  Dedekind statement to exactly the integral-closedness (normality) of the coordinate ring.

## The remaining gap: integral closedness (normality)

The integrally-closed hypothesis of `isDedekindDomain` is *not* discharged here, and (as of the
current Mathlib pin) cannot be discharged from existing API. It is equivalent to the coordinate ring
being **normal**, which for the coordinate ring of a curve is equivalent to the curve being
nonsingular. Mathlib has no `RegularRing → IsIntegrallyClosed` (Serre R1+S2 / Auslander–Buchsbaum)
result, no integral-closedness criterion for `AdjoinRoot`, and no bridge from the pointwise
nonsingularity API (`WeierstrassCurve.Affine.Nonsingular`, `Δ` a unit) to normality of the ring.
The intended route — showing every localization of `F[W]` at a maximal ideal is a DVR (via the
Jacobian/nonsingularity criterion) and invoking `IsIntegrallyClosed.of_localization_maximal` — needs
DVR-at-each-closed-point machinery for the coordinate ring that does not yet exist. So this file
deliberately carries integral closedness as a hypothesis; discharging it is a separate,
substantial piece of work.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.1, II.3 (curves and
  divisors), III.8 (the Weil pairing).
-/

open Module Polynomial

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}

/-- The affine coordinate ring `F[W]` is a finite `F[X]`-module: it is `AdjoinRoot` of the monic
`Y`-polynomial `W.polynomial`, hence free of rank `2` (basis `{1, Y}`). -/
instance instModuleFinite : Module.Finite F[X] W.CoordinateRing :=
  monic_polynomial.finite_adjoinRoot

/-- The affine coordinate ring `F[W]` is a free `F[X]`-module (of rank `2`). -/
instance instModuleFree : Module.Free F[X] W.CoordinateRing :=
  monic_polynomial.free_adjoinRoot

/-- **Dedekind pillar 1.** The affine coordinate ring `F[W]` is a Noetherian ring: it is
module-finite over the Noetherian ring `F[X]`. -/
instance instIsNoetherianRing : IsNoetherianRing W.CoordinateRing :=
  IsNoetherianRing.of_finite F[X] W.CoordinateRing

/-- **Dedekind pillar 2.** The affine coordinate ring `F[W]` has Krull dimension `≤ 1`: it is a
domain integral over the dimension-one ring `F[X]` (a PID, since `F` is a field). -/
instance instDimensionLEOne : Ring.DimensionLEOne W.CoordinateRing :=
  Ring.DimensionLEOne.of_isIntegral (R := F[X]) W.CoordinateRing

/-- **Dedekind pillar 3 (conditional).** The affine coordinate ring `F[W]` of a Weierstrass curve
over a field is a Dedekind domain, *provided it is integrally closed*. The Noetherian and
dimension-`≤ 1` conditions hold unconditionally (`instIsNoetherianRing`, `instDimensionLEOne`); the
integral-closedness (normality) hypothesis is the only remaining input, and is left as a typeclass
assumption because it has no support in the current Mathlib API (see the module docstring). -/
theorem isDedekindDomain [IsIntegrallyClosed W.CoordinateRing] :
    IsDedekindDomain W.CoordinateRing :=
  (isDedekindDomain_iff W.CoordinateRing (FractionRing W.CoordinateRing)).mpr
    ⟨inferInstance, inferInstance, inferInstance,
      fun {_} => (isIntegrallyClosed_iff (FractionRing W.CoordinateRing)).mp inferInstance⟩

end WeierstrassCurve.Affine.CoordinateRing
