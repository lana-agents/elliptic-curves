/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import EllipticCurves.FunctionField.CoordinateRingNormalAlgClosed
import EllipticCurves.FunctionField.CoordinateRingBaseChange
import EllipticCurves.FunctionField.IntegrallyClosedDescent
import EllipticCurves.Torsion.CoordinateRingDedekind

/-!
# Normality of the affine coordinate ring over an arbitrary field

Let `W` be an elliptic curve (`[W.IsElliptic]`) over an **arbitrary** field `F`. This file removes
the algebraic-closedness hypothesis from the normality results, proving that `W.CoordinateRing` is
integrally closed — hence a Dedekind domain — with no assumption on `F` beyond that it is a field.

## Strategy (faithfully-flat descent from the algebraic closure)

Let `K := AlgebraicClosure F` and `B := (W.map (algebraMap F K)).CoordinateRing`.

* `B` is integrally closed by `isIntegrallyClosed_of_isAlgClosed` (the algebraically-closed case),
  since `K` is algebraically closed and `W.map (algebraMap F K)` is again elliptic.
* `B` is a faithfully-flat `W.CoordinateRing`-algebra by
  `instFaithfullyFlatCoordinateRingMap` (base change of the coordinate ring).
* `IsIntegrallyClosed.of_faithfullyFlat` descends integral-closedness from `B` to
  `W.CoordinateRing`.

The Dedekind-domain conclusion then follows from the conditional
`CoordinateRing.isDedekindDomain`.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.instIsIntegrallyClosed`
* `WeierstrassCurve.Affine.CoordinateRing.instIsDedekindDomain`

Both are registered as instances, so every downstream consumer that previously carried an explicit
`[IsDedekindDomain W.CoordinateRing]` hypothesis now has it discharged automatically for any
elliptic curve over any field.
-/

open Polynomial

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]

/-- **The affine coordinate ring of an elliptic curve over an arbitrary field is integrally
closed.** Proved by faithfully-flat descent of integral-closedness from the algebraic closure
`K := AlgebraicClosure F`, where the base-changed coordinate ring
`(W.map (algebraMap F K)).CoordinateRing` is integrally closed by the algebraically-closed case. -/
instance instIsIntegrallyClosed : IsIntegrallyClosed W.CoordinateRing := by
  have hB : IsIntegrallyClosed (W.map (algebraMap F (AlgebraicClosure F))).CoordinateRing :=
    isIntegrallyClosed_of_isAlgClosed
  exact IsIntegrallyClosed.of_faithfullyFlat (A := W.CoordinateRing)
    (B := (W.map (algebraMap F (AlgebraicClosure F))).CoordinateRing)

/-- **The affine coordinate ring of an elliptic curve over an arbitrary field is a Dedekind
domain.** Follows from `instIsIntegrallyClosed` via the conditional `isDedekindDomain`. -/
instance instIsDedekindDomain : IsDedekindDomain W.CoordinateRing :=
  isDedekindDomain

end WeierstrassCurve.Affine.CoordinateRing
