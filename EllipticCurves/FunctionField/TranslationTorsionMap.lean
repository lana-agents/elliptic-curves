/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationTorsion

/-!
# Transporting `n`-torsion from the base field to `F(W)` via the base-change point map

The `hcomm` discharge of the rung-6 Weil-pairing element reads its commuting hypothesis off a
torsion relation *over the function field* `F(W)`.  For the `n = 2` track,
`FunctionField/TranslationTorsion.lean` (#433) discharged the `2`-torsion datum
`translatePoint hT + translatePoint hT = 0` from the base-field relation `T + T = 0` in `W.Point`
by the affine vertical-tangent characterisation.  That route is `n`-specific: it uses that a
`2`-torsion point is its own negation, which has a clean coordinate form (`yT = W.negY xT yT`).

For the `n = 3` track — and for a *uniform* treatment of every `n` — the clean tool is the
**base-change group homomorphism on points**, `WeierstrassCurve.Affine.Point.map`, applied to the
canonical `F`-algebra map `F → F(W)`.  Because it is an `AddMonoidHom`, it commutes with `nsmul`
and sends `0` to `0`, so *any* `n`-torsion relation `n • T = 0` over the base field transports
verbatim to `n • (translatePoint hT) = 0` over `F(W)`.  This is exactly the commuting datum the
`n = 3` `hcomm` discharge (the `mulByThreeEndo` mirror of `TranslationDoublingComm.lean` PR #164)
consumes, and it subsumes the `n = 2` case.

The key observation making Mathlib's `Point.map` directly usable here is that the base-changed curve
`W ⁄ F(W) = W.map (algebraMap F F(W))` used throughout the `GenericPoint`/`Translation*` files is
literally the target of `Point.map (Algebra.ofId F F(W))` (with source `W ⁄ F = W.map (algebraMap
F F)`, which reduces to `W`), and `translatePoint hT` is the image of the base-field point
`torsionPoint hT` under that map.

## Main results

* `torsionPointMap` — the base-change group homomorphism `W.Point →+ (W ⁄ F(W)).Point` induced by
  `Algebra.ofId F F(W)`;
* `torsionPointMap_torsionPoint` — it sends the fixed `F`-point `T = (xT, yT)` (`torsionPoint hT`)
  to its constant base change `translatePoint hT`;
* `translatePoint_nsmul_eq_zero` — **the uniform transport**: `n • T = 0` in `W.Point` gives
  `n • (translatePoint hT) = 0` in `(W ⁄ F(W)).Point`, for every `n`;
* `translatePoint_add_add_self` — the concrete `n = 3` form
  `T + T + T = 0 ⟹ translatePoint hT + translatePoint hT + translatePoint hT = 0`, the commuting
  datum the `n = 3` `hcomm` discharge consumes.

Everything here is Ward- and normality-independent: it needs only `[Field F] [W.IsElliptic]`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {xT yT : F}

open Classical in
/-- **The base-change point homomorphism** `W.Point →+ (W ⁄ F(W)).Point`, induced by the canonical
`F`-algebra map `Algebra.ofId F F(W)` via Mathlib's functoriality of points
(`WeierstrassCurve.Affine.Point.map`).  Its source `W ⁄ F = W.map (algebraMap F F)` reduces to `W`
and its target `W ⁄ F(W) = W.map (algebraMap F F(W))` is the base-changed curve carrying
`genericPoint`/`translatePoint`.  Being an `AddMonoidHom`, it commutes with `nsmul` — the mechanism
that transports base-field torsion to `F(W)`. -/
noncomputable def torsionPointMap :
    W.Point →+ (W.map (algebraMap F W.FunctionField)).Point :=
  Point.map (W' := W) (Algebra.ofId F W.FunctionField)

open Classical in
/-- **The base-change map sends `T` to `translatePoint hT`.**  The fixed `F`-point
`torsionPoint hT = (xT, yT)` maps to the constant point `translatePoint hT = (algebraMap F F(W) xT,
algebraMap F F(W) yT)`, since `Point.map` acts on `some`-points by applying the algebra map to each
coordinate (`Point.map_some`) and `Algebra.ofId F F(W)` is `algebraMap F F(W)`. -/
theorem torsionPointMap_torsionPoint (hT : W.Equation xT yT) :
    torsionPointMap (torsionPoint hT) = translatePoint hT :=
  rfl

open Classical in
/-- **Uniform torsion transport.**  If the fixed `F`-point `T = (xT, yT)` is `n`-torsion over the
base field (`n • T = 0` in `W.Point`), then its constant base change `translatePoint hT` is
`n`-torsion over `F(W)` (`n • translatePoint hT = 0` in `(W ⁄ F(W)).Point`).  Immediate from the
base-change homomorphism `torsionPointMap` commuting with `nsmul` and fixing `0`. -/
theorem translatePoint_nsmul_eq_zero (hT : W.Equation xT yT) {n : ℕ}
    (hn : n • torsionPoint hT = 0) : n • translatePoint hT = 0 := by
  rw [← torsionPointMap_torsionPoint hT, ← map_nsmul, hn, map_zero]

open Classical in
/-- **The `n = 3` transport form.**  From the base-field `3`-torsion relation
`T + T + T = 0` in `W.Point`, the constant translate satisfies
`translatePoint hT + translatePoint hT + translatePoint hT = 0` over `F(W)` — the commuting datum
the `n = 3` `hcomm` discharge (`mulByThreeEndo` mirror of `TranslationDoublingComm.lean` PR #164)
consumes.  A specialisation of `translatePoint_nsmul_eq_zero` at `n = 3`. -/
theorem translatePoint_add_add_self (hT : W.Equation xT yT)
    (htors : torsionPoint hT + torsionPoint hT + torsionPoint hT = 0) :
    translatePoint hT + translatePoint hT + translatePoint hT = 0 := by
  have h3 : (3 : ℕ) • translatePoint hT = 0 :=
    translatePoint_nsmul_eq_zero hT (by
      rw [show (3 : ℕ) = 2 + 1 by rfl, add_smul, two_nsmul, one_nsmul, htors])
  rwa [show (3 : ℕ) = 2 + 1 by rfl, add_smul, two_nsmul, one_nsmul] at h3

end CoordinateRing

end WeierstrassCurve.Affine
