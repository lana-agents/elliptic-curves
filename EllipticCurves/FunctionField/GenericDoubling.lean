/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.GenericPoint
import EllipticCurves.FunctionField.MulByTwoEndomorphism

/-!
# The doubling correspondence: `mulByTwoEndo` acts as `[2]•` on the generic point

Let `W` be an elliptic curve over a field `F` of characteristic `≠ 2`.  Building on
`GenericPoint.lean` (the generic point `𝒫 = (genX W, genY W)` as an element of the Mathlib group
`(W ⁄ F(W)).Point`), this file identifies the multiplication-by-`2` endomorphism
`mulByTwoEndo : F(W) →+* F(W)` with the *group double* `𝒫 ↦ 𝒫 + 𝒫`:

```
𝒫 + 𝒫 = (mulByTwoEndo h2 (genX W), mulByTwoEndo h2 (genY W)).
```

`mulByTwoEndo` sends the coordinate generators to the classical division-polynomial doubling
coordinates `(Φ₂/Ψ₂Sq, ω₂/ψ₂³)` (`mulByTwoEndo_genX`/`_genY`), so this is exactly the duplication
formula `x(2•P) = Φ₂/Ψ₂Sq`, `y(2•P) = ω₂/ψ₂³` at the generic point — the doubling analogue of the
translation correspondence `genericPoint_add_translatePoint`, and the `n = 2` slice of the bridge
`mulByNEndo = [n]•` needed to discharge `hcomm` in the rung-6 Weil-pairing element (#419 / #433).

## Contents

* `genY_ne_negY_gen`             — the generic point is not `2`-torsion: `genY ≠ negY genX genY`
  (its `ψ₂`-value `2·genY + a₁·genX + a₃` is nonzero, `psiTwo_gen_ne`), so the group double takes the
  tangent (`add_of_Y_ne`) branch;
* `nonsingular_mulByTwoEndo_gen`  — the doubling coordinates `(mulByTwoEndo genX, mulByTwoEndo genY)`
  are a nonsingular point (they lie on the curve by `doubling_equation_gen`);
* `addX_gen_eq_mulByTwo`          — the `x`-coordinate identity `addX = mulByTwoEndo genX`;
* `addY_gen_eq_mulByTwo`          — the `y`-coordinate identity `addY = mulByTwoEndo genY`;
* `genericPoint_add_self`         — the **doubling correspondence** `𝒫 + 𝒫 = (mulByTwoEndo genX,
  mulByTwoEndo genY)`.

Everything here is Ward- and normality-independent: it needs only `[Field F] [W.IsElliptic]` and
`(2 : F) ≠ 0`, no `IsDedekindDomain` and no elliptic-net machinery.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The generic point is not `2`-torsion.** Its `ψ₂`-value `2·genY + a₁·genX + a₃ =
genY − negY genX genY` is nonzero (`psiTwo_gen_ne`), so `genY ≠ negY genX genY`; hence the group
double `𝒫 + 𝒫` takes the tangent (doubling) branch `add_of_Y_ne` of the affine addition law. -/
theorem genY_ne_negY_gen (h2 : (2 : F) ≠ 0) :
    genY W ≠ (W.map (algebraMap F W.FunctionField)).negY (genX W) (genY W) := by
  intro h
  refine psiTwo_gen_ne (W := W) h2 ?_
  rw [ψ_two_evalEval]
  rw [negY] at h
  linear_combination h

/-- **The doubling coordinates form a nonsingular point.** The images `mulByTwoEndo h2 (genX W)`,
`mulByTwoEndo h2 (genY W)` are the classical division-polynomial doubling coordinates
`(Φ₂/Ψ₂Sq, ω₂/ψ₂³)` (`mulByTwoEndo_genX`/`_genY`), which lie on the base-changed elliptic curve by
`doubling_equation_gen`; on an elliptic curve, every equation point is nonsingular. -/
theorem nonsingular_mulByTwoEndo_gen (h2 : (2 : F) ≠ 0) :
    (W.map (algebraMap F W.FunctionField)).Nonsingular
      (mulByTwoEndo h2 (genX W)) (mulByTwoEndo h2 (genY W)) := by
  rw [mulByTwoEndo_genX, mulByTwoEndo_genY]
  exact (W.map (algebraMap F W.FunctionField)).equation_iff_nonsingular.mp
    (doubling_equation_gen h2)

open Classical in
/-- **The `x`-coordinate of the duplication formula.** The `x`-coordinate `addX` of the group double
`𝒫 + 𝒫` (with the tangent slope) equals `mulByTwoEndo h2 (genX W) = Φ₂(genX)/Ψ₂Sq(genX)`. -/
theorem addX_gen_eq_mulByTwo (h2 : (2 : F) ≠ 0) :
    (W.map (algebraMap F W.FunctionField)).addX (genX W) (genX W)
        ((W.map (algebraMap F W.FunctionField)).slope (genX W) (genX W) (genY W) (genY W))
      = mulByTwoEndo h2 (genX W) := by
  sorry

open Classical in
/-- **The `y`-coordinate of the duplication formula.** The `y`-coordinate `addY` of the group double
`𝒫 + 𝒫` (with the tangent slope) equals `mulByTwoEndo h2 (genY W) = ω₂(genX, genY)/ψ₂(genX, genY)³`.
-/
theorem addY_gen_eq_mulByTwo (h2 : (2 : F) ≠ 0) :
    (W.map (algebraMap F W.FunctionField)).addY (genX W) (genX W) (genY W)
        ((W.map (algebraMap F W.FunctionField)).slope (genX W) (genX W) (genY W) (genY W))
      = mulByTwoEndo h2 (genY W) := by
  sorry

open Classical in
/-- **The doubling correspondence.** The multiplication-by-`2` endomorphism `mulByTwoEndo h2` acts on
the coordinate generators of `F(W)` exactly as the group double `𝒫 ↦ 𝒫 + 𝒫` in `(W ⁄ F(W)).Point`:

```
𝒫 + 𝒫 = (mulByTwoEndo h2 (genX W), mulByTwoEndo h2 (genY W)).
```

Since the generic point is not `2`-torsion (`genY_ne_negY_gen`), the double takes the tangent branch
`add_self_of_Y_ne`, whose `addX`/`addY` coordinates are the division-polynomial doubling coordinates
(`addX_gen_eq_mulByTwo`/`addY_gen_eq_mulByTwo`).  This is the group-theoretic reading of
`mulByTwoEndo` — the `n = 2` bridge `mulByNEndo = [n]•` — that the `hcomm` discharge of #419 consumes.
-/
theorem genericPoint_add_self (h2 : (2 : F) ≠ 0) :
    genericPoint + genericPoint
      = Point.some (mulByTwoEndo h2 (genX W)) (mulByTwoEndo h2 (genY W))
          (nonsingular_mulByTwoEndo_gen h2) := by
  rw [genericPoint, Point.add_self_of_Y_ne (genY_ne_negY_gen h2), Point.some.injEq]
  exact ⟨addX_gen_eq_mulByTwo h2, addY_gen_eq_mulByTwo h2⟩

end CoordinateRing

end WeierstrassCurve.Affine
