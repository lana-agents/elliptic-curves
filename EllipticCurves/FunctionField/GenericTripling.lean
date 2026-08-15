/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.GenericDoubling
import EllipticCurves.FunctionField.MulByThreeEndomorphism

/-!
# The tripling correspondence: `mulByThreeEndo` acts as `[3]•` on the generic point

Let `W` be an elliptic curve over a field `F` of characteristic `≠ 2, 3`.  Building on
`GenericPoint.lean` (the generic point `𝒫 = (genX W, genY W)` as an element of the Mathlib group
`(W ⁄ F(W)).Point`) and the merged doubling correspondence `GenericDoubling.lean`
(`genericPoint_add_self : 𝒫 + 𝒫 = (mulByTwoEndo genX, mulByTwoEndo genY)`), this file identifies the
multiplication-by-`3` endomorphism `mulByThreeEndo : F(W) →+* F(W)` with the *group triple*
`𝒫 ↦ 𝒫 + 𝒫 + 𝒫 = [3]•𝒫`:

```
𝒫 + 𝒫 + 𝒫 = (mulByThreeEndo h2 h3 (genX W), mulByThreeEndo h2 h3 (genY W)).
```

`mulByThreeEndo` sends the coordinate generators to the classical division-polynomial tripling
coordinates `(Φ₃/ΨSq₃, ω₃/(2 ψ₃³))` (`mulByThreeEndo_genX`/`_genY`), so this is exactly the tripling
formula at the generic point — the `n = 3` mirror of `genericPoint_add_self`, and the `n = 3` slice
of the bridge `mulByNEndo = [n]•`.

## Contents

* `nonsingular_mulByThreeEndo_gen`  — the tripling coordinates
  `(mulByThreeEndo genX, mulByThreeEndo genY)` are a nonsingular point (they lie on the curve by
  `tripling_equation_gen`);
* `mulByTwoEndo_genX_ne_genX`       — `x(2•𝒫) ≠ x(𝒫)` at the generic point, so the secant sum
  `(2•𝒫) + 𝒫` takes the `add_of_X_ne` branch of the affine addition law.

Everything here is Ward- and normality-independent: it needs only `[Field F] [W.IsElliptic]`,
`(2 : F) ≠ 0`, and `(3 : F) ≠ 0`, no `IsDedekindDomain` and no elliptic-net machinery.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The tripling coordinates form a nonsingular point.** The images
`mulByThreeEndo h2 h3 (genX W)`, `mulByThreeEndo h2 h3 (genY W)` are the classical
division-polynomial tripling coordinates `(Φ₃/ΨSq₃, ω₃/(2 ψ₃³))` (`mulByThreeEndo_genX`/`_genY`),
which lie on the base-changed elliptic curve by `tripling_equation_gen`; on an elliptic curve,
every equation point is nonsingular. -/
theorem nonsingular_mulByThreeEndo_gen (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (W.map (algebraMap F W.FunctionField)).Nonsingular
      (mulByThreeEndo h2 h3 (genX W)) (mulByThreeEndo h2 h3 (genY W)) := by
  rw [mulByThreeEndo_genX, mulByThreeEndo_genY]
  exact (W.map (algebraMap F W.FunctionField)).equation_iff_nonsingular.mp
    (tripling_equation_gen h2 h3)

omit [W.IsElliptic] in
/-- **`x(2•𝒫) ≠ x(𝒫)`.** The `x`-coordinate of the doubled generic point,
`mulByTwoEndo h2 (genX W) = Φ₂(genX)/Ψ₂Sq(genX)`, is different from the generic `x`-coordinate
`genX W`.  Geometrically `x(2P) = x(P) ⟺ 2P = ±P ⟺ 3P = O` (or `P = O`), false at the generic point.
Algebraically: were they equal, `genX` would be a root of the nonzero `F`-polynomial
`Φ₂ - X·Ψ₂Sq` (its degree-`4` coefficient is `1 - 4 = -3 ≠ 0`, using `(3 : F) ≠ 0`), contradicting
`transcendental_genX`.  This distinctness is what makes the secant sum `(2•𝒫) + 𝒫` take the
`add_of_X_ne` branch of the affine addition law. -/
theorem mulByTwoEndo_genX_ne_genX (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    mulByTwoEndo h2 (genX W) ≠ genX W := by
  rw [mulByTwoEndo_genX]
  -- The doubling denominator `Ψ₂Sq(genX)` does not vanish (the generic point is not `2`-torsion).
  have hden : ((W.map (algebraMap F W.FunctionField)).Ψ₂Sq).eval (genX W) ≠ 0 := by
    have hsq := ψ_sq_evalEval (W := W.map (algebraMap F W.FunctionField)) equation_gen 2
    rw [ΨSq_two] at hsq
    rw [← hsq]
    exact pow_ne_zero 2 (psiTwo_gen_ne h2)
  intro hcontra
  -- If `x(2P) = x(P)`, then `Φ₂(genX) = genX · Ψ₂Sq(genX)`.
  have hrel : ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W)
      = genX W * ((W.map (algebraMap F W.FunctionField)).Ψ₂Sq).eval (genX W) := by
    field_simp [hden] at hcontra
    linear_combination hcontra
  -- The candidate annihilating `F`-polynomial of `genX`.
  set q : F[X] := W.Φ 2 - X * W.Ψ₂Sq with hq
  -- `q` is nonzero: its degree-`4` coefficient is `1 - 4 = -3 ≠ 0`.
  have hqne : q ≠ 0 := by
    intro h0
    have hcoeff : q.coeff 4 = -3 := by
      rw [hq, coeff_sub, coeff_X_mul,
        show (4 : ℕ) = (2 : ℤ).natAbs ^ 2 by decide, W.coeff_Φ 2, W.coeff_Ψ₂Sq]
      norm_num
    rw [h0, coeff_zero] at hcoeff
    exact h3 (by linear_combination hcoeff)
  -- `genX` is a root of `q`, hence algebraic over `F` — contradicting `transcendental_genX`.
  refine transcendental_genX (W := W) ⟨q, hqne, ?_⟩
  have e1 : (aeval (genX W)) (W.Φ 2)
      = ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) := by
    rw [map_Φ, aeval_def, eval₂_eq_eval_map]
  have e2 : (aeval (genX W)) W.Ψ₂Sq
      = ((W.map (algebraMap F W.FunctionField)).Ψ₂Sq).eval (genX W) := by
    rw [map_Ψ₂Sq, aeval_def, eval₂_eq_eval_map]
  rw [hq, map_sub, map_mul, aeval_X, e1, e2, hrel]
  ring

end CoordinateRing

end WeierstrassCurve.Affine
