/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByThreeEndomorphism

/-!
# Integrality of the generic `x`-coordinate over the multiplication-by-`3` subfield

Let `W` be a Weierstrass curve over a field `F` of characteristic `≠ 2, 3`, with function field
`F(W) = Frac F[W]`. The multiplication-by-`3` endomorphism
`mulByThreeEndo h2 h3 : F(W) →+* F(W)` (`EllipticCurves/FunctionField/MulByThreeEndomorphism.lean`)
is an injective field homomorphism; its image `[3]∗F(W)` is a subfield of `F(W)`, and the extension
`F(W) / [3]∗F(W)` is the degree-`9` extension underlying the fact that `[3] : E → E` is a finite
morphism of degree `9 = 3²`. This file supplies the **integrality datum** for the generic
`x`-coordinate — the first half of the finiteness gate — as the `n = 3` analogue of the merged
`mulByTwoEndo_isIntegralElem_genX` (`MulByTwoFinite.lean`, issue #421 Brick C).

## Main statement

* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeEndo_isIntegralElem_genX`: the generic
  `x`-coordinate `genX = x(P)` is integral over the image of `mulByThreeEndo h2 h3`, and in fact
  is a root of the **explicit monic degree-`9` polynomial**
  `q(T) = Φ₃(genX ; T) - x(3 • P) · ΨSq₃(genX ; T)`
  whose coefficients lie in `[3]∗F(W)` (via `eval₂ (mulByThreeEndo h2 h3)`). Monicity is because
  `Φ₃` has degree `9` with leading coefficient `1` while `ΨSq₃` has degree `≤ 8`.

The mechanism is the identity `x(3 • P) = Φ₃(genX)/ΨSq₃(genX)`, i.e. `mulByThreeEndo h2 h3 (genX)`
multiplied by the (nonvanishing) denominator `ΨSq₃(genX)` returns the numerator `Φ₃(genX)` — so
substituting `genX` into `q` gives `Φ₃(genX) - x(3 • P)·ΨSq₃(genX) = 0`. This is the same
annihilating polynomial used in the dominance argument `isAlgebraic_genX_of_three`, here read
*relative to the image subfield* `[3]∗F(W)`, which upgrades algebraicity to integrality of degree
`≤ 9`.

## Scope

This delivers the sanctioned first brick of the `n = 3` Brick C (issue #428): the degree-`≤ 9`
integrality of `genX` over `[3]∗F(W)`. The complementary facts — integrality of the generic
`y`-coordinate `genY` and the module-finiteness `Module.Finite ([3]∗F(W)) F(W)` — mirror the merged
n=2 files (`MulByThreeModuleFinite.lean`, `MulByThreeExtensionFinite.lean`). Only `[Field F]`,
`(2 : F) ≠ 0` and `(3 : F) ≠ 0` are used; Ward-independent, no normality instance.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2 (finite maps of curves),
  III.6, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine
namespace CoordinateRing

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] {W : Affine F}

/-- The multiplication-by-`3` endomorphism fixes the base field `F ⊆ F(W)`: for `c : F`,
`[3]∗(c) = c`. (The pullback of a constant function is itself.) -/
lemma mulByThreeEndo_algebraMap_base (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (c : F) :
    mulByThreeEndo h2 h3 (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c := by
  have hst := IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField c
  rw [hst, mulByThreeEndo_algebraMap, mulByThreeCoordHom_algebraMap, ← hst]

/-- `[3]∗` composed with the base embedding `F → F(W)` is the base embedding: `[3]∗` fixes `F`. -/
lemma mulByThreeEndo_comp_algebraMap (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (mulByThreeEndo h2 h3).comp (algebraMap F W.FunctionField) = algebraMap F W.FunctionField :=
  RingHom.ext (mulByThreeEndo_algebraMap_base h2 h3)

/-- Evaluating a base-changed univariate polynomial `q.map (F → F(W))` at `genX` through
`eval₂ (mulByThreeEndo h2 h3)` is the same as its ordinary evaluation, since `[3]∗` fixes the
(base-field) coefficients of `q.map`. -/
lemma eval₂_mulByThreeEndo_map (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (q : F[X]) :
    eval₂ (mulByThreeEndo h2 h3) (genX W) (q.map (algebraMap F W.FunctionField)) =
      (q.map (algebraMap F W.FunctionField)).eval (genX W) := by
  rw [eval₂_map, mulByThreeEndo_comp_algebraMap, ← eval_map]

/-- **The generic `x`-coordinate is integral over `[3]∗F(W)`.** `genX = x(P)` is a root of the monic
degree-`9` polynomial `Φ₃(genX ; T) - x(3 • P)·ΨSq₃(genX ; T)` (with coefficients in the image of
`mulByThreeEndo`), so `F(W)` is a degree-`≤ 9` integral extension of the multiplication-by-`3`
subfield `[3]∗F(W)`. -/
theorem mulByThreeEndo_isIntegralElem_genX (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (mulByThreeEndo h2 h3).IsIntegralElem (genX W) := by
  set φ := algebraMap F W.FunctionField with hφ
  -- the denominator `ΨSq₃(genX)` does not vanish at the generic point
  have hden : ((W.map φ).ΨSq 3).eval (genX W) ≠ 0 := by
    have hsq := ψ_sq_evalEval (W := W.map φ) equation_gen 3
    rw [← hsq]
    exact pow_ne_zero 2 (psiThree_gen_ne h3)
  refine ⟨(W.map φ).Φ 3 - C (genX W) * (W.map φ).ΨSq 3, ?_, ?_⟩
  · -- the polynomial is monic: degree `≤ 9` with degree-`9` coefficient `1`
    apply monic_of_natDegree_le_of_coeff_eq_one 9
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact ((W.map φ).natDegree_Φ_le 3).trans (by decide)
      · exact (natDegree_C_mul_le _ _).trans (((W.map φ).natDegree_ΨSq_le 3).trans (by decide))
    · have hΨle : ((W.map φ).ΨSq 3).natDegree < (3 : ℤ).natAbs ^ 2 :=
        lt_of_le_of_lt ((W.map φ).natDegree_ΨSq_le 3) (by decide)
      rw [coeff_sub, coeff_C_mul, show (9 : ℕ) = (3 : ℤ).natAbs ^ 2 by decide,
        (W.map φ).coeff_Φ 3, coeff_eq_zero_of_natDegree_lt hΨle, mul_zero, sub_zero]
  · -- substituting `genX` gives `Φ₃(genX) - x(3 • P)·ΨSq₃(genX) = 0`
    have hEA : eval₂ (mulByThreeEndo h2 h3) (genX W) ((W.map φ).Φ 3) =
        ((W.map φ).Φ 3).eval (genX W) := by
      rw [hφ, map_Φ]; exact eval₂_mulByThreeEndo_map h2 h3 (W.Φ 3)
    have hEB : eval₂ (mulByThreeEndo h2 h3) (genX W) ((W.map φ).ΨSq 3) =
        ((W.map φ).ΨSq 3).eval (genX W) := by
      rw [hφ, map_ΨSq]; exact eval₂_mulByThreeEndo_map h2 h3 (W.ΨSq 3)
    rw [eval₂_sub, eval₂_mul, eval₂_C, hEA, hEB, mulByThreeEndo_genX h2 h3,
      div_mul_cancel₀ _ hden, sub_self]

end CoordinateRing
end WeierstrassCurve.Affine
