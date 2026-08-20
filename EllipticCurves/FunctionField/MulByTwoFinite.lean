/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoEndomorphism

/-!
# Integrality of the generic `x`-coordinate over the multiplication-by-`2` subfield

Let `W` be a Weierstrass curve over a field `F` of characteristic `≠ 2`, with function field
`F(W) = Frac F[W]`. The multiplication-by-`2` endomorphism
`mulByTwoEndo h2 : F(W) →+* F(W)` (`EllipticCurves/FunctionField/MulByTwoEndomorphism.lean`) is an
injective field homomorphism; its image `[2]∗F(W)` is a subfield of `F(W)`, and the extension
`F(W) / [2]∗F(W)` is the degree-`4` extension underlying the fact that `[2] : E → E` is a finite
morphism of degree `4 = 2²`. This file supplies the **integrality datum** for the generic
`x`-coordinate — the concrete first half of the finiteness gate that the divisor-level pullback
`[2]∗` (issue #414, rung 4) requires.

## Main statement

* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoEndo_isIntegralElem_genX`: the generic
  `x`-coordinate `genX = x(P)` is integral over the image of `mulByTwoEndo h2`, and in fact is a
  root of the **explicit monic quartic**
  `q(T) = Φ₂(genX ; T) - x(2 • P) · Ψ₂Sq(genX ; T)`
  whose coefficients lie in `[2]∗F(W)` (via `eval₂ (mulByTwoEndo h2)`). Monicity is because `Φ₂`
  has degree `4` with leading coefficient `1` while `Ψ₂Sq` has degree `≤ 3`.
* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoEndoAlgHom`: `[2]∗` as an `F`-algebra
  endomorphism of `F(W)`.  It lives here rather than in `MulByTwoEndomorphism.lean` because its
  `commutes'` field is `mulByTwoEndo_algebraMap_base`, which is proved in this file; both
  `MulByTwoDegree` (for `AlgHom.fieldRange` / `IntermediateField.map`) and
  `TranslationDoublingCommGeneral` (for `Point.map`) consume it.

The mechanism is the identity `x(2 • P) = Φ₂(genX)/Ψ₂Sq(genX)`, i.e. `mulByTwoEndo h2 (genX)`
multiplied by the (nonvanishing) denominator `Ψ₂Sq(genX)` returns the numerator `Φ₂(genX)` — so
substituting `genX` into `q` gives `Φ₂(genX) - x(2 • P)·Ψ₂Sq(genX) = 0`. This is the same
annihilating polynomial used in the dominance argument `isAlgebraic_genX_of`, here read *relative to
the image subfield* `[2]∗F(W)` (rather than the relative algebraic closure of `F`), which upgrades
algebraicity to integrality of degree `≤ 4`.

## Scope

This delivers the sanctioned first brick of issue #421 (Rung 4 / Brick C): the degree-`≤ 4`
integrality of `genX` over `[2]∗F(W)`. The complementary facts — integrality of the generic
`y`-coordinate `genY` (which follows by transitivity, being integral over `[2]∗F(W)[genX]` via the
monic-in-`Y` Weierstrass equation), the full module-finiteness `Module.Finite ([2]∗F(W)) F(W)`, and
the identification of the Dedekind ring `B` (the integral closure of `[2]∗F[W]` in `F(W)`, subtle
because `[2]∗F[W] ⊄ F[W]`) — remain for a follow-on. Only `[Field F]` and `(2 : F) ≠ 0` are used;
Ward-independent, no normality instance.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2 (finite maps of curves),
  III.6, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine
namespace CoordinateRing

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] {W : Affine F}

/-- The multiplication-by-`2` endomorphism fixes the base field `F ⊆ F(W)`: for `c : F`,
`[2]∗(c) = c`. (The pullback of a constant function is itself.) -/
lemma mulByTwoEndo_algebraMap_base (h2 : (2 : F) ≠ 0) (c : F) :
    mulByTwoEndo h2 (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c := by
  have hst := IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField c
  rw [hst, mulByTwoEndo_algebraMap, mulByTwoCoordHom_algebraMap, ← hst]

/-- `[2]∗` composed with the base embedding `F → F(W)` is the base embedding: `[2]∗` fixes `F`. -/
lemma mulByTwoEndo_comp_algebraMap (h2 : (2 : F) ≠ 0) :
    (mulByTwoEndo h2).comp (algebraMap F W.FunctionField) = algebraMap F W.FunctionField :=
  RingHom.ext (mulByTwoEndo_algebraMap_base h2)

/-- **`[2]∗` as an `F`-algebra endomorphism of `F(W)`.**  `mulByTwoEndo` is a bare `RingHom` and
`mulByTwoAlgHom` is the *coordinate-ring* map `F[W] →ₐ[F] F(W)`; neither is an `F`-algebra
endomorphism of `F(W)`, which is what the `IntermediateField` tower of `MulByTwoDegree` and the
generic-point transport of `TranslationDoublingCommGeneral` both need.  It is `mulByTwoEndo`
together with `mulByTwoEndo_algebraMap_base`, and it lives here because that is the earliest file
where both halves exist. -/
noncomputable def mulByTwoEndoAlgHom (h2 : (2 : F) ≠ 0) :
    W.FunctionField →ₐ[F] W.FunctionField where
  toRingHom := mulByTwoEndo h2
  commutes' := mulByTwoEndo_algebraMap_base h2

@[simp] lemma mulByTwoEndoAlgHom_apply (h2 : (2 : F) ≠ 0) (f : W.FunctionField) :
    mulByTwoEndoAlgHom h2 f = mulByTwoEndo h2 f := rfl

/-- Evaluating a base-changed univariate polynomial `q.map (F → F(W))` at `genX` through
`eval₂ (mulByTwoEndo h2)` is the same as its ordinary evaluation, since `[2]∗` fixes the
(base-field) coefficients of `q.map`. -/
lemma eval₂_mulByTwoEndo_map (h2 : (2 : F) ≠ 0) (q : F[X]) :
    eval₂ (mulByTwoEndo h2) (genX W) (q.map (algebraMap F W.FunctionField)) =
      (q.map (algebraMap F W.FunctionField)).eval (genX W) := by
  rw [eval₂_map, mulByTwoEndo_comp_algebraMap, ← eval_map]

/-- **The generic `x`-coordinate is integral over `[2]∗F(W)`.** `genX = x(P)` is a root of the monic
quartic `Φ₂(genX ; T) - x(2 • P)·Ψ₂Sq(genX ; T)` (with coefficients in the image of `mulByTwoEndo`),
so `F(W)` is a degree-`≤ 4` integral extension of the multiplication-by-`2` subfield `[2]∗F(W)`. -/
theorem mulByTwoEndo_isIntegralElem_genX (h2 : (2 : F) ≠ 0) :
    (mulByTwoEndo h2).IsIntegralElem (genX W) := by
  set φ := algebraMap F W.FunctionField with hφ
  -- the denominator `Ψ₂Sq(genX)` does not vanish at the generic point
  have hden : ((W.map φ).Ψ₂Sq).eval (genX W) ≠ 0 := by
    have hsq := ψ_sq_evalEval (W := W.map φ) equation_gen 2
    rw [ΨSq_two] at hsq
    rw [← hsq]
    exact pow_ne_zero 2 (psiTwo_gen_ne h2)
  refine ⟨(W.map φ).Φ 2 - C (genX W) * (W.map φ).Ψ₂Sq, ?_, ?_⟩
  · -- the quartic is monic: degree `≤ 4` with degree-`4` coefficient `1`
    apply monic_of_natDegree_le_of_coeff_eq_one 4
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact ((W.map φ).natDegree_Φ_le 2).trans (by decide)
      · exact (natDegree_C_mul_le _ _).trans ((W.map φ).natDegree_Ψ₂Sq_le.trans (by decide))
    · have hΨle : (W.map φ).Ψ₂Sq.natDegree < (2 : ℤ).natAbs ^ 2 :=
        lt_of_le_of_lt (W.map φ).natDegree_Ψ₂Sq_le (by decide)
      rw [coeff_sub, coeff_C_mul, show (4 : ℕ) = (2 : ℤ).natAbs ^ 2 by decide,
        (W.map φ).coeff_Φ 2, coeff_eq_zero_of_natDegree_lt hΨle, mul_zero, sub_zero]
  · -- substituting `genX` gives `Φ₂(genX) - x(2 • P)·Ψ₂Sq(genX) = 0`
    have hEA : eval₂ (mulByTwoEndo h2) (genX W) ((W.map φ).Φ 2) =
        ((W.map φ).Φ 2).eval (genX W) := by
      rw [hφ, map_Φ]; exact eval₂_mulByTwoEndo_map h2 (W.Φ 2)
    have hEB : eval₂ (mulByTwoEndo h2) (genX W) ((W.map φ).Ψ₂Sq) =
        ((W.map φ).Ψ₂Sq).eval (genX W) := by
      rw [hφ, map_Ψ₂Sq]; exact eval₂_mulByTwoEndo_map h2 W.Ψ₂Sq
    rw [eval₂_sub, eval₂_mul, eval₂_C, hEA, hEB, mulByTwoEndo_genX h2,
      div_mul_cancel₀ _ hden, sub_self]

end CoordinateRing
end WeierstrassCurve.Affine
