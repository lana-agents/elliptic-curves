/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationPullback
import EllipticCurves.Torsion.OmegaTwo

/-!
# The multiplication-by-`2` pullback on the function field of a Weierstrass curve

Let `W` be a Weierstrass curve over a field `F` of characteristic `≠ 2`, with affine coordinate ring
`F[W] = AdjoinRoot W.polynomial` and function field `F(W) = Frac F[W]`. The duplication map
`P ↦ 2 • P` is a morphism of the curve, and pulling back rational functions along it gives an
`F`-algebra endomorphism `[2]∗` of `F(W)`. This file builds the *coordinate-ring half* of that
pullback: the ring homomorphism

* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoCoordHom h2 : F[W] →+* F(W)`

sending the generic point `P = (x, y)` to `2 • P`, i.e. realising on the coordinate generators the
classical division-polynomial doubling coordinates

* `x ↦ Φ₂(x) / Ψ₂Sq(x)` and
* `y ↦ ω₂(x, y) / (2 ψ₂(x, y)³)`, where
  `ω₂(x, y) = preΨ₄(x) - ψ₂(x, y)·(a₁ Φ₂(x) + a₃ Ψ₂Sq(x))`,

using the on-curve doubling identity `WeierstrassCurve.Affine.doubling_equation` over the
base-changed curve `W ⁄ F(W)`. This is the multiplication-by-`n` analogue (for `n = 2`) of the
translation pullback `translateCoordHom`, and a substrate for a divisor-theoretic Weil pairing.

## The construction

`W.CoordinateRing = AdjoinRoot W.polynomial` has base ring `F[X]`, so `AdjoinRoot.lift` needs a ring
hom `i : F[X] →+* F(W)` (the image of the `X`-variable), the image of the root `Y`, and a proof of
the single obligation `W.polynomial.eval₂ i (root image) = 0`. We take `i` and the root image to be
the `x`- and `y`-coordinates of `2 • P`, and discharge the obligation by

* the **generic point on the curve** `equation_gen` — that the coordinate generators `(genX, genY)`
  satisfy the Weierstrass equation over `F(W)` (reused verbatim from `TranslationPullback`);
* Mathlib's on-curve **doubling identity** `WeierstrassCurve.Affine.doubling_equation`, applied over
  the base-changed curve `W ⁄ F(W)` to the generic point (`doubling_equation_gen`);
* the **genericity** `psiTwo_gen_ne` — that `ψ₂` does not vanish at the generic point, so `P` is not
  `2`-torsion and the duplication branch is the applicable one.

The genericity is the genuinely new input: over the function field, `ψ₂(genX, genY)` is the image
of `mk W (W.ψ 2)`, and the latter is nonzero because `ψ₂ = 2Y + a₁X + a₃` has `Y`-degree `1` while
`W.polynomial` is monic of `Y`-degree `2`, so `W.polynomial ∤ W.ψ 2`.

## Main definitions and statements

* `WeierstrassCurve.Affine.CoordinateRing.genPsi_mk_map_evalEval`: naturality of bivariate
  evaluation through `mk` and the structural embedding `genPsi`.
* `WeierstrassCurve.Affine.CoordinateRing.psiTwo_gen_ne`: `ψ₂` does not vanish at the generic point.
* `WeierstrassCurve.Affine.CoordinateRing.doubling_equation_gen`: the doubled generic point lies on
  `W ⁄ F(W)`.
* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoCoordHom`: the multiplication-by-`2` pullback
  `F[W] →+* F(W)`, with generator images `mulByTwoCoordHom_X` and `mulByTwoCoordHom_root`.

## The endomorphism is built elsewhere, and the prediction was half right

⚠️ **This section used to be headed `## Remaining work`** and to read:

> Extending `mulByTwoCoordHom : F[W] →+* F(W)` to the full endomorphism `F(W) →+* F(W)` needs
> `Function.Injective (mulByTwoCoordHom h2)` (so that `IsFractionRing.lift` applies) — i.e. that
> the duplication map is *dominant*. Dominance follows because the `x`-coordinate image
> `Φ₂(genX)/Ψ₂Sq(genX)` is a nonconstant rational function of `genX`, forcing `genX` algebraic
> over the image, contradicting its transcendence; this is the same architecture as
> `TranslationEndomorphism` and is deferred to a follow-up.

The extension is `WeierstrassCurve.Affine.CoordinateRing.mulByTwoEndo`
(`EllipticCurves.FunctionField.MulByTwoEndomorphism`), off `mulByTwoCoordHom_injective`, and the
predicted *argument* is the argument that was used: `isAlgebraic_genX_of_two` annihilates `genX`
by `Φ₂ − x(2 • P) · Ψ₂Sq`, which is nonzero because `deg Φ₂ = 4 > 3 ≥ deg Ψ₂Sq`, and
`transcendental_genX` closes it.

⚠️ **The one word that is wrong is "same".**  `MulByTwoEndomorphism`'s own docstring opens its
dominance section with *"Unlike translation — whose dominance used the inverse morphism `· + (-T)`
and the point group law — the multiplication-by-`2` map has no inverse morphism, so a different
(and slightly simpler) argument is used"*.  So the architecture is **not** that of
`TranslationEndomorphism`; the two share only the final Zariski/Krull-dimension step.  The
prediction was right about the route and wrong about the analogy, which is why it is quoted rather
than deleted.

The reusable crux — the on-curve doubling identity at the generic point — is what this file
establishes.

## ⚠️ One `@[simp]` attribute was removed here, and the lemma kept (`#1278`)

`mulByTwoCoordHom_X` carried `@[simp]` and **could never fire**: its LHS is `mk W (C X)`, and
`AdjoinRoot.mk_C` — itself `@[simp]` — rewrites that to `AdjoinRoot.of W.polynomial X` before the
pattern is tried. Measured with Mathlib's `simpNF` environment linter, which had never been run on
this tree. The lemma is unchanged and has ten named consumers across four other files; only the
attribute went.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.6 (the duplication
  formula), III.8 (the Weil pairing).
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine
namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-- **Naturality of bivariate evaluation.** For a bivariate polynomial `g : F[X][Y]`, the image of
its class `mk W g` under the structural embedding `genPsi W : F[W] →+* F(W)` equals the evaluation
of `g` (base changed to `F(W)`) at the generic point `(genX, genY)`. This transports the class-group
description of a coordinate function to a concrete rational function of the generators. -/
lemma genPsi_mk_map_evalEval (g : F[X][Y]) :
    genPsi W (mk W g) =
      (g.map (mapRingHom (algebraMap F W.FunctionField))).evalEval (genX W) (genY W) := by
  have hcomp : (genPsi W).comp (AdjoinRoot.of W.polynomial)
      = eval₂RingHom (algebraMap F W.FunctionField) (genX W) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, genPsi,
        ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
    · rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, genX, genPsi]
      rfl
  rw [← eval₂_eval₂RingHom_apply, ← hcomp, ← AdjoinRoot.aeval_eq, aeval_def, hom_eval₂,
    AdjoinRoot.algebraMap_eq, ← genY]

/-- **Genericity of `ψ₂`.** Over a field of characteristic `≠ 2`, the `2`-division polynomial `ψ₂`
does not vanish at the generic point `(genX, genY)` of the base-changed curve `W ⁄ F(W)`; i.e. the
generic point is not `2`-torsion. -/
lemma psiTwo_gen_ne (h2 : (2 : F) ≠ 0) :
    ((W.map (algebraMap F W.FunctionField)).ψ 2).evalEval (genX W) (genY W) ≠ 0 := by
  rw [map_ψ, ← genPsi_mk_map_evalEval]
  intro hz
  have hmk : mk W (W.ψ 2) = 0 :=
    (injective_iff_map_eq_zero _).mp
      (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ hz
  have h0 : W.ψ 2 ≠ 0 := by
    intro h
    have hnd : (W.ψ 2).natDegree = 1 := by
      rw [ψ_two, ψ₂, polynomialY]
      exact natDegree_linear (b := C W.a₁ * X + C W.a₃) (C_ne_zero.mpr h2)
    rw [h, natDegree_zero] at hnd
    exact one_ne_zero hnd.symm
  have hdeg : (W.ψ 2).natDegree < W.polynomial.natDegree := by
    rw [natDegree_polynomial, ψ_two, ψ₂, polynomialY]
    exact lt_of_le_of_lt natDegree_linear_le (by norm_num)
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial h0 hdeg hmk

/-- The scalar `2` is nonzero in the function field when it is nonzero in the base field. -/
private lemma two_ne_zero_functionField (h2 : (2 : F) ≠ 0) : (2 : W.FunctionField) ≠ 0 := by
  have hinj := (algebraMap F W.FunctionField).injective
  intro h
  exact h2 (hinj (by rw [map_ofNat, map_zero]; exact h))

/-- **The doubled generic point lies on the curve.** Applying the division-polynomial doubling
identity `doubling_equation` over the base-changed curve `W ⁄ F(W)` to the generic point
`(genX, genY)` (which lies on the curve by `equation_gen` and is not `2`-torsion by
`psiTwo_gen_ne`), the classical doubling coordinates satisfy the Weierstrass equation. This is the
element-level
`F(W)`-identity consumed by the multiplication-by-`2` pullback. -/
theorem doubling_equation_gen (h2 : (2 : F) ≠ 0) :
    (W.map (algebraMap F W.FunctionField)).Equation
      (((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) /
        (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W))
      (((W.map (algebraMap F W.FunctionField)).preΨ₄.eval (genX W) -
          ((W.map (algebraMap F W.FunctionField)).ψ 2).evalEval (genX W) (genY W) *
            ((W.map (algebraMap F W.FunctionField)).a₁ *
                ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) +
              (W.map (algebraMap F W.FunctionField)).a₃ *
                (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W))) /
        (2 * ((W.map (algebraMap F W.FunctionField)).ψ 2).evalEval (genX W) (genY W) ^ 3)) :=
  doubling_equation equation_gen (two_ne_zero_functionField h2) (psiTwo_gen_ne h2)

/-- **The multiplication-by-`2` pullback (coordinate-ring half).** The ring homomorphism
`F[W] →+* F(W)` sending the generic point `P = (x, y)` to the doubled point `2 • P`. It is
`AdjoinRoot.lift` of the division-polynomial doubling coordinates, whose well-definedness obligation
`W.polynomial.eval₂ _ _ = 0` is exactly that `2 • P` lies on the curve, discharged by
`doubling_equation_gen`. -/
noncomputable def mulByTwoCoordHom (h2 : (2 : F) ≠ 0) :
    W.CoordinateRing →+* W.FunctionField :=
  AdjoinRoot.lift
    (eval₂RingHom (algebraMap F W.FunctionField)
      (((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) /
        (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W)))
    (((W.map (algebraMap F W.FunctionField)).preΨ₄.eval (genX W) -
        ((W.map (algebraMap F W.FunctionField)).ψ 2).evalEval (genX W) (genY W) *
          ((W.map (algebraMap F W.FunctionField)).a₁ *
              ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) +
            (W.map (algebraMap F W.FunctionField)).a₃ *
              (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W))) /
      (2 * ((W.map (algebraMap F W.FunctionField)).ψ 2).evalEval (genX W) (genY W) ^ 3))
    (by
      rw [eval₂_eval₂RingHom_apply, ← map_polynomial]
      exact doubling_equation_gen h2)

/-- Image of the `x`-generator under the multiplication-by-`2` pullback: the `x`-coordinate of
`2 • P`. -/
lemma mulByTwoCoordHom_X (h2 : (2 : F) ≠ 0) :
    mulByTwoCoordHom h2 (mk W (C X)) =
      ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) /
        (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W) := by
  rw [mulByTwoCoordHom,
    show mk W (C X) = AdjoinRoot.of W.polynomial X from rfl,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]

/-- Image of the `y`-generator (the root) under the multiplication-by-`2` pullback: the
`y`-coordinate of `2 • P`. -/
@[simp] lemma mulByTwoCoordHom_root (h2 : (2 : F) ≠ 0) :
    mulByTwoCoordHom h2 (AdjoinRoot.root W.polynomial) =
      ((W.map (algebraMap F W.FunctionField)).preΨ₄.eval (genX W) -
          ((W.map (algebraMap F W.FunctionField)).ψ 2).evalEval (genX W) (genY W) *
            ((W.map (algebraMap F W.FunctionField)).a₁ *
                ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) +
              (W.map (algebraMap F W.FunctionField)).a₃ *
                (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W))) /
        (2 * ((W.map (algebraMap F W.FunctionField)).ψ 2).evalEval (genX W) (genY W) ^ 3) := by
  rw [mulByTwoCoordHom, AdjoinRoot.lift_root]

end CoordinateRing
end WeierstrassCurve.Affine
