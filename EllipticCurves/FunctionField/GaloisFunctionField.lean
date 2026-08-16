/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationComposition
import EllipticCurves.FunctionField.MulByTwoEndomorphism
import EllipticCurves.FunctionField.MulByThreeEndomorphism

/-!
# The Galois action on the function field and its commutation with the geometric endomorphisms

Let `W` be an elliptic curve over a field `S`, let `F` be a field extension of `S`, and let
`σ : F ≃ₐ[S] F` be an `S`-algebra automorphism of `F` (a Galois automorphism when `F / S` is
Galois). Working over the **base-changed curve** `W⁄F : Affine F`, every single-field
`FunctionField/*` construction (`genX (W⁄F)`, `translateEndo (W := W⁄F)`, `mulByTwoEndo`, …)
instantiates verbatim. This file builds the **σ-semilinear automorphism** of the function field
`F(W⁄F)` induced by `σ`, and proves it commutes with the **translation endomorphism** — the
reusable, Ward-, normality-, and rung-4-**independent** substrate for the Galois-equivariance of the
divisor-theoretic Weil-pairing element `e_n(S, T)` (issue #419, Silverman AEC III.8).

The `mulByTwoEndo` / `mulByThreeEndo` commutation (`σ⋆ ∘ [n]∗ = [n]∗ ∘ σ⋆`) is also proved here.
Unlike `translateEndo` (whose generator images are pure `addX`/`addY`/`slope` expressions handled by
the curve-stability lemma `galoisFunctionField_curve_stable`), the `[n]∗` generator images are
division-polynomial rational functions `Φₙ/ΨSqₙ`, `ωₙ/ψₙ³`, whose `σ⋆`-invariance goes through the
coefficient-transport lemmas `WeierstrassCurve.map_Φ` / `map_Ψ` / `map_ψ` / `map_preΨ` (etc.) of
`Mathlib`'s division polynomials combined with `galoisFunctionField_curve_stable`: applying `σ⋆`
coefficientwise to a division polynomial of `W ⁄ F(W⁄F)` returns the same polynomial, so evaluating
it at the (σ⋆-fixed) generators is σ⋆-invariant. Note there is **no point-shift** on the right-hand
side (unlike `translateEndo`): the `[n]∗` coordinates have coefficients pulled from `algebraMap S F`
(the base curve lives over `S`), which `σ` fixes.

## The construction avoids the transport hazard

The base-changed curve is **σ-stable**: `(W⁄F).map (σ : F →+* F) = W⁄F`
(`baseChange_map_algEquiv`), because `σ` is an `S`-algebra map and `W⁄F`'s coefficients lie in the
image of `algebraMap S F`. Rather than transport `CoordinateRing.map σ` across this *propositional*
equality (whose codomain is `((W⁄F).map σ).CoordinateRing`, not literally `(W⁄F).CoordinateRing`),
we build the semilinear map as a genuine **self-map** `galoisCoordEndo σ` of `(W⁄F).CoordinateRing`
via `AdjoinRoot.lift`, using the σ-stability only as a propositional rewrite inside the
well-definedness proof. This keeps every type literally `(W⁄F).CoordinateRing` / `F(W⁄F)`, so the
generator images and endomorphism-commutation lemmas need no `Eq.mpr` casts.

## Main definitions

* `galoisCoordEndo σ` — the σ-semilinear ring endomorphism of `(W⁄F).CoordinateRing`
  (`X ↦ X`, `Y ↦ Y`, and `c ↦ σ c` on `F`-constants);
* `galoisCoordRing σ` — its packaging as a `RingEquiv` (inverse from `σ⁻¹`);
* `galoisFunctionField σ` — the induced σ-semilinear automorphism of the function field `F(W⁄F)`.

## Main statements

* `galoisFunctionField_genX` / `_genY` — `σ⋆` fixes the coordinate generators;
* `galoisFunctionField_algebraMap` — `σ⋆ (algebraMap c) = algebraMap (σ c)` (σ-semilinearity);
* `galoisFunctionField_curve_stable` — `σ⋆` fixes the base-changed curve `W ⁄ F(W⁄F)`;
* `galoisFunctionField_translateEndo` — `σ⋆ ∘ translateEndo h = translateEndo (σ·h) ∘ σ⋆`;
* `galoisFunctionField_mulByTwoEndo` / `_mulByThreeEndo` — `σ⋆ ∘ [n]∗ = [n]∗ ∘ σ⋆` for `n = 2, 3`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine.CoordinateRing

variable {S F : Type*} [Field S] [Field F] [Algebra S F] {W : Affine S}

/-- The base-field constant `c`, viewed in `(W⁄F).CoordinateRing`, is `AdjoinRoot.of` of `C c`. -/
lemma algebraMap_coordinateRing_eq_of (c : F) :
    algebraMap F (W⁄F).CoordinateRing c = AdjoinRoot.of (W⁄F).polynomial (C c) := by
  rw [IsScalarTower.algebraMap_apply F F[X] (W⁄F).CoordinateRing, AdjoinRoot.algebraMap_eq,
    ← Polynomial.C_eq_algebraMap]

/-! ### σ-stability of the base-changed curve -/

/-- The base-changed curve `W⁄F` is stable under an `S`-algebra automorphism `σ` of `F`, because
its coefficients lie in the image of `algebraMap S F` and `σ` fixes that image. -/
lemma baseChange_map_algEquiv (σ : F ≃ₐ[S] F) : (W⁄F).map (σ : F →+* F) = W⁄F := by
  have hcomp : (σ : F →+* F).comp (algebraMap S F) = algebraMap S F :=
    RingHom.ext fun s => σ.commutes s
  change (W.map (algebraMap S F)).map (σ : F →+* F) = W.map (algebraMap S F)
  simp only [WeierstrassCurve.map_map, hcomp]

/-- The σ-stability at the level of the curve polynomial: `σ` fixes `(W⁄F).polynomial`. -/
lemma polynomial_map_algEquiv (σ : F ≃ₐ[S] F) :
    (W⁄F).polynomial.map (mapRingHom (σ : F →+* F)) = (W⁄F).polynomial := by
  rw [← WeierstrassCurve.Affine.map_polynomial, baseChange_map_algEquiv]

/-! ### The σ-semilinear endomorphism of the coordinate ring -/

/-- **The σ-semilinear ring endomorphism of `(W⁄F).CoordinateRing`.** It sends the coordinate
generators `X`, `Y` (the class of `AdjoinRoot.root`) to themselves and acts by `σ` on the
`F`-constants. Built as `AdjoinRoot.lift` of `σ`-twisted constants, well-defined because `σ` fixes
`(W⁄F).polynomial` (`polynomial_map_algEquiv`). -/
noncomputable def galoisCoordEndo (σ : F ≃ₐ[S] F) :
    (W⁄F).CoordinateRing →+* (W⁄F).CoordinateRing :=
  AdjoinRoot.lift ((AdjoinRoot.of (W⁄F).polynomial).comp (mapRingHom (σ : F →+* F)))
    (AdjoinRoot.root (W⁄F).polynomial)
    (by rw [← Polynomial.eval₂_map, polynomial_map_algEquiv, AdjoinRoot.eval₂_root])

/-- `galoisCoordEndo σ` on an element coming from a coefficient polynomial `p : F[X]` via
`AdjoinRoot.of`: it maps `p` through `σ` coefficientwise. -/
lemma galoisCoordEndo_of (σ : F ≃ₐ[S] F) (p : F[X]) :
    galoisCoordEndo σ (AdjoinRoot.of (W⁄F).polynomial p)
      = AdjoinRoot.of (W⁄F).polynomial (p.map (σ : F →+* F)) := by
  rw [galoisCoordEndo, AdjoinRoot.lift_of, RingHom.comp_apply, coe_mapRingHom]

/-- `galoisCoordEndo σ` fixes the `Y`-generator (the class of `AdjoinRoot.root`). -/
@[simp] lemma galoisCoordEndo_root (σ : F ≃ₐ[S] F) :
    galoisCoordEndo σ (AdjoinRoot.root (W⁄F).polynomial) = AdjoinRoot.root (W⁄F).polynomial := by
  rw [galoisCoordEndo, AdjoinRoot.lift_root]

/-- `galoisCoordEndo σ` fixes the `X`-generator `mk (C X)`. -/
@[simp] lemma galoisCoordEndo_mk_C_X (σ : F ≃ₐ[S] F) :
    galoisCoordEndo σ (mk (W⁄F) (C X)) = mk (W⁄F) (C X) := by
  have h : mk (W⁄F) (C X) = AdjoinRoot.of (W⁄F).polynomial X := rfl
  rw [h, galoisCoordEndo_of, Polynomial.map_X]

/-- `galoisCoordEndo σ` acts by `σ` on the `F`-constants of the coordinate ring. -/
@[simp] lemma galoisCoordEndo_algebraMap (σ : F ≃ₐ[S] F) (c : F) :
    galoisCoordEndo σ (algebraMap F (W⁄F).CoordinateRing c)
      = algebraMap F (W⁄F).CoordinateRing (σ c) := by
  have hcoe : ((σ : F →+* F) c) = σ c := rfl
  rw [algebraMap_coordinateRing_eq_of, galoisCoordEndo_of, Polynomial.map_C, hcoe,
    ← algebraMap_coordinateRing_eq_of]

/-- `galoisCoordEndo σ⁻¹` is a two-sided inverse of `galoisCoordEndo σ`: their composite fixes both
generators and undoes `σ` on the constants. -/
lemma galoisCoordEndo_comp (σ : F ≃ₐ[S] F) :
    (galoisCoordEndo σ.symm).comp (galoisCoordEndo σ) = RingHom.id (W⁄F).CoordinateRing := by
  refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
  · simp only [RingHom.comp_apply, RingHom.id_apply, ← algebraMap_coordinateRing_eq_of,
      galoisCoordEndo_algebraMap, AlgEquiv.symm_apply_apply]
  · change (galoisCoordEndo σ.symm) (galoisCoordEndo σ (AdjoinRoot.of (W⁄F).polynomial X))
      = RingHom.id _ (AdjoinRoot.of (W⁄F).polynomial X)
    have hX : AdjoinRoot.of (W⁄F).polynomial X = mk (W⁄F) (C X) := rfl
    rw [hX, galoisCoordEndo_mk_C_X, galoisCoordEndo_mk_C_X, RingHom.id_apply]
  · rw [RingHom.comp_apply, galoisCoordEndo_root, galoisCoordEndo_root, RingHom.id_apply]

/-- **The σ-semilinear automorphism of `(W⁄F).CoordinateRing`.** -/
noncomputable def galoisCoordRing (σ : F ≃ₐ[S] F) :
    (W⁄F).CoordinateRing ≃+* (W⁄F).CoordinateRing :=
  RingEquiv.ofRingHom (galoisCoordEndo σ) (galoisCoordEndo σ.symm)
    (by simpa using galoisCoordEndo_comp σ.symm)
    (galoisCoordEndo_comp σ)

@[simp] lemma galoisCoordRing_apply (σ : F ≃ₐ[S] F) (a : (W⁄F).CoordinateRing) :
    galoisCoordRing σ a = galoisCoordEndo σ a := rfl

/-! ### The σ-semilinear automorphism of the function field -/

/-- **The σ-semilinear automorphism of the function field `F(W⁄F)`** induced by an `S`-algebra
automorphism `σ` of `F`, obtained from `galoisCoordRing σ` by functoriality of the fraction field.
It fixes the coordinate generators `genX`, `genY` and acts by `σ` on the base constants. -/
noncomputable def galoisFunctionField (σ : F ≃ₐ[S] F) :
    (W⁄F).FunctionField ≃+* (W⁄F).FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (A := (W⁄F).CoordinateRing) (B := (W⁄F).CoordinateRing)
    (K := (W⁄F).FunctionField) (L := (W⁄F).FunctionField) (galoisCoordRing σ)

/-- Defining property of `galoisFunctionField`: it agrees with `galoisCoordRing σ` on the image of
the coordinate ring. -/
lemma galoisFunctionField_algebraMap_coordRing (σ : F ≃ₐ[S] F) (a : (W⁄F).CoordinateRing) :
    galoisFunctionField σ (algebraMap (W⁄F).CoordinateRing (W⁄F).FunctionField a)
      = algebraMap (W⁄F).CoordinateRing (W⁄F).FunctionField (galoisCoordEndo σ a) := by
  rw [galoisFunctionField, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

/-- `galoisFunctionField σ` fixes the generic `x`-coordinate. -/
@[simp] lemma galoisFunctionField_genX (σ : F ≃ₐ[S] F) :
    galoisFunctionField σ (genX (W⁄F)) = genX (W⁄F) := by
  rw [genX, genPsi, galoisFunctionField_algebraMap_coordRing, galoisCoordEndo_mk_C_X]

/-- `galoisFunctionField σ` fixes the generic `y`-coordinate. -/
@[simp] lemma galoisFunctionField_genY (σ : F ≃ₐ[S] F) :
    galoisFunctionField σ (genY (W⁄F)) = genY (W⁄F) := by
  rw [genY, genPsi, galoisFunctionField_algebraMap_coordRing, galoisCoordEndo_root]

/-- **σ-semilinearity on constants.** `galoisFunctionField σ` acts by `σ` on the base field `F`. -/
@[simp] lemma galoisFunctionField_algebraMap (σ : F ≃ₐ[S] F) (c : F) :
    galoisFunctionField σ (algebraMap F (W⁄F).FunctionField c)
      = algebraMap F (W⁄F).FunctionField (σ c) := by
  rw [IsScalarTower.algebraMap_apply F (W⁄F).CoordinateRing (W⁄F).FunctionField c,
    galoisFunctionField_algebraMap_coordRing, galoisCoordEndo_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-! ### Equivariance of the translation endomorphism -/

section Equivariance

variable {x₂ y₂ : F}

/-- If `(x₂, y₂)` lies on `W⁄F`, so does its `σ`-image `(σ x₂, σ y₂)` — `σ` fixes `W⁄F`. -/
lemma equation_algEquiv (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂) :
    (W⁄F).Equation (σ x₂) (σ y₂) := by
  have h := (WeierstrassCurve.Affine.map_equation (W := W⁄F) (f := (σ : F →+* F))
    (EquivLike.injective σ) x₂ y₂).mpr h₂
  rwa [baseChange_map_algEquiv] at h

/-- **Curve stability.** Although `galoisFunctionField σ` twists `F` by `σ`, the coefficients of
`W⁄F` come from `S`, which `σ` fixes, so base-changing `W ⁄ F(W⁄F)` along `galoisFunctionField σ`
returns the same curve. -/
lemma galoisFunctionField_curve_stable (σ : F ≃ₐ[S] F) :
    ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).map
        (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField)
      = (W⁄F).map (algebraMap F (W⁄F).FunctionField) := by
  have hcomp : ((galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField).comp
      (algebraMap F (W⁄F).FunctionField)).comp (algebraMap S F)
        = (algebraMap F (W⁄F).FunctionField).comp (algebraMap S F) := by
    ext s
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
      galoisFunctionField_algebraMap, σ.commutes]
  change ((W.map (algebraMap S F)).map (algebraMap F (W⁄F).FunctionField)).map
      (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField)
    = (W.map (algebraMap S F)).map (algebraMap F (W⁄F).FunctionField)
  simp only [WeierstrassCurve.map_map]
  rw [← RingHom.comp_assoc, hcomp]

/-- `galoisFunctionField σ` commutes with the addition-law `x`-coordinate `addX` of `W ⁄ F(W⁄F)`. -/
lemma galoisFunctionField_addX (σ : F ≃ₐ[S] F) (x₁ x₃ ℓ : (W⁄F).FunctionField) :
    galoisFunctionField σ (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).addX x₁ x₃ ℓ)
      = ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).addX
          (galoisFunctionField σ x₁) (galoisFunctionField σ x₃) (galoisFunctionField σ ℓ) := by
  have h := WeierstrassCurve.Affine.map_addX (W' := (W⁄F).map (algebraMap F (W⁄F).FunctionField))
    (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField)
    (x₁ := x₁) (x₂ := x₃) (ℓ := ℓ)
  rw [galoisFunctionField_curve_stable] at h
  exact h.symm

/-- `galoisFunctionField σ` commutes with the addition-law `y`-coordinate `addY` of `W ⁄ F(W⁄F)`. -/
lemma galoisFunctionField_addY (σ : F ≃ₐ[S] F) (x₁ x₃ y₁ ℓ : (W⁄F).FunctionField) :
    galoisFunctionField σ (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).addY x₁ x₃ y₁ ℓ)
      = ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).addY
          (galoisFunctionField σ x₁) (galoisFunctionField σ x₃) (galoisFunctionField σ y₁)
          (galoisFunctionField σ ℓ) := by
  have h := WeierstrassCurve.Affine.map_addY (W' := (W⁄F).map (algebraMap F (W⁄F).FunctionField))
    (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField)
    (x₁ := x₁) (x₂ := x₃) (y₁ := y₁) (ℓ := ℓ)
  rw [galoisFunctionField_curve_stable] at h
  exact h.symm

open Classical in
/-- `galoisFunctionField σ` commutes with the slope `slope` of `W ⁄ F(W⁄F)`. -/
lemma galoisFunctionField_slope (σ : F ≃ₐ[S] F) (x₁ x₃ y₁ y₃ : (W⁄F).FunctionField) :
    galoisFunctionField σ (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).slope x₁ x₃ y₁ y₃)
      = ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).slope
          (galoisFunctionField σ x₁) (galoisFunctionField σ x₃)
          (galoisFunctionField σ y₁) (galoisFunctionField σ y₃) := by
  have h := WeierstrassCurve.Affine.map_slope (W := (W⁄F).map (algebraMap F (W⁄F).FunctionField))
    (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField) x₁ x₃ y₁ y₃
  rw [galoisFunctionField_curve_stable] at h
  exact h.symm

section IsElliptic

variable [W.IsElliptic]

/-- The base-changed curve `W⁄F` is elliptic (bridging the `WeierstrassCurve.map` instance across
the `baseChange` definition, which is not unfolded during instance synthesis). -/
instance : (W⁄F).IsElliptic := inferInstanceAs (W.map (algebraMap S F)).IsElliptic

open Classical in
/-- **Equivariance of the translation endomorphism.**
`galoisFunctionField σ ∘ translateEndo h₂ = translateEndo (σ·h₂) ∘ galoisFunctionField σ`, where
`σ·h₂` is the translated point `(σ x₂, σ y₂)`. The reusable substrate for the Galois-equivariance of
`e_n` in the translation slot. -/
theorem galoisFunctionField_translateEndo (σ : F ≃ₐ[S] F) (h₂ : (W⁄F).Equation x₂ y₂)
    (z : (W⁄F).FunctionField) :
    galoisFunctionField σ (translateEndo h₂ z)
      = translateEndo (equation_algEquiv σ h₂) (galoisFunctionField σ z) := by
  -- The coordinate-ring identity `σ⋆ ∘ translateCoordHom h₂ = translateCoordHom (σ·h₂) ∘ σ⋆`.
  have hcr : (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField).comp
      (translateCoordHom h₂)
      = (translateCoordHom (equation_algEquiv σ h₂)).comp (galoisCoordEndo σ) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ← algebraMap_coordinateRing_eq_of,
        translateCoordHom_algebraMap, galoisFunctionField_algebraMap, galoisCoordEndo_algebraMap]
    · change galoisFunctionField σ (translateCoordHom h₂ (mk (W⁄F) (C X)))
        = translateCoordHom (equation_algEquiv σ h₂) (galoisCoordEndo σ (mk (W⁄F) (C X)))
      rw [galoisCoordEndo_mk_C_X, translateCoordHom_X, translateCoordHom_X]
      simp only [galoisFunctionField_addX, galoisFunctionField_slope, galoisFunctionField_genX,
        galoisFunctionField_genY, galoisFunctionField_algebraMap]
    · change galoisFunctionField σ (translateCoordHom h₂ (AdjoinRoot.root (W⁄F).polynomial))
        = translateCoordHom (equation_algEquiv σ h₂)
            (galoisCoordEndo σ (AdjoinRoot.root (W⁄F).polynomial))
      rw [galoisCoordEndo_root, translateCoordHom_root, translateCoordHom_root]
      simp only [galoisFunctionField_addY, galoisFunctionField_slope, galoisFunctionField_genX,
        galoisFunctionField_genY, galoisFunctionField_algebraMap]
  have key : (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField).comp
      (translateEndo h₂)
      = (translateEndo (equation_algEquiv σ h₂)).comp
          (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField) := by
    refine IsFractionRing.ringHom_ext (A := (W⁄F).CoordinateRing) (fun a => ?_)
    have hcra := RingHom.congr_fun hcr a
    simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom, translateEndo_algebraMap,
      galoisFunctionField_algebraMap_coordRing] using hcra
  have := RingHom.congr_fun key z
  simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom] using this

end IsElliptic

end Equivariance

/-! ### Equivariance of the multiplication-by-`n` endomorphisms

Unlike `translateEndo`, whose generator images are `addX`/`addY`/`slope` expressions, the `[n]∗`
generator images are the division-polynomial rational functions `Φₙ/ΨSqₙ`, `ωₙ/ψₙ³`. Their
`σ⋆`-invariance is packaged through the atomic lemmas below: applying `galoisFunctionField σ`
coefficientwise to any division polynomial of `W ⁄ F(W⁄F)` returns the same polynomial
(`WeierstrassCurve.map_Φ`/… together with `galoisFunctionField_curve_stable`), so evaluating it at
the σ⋆-fixed generators `genX`, `genY` is σ⋆-invariant. There is no point-shift on the right-hand
side: the coefficients of the base-changed curve come from `S`, which `σ` fixes. -/

section MulByEndo

open scoped Polynomial.Bivariate

/-- If a univariate polynomial `p` over `F(W⁄F)` is σ⋆-invariant coefficientwise
(`p.map σ⋆ = p`), then `σ⋆` fixes its value at the (σ⋆-fixed) generic `x`-coordinate. -/
lemma galoisFunctionField_eval_genX (σ : F ≃ₐ[S] F) {p : (W⁄F).FunctionField[X]}
    (hp : p.map (galoisFunctionField (W := W) σ :
        (W⁄F).FunctionField →+* (W⁄F).FunctionField) = p) :
    galoisFunctionField σ (p.eval (genX (W⁄F))) = p.eval (genX (W⁄F)) := by
  have h : (p.map (galoisFunctionField (W := W) σ :
        (W⁄F).FunctionField →+* (W⁄F).FunctionField)).eval
        ((galoisFunctionField (W := W) σ :
          (W⁄F).FunctionField →+* (W⁄F).FunctionField) (genX (W⁄F)))
      = (galoisFunctionField (W := W) σ :
          (W⁄F).FunctionField →+* (W⁄F).FunctionField) (p.eval (genX (W⁄F))) :=
    Polynomial.eval_map_apply ..
  rw [hp, RingEquiv.coe_toRingHom, galoisFunctionField_genX] at h
  exact h.symm

/-- If a bivariate polynomial `q` over `F(W⁄F)` is σ⋆-invariant coefficientwise
(`q.map (mapRingHom σ⋆) = q`), then `σ⋆` fixes its value at the (σ⋆-fixed) generic point. -/
lemma galoisFunctionField_evalEval_gen (σ : F ≃ₐ[S] F) {q : (W⁄F).FunctionField[X][Y]}
    (hq : q.map (mapRingHom (galoisFunctionField (W := W) σ :
        (W⁄F).FunctionField →+* (W⁄F).FunctionField)) = q) :
    galoisFunctionField σ (q.evalEval (genX (W⁄F)) (genY (W⁄F)))
      = q.evalEval (genX (W⁄F)) (genY (W⁄F)) := by
  have h : (q.map (mapRingHom (galoisFunctionField (W := W) σ :
        (W⁄F).FunctionField →+* (W⁄F).FunctionField))).evalEval
        ((galoisFunctionField (W := W) σ :
          (W⁄F).FunctionField →+* (W⁄F).FunctionField) (genX (W⁄F)))
        ((galoisFunctionField (W := W) σ :
          (W⁄F).FunctionField →+* (W⁄F).FunctionField) (genY (W⁄F)))
      = (galoisFunctionField (W := W) σ :
          (W⁄F).FunctionField →+* (W⁄F).FunctionField) (q.evalEval (genX (W⁄F)) (genY (W⁄F))) :=
    Polynomial.map_mapRingHom_evalEval ..
  rw [hq, RingEquiv.coe_toRingHom, galoisFunctionField_genX, galoisFunctionField_genY] at h
  exact h.symm

/-- `σ⋆` fixes the coefficients `aᵢ` of the base-changed curve `W ⁄ F(W⁄F)` (they come from `S`),
packaged as fixing the `a₁` coefficient. -/
@[simp] lemma galoisFunctionField_map_a₁ (σ : F ≃ₐ[S] F) :
    galoisFunctionField σ (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).a₁)
      = ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).a₁ :=
  congrArg WeierstrassCurve.a₁ (galoisFunctionField_curve_stable (W := W) σ)

/-- `σ⋆` fixes the `a₃` coefficient of the base-changed curve `W ⁄ F(W⁄F)`. -/
@[simp] lemma galoisFunctionField_map_a₃ (σ : F ≃ₐ[S] F) :
    galoisFunctionField σ (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).a₃)
      = ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).a₃ :=
  congrArg WeierstrassCurve.a₃ (galoisFunctionField_curve_stable (W := W) σ)

/-- `σ⋆` fixes `Φₙ(genX)` (the `x`-numerator of `[n]∗`). -/
@[simp] lemma galoisFunctionField_Φ_eval (σ : F ≃ₐ[S] F) (n : ℤ) :
    galoisFunctionField σ
        ((((W⁄F).map (algebraMap F (W⁄F).FunctionField)).Φ n).eval (genX (W⁄F)))
      = (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).Φ n).eval (genX (W⁄F)) :=
  galoisFunctionField_eval_genX σ
    (by simp only [← WeierstrassCurve.map_Φ, galoisFunctionField_curve_stable])

/-- `σ⋆` fixes `Ψ₂Sq(genX)` (the `x`-denominator of `[2]∗`). -/
@[simp] lemma galoisFunctionField_Ψ₂Sq_eval (σ : F ≃ₐ[S] F) :
    galoisFunctionField σ
        (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).Ψ₂Sq.eval (genX (W⁄F)))
      = ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).Ψ₂Sq.eval (genX (W⁄F)) :=
  galoisFunctionField_eval_genX σ
    (by simp only [← WeierstrassCurve.map_Ψ₂Sq, galoisFunctionField_curve_stable])

/-- `σ⋆` fixes `ΨSqₙ(genX)` (the `x`-denominator of `[n]∗`). -/
@[simp] lemma galoisFunctionField_ΨSq_eval (σ : F ≃ₐ[S] F) (n : ℤ) :
    galoisFunctionField σ
        ((((W⁄F).map (algebraMap F (W⁄F).FunctionField)).ΨSq n).eval (genX (W⁄F)))
      = (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).ΨSq n).eval (genX (W⁄F)) :=
  galoisFunctionField_eval_genX σ
    (by simp only [← WeierstrassCurve.map_ΨSq, galoisFunctionField_curve_stable])

/-- `σ⋆` fixes `preΨ₄(genX)`. -/
@[simp] lemma galoisFunctionField_preΨ₄_eval (σ : F ≃ₐ[S] F) :
    galoisFunctionField σ
        (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).preΨ₄.eval (genX (W⁄F)))
      = ((W⁄F).map (algebraMap F (W⁄F).FunctionField)).preΨ₄.eval (genX (W⁄F)) :=
  galoisFunctionField_eval_genX σ
    (by simp only [← WeierstrassCurve.map_preΨ₄, galoisFunctionField_curve_stable])

/-- `σ⋆` fixes `preΨₙ(genX)`. -/
@[simp] lemma galoisFunctionField_preΨ_eval (σ : F ≃ₐ[S] F) (n : ℤ) :
    galoisFunctionField σ
        ((((W⁄F).map (algebraMap F (W⁄F).FunctionField)).preΨ n).eval (genX (W⁄F)))
      = (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).preΨ n).eval (genX (W⁄F)) :=
  galoisFunctionField_eval_genX σ
    (by simp only [← WeierstrassCurve.map_preΨ, galoisFunctionField_curve_stable])

/-- `σ⋆` fixes `ψₙ(genX, genY)` (the bivariate division polynomial). -/
@[simp] lemma galoisFunctionField_ψ_evalEval (σ : F ≃ₐ[S] F) (n : ℤ) :
    galoisFunctionField σ
        ((((W⁄F).map (algebraMap F (W⁄F).FunctionField)).ψ n).evalEval
          (genX (W⁄F)) (genY (W⁄F)))
      = (((W⁄F).map (algebraMap F (W⁄F).FunctionField)).ψ n).evalEval
          (genX (W⁄F)) (genY (W⁄F)) :=
  galoisFunctionField_evalEval_gen σ
    (by simp only [← WeierstrassCurve.map_ψ, galoisFunctionField_curve_stable])

/-- **Equivariance of the multiplication-by-`2` endomorphism.**
`galoisFunctionField σ ∘ mulByTwoEndo h2 = mulByTwoEndo h2 ∘ galoisFunctionField σ` — with no
point-shift, since the `[2]∗` coordinates have `S`-coefficients which `σ` fixes. -/
theorem galoisFunctionField_mulByTwoEndo (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0)
    (z : (W⁄F).FunctionField) :
    galoisFunctionField σ (mulByTwoEndo h2 z) = mulByTwoEndo h2 (galoisFunctionField σ z) := by
  -- coordinate-ring identity `σ⋆ ∘ mulByTwoCoordHom = mulByTwoCoordHom ∘ σ⋆`
  have hcr : (galoisFunctionField (W := W) σ :
        (W⁄F).FunctionField →+* (W⁄F).FunctionField).comp (mulByTwoCoordHom h2)
      = (mulByTwoCoordHom h2).comp (galoisCoordEndo σ) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ← algebraMap_coordinateRing_eq_of,
        mulByTwoCoordHom_algebraMap, galoisFunctionField_algebraMap, galoisCoordEndo_algebraMap]
    · change galoisFunctionField σ (mulByTwoCoordHom h2 (mk (W⁄F) (C X)))
        = mulByTwoCoordHom h2 (galoisCoordEndo σ (mk (W⁄F) (C X)))
      rw [galoisCoordEndo_mk_C_X, mulByTwoCoordHom_X, map_div₀]
      simp only [galoisFunctionField_Φ_eval, galoisFunctionField_Ψ₂Sq_eval]
    · change galoisFunctionField σ (mulByTwoCoordHom h2 (AdjoinRoot.root (W⁄F).polynomial))
        = mulByTwoCoordHom h2 (galoisCoordEndo σ (AdjoinRoot.root (W⁄F).polynomial))
      rw [galoisCoordEndo_root, mulByTwoCoordHom_root]
      simp only [map_div₀, map_sub, map_mul, map_add, map_pow, map_ofNat,
        galoisFunctionField_map_a₁, galoisFunctionField_map_a₃, galoisFunctionField_Φ_eval,
        galoisFunctionField_Ψ₂Sq_eval, galoisFunctionField_preΨ₄_eval,
        galoisFunctionField_ψ_evalEval]
  -- lift to the function field via the universal property of the fraction field
  have key : (galoisFunctionField (W := W) σ :
        (W⁄F).FunctionField →+* (W⁄F).FunctionField).comp (mulByTwoEndo h2)
      = (mulByTwoEndo h2).comp
          (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField) := by
    refine IsFractionRing.ringHom_ext (A := (W⁄F).CoordinateRing) (fun a => ?_)
    have hcra := RingHom.congr_fun hcr a
    simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom, mulByTwoEndo_algebraMap,
      galoisFunctionField_algebraMap_coordRing] using hcra
  have := RingHom.congr_fun key z
  simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom] using this

/-- **Equivariance of the multiplication-by-`3` endomorphism.**
`galoisFunctionField σ ∘ mulByThreeEndo h2 h3 = mulByThreeEndo h2 h3 ∘ galoisFunctionField σ` —
with no point-shift, since the `[3]∗` coordinates have `S`-coefficients which `σ` fixes. -/
theorem galoisFunctionField_mulByThreeEndo (σ : F ≃ₐ[S] F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (z : (W⁄F).FunctionField) :
    galoisFunctionField σ (mulByThreeEndo h2 h3 z)
      = mulByThreeEndo h2 h3 (galoisFunctionField σ z) := by
  have hcr : (galoisFunctionField (W := W) σ :
        (W⁄F).FunctionField →+* (W⁄F).FunctionField).comp (mulByThreeCoordHom h2 h3)
      = (mulByThreeCoordHom h2 h3).comp (galoisCoordEndo σ) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ← algebraMap_coordinateRing_eq_of,
        mulByThreeCoordHom_algebraMap, galoisFunctionField_algebraMap, galoisCoordEndo_algebraMap]
    · change galoisFunctionField σ (mulByThreeCoordHom h2 h3 (mk (W⁄F) (C X)))
        = mulByThreeCoordHom h2 h3 (galoisCoordEndo σ (mk (W⁄F) (C X)))
      rw [galoisCoordEndo_mk_C_X, mulByThreeCoordHom_X, map_div₀]
      simp only [galoisFunctionField_Φ_eval, galoisFunctionField_ΨSq_eval]
    · change galoisFunctionField σ (mulByThreeCoordHom h2 h3 (AdjoinRoot.root (W⁄F).polynomial))
        = mulByThreeCoordHom h2 h3 (galoisCoordEndo σ (AdjoinRoot.root (W⁄F).polynomial))
      rw [galoisCoordEndo_root, mulByThreeCoordHom_root]
      simp only [map_div₀, map_sub, map_mul, map_add, map_pow, map_ofNat,
        galoisFunctionField_map_a₁, galoisFunctionField_map_a₃, galoisFunctionField_genX,
        galoisFunctionField_genY, galoisFunctionField_Φ_eval,
        galoisFunctionField_preΨ_eval, galoisFunctionField_preΨ₄_eval,
        galoisFunctionField_ψ_evalEval]
  have key : (galoisFunctionField (W := W) σ :
        (W⁄F).FunctionField →+* (W⁄F).FunctionField).comp (mulByThreeEndo h2 h3)
      = (mulByThreeEndo h2 h3).comp
          (galoisFunctionField (W := W) σ : (W⁄F).FunctionField →+* (W⁄F).FunctionField) := by
    refine IsFractionRing.ringHom_ext (A := (W⁄F).CoordinateRing) (fun a => ?_)
    have hcra := RingHom.congr_fun hcr a
    simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom, mulByThreeEndo_algebraMap,
      galoisFunctionField_algebraMap_coordRing] using hcra
  have := RingHom.congr_fun key z
  simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom] using this

end MulByEndo

end WeierstrassCurve.Affine.CoordinateRing
