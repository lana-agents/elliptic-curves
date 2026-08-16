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

The `mulByTwoEndo` / `mulByThreeEndo` commutation (`σ⋆ ∘ [n]∗ = [n]∗ ∘ σ⋆`) is a separate follow-on:
unlike `translateEndo` (whose generator images are pure `addX`/`addY`/`slope` expressions handled by
the curve-stability lemma `galoisFunctionField_curve_stable`), the `[n]∗` generator images are
division-polynomial rational functions `Φₙ/ΨSqₙ`, whose `σ⋆`-invariance needs `map_Φ` / `map_Ψ`-type
coefficient-transport lemmas. All the substrate it would consume (the semilinear automorphism, the
generator/constant images, and `galoisFunctionField_curve_stable`) is delivered here.

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
* `galoisFunctionField_translateEndo` — `σ⋆ ∘ translateEndo h = translateEndo (σ·h) ∘ σ⋆`.

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

end WeierstrassCurve.Affine.CoordinateRing
