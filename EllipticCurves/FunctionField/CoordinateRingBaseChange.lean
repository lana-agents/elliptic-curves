/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Base change of the affine coordinate ring of a Weierstrass curve

Let `W` be a Weierstrass curve over a field `F` and let `K` be a field that is an `F`-algebra.
Writing `A := W.CoordinateRing = AdjoinRoot W.polynomial` and
`B := (W.map (algebraMap F K)).CoordinateRing`, this file provides:

* `WeierstrassCurve.Affine.CoordinateRing.baseChangeAlgEquiv`: the `K`-algebra isomorphism
  `B ≃ₐ[K] K ⊗[F] A`, obtained by composing `AdjoinRoot.tensorAlgEquiv` with
  `AdjoinRoot.mapAlgEquiv` along the `K`-algebra isomorphism `(polyEquivTensor' F K).symm`.

* the `Algebra A B` structure whose `algebraMap` is `CoordinateRing.map W (algebraMap F K)`.

* `Module.FaithfullyFlat A B`. Since `F` is a field, `K` is a faithfully flat `F`-module, hence
  `A ⊗[F] K` is a faithfully flat `A`-module; `baseChangeAlgEquiv` transports this to `B`.

## Design note on the instances

The `Algebra A B` and `Module.FaithfullyFlat A B` structures are registered as global
`instance`s: `B` carries no other `A`-algebra/module structure, so there is no diamond with any
existing declaration. Downstream files that use `A := W.CoordinateRing`,
`B := (W.map (algebraMap F K)).CoordinateRing` with algebra map
`CoordinateRing.map W (algebraMap F K)` therefore see the intended `Module.FaithfullyFlat A B`.
-/

open Polynomial TensorProduct

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
    (K : Type*) [Field K] [Algebra F K]

/-- The polynomial `W.polynomial : F[X][Y]` pushed into `(K ⊗[F] F[X])[X]` via the right
tensor-factor inclusion. Its `AdjoinRoot` mediates the base change. -/
private noncomputable def basePoly : Polynomial (K ⊗[F] F[X]) :=
  W.polynomial.map (Algebra.TensorProduct.includeRight (R := F) (A := K) (B := F[X])).toRingHom

/-- Base change of `AdjoinRoot` along `F → K`: `K ⊗[F] A ≃ₐ[K] AdjoinRoot (basePoly)`. -/
private noncomputable def e1 :
    K ⊗[F] W.CoordinateRing ≃ₐ[K] AdjoinRoot (basePoly W K) :=
  AdjoinRoot.tensorAlgEquiv W.polynomial (basePoly W K) rfl

/-- The two composite ring homomorphisms `F[X] → K[X]` agree:
`(polyEquivTensor' F K).symm ∘ includeRight = mapRingHom (algebraMap F K)`. -/
private lemma polyEquivTensor_symm_comp_includeRight :
    (↑(polyEquivTensor' (R := F) K).symm : (K ⊗[F] F[X]) →+* K[X]).comp
        (Algebra.TensorProduct.includeRight (R := F) (A := K) (B := F[X])).toRingHom
      = (Polynomial.mapRingHom (algebraMap F K)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [Algebra.TensorProduct.includeRight_apply, coe_polyEquivTensor'_symm,
      polyEquivTensor_symm_apply_tmul_eq_smul]
  · simp [Algebra.TensorProduct.includeRight_apply, coe_polyEquivTensor'_symm,
      polyEquivTensor_symm_apply_tmul_eq_smul]

/-- The base-changed polynomial `basePoly`, transported along `(polyEquivTensor' F K).symm`, is the
Weierstrass polynomial of the base-changed curve. -/
private lemma basePoly_map_polyEquivTensor_symm :
    (basePoly W K).map (↑(polyEquivTensor' (R := F) K).symm : (K ⊗[F] F[X]) →+* K[X])
      = (W.map (algebraMap F K)).polynomial := by
  rw [basePoly, Polynomial.map_map, polyEquivTensor_symm_comp_includeRight,
    WeierstrassCurve.Affine.map_polynomial]

/-- Transport `AdjoinRoot (basePoly)` (over `K ⊗[F] F[X]`) to `B = (W.map …).CoordinateRing`
(over `K[X]`) along the `K`-algebra isomorphism `(polyEquivTensor' F K).symm`. -/
private noncomputable def e2 :
    AdjoinRoot (basePoly W K) ≃ₐ[K] (W.map (algebraMap F K)).CoordinateRing :=
  AdjoinRoot.mapAlgEquiv (polyEquivTensor' (R := F) K).symm (basePoly W K)
    (W.map (algebraMap F K)).polynomial
    (by rw [basePoly_map_polyEquivTensor_symm])

/-- **Base change of the affine coordinate ring.** For a Weierstrass curve `W` over a field `F` and
a field `K` that is an `F`-algebra, the coordinate ring of the base-changed curve is the base change
of the coordinate ring:
`(W.map (algebraMap F K)).CoordinateRing ≃ₐ[K] K ⊗[F] W.CoordinateRing`. -/
noncomputable def baseChangeAlgEquiv :
    (W.map (algebraMap F K)).CoordinateRing ≃ₐ[K] K ⊗[F] W.CoordinateRing :=
  ((e1 W K).trans (e2 W K)).symm

/-- `(e1.trans e2)` applied to `1 ⊗ₜ a` recovers `CoordinateRing.map W (algebraMap F K) a`. -/
private lemma e1_trans_e2_includeRight (a : W.CoordinateRing) :
    (e1 W K).trans (e2 W K) (1 ⊗ₜ[F] a) = CoordinateRing.map W (algebraMap F K) a := by
  have key :
      ((e1 W K).trans (e2 W K)).toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := F) (A := K) (B := W.CoordinateRing)).toRingHom
        = CoordinateRing.map W (algebraMap F K) := by
    refine AdjoinRoot.ringHom_ext (RingHom.ext fun r => ?_) ?_
    · simp only [RingHom.comp_apply, AlgEquiv.coe_toAlgHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.trans_apply,
        Algebra.TensorProduct.includeRight_apply, e1, AdjoinRoot.tensorAlgEquiv_of, e2,
        AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of, coe_polyEquivTensor'_symm,
        polyEquivTensor_symm_apply_tmul_eq_smul, one_smul, CoordinateRing.map,
        AdjoinRoot.lift_of, Polynomial.coe_mapRingHom]
    · simp only [RingHom.comp_apply, AlgEquiv.coe_toAlgHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.trans_apply,
        Algebra.TensorProduct.includeRight_apply, e1, AdjoinRoot.tensorAlgEquiv_root, e2,
        AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root, CoordinateRing.map, AdjoinRoot.lift_root]
  have h := DFunLike.congr_fun key a
  simp only [RingHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply] at h
  exact h

@[simp]
theorem baseChangeAlgEquiv_map (a : W.CoordinateRing) :
    baseChangeAlgEquiv W K (CoordinateRing.map W (algebraMap F K) a) = 1 ⊗ₜ[F] a := by
  rw [baseChangeAlgEquiv, AlgEquiv.symm_apply_eq, e1_trans_e2_includeRight]

/-- The `Algebra W.CoordinateRing (W.map (algebraMap F K)).CoordinateRing` structure whose
`algebraMap` is `CoordinateRing.map W (algebraMap F K)`. As `B` carries no other
`W.CoordinateRing`-algebra structure this creates no diamond. -/
noncomputable instance instAlgebraCoordinateRingMap :
    Algebra W.CoordinateRing (W.map (algebraMap F K)).CoordinateRing :=
  RingHom.toAlgebra (CoordinateRing.map W (algebraMap F K))

/-- Multiplying by `1 ⊗ₜ a` on `K ⊗[F] A` corresponds, under `TensorProduct.comm`, to the
`A`-scalar action on `A ⊗[F] K`. -/
private lemma comm_one_tmul_mul (a : W.CoordinateRing) (y : K ⊗[F] W.CoordinateRing) :
    (TensorProduct.comm F K W.CoordinateRing) (((1 : K) ⊗ₜ[F] a) * y)
      = a • (TensorProduct.comm F K W.CoordinateRing) y := by
  induction y with
  | zero => simp
  | tmul k x =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.comm_tmul,
      TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  | add y1 y2 h1 h2 => rw [mul_add, map_add, map_add, h1, h2, smul_add]

/-- `B = (W.map (algebraMap F K)).CoordinateRing` is `A`-linearly isomorphic to `A ⊗[F] K`, where
the `A`-action on `B` is via `CoordinateRing.map W (algebraMap F K)`. This is the linear form of
`baseChangeAlgEquiv` needed to transport faithful flatness. -/
noncomputable def baseChangeLinearEquiv :
    (W.map (algebraMap F K)).CoordinateRing ≃ₗ[W.CoordinateRing] W.CoordinateRing ⊗[F] K where
  toFun b := TensorProduct.comm F K W.CoordinateRing (baseChangeAlgEquiv W K b)
  invFun t := (baseChangeAlgEquiv W K).symm ((TensorProduct.comm F K W.CoordinateRing).symm t)
  left_inv b := by simp
  right_inv t := by simp
  map_add' b1 b2 := by simp
  map_smul' a b := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, baseChangeAlgEquiv_map,
      comm_one_tmul_mul]

/-- **Faithful flatness of the base-changed coordinate ring.** For a Weierstrass curve `W` over a
field `F` and a field `K` that is an `F`-algebra, `(W.map (algebraMap F K)).CoordinateRing` is a
faithfully flat `W.CoordinateRing`-module (via `CoordinateRing.map W (algebraMap F K)`).

`F` is a field, so `K` is a faithfully flat `F`-module; base change makes `A ⊗[F] K` a faithfully
flat `A`-module, and `baseChangeLinearEquiv` transports this to `B`. -/
noncomputable instance instFaithfullyFlatCoordinateRingMap :
    Module.FaithfullyFlat W.CoordinateRing (W.map (algebraMap F K)).CoordinateRing := by
  haveI : Module.FaithfullyFlat F K := inferInstance
  haveI : Module.FaithfullyFlat W.CoordinateRing (W.CoordinateRing ⊗[F] K) := inferInstance
  exact Module.FaithfullyFlat.of_linearEquiv _ _ (baseChangeLinearEquiv W K)

end WeierstrassCurve.Affine.CoordinateRing
