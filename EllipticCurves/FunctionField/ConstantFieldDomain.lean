/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.ConstantField
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Basic

/-!
# Discharging the geometric-integrality hypothesis of the constant field

`ConstantField.lean` (#434) reduced `algebraicClosure F W.FunctionField = ⊥` — the statement that
`F` is the field of constants of `F(W)` — to the geometric-integrality datum
`IsDomain (AlgebraicClosure F ⊗[F] W.FunctionField)`.  This file **discharges that hypothesis
unconditionally**, making the constant-field statement (and hence the constancy / translation-slot
bilinearity of the Weil-pairing element, #162) hold for `[Field F]` alone.

## Strategy

Write `F̄ := AlgebraicClosure F`, a field hence a domain.

1. **The coordinate ring base-changes to a domain.**  `W.CoordinateRing = AdjoinRoot W.polynomial`
   with `W.polynomial : F[X][Y]`.  By `AdjoinRoot.tensorAlgEquiv`,
   `F̄ ⊗[F] W.CoordinateRing ≃ₐ[F̄] AdjoinRoot q` where `q := W.polynomial.map includeRight`.  Under
   the base-ring isomorphism `F̄ ⊗[F] F[X] ≃ₐ[F] F̄[X]` (`polyEquivTensor`), `q` corresponds to
   `(W.map (algebraMap F F̄)).polynomial`, which is irreducible (`irreducible_polynomial` over the
   domain `F̄`), hence prime; primeness transfers back to `q`, so `AdjoinRoot q` — and therefore
   `F̄ ⊗[F] W.CoordinateRing` — is a domain.

2. **The function field base-changes to a domain.**  `W.FunctionField` is the fraction ring
   `FractionRing W.CoordinateRing`, i.e. the localisation of `W.CoordinateRing` at its
   non-zero-divisors.  By
   `IsLocalization.tensorProduct_tensorProduct_right`, `F̄ ⊗[F] W.FunctionField` is the localisation
   of the domain `F̄ ⊗[F] W.CoordinateRing` at the image of those non-zero-divisors — a submonoid of
   the non-zero-divisors (base change along the injective `includeRight`), so the localisation is a
   domain.

## Main results

* `WeierstrassCurve.Affine.isDomain_tensor_coordinateRing` —
  `IsDomain (AlgebraicClosure F ⊗[F] W.CoordinateRing)`.
* `WeierstrassCurve.Affine.isDomain_tensor_functionField` —
  `IsDomain (AlgebraicClosure F ⊗[F] W.FunctionField)`.
* `WeierstrassCurve.Affine.algebraicClosure_functionField_eq_bot` — the **unconditional** constant
  field statement `algebraicClosure F W.FunctionField = ⊥`.

No `IsElliptic` hypothesis is needed: the argument is pure geometric integrality of the Weierstrass
polynomial over any field.
-/

open scoped TensorProduct IntermediateField Polynomial
open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : Affine F)

/-- **The coordinate ring base-changes to a domain.**  The base change of `W.CoordinateRing` to the
algebraic closure `F̄ := AlgebraicClosure F` is an integral domain — the geometric integrality of
the affine Weierstrass curve. -/
instance isDomain_tensor_coordinateRing :
    IsDomain (AlgebraicClosure F ⊗[F] W.CoordinateRing) := by
  set F' := AlgebraicClosure F
  -- the base-ring isomorphism `F̄ ⊗[F] F[X] ≃+* F̄[X]`
  set e : F' ⊗[F] F[X] ≃+* F'[X] := (polyEquivTensor F F').symm.toRingEquiv with he
  -- the base-changed polynomial `q` over `F̄ ⊗[F] F[X]`
  set incR : F[X] →+* F' ⊗[F] F[X] :=
    (Algebra.TensorProduct.includeRight (R := F) (A := F') (B := F[X])).toRingHom with hincR
  set q : Polynomial (F' ⊗[F] F[X]) := W.polynomial.map incR with hq
  -- `e ∘ incR = mapRingHom (algebraMap F F')`
  have hcomp : (e : F' ⊗[F] F[X] →+* F'[X]).comp incR =
      Polynomial.mapRingHom (algebraMap F F') := by
    refine RingHom.ext fun p => ?_
    simp only [RingHom.comp_apply, hincR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, he,
      AlgEquiv.coe_ringEquiv, polyEquivTensor_symm_apply_tmul_eq_smul, one_smul,
      coe_mapRingHom]
  -- hence `q.map e = (W.map (algebraMap F F')).polynomial`
  have hqe : q.map (e : F' ⊗[F] F[X] →+* F'[X]) = (W.map (algebraMap F F')).polynomial := by
    rw [hq, Polynomial.map_map, hcomp, ← map_polynomial]
  -- `(W.map (algebraMap F F')).polynomial` is prime (irreducible over the domain `F̄`), so `q` is
  have hprime : Prime q := by
    have hirr : Irreducible ((W.map (algebraMap F F')).polynomial) := irreducible_polynomial
    rw [← hqe] at hirr
    have : Irreducible ((Polynomial.mapEquiv e) q) := by
      simpa only [Polynomial.mapEquiv_apply] using hirr
    have hprime' : Prime ((Polynomial.mapEquiv e) q) := this.prime
    exact (MulEquiv.prime_iff (Polynomial.mapEquiv e)).mp hprime'
  haveI : IsDomain (AdjoinRoot q) := AdjoinRoot.isDomain_of_prime hprime
  -- transfer along the base-change iso `F̄ ⊗[F] AdjoinRoot W.polynomial ≃ₐ AdjoinRoot q`
  exact Function.Injective.isDomain
    (AdjoinRoot.tensorAlgEquiv (R := F) (T := F') W.polynomial q rfl).toAlgHom.toRingHom
    (AdjoinRoot.tensorAlgEquiv (R := F) (T := F') W.polynomial q rfl).injective

/-- **The function field base-changes to a domain.**  The base change of `W.FunctionField` to the
algebraic closure `F̄ := AlgebraicClosure F` is an integral domain.  This is the exact
`IsDomain (AlgebraicClosure F ⊗[F] W.FunctionField)` datum carried by `ConstantField.lean` (#434)
and `WeilPairingConstant.lean` (#162). -/
instance isDomain_tensor_functionField :
    IsDomain (AlgebraicClosure F ⊗[F] W.FunctionField) := by
  set F' := AlgebraicClosure F
  let A := W.CoordinateRing
  let B := W.FunctionField
  -- the algebra structure on the base change making it a localisation
  letI : Algebra (F' ⊗[F] A) (F' ⊗[F] B) :=
    (Algebra.TensorProduct.map (AlgHom.id F F') (IsScalarTower.toAlgHom F A B)).toAlgebra
  haveI : IsScalarTower F' (F' ⊗[F] A) (F' ⊗[F] B) :=
    IsScalarTower.of_algebraMap_eq <| by
      intro x
      have hL : algebraMap F' (F' ⊗[F] B) x = x ⊗ₜ[F] 1 := rfl
      have hR : algebraMap F' (F' ⊗[F] A) x = x ⊗ₜ[F] 1 := rfl
      rw [hL, RingHom.algebraMap_toAlgebra, hR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one]
  haveI hloc : IsLocalization
      ((nonZeroDivisors A).map (Algebra.TensorProduct.includeRight (R := F) (A := F')))
      (F' ⊗[F] B) :=
    IsLocalization.tensorProduct_tensorProduct_right F F' (nonZeroDivisors A) B <| by
      refine RingHom.ext fun a => ?_
      simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.includeRight_apply]
  -- the localising submonoid lands in the non-zero-divisors of the domain `F̄ ⊗[F] A`
  have hle : (nonZeroDivisors A).map (Algebra.TensorProduct.includeRight (R := F) (A := F')) ≤
      nonZeroDivisors (F' ⊗[F] A) :=
    map_le_nonZeroDivisors_of_injective _
      (Algebra.TensorProduct.includeRight_injective (algebraMap F F').injective) (le_refl _)
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (F' ⊗[F] B) hle

/-- **The constant field of the Weierstrass function field (unconditional).**  For any Weierstrass
curve `W` over a field `F`, the base field `F` is relatively algebraically closed in its function
field `F(W)`: `algebraicClosure F W.FunctionField = ⊥`.  Equivalently, `F` is the full field of
constants of `F(W)`.

This discharges the `halg` hypothesis carried by `WeilPairingConstant.lean` (#162), making the
Weil-pairing element's constancy and translation-slot bilinearity unconditional. -/
theorem algebraicClosure_functionField_eq_bot :
    algebraicClosure F W.FunctionField = ⊥ :=
  algebraicClosure_functionField_eq_bot_of_isDomain_tensor (isDomain_tensor_functionField W)

end WeierstrassCurve.Affine
