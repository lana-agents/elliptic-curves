/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Automorphisms of a free module as a matrix general linear group

A basis `b : Basis n R M` of a module over a commutative ring identifies the group of
`R`-linear automorphisms of `M` with the matrix general linear group:
$$ \operatorname{Aut}_R(M) \;\cong\; \mathrm{GL}_n(R). $$

Mathlib has both halves of this — `LinearMap.toMatrixAlgEquiv`, the algebra equivalence
`(M →ₗ[R] M) ≃ₐ[R] Matrix n n R`, and
`LinearMap.GeneralLinearGroup.generalLinearEquiv : (M →ₗ[R] M)ˣ ≃* (M ≃ₗ[R] M)` — but does not
package their composite as a single multiplicative equivalence onto `GL n R`. This file supplies
it, together with the formula for a matrix entry, which is the only thing a consumer ever needs
once the equivalence exists.

There is nothing about elliptic curves here; the file is stated for an arbitrary commutative ring
and would be at home in Mathlib.

## Motivation

For an elliptic curve over a field `F` with `(2 : F) ≠ 0` and `F` algebraically closed, the
`2`-adic Tate module `T₂E` is free of rank two over `ℤ_[2]`
(`EllipticCurves.TateModule.Free`). Feeding a basis of it into `Basis.linearEquivMulEquivGL`
converts the abstract Galois representation `ρ_2 : G → Aut_{ℤ_2}(T₂E)` of
`EllipticCurves.TateModule.GaloisAction` into the classical matrix representation
`ρ_{E,2} : G → GL₂(ℤ_2)`. That is done in
`EllipticCurves.TateModule.MatrixRepresentation`.

## Main definitions

* `Module.Basis.linearEquivMulEquivGL`: the multiplicative equivalence
  `(M ≃ₗ[R] M) ≃* GL n R` attached to a basis.

## Main statements

* `Module.Basis.coe_linearEquivMulEquivGL_apply`: the matrix entry formula
  `(b.linearEquivMulEquivGL e) i j = b.repr (e (b j)) i`, matching Mathlib's convention for
  `LinearMap.toMatrix` (column `j` records the image of the `j`-th basis vector).
-/

namespace Module.Basis

variable {R M n : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype n] [DecidableEq n]

/-- **A basis identifies `Aut_R(M)` with `GL n R`.** The forward map sends an `R`-linear
automorphism to its matrix in the basis `b`; it is multiplicative because
`LinearMap.toMatrixAlgEquiv` is an algebra equivalence, and lands in the units because an
automorphism is invertible. -/
noncomputable def linearEquivMulEquivGL (b : Basis n R M) :
    (M ≃ₗ[R] M) ≃* Matrix.GeneralLinearGroup n R :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv)

/-- **The matrix entries.** Column `j` of the matrix of `e` is the coordinate vector of `e (b j)`,
which is Mathlib's convention for `LinearMap.toMatrix`. -/
@[simp]
theorem coe_linearEquivMulEquivGL_apply (b : Basis n R M) (e : M ≃ₗ[R] M) (i j : n) :
    (b.linearEquivMulEquivGL e : Matrix n n R) i j = b.repr (e (b j)) i := by
  change LinearMap.toMatrixAlgEquiv b (e : M →ₗ[R] M) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

/-- The inverse of `b.linearEquivMulEquivGL e` is the matrix of `e.symm`. -/
theorem coe_inv_linearEquivMulEquivGL_apply (b : Basis n R M) (e : M ≃ₗ[R] M) (i j : n) :
    (((b.linearEquivMulEquivGL e)⁻¹ : Matrix.GeneralLinearGroup n R) : Matrix n n R) i j
      = b.repr (e.symm (b j)) i := by
  have : (b.linearEquivMulEquivGL e)⁻¹ = b.linearEquivMulEquivGL e.symm := by
    rw [← map_inv]
    rfl
  rw [this, coe_linearEquivMulEquivGL_apply]

end Module.Basis
