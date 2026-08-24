/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.GeneralLinearGroup
import EllipticCurves.TateModule.MatrixRep

/-!
# The two routes from a basis of `T₂E` to `GL₂(ℤ₂)` agree

`EllipticCurves.TateModule.MatrixRep` builds the matrix form of the `2`-adic Galois representation
by way of `matrixAutEquivTwo`, the multiplicative equivalence

```
GL (Fin 2) ℤ_[2] ≃* Aut_{ℤ_[2]}(T₂E)
```

assembled from `Matrix.GeneralLinearGroup.toLin'` and
`LinearMap.GeneralLinearGroup.generalLinearEquiv`.
`EllipticCurves.TateModule.GeneralLinearGroup` builds the same identification for an arbitrary
free module over an arbitrary commutative ring, as `Module.Basis.linearEquivMulEquivGL`, but along
the other chain, through `LinearMap.toMatrixAlgEquiv`.

Two independent constructions of one object are a liability rather than an asset until they are
known to coincide, so this file proves they do — `matrixAutEquivTwo b` is exactly
`(b.linearEquivMulEquivGL).symm` — and transports the consequences. In particular the entry
formulas of the general file become available for the `2`-adic representation, including the one
for the *inverse* matrix, which `MatrixRep` does not supply.

## Main statements

* `WeierstrassCurve.Affine.matrixAutEquivTwo_eq` :
  `matrixAutEquivTwo b = b.linearEquivMulEquivGL.symm`.
* `WeierstrassCurve.Affine.galoisRepMatrixTwo_eq` :
  `ρ_{E,2}(σ) = b.linearEquivMulEquivGL (galoisRep 2 σ)`, the same representation read along the
  general chain.
* `WeierstrassCurve.Affine.coe_galoisRepMatrixTwo_inv_apply` : the entries of `ρ_{E,2}(σ)⁻¹`.

Nothing here strengthens what `MatrixRep` claims: continuity of `ρ_{E,2}` is still not asserted,
and only `ℓ = 2` is in scope.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and VII.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-- **The two identifications of `Aut_{ℤ_[2]}(T₂E)` with `GL₂(ℤ_[2])` agree.**

`matrixAutEquivTwo b` goes `GL → Aut` through `Matrix.GeneralLinearGroup.toLin'`, while
`b.linearEquivMulEquivGL` goes `Aut → GL` through `LinearMap.toMatrixAlgEquiv`. Both send a matrix
`M` to the endomorphism `v ↦ ∑ i, (M *ᵥ b.repr v) i • b i`, so they are mutually inverse. -/
theorem matrixAutEquivTwo_eq : matrixAutEquivTwo b = b.linearEquivMulEquivGL.symm := by
  refine MulEquiv.ext fun M => LinearEquiv.ext fun v => ?_
  have hl : matrixAutEquivTwo b M v = (Matrix.GeneralLinearGroup.toLin' b M).toLinearEquiv v := rfl
  have hr : b.linearEquivMulEquivGL.symm M v
      = Matrix.toLinAlgEquiv b (M : Matrix (Fin 2) (Fin 2) ℤ_[2]) v := rfl
  rw [hl, Matrix.GeneralLinearGroup.toLin'_apply b M v, Fintype.linearCombination_apply, hr,
    Matrix.toLinAlgEquiv_apply]

/-- The other direction of `matrixAutEquivTwo_eq`. -/
theorem linearEquivMulEquivGL_eq : b.linearEquivMulEquivGL = (matrixAutEquivTwo b).symm := by
  rw [matrixAutEquivTwo_eq, MulEquiv.symm_symm]

/-- **`ρ_{E,2}` read along the general chain.** `galoisRepMatrixTwo` is `galoisRep 2` pushed through
`Module.Basis.linearEquivMulEquivGL`, so every lemma about the latter applies to it. -/
theorem galoisRepMatrixTwo_eq (σ : F ≃ₐ[S] F) :
    galoisRepMatrixTwo b σ = b.linearEquivMulEquivGL (galoisRep 2 σ) := by
  have hc : galoisRepMatrixTwo b σ = (matrixAutEquivTwo b).symm (galoisRep 2 σ) := rfl
  rw [hc, matrixAutEquivTwo_eq, MulEquiv.symm_symm]

/-- The entries of `ρ_{E,2}(σ)`, re-derived from the general entry formula. This is
`galoisRepMatrixTwo_apply_coe`; it is restated here to confirm that the two chains produce the same
matrix entry-by-entry, and not merely the same abstract group element. -/
theorem coe_galoisRepMatrixTwo_apply' (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j = b.repr (σ • b j) i := by
  rw [galoisRepMatrixTwo_eq, Module.Basis.coe_linearEquivMulEquivGL_apply, galoisRep_apply_coe]

/-- **The entries of `ρ_{E,2}(σ)⁻¹`.** Column `j` records the coordinates of `σ⁻¹ • b j`, since
`ρ_{E,2}` is a homomorphism from a group. `MatrixRep` supplies no formula for the inverse matrix;
this one comes for free from `Module.Basis.coe_inv_linearEquivMulEquivGL_apply`. -/
theorem coe_galoisRepMatrixTwo_inv_apply (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (((galoisRepMatrixTwo b σ)⁻¹ : GL (Fin 2) ℤ_[2]) : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j
      = b.repr (σ⁻¹ • b j) i := by
  rw [← map_inv, coe_galoisRepMatrixTwo_apply']

end WeierstrassCurve.Affine
