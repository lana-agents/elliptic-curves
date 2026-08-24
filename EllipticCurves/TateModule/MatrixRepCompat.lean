/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.MatrixRep
import EllipticCurves.TateModule.PrimaryMatrixRepCompat

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
known to coincide, so this file records that they do — `matrixAutEquivTwo b` is exactly
`(b.linearEquivMulEquivGL).symm` — and transports the consequences. In particular the entry
formulas of the general file become available for the `2`-adic representation, including the one
for the *inverse* matrix, which `MatrixRep` does not supply.

## What this file contains, and what it does not

**Every argument is elsewhere and this file contains none.** The identity of the two chains is
`Module.Basis.linearEquivMulEquivGL_symm` (`EllipticCurves.TateModule.GeneralLinearGroup`), stated
for an arbitrary basis of an arbitrary module over an arbitrary commutative ring; its transport to
the Tate module is `EllipticCurves.TateModule.PrimaryMatrixRepCompat`, stated at an arbitrary
prime. **This file supplies the prime `ℓ = 2` and every proof below is one line.**

⚠️ **The four public names and statements are unchanged**, because they are consumed by spelling
and a reader who arrives here from `MatrixRep` should find them where they were.

⚠️ **One declaration this file used to carry has moved rather than been instantiated.**
`linearEquivMulEquivGL_eq` carries no `Two` in its name even though its statement mentioned
`matrixAutEquivTwo`, so a generic form of it in the same namespace would be a **name collision**
and not a twin. It is generalised in place, at
`EllipticCurves.TateModule.PrimaryMatrixRepCompat`, under the same fully qualified name
`WeierstrassCurve.Affine.linearEquivMulEquivGL_eq`; nothing that referred to it needs to change.

## Main statements

* `WeierstrassCurve.Affine.matrixAutEquivTwo_eq` :
  `matrixAutEquivTwo b = b.linearEquivMulEquivGL.symm`.
* `WeierstrassCurve.Affine.galoisRepMatrixTwo_eq` :
  `ρ_{E,2}(σ) = b.linearEquivMulEquivGL (galoisRep 2 σ)`, the same representation read along the
  general chain.
* `WeierstrassCurve.Affine.coe_galoisRepMatrixTwo_inv_apply` : the entries of `ρ_{E,2}(σ)⁻¹`.

## Scope

Nothing here strengthens what `MatrixRep` claims: continuity of `ρ_{E,2}` is still not asserted.
⚠️ **This file is `ℓ = 2` only because its statements are the `ℓ = 2` *names*, and for no other
reason.** The clause it used to carry here — *"and only `ℓ = 2` is in scope"* — read as a claim
about the development and was retired when the arbitrary-prime form landed: the `ℓ = 3` names are
`EllipticCurves.TateModule.MatrixRepCompatThree`, over the generic
`EllipticCurves.TateModule.PrimaryMatrixRepCompat`. ⚠️ At `ℓ ≥ 5` the generic statements hold too
and there is simply no basis of `T_ℓE` to feed them; see that file's Scope.

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
`M` to the endomorphism `v ↦ ∑ i, (M *ᵥ b.repr v) i • b i`, so they are mutually inverse.
Definitionally `matrixAutEquiv_eq` at `ℓ = 2`. -/
theorem matrixAutEquivTwo_eq : matrixAutEquivTwo b = b.linearEquivMulEquivGL.symm :=
  matrixAutEquiv_eq b

/-- **`ρ_{E,2}` read along the general chain.** `galoisRepMatrixTwo` is `galoisRep 2` pushed through
`Module.Basis.linearEquivMulEquivGL`, so every lemma about the latter applies to it. -/
theorem galoisRepMatrixTwo_eq (σ : F ≃ₐ[S] F) :
    galoisRepMatrixTwo b σ = b.linearEquivMulEquivGL (galoisRep 2 σ) :=
  galoisRepMatrix_eq b σ

/-- The entries of `ρ_{E,2}(σ)`, re-derived from the general entry formula. This is
`galoisRepMatrixTwo_apply_coe`; it is restated here to confirm that the two chains produce the same
matrix entry-by-entry, and not merely the same abstract group element. -/
theorem coe_galoisRepMatrixTwo_apply' (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j = b.repr (σ • b j) i :=
  coe_galoisRepMatrix_apply' b σ i j

/-- **The entries of `ρ_{E,2}(σ)⁻¹`.** Column `j` records the coordinates of `σ⁻¹ • b j`, since
`ρ_{E,2}` is a homomorphism from a group. `MatrixRep` supplies no formula for the inverse matrix;
this one comes for free from `Module.Basis.coe_inv_linearEquivMulEquivGL_apply`. -/
theorem coe_galoisRepMatrixTwo_inv_apply (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (((galoisRepMatrixTwo b σ)⁻¹ : GL (Fin 2) ℤ_[2]) : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j
      = b.repr (σ⁻¹ • b j) i :=
  coe_galoisRepMatrix_inv_apply b σ i j

end WeierstrassCurve.Affine
