/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.GeneralLinearGroup
import EllipticCurves.TateModule.PrimaryMatrixRep

/-!
# The two routes from a basis of `T_ℓE` to `GL₂(ℤ_ℓ)` agree, at an arbitrary prime

`EllipticCurves.TateModule.PrimaryMatrixRep` builds the matrix form of the `ℓ`-adic Galois
representation by way of `matrixAutEquiv`, the multiplicative equivalence

```
GL (Fin 2) ℤ_[ℓ] ≃* Aut_{ℤ_[ℓ]}(T_ℓE)
```

assembled from `Matrix.GeneralLinearGroup.toLin'` and
`LinearMap.GeneralLinearGroup.generalLinearEquiv`.
`EllipticCurves.TateModule.GeneralLinearGroup` builds the same identification for an arbitrary
free module over an arbitrary commutative ring, as `Module.Basis.linearEquivMulEquivGL`, but along
the other chain, through `LinearMap.toMatrixAlgEquiv`.

Two independent constructions of one object are a liability rather than an asset until they are
known to coincide. This file records that they do — `matrixAutEquiv b` is exactly
`(b.linearEquivMulEquivGL).symm` — and transports the consequences to `ρ_{E,ℓ}`. In particular the
entry formulas of the general file become available for the `ℓ`-adic representation, including the
one for the *inverse* matrix, which `PrimaryMatrixRep` does not supply.

## What this file is, and where its content actually lives

This is the **extraction** of `EllipticCurves.TateModule.MatrixRepCompat` to an arbitrary prime.
That file was written at `ℓ = 2` because `matrixAutEquivTwo` and `galoisRepMatrixTwo` were the only
spellings available; `EllipticCurves.TateModule.PrimaryMatrixRep` has since made both `ℓ`-generic,
so nothing `2`-specific is left.

⚠️ **The agreement itself is not proved here, and it is not about elliptic curves.** Neither
`Module.Basis.linearEquivMulEquivGL` nor the Mathlib composite mentions a prime, a Tate module or a
curve, so the identity is a statement about an arbitrary basis of an arbitrary module over an
arbitrary commutative ring. It is `Module.Basis.linearEquivMulEquivGL_symm`, in
`EllipticCurves.TateModule.GeneralLinearGroup`, where both spellings are defined. ⚠️ **Everything
below is transport**: `matrixAutEquiv_eq` is that lemma read at `R = ℤ_[ℓ]` and
`M = T_ℓE`, and the other four are consequences of it and of the entry formulas.

## Main statements

* `WeierstrassCurve.Affine.matrixAutEquiv_eq` :
  `matrixAutEquiv b = b.linearEquivMulEquivGL.symm`.
* `WeierstrassCurve.Affine.galoisRepMatrix_eq` :
  `ρ_{E,ℓ}(σ) = b.linearEquivMulEquivGL (galoisRep ℓ σ)`, the same representation read along the
  general chain.
* `WeierstrassCurve.Affine.coe_galoisRepMatrix_inv_apply` : the entries of `ρ_{E,ℓ}(σ)⁻¹`.

## Naming

The rule is `EllipticCurves.TateModule.PrimaryMatrixRep`'s and it is settled: **the generic name is
the `ℓ = 2` name with `Two` dropped.** So `matrixAutEquivTwo_eq` becomes `matrixAutEquiv_eq` and
`coe_galoisRepMatrixTwo_inv_apply` becomes `coe_galoisRepMatrix_inv_apply`. ⚠️ No name here takes
`_of_nonempty`, because no statement here takes a hypothesis; see Scope.

⚠️ **`coe_galoisRepMatrix_apply'` keeps its prime.** It is the `ℓ = 2` file's inherited spelling and
it is load-bearing: `galoisRepMatrix_apply_coe` already exists, in
`EllipticCurves.TateModule.PrimaryMatrixRep`, and is a **different** lemma — same statement, proved
from `galoisRepMatrix_mulVec` rather than from the general entry formula. The primed name is what
records that the two chains agree entry-by-entry and not merely as abstract group elements.

⚠️ **`linearEquivMulEquivGL_eq` is unsuffixed and is generalised in place, with no `Three` twin.**
Its `ℓ = 2` form was `b.linearEquivMulEquivGL = (matrixAutEquivTwo b).symm`, which mentions `2` and
is therefore not already generic; but a second `WeierstrassCurve.Affine.linearEquivMulEquivGL_eq`
in the same namespace would be a **name collision**, not a duplication, so it can only be
generalised. It then needs no `ℓ = 3` twin either: the statement below, applied to a basis of
`T₃E`, already *is* the `ℓ = 3` statement.

## Scope

* ⚠️ **No hypothesis, and no `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`.** The basis is an explicit
  argument and nothing below needs one to *exist*. `EllipticCurves.TateModule.PrimaryFree`
  *produces* that hypothesis; each of `EllipticCurves.TateModule.PrimaryMatrixRep`,
  `PrimaryDeterminant`, `PrimaryMatrixRepBasisChange` and `PrimaryMatrixContinuity` then carries
  it, under an `_of_nonempty` suffix, on at least one declaration. ⚠️ **This file is the first of
  their successors to carry it on none**: `grep -c '_of_nonempty'` on it returns `0`.
* ⚠️ **Consequently the statements below are already available at every prime, `ℓ ≥ 5` included** —
  what is missing at `ℓ ≥ 5` is not a theorem here but a **basis to feed them**, i.e.
  `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`, which needs `#E[ℓ^k]`.  ⚠️ This clause used to add
  *"and surjectivity of `[ℓ]` on `E(F̄)` and so runs through the multiplication-by-`n` coordinate
  formula `x(nP) = Φₙ/ΨSqₙ`"*, and both halves are stale: surjectivity holds at every nonzero index
  (`nsmul_surjective_of_two_ne_zero`, `EllipticCurves.Torsion.TwoTorsionOrder`) and the coordinate
  formula is proved at every index (`hasXCoordFormula_of_two_ne_zero`,
  `EllipticCurves.Torsion.NsmulOrder`).  ⚠️ `#E[ℓ^k]` alone was what was left, and it is left
  no longer: `card_torsion_pow_mul_self_of_odd` (`EllipticCurves.Torsion.PrimaryTowerOdd`) supplies
  it at every odd `ℓ` with `(ℓ : F) ≠ 0`.
  Instantiations exist at `ℓ = 2` (`EllipticCurves.TateModule.MatrixRepCompat`) and at `ℓ = 3`
  (`EllipticCurves.TateModule.MatrixRepCompatThree`); at `ℓ ≥ 5` there is still nothing to
  instantiate *with* — the basis has to be built first (`#268`) — and the statements here remain
  true but so far unused.
* **Nothing here strengthens what `PrimaryMatrixRep` claims.** Continuity of `ρ_{E,ℓ}` is not
  asserted — it is supplied separately, at an arbitrary prime, by
  `EllipticCurves.TateModule.PrimaryMatrixContinuity`.
* Also out of scope: injectivity of `ρ_{E,ℓ}`, its determinant character, the comparison with the
  cyclotomic character, and any description of its image.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and VII.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))

/-- **The two identifications of `Aut_{ℤ_[ℓ]}(T_ℓE)` with `GL₂(ℤ_[ℓ])` agree.**

`matrixAutEquiv b` goes `GL → Aut` through `Matrix.GeneralLinearGroup.toLin'`, while
`b.linearEquivMulEquivGL` goes `Aut → GL` through `LinearMap.toMatrixAlgEquiv`. ⚠️ This is
`Module.Basis.linearEquivMulEquivGL_symm` read at `R = ℤ_[ℓ]` and `M = T_ℓE`; the argument that
they are mutually inverse is there, where neither definition knows about a curve. -/
theorem matrixAutEquiv_eq : matrixAutEquiv b = b.linearEquivMulEquivGL.symm :=
  (b.linearEquivMulEquivGL_symm).symm

/-- The other direction of `matrixAutEquiv_eq`. -/
theorem linearEquivMulEquivGL_eq : b.linearEquivMulEquivGL = (matrixAutEquiv b).symm := by
  rw [matrixAutEquiv_eq, MulEquiv.symm_symm]

/-- **`ρ_{E,ℓ}` read along the general chain.** `galoisRepMatrix` is `galoisRep ℓ` pushed through
`Module.Basis.linearEquivMulEquivGL`, so every lemma about the latter applies to it. -/
theorem galoisRepMatrix_eq (σ : F ≃ₐ[S] F) :
    galoisRepMatrix b σ = b.linearEquivMulEquivGL (galoisRep ℓ σ) := by
  have hc : galoisRepMatrix b σ = (matrixAutEquiv b).symm (galoisRep ℓ σ) := rfl
  rw [hc, matrixAutEquiv_eq, MulEquiv.symm_symm]

/-- The entries of `ρ_{E,ℓ}(σ)`, re-derived from the general entry formula. This is
`galoisRepMatrix_apply_coe`; it is restated here to confirm that the two chains produce the same
matrix entry-by-entry, and not merely the same abstract group element. -/
theorem coe_galoisRepMatrix_apply' (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) i j = b.repr (σ • b j) i := by
  rw [galoisRepMatrix_eq, Module.Basis.coe_linearEquivMulEquivGL_apply, galoisRep_apply_coe]

/-- **The entries of `ρ_{E,ℓ}(σ)⁻¹`.** Column `j` records the coordinates of `σ⁻¹ • b j`, since
`ρ_{E,ℓ}` is a homomorphism from a group. `PrimaryMatrixRep` supplies no formula for the inverse
matrix; this one comes for free from `Module.Basis.coe_inv_linearEquivMulEquivGL_apply`. -/
theorem coe_galoisRepMatrix_inv_apply (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (((galoisRepMatrix b σ)⁻¹ : GL (Fin 2) ℤ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) i j
      = b.repr (σ⁻¹ • b j) i := by
  rw [← map_inv, coe_galoisRepMatrix_apply']

end WeierstrassCurve.Affine
