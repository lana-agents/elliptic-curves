/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Free
import EllipticCurves.TateModule.GaloisAction
import EllipticCurves.TateModule.GeneralLinearGroup

/-!
# The matrix form of the `2`-adic Galois representation, `ρ_{E,2} : G → GL₂(ℤ₂)`

`EllipticCurves.TateModule.GaloisAction` builds the abstract `ℓ`-adic representation
$$ \rho_\ell : \operatorname{Gal}(F/S) \longrightarrow
     \operatorname{Aut}_{\mathbb{Z}_\ell}(T_\ell E) $$
of a Weierstrass curve `W'` over `S` base-changed to `F`. `EllipticCurves.TateModule.Free` shows
that at `ℓ = 2`, over an algebraically closed `F` with `(2 : F) ≠ 0`, the Tate module `T₂E` is free
of rank two over `ℤ_[2]`. Choosing a basis therefore turns `ρ_2` into the classical **matrix
representation**
$$ \rho_{E,2} : \operatorname{Gal}(F/S) \longrightarrow \mathrm{GL}_2(\mathbb{Z}_2), $$
which is the object of Silverman, *AEC*, III.7 and Remark 7.1.2. This file makes that step.

The rank-two statement is what makes `GL₂` — rather than an unspecified `Aut` — the right target,
and it only became available with `EllipticCurves.TateModule.Free`; before that, nothing in this
development distinguished `T₂E` from the zero module.

## Hypotheses, stated plainly

Everything below assumes `F` is **algebraically closed**, `W'` is elliptic over `S` (so that the
base change `W'⁄F` is elliptic), and `(2 : F) ≠ 0`, i.e. `char F ≠ 2`. In the intended application
`S` is a number field or a local field, `F` is an algebraic closure of `S`, and
`Gal(F/S) = F ≃ₐ[S] F` is the absolute Galois group.

## What is *not* claimed

* **Continuity.** `ρ_{E,2}` is built here purely as a group homomorphism. The profinite topology
  on `Gal(F/S)` and the `2`-adic topology on `T₂E` play no role, and no continuity statement is
  made — `galoisRep`'s own docstring already disclaims this, and nothing here upgrades it.
* **Odd `ℓ`.** Only `ℓ = 2`. For odd `ℓ` the freeness of `T_ℓ E` needs surjectivity of `[ℓ]` on
  `E(F̄)` and `E[ℓ^k] ≅ (ℤ/ℓ^kℤ)²`, neither of which is available yet.
* **`det ρ_{E,2} =` the cyclotomic character.** That identification needs the Weil pairing and is a
  separate development.

## Main definitions

* `WeierstrassCurve.Affine.galoisRepGL`: the matrix representation
  `Gal(F/S) →* GL (Fin 2) ℤ_[2]` attached to a basis of `T₂E`.

## Main statements

* `WeierstrassCurve.Affine.tateModule.nonempty_basis_tateModule_two`: `T₂E` has a `Fin 2`-indexed
  `ℤ_[2]`-basis.
* `WeierstrassCurve.Affine.coe_galoisRepGL_apply`: the matrix entries of `ρ_{E,2}(σ)` are the
  coordinates of `σ • bⱼ`.
* `WeierstrassCurve.Affine.nonempty_galoisRepGL`: the representation exists, for any choice of
  basis.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and Remark 7.1.2.
-/

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

namespace tateModule

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} [IsAlgClosed F] [W.IsElliptic]

/-- **`T₂E` has a two-element basis over `ℤ_[2]`.** Immediate from
`free_tateModule_two`, `finite_tateModule_two` and `finrank_tateModule_two`, but those are
*theorems* taking `(2 : F) ≠ 0` rather than instances, so they have to be introduced by hand before
`Module.finBasisOfFinrankEq` can fire.

The basis is not canonical — it depends on a choice of coherent system of generating pairs of the
groups `E[2^k]` — hence the `Nonempty`. -/
theorem nonempty_basis_tateModule_two (h2 : (2 : F) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) ℤ_[2] (W.tateModule 2)) := by
  haveI := free_tateModule_two (W := W) h2
  haveI := finite_tateModule_two (W := W) h2
  exact ⟨Module.finBasisOfFinrankEq ℤ_[2] _ (finrank_tateModule_two (W := W) h2)⟩

end tateModule

/-! ### The representation -/

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

/-- **The `2`-adic Galois representation in matrix form**,
`ρ_{E,2} : Gal(F/S) →* GL₂(ℤ_2)`, relative to a basis `b` of `T₂E`.

This is `galoisRep 2` read through the identification `Aut_{ℤ_2}(T₂E) ≅ GL₂(ℤ_2)` supplied by `b`.
Changing `b` conjugates the representation, so `galoisRepGL` is well defined only up to
conjugation; the basis is kept as an explicit argument rather than hidden behind a `Nonempty`
precisely so that the matrix entries stay computable (see `coe_galoisRepGL_apply`). -/
noncomputable def galoisRepGL (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :
    Gal(F/S) →* Matrix.GeneralLinearGroup (Fin 2) ℤ_[2] :=
  b.linearEquivMulEquivGL.toMonoidHom.comp (galoisRep 2)

/-- **The matrix entries of `ρ_{E,2}(σ)`.** Column `j` is the coordinate vector of the Galois
translate `σ • b j` of the `j`-th basis vector — the classical description of the representation. -/
@[simp]
theorem coe_galoisRepGL_apply (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))
    (σ : Gal(F/S)) (i j : Fin 2) :
    (galoisRepGL b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j = b.repr (σ • b j) i :=
  Module.Basis.coe_linearEquivMulEquivGL_apply b _ i j

/-- `ρ_{E,2}` sends a Galois automorphism to the matrix of the map it induces on `T₂E`. -/
theorem galoisRepGL_apply (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) (σ : Gal(F/S)) :
    galoisRepGL b σ = b.linearEquivMulEquivGL (galoisRep 2 σ) :=
  rfl

omit [DecidableEq F] in
/-- **The representation exists.** Over an algebraically closed `F` of characteristic `≠ 2`, an
elliptic curve over `S` has a `2`-adic matrix representation of its Galois group.

Note that this statement is, on its own, weak: `Nonempty (G →* GL (Fin 2) ℤ_[2])` holds for every
group `G`, witnessed by the trivial homomorphism. The content is in `galoisRepGL` and
`coe_galoisRepGL_apply`, which exhibit the map and its entries; and in
`tateModule.nontrivial_tateModule_two` together with `tateModule.finrank_tateModule_two`, which
say the module being represented on is not the zero module. -/
theorem nonempty_galoisRepGL [IsAlgClosed F] [(W'⁄F).IsElliptic] (h2 : (2 : F) ≠ 0) :
    Nonempty (Gal(F/S) →* Matrix.GeneralLinearGroup (Fin 2) ℤ_[2]) := by
  classical
  exact (tateModule.nonempty_basis_tateModule_two (W := W'⁄F) h2).map galoisRepGL

end WeierstrassCurve.Affine
