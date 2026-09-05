/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.PrimaryMatrixRep
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Changing the basis conjugates `ρ_{E,ℓ}`, at an arbitrary prime

`galoisRepMatrix b : G →* GL₂(ℤ_[ℓ])` of `EllipticCurves.TateModule.PrimaryMatrixRep` depends on a
choice of basis `b` of `T_ℓE`. This file proves that the dependence is exactly a conjugation:

```
galoisRepMatrix b' σ = c * galoisRepMatrix b σ * c⁻¹,   c = basisChangeGL b b'
```

uniformly in `σ`, hence also as an identity of monoid homomorphisms
(`galoisRepMatrix_eq_conj_comp`). It is what licenses the standard phrase *"the `ℓ`-adic
representation attached to `E`, well defined up to conjugation"*.

## What this file is

This is the **extraction** of `EllipticCurves.TateModule.MatrixRepBasisChange` to an arbitrary
prime, in the same shape as `EllipticCurves.TateModule.PrimaryMatrixRep` and
`EllipticCurves.TateModule.PrimaryDeterminant`. That file was written at `ℓ = 2` because
`galoisRepMatrixTwo` was the only matrix representation available; nothing in the conjugation law
uses `2` for anything but the type, and it said so in its own words.

⚠️ **Nothing here is new mathematics and nothing here takes a hypothesis.** Unlike the three
extractions that precede it (`EllipticCurves.Torsion.PrimaryBasis`,
`EllipticCurves.TateModule.PrimaryFree`, `EllipticCurves.TateModule.PrimaryMatrixRep`) there is no
`_of_nonempty` suffix anywhere below, because no statement here consumes the rank-two input
`Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`: the conjugation law is about two bases that are *given*,
and a basis indexed by `Fin 2` is exactly what makes the `GL₂` shape typecheck in the first place.
A reader who has seen the other three extractions will look for such a hypothesis; there is none.

⚠️ **This file therefore supplies no representation of any curve**, for the same reason
`EllipticCurves.TateModule.PrimaryMatrixRep` does not: it produces no basis. The instantiations are
`EllipticCurves.TateModule.MatrixRepBasisChange` (`ℓ = 2`) and
`EllipticCurves.TateModule.MatrixRepBasisChangeThree` (`ℓ = 3`).

## Where `basisChangeGL` lives, and why it moved here

The `basisChangeGL` section below is about an arbitrary finite-rank free module over an arbitrary
commutative ring; no prime, no Tate module and no elliptic curve enters it. It was written in
`EllipticCurves.TateModule.MatrixRepBasisChange` and is **moved** here unchanged — same namespace
`WeierstrassCurve.Affine.tateModule`, same statements, same proofs.

⚠️ The move is forced by the import graph and not by genericity: `basisChangeGL` was already
generic where it stood, but the file it stood in imports `EllipticCurves.TateModule.MatrixRep` and
`EllipticCurves.TateModule.OpenKernel`, so an `ℓ`-generic file that referred to it from there would
sit *above* the `ℓ = 2` layer and drag `EllipticCurves.Torsion.TwoPrimary` into every future
instantiation. Every other extraction on this front puts the generic file strictly below its
instances, and this one does too.

## Main definitions

* `WeierstrassCurve.Affine.tateModule.basisChangeGL` : the change-of-basis matrix `b'.toMatrix b`
  packaged as an element of `GL ι R`, with `b.toMatrix b'` as its inverse.

## Main statements

* `WeierstrassCurve.Affine.galoisRepMatrix_conj` : `ρ_{b'}(σ) = c ρ_b(σ) c⁻¹`.
* `WeierstrassCurve.Affine.galoisRepMatrix_eq_conj_comp` : the same as an equality of monoid
  homomorphisms `G →* GL₂(ℤ_[ℓ])`.
* `WeierstrassCurve.Affine.range_galoisRepMatrix_map` : the image of `ρ_{E,ℓ}` is well defined up
  to conjugacy in `GL₂(ℤ_[ℓ])`.

## Scope

* **Closedness of the kernel is not here.** `isClosed_ker_galoisRepMatrixTwo` and its `ℓ = 3` twin
  need the level filtration and the profinite topology on `G`, which live above this file; they are
  stated in the two instantiating files.
* ⚠️ **Nothing here bears on whether the conjugacy class is nontrivial**, i.e. on the image of
  `ρ_{E,ℓ}`: that is a statement about `F / S`, and `G` may be trivial for all this file knows.
  What *is* discriminated is that the conjugating element is genuinely not always `1`
  (`tateModule.basisChangeGL_reindex_swap_ne_one`), so the law is not `b' = b` in disguise. That
  certificate is stated over an arbitrary `Nontrivial` commutative ring and an arbitrary
  `Fin 2`-indexed basis, so it covers every prime at once and is **not** restated in the
  instantiating files.
* ⚠️ **`ℓ ≥ 5` gains nothing from this file being generic — but the reason this bullet gave is
  false, and only the conclusion survives.** ⚠️ **It used to read** *"its statements are about a
  basis of `T_ℓE`, and at `ℓ ≥ 5` there is none, because `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)` is gated at `ℓ
  ≥ 5` on `#E[ℓ^k]` alone"*.  **There is a basis at every prime `ℓ` with `(2 : F) ≠ 0` and
  `(ℓ : F) ≠ 0`**: `nonempty_basis_tateModule_of_natCast_ne_zero`
  (`EllipticCurves.TateModule.MatrixRepGeneral`) produces one from `#268`, under `[IsAlgClosed F]`
  and `[W.IsElliptic]`.  ⚠️ **`(2 : F) ≠ 0` is the second hypothesis and this sentence used to name
  only the first** (`#1137`); it enters at `card_torsion_eq_sq`
  (`EllipticCurves.Torsion.StructureGeneral`), whose docstring says what it costs.  ⚠️ That module
  is a **sibling** rather than a discharger — neither it nor this file is in the other's import
  closure — so the name is not usable here either, though for a different reason than a forward
  reference.  ⚠️ This bullet used to say it was
  gated *"on `[ℓ]`-surjectivity and `#E[ℓ^k]`, both of which need the general coordinate formula
  `x(nP) = Φₙ/ΨSqₙ`, i.e. the `ωₙ` crux"*, and **all three clauses are wrong**: `[ℓ]`-surjectivity
  holds at every nonzero index with `(2 : F) ≠ 0` (`nsmul_surjective_of_two_ne_zero`,
  `EllipticCurves.Torsion.TwoTorsionOrder`); the coordinate formula is proved at every index with
  `(2 : F) ≠ 0` (`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`); and it is
  **not** the `ωₙ` crux — that is `#404`'s on-curve identity, closed in
  `EllipticCurves.Torsion.OmegaCrux` (PR #557), and `EllipticCurves.FunctionField.MulByNPullback` is
  the module that keeps the two apart.  ⚠️ **`#E[ℓ^k]` is no longer open at `ℓ ≥ 5`.**
  `card_torsion_pow_mul_self_of_odd` (`EllipticCurves.Torsion.PrimaryTowerOdd`) supplies it at every
  odd `ℓ` with `(ℓ : F) ≠ 0`, over `F̄` with `(2 : F) ≠ 0`, and discharges
  `EllipticCurves.Torsion.PrimaryTower`'s gate list — which this bullet used to cite as open — with
  it.  ⚠️ **Exactly one clause of this bullet survives, and it survives for a different reason than
  the one it was written for.** Instantiating this file at `ℓ ≥ 5` is separate work and is not done
  here — and, unlike the four sibling `Primary*` files whose bullets carried this same sentence, it
  is **not done anywhere**: this file's reverse import cone is
  `EllipticCurves.TateModule.MatrixRepBasisChange` (`ℓ = 2`),
  `EllipticCurves.TateModule.MatrixRepBasisChangeThree` (`ℓ = 3`),
  `EllipticCurves.TateModule.MatrixRepMod` (mod `n`) and
  `EllipticCurves.FunctionField.MatrixRepDeterminantCharacter`, and none of them states the
  conjugation law at a general prime.  What being generic buys is that when someone writes that
  file, it is again a list of instantiations.

## ⚠️ One `@[simp]` attribute was removed here, and the lemma kept (`#1278`)

`basisChangeGL_mulVec` carried `@[simp]`, and the default simp set **already proves it** — through
`coe_basisChangeGL` and `Module.Basis.toMatrix_mulVec_repr`. Measured with Mathlib's `simpNF`
environment linter, which had never been run on this tree. The lemma is unchanged and is still
used by name below.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

namespace tateModule

/-! ### The change-of-basis element of `GL ι R`

This section is about an arbitrary finite-rank free module; nothing about elliptic curves enters.
It is `Module.Basis.toMatrix` packaged as a *unit*, which is what a conjugation statement needs and
which Mathlib does not provide (it has `Module.Basis.invertibleToMatrix`, an `Invertible` instance
on the matrix, but no `GL`-valued form). -/

variable {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]

/-- The change of basis from `b` to `b'` as an element of `GL ι R`: the matrix `b'.toMatrix b`,
whose two-sided inverse is `b.toMatrix b'`.

The direction is fixed by `basisChangeGL_mulVec`: this is the matrix taking `b`-coordinates to
`b'`-coordinates. -/
noncomputable def basisChangeGL (b b' : Module.Basis ι R M) : GL ι R :=
  ⟨b'.toMatrix b, b.toMatrix b', b'.toMatrix_mul_toMatrix_flip b,
    b.toMatrix_mul_toMatrix_flip b'⟩

variable (b b' : Module.Basis ι R M)

@[simp]
lemma coe_basisChangeGL : (basisChangeGL b b' : Matrix ι ι R) = b'.toMatrix b := rfl

@[simp]
lemma coe_basisChangeGL_inv : ((basisChangeGL b b')⁻¹ : GL ι R).val = b.toMatrix b' := rfl

/-- **`basisChangeGL b b'` converts `b`-coordinates into `b'`-coordinates.** This is the
computation rule; everything else about `basisChangeGL` follows from it. -/
lemma basisChangeGL_mulVec (m : M) :
    (basisChangeGL b b' : Matrix ι ι R) *ᵥ ⇑(b.repr m) = ⇑(b'.repr m) :=
  b.toMatrix_mulVec_repr b' m

@[simp]
lemma basisChangeGL_self : basisChangeGL b b = 1 :=
  Units.ext <| by simp

lemma basisChangeGL_mul (b'' : Module.Basis ι R M) :
    basisChangeGL b' b'' * basisChangeGL b b' = basisChangeGL b b'' :=
  Units.ext <| by simp [Module.Basis.toMatrix_mul_toMatrix]

lemma basisChangeGL_symm : (basisChangeGL b b')⁻¹ = basisChangeGL b' b := rfl

/-- **The conjugating element is not always `1`.** Reindexing a basis of a rank-`2` module along
the transposition of the two indices changes it, and the resulting change-of-basis element is the
permutation matrix, whose `(0, 0)` entry is `0`.

This is the non-vacuity certificate for `galoisRepMatrix_conj`: without it, the conjugation law
would be consistent with `basisChangeGL` being constantly `1`, i.e. with the law saying nothing
beyond `b' = b`. ⚠️ It is stated over an arbitrary `Nontrivial` commutative ring, so it covers
every prime at once and the instantiating files do not restate it. -/
lemma basisChangeGL_reindex_swap_ne_one [Nontrivial R] (c : Module.Basis (Fin 2) R M) :
    basisChangeGL c (c.reindex (Equiv.swap 0 1)) ≠ 1 := by
  intro h
  have h00 := congrFun₂
    (congrArg (fun u : GL (Fin 2) R => (u : Matrix (Fin 2) (Fin 2) R)) h) 0 0
  simp [Module.Basis.toMatrix_apply] at h00

end tateModule

/-! ### The conjugation law for `ρ_{E,ℓ}` -/

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]

variable (b b' : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))

open tateModule in
/-- **The matrix form of the conjugation law**: `ρ_{b'}(σ)` and `ρ_b(σ)` intertwine the change of
basis. Stated multiplicatively rather than as a conjugation because that is the form the proof
produces and the form with no inverses in it. -/
theorem coe_galoisRepMatrix_mul_basisChange (σ : F ≃ₐ[S] F) :
    (galoisRepMatrix b' σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) * b'.toMatrix b
      = b'.toMatrix b * (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨m, rfl⟩ : ∃ m, ⇑(b.repr m) = v :=
    ⟨b.equivFun.symm v, by rw [← Module.Basis.equivFun_apply]; exact b.equivFun.apply_symm_apply v⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Module.Basis.toMatrix_mulVec_repr,
    ← galoisRepMatrix_mulVec, ← galoisRepMatrix_mulVec, Module.Basis.toMatrix_mulVec_repr]

open tateModule in
/-- **`ρ_{b'}(σ) · c = c · ρ_b(σ)`** in `GL₂(ℤ_[ℓ])`, where `c = basisChangeGL b b'`. -/
theorem galoisRepMatrix_mul_basisChangeGL (σ : F ≃ₐ[S] F) :
    galoisRepMatrix b' σ * basisChangeGL b b' = basisChangeGL b b' * galoisRepMatrix b σ :=
  Units.ext <| by
    simpa [coe_basisChangeGL] using coe_galoisRepMatrix_mul_basisChange b b' σ

open tateModule in
/-- **Changing the basis conjugates the `ℓ`-adic representation.**

`ρ_{E,ℓ}` depends on a choice of basis of `T_ℓE`, and this is exactly how: the representations
attached to two bases differ by conjugation by the change-of-basis element, uniformly in `σ`. It is
the theorem behind the classical phrase *"the `ℓ`-adic representation attached to `E`, well defined
up to conjugation"*, and it is what makes every conjugation-invariant of `ρ_{E,ℓ}` — its kernel,
its determinant and trace, its image up to conjugacy — independent of the choice. -/
theorem galoisRepMatrix_conj (σ : F ≃ₐ[S] F) :
    galoisRepMatrix b' σ = basisChangeGL b b' * galoisRepMatrix b σ * (basisChangeGL b b')⁻¹ := by
  rw [← galoisRepMatrix_mul_basisChangeGL, mul_inv_cancel_right]

open tateModule in
/-- **The conjugation law as an identity of representations**, not merely of their values: the two
monoid homomorphisms `G →* GL₂(ℤ_[ℓ])` differ by an inner automorphism of `GL₂(ℤ_[ℓ])`. This is the
form to quote when the point is that the *representation* is well defined up to conjugation. -/
theorem galoisRepMatrix_eq_conj_comp :
    galoisRepMatrix b' =
      (MulAut.conj (basisChangeGL b b')).toMonoidHom.comp (galoisRepMatrix b) :=
  MonoidHom.ext fun σ => by
    simpa using galoisRepMatrix_conj b b' σ

open tateModule in
/-- **The image of `ρ_{E,ℓ}` is well defined up to conjugacy in `GL₂(ℤ_[ℓ])`.** Not merely
isomorphic: it is carried onto the other by an inner automorphism of the ambient group. -/
theorem range_galoisRepMatrix_map :
    (galoisRepMatrix b').range =
      (galoisRepMatrix b).range.map (MulAut.conj (basisChangeGL b b')).toMonoidHom := by
  rw [galoisRepMatrix_eq_conj_comp b b', MonoidHom.range_comp]

end WeierstrassCurve.Affine
