/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.MatrixRep
import EllipticCurves.TateModule.OpenKernel
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Changing the basis conjugates `ρ_{E,2}`

`galoisRepMatrixTwo b : G →* GL₂(ℤ_[2])` of `EllipticCurves.TateModule.MatrixRep` depends on a
choice of basis `b` of `T₂E`, and the docstrings on this front have said since that file was
written that *"different bases give representations differing by conjugation"*. That sentence was
never a theorem. This file makes it one:

```
galoisRepMatrixTwo b' σ = c * galoisRepMatrixTwo b σ * c⁻¹,   c = basisChangeGL b b'
```

uniformly in `σ`, hence also as an identity of monoid homomorphisms
(`galoisRepMatrixTwo_eq_conj_comp`). It is what licenses the standard phrase *"the `2`-adic
representation attached to `E`, well defined up to conjugation"*.

## Why it is worth having

Each individual consequence of "changing the basis only conjugates" was previously either proved
by a separate ad hoc argument or left as a remark:

* the **kernel** does not depend on `b` — proved directly in `EllipticCurves.TateModule.Kernel`
  (`ker_galoisRepMatrixTwo`) from the fact that `(matrixAutEquivTwo b).symm` is injective, which is
  a shorter route than conjugation and is left alone here; this file only adds the topological
  corollary `isClosed_ker_galoisRepMatrixTwo`;
* `det`, `trace` and `charpoly` do not depend on `b` — proved in
  `EllipticCurves.TateModule.Determinant`, again by a direct argument;
* **continuity** does not depend on `b` — this turned out to need no argument at all, since
  `continuous_galoisRepMatrixTwo` of `EllipticCurves.TateModule.MatrixContinuity` carries no
  hypothesis on the basis whatsoever (see the historical note below).

The conjugation law is the single statement all three are instances of, and unlike them it also
covers the invariants nobody has yet formalised (the image up to conjugacy — see
`range_galoisRepMatrixTwo_map`, the characteristic ideal, reductions mod `2^k`, …). It is stated
here once so that no future file has to re-derive it.

## A historical note, and a correction to three module docstrings

Issues `#592` (`Continuity.lean`), `#597` (`Profinite.lean`) and `#598` (`OpenKernel.lean`) each
recorded that continuity of `galoisRepMatrixTwo b` into `GL₂(ℤ_[2])` was unavailable because it
*"needs `b.repr` to be continuous, i.e. a basis compatible with the level filtration"*. That is
**false**, and `EllipticCurves.TateModule.MatrixContinuity` proves it false: `b.equivFun.symm` is
continuous for *any* basis, its source `Fin 2 → ℤ_[2]` is compact and its target is Hausdorff, so
`b.equivFun` is continuous by `Continuous.homeoOfEquivCompactToT2`. No compatibility with the level
filtration enters. The three docstrings are corrected in the same commit as this file; they are
recorded here too because the claim survived three merged pull requests and a reader who has seen
it should be able to find its refutation.

The corollary is that continuity is basis-independent for the trivial reason — every basis works —
and *not* because conjugation is a homeomorphism. The conjugation-is-a-homeomorphism argument is
still the correct one for a hypothetical `ρ` known continuous in one basis only, but it is not
needed here, so it is not stated.

## Main definitions

* `WeierstrassCurve.Affine.tateModule.basisChangeGL` : the change-of-basis matrix `b'.toMatrix b`
  packaged as an element of `GL ι R`, with `b.toMatrix b'` as its inverse.

## Main statements

* `WeierstrassCurve.Affine.galoisRepMatrixTwo_conj` : `ρ_{b'}(σ) = c ρ_b(σ) c⁻¹`.
* `WeierstrassCurve.Affine.galoisRepMatrixTwo_eq_conj_comp` : the same as an equality of monoid
  homomorphisms `G →* GL₂(ℤ_[2])`.
* `WeierstrassCurve.Affine.range_galoisRepMatrixTwo_map` : the image of `ρ_{E,2}` is well defined
  up to conjugacy in `GL₂(ℤ_[2])`.
* `WeierstrassCurve.Affine.isClosed_ker_galoisRepMatrixTwo` : `ker ρ_{E,2}` is closed in `G`, in
  every basis.

## Scope

`ℓ = 2` only, because `galoisRepMatrixTwo` is. ⚠️ The reason this paragraph used to give —
*"a basis of `T_ℓE` is available only at `ℓ = 2`, through the `2`-primary tower"* — is false as of
`EllipticCurves.TateModule.FreeThree`, which gives `Module.Free ℤ_[3] T₃E` and
`finrank ℤ_[3] T₃E = 2` and hence a basis at `ℓ = 3`. So is the deadline in its continuation,
*"once `T_ℓE ≅ ℤ_ℓ²` is available at odd `ℓ`"*: that day has arrived at `ℓ = 3`. The conjugation
law itself is insensitive to `ℓ` and will transfer verbatim as soon as an `ℓ = 3` matrix
representation is stated; at `ℓ ≥ 5` the Tate module itself is still out of reach.

Nothing here bears on **whether the conjugacy class is nontrivial**, i.e. on the image of
`ρ_{E,2}`: that is a statement about `F / S`, and `G` may be trivial for all this file knows. What
*is* discriminated is that the conjugating element is genuinely not always `1`
(`basisChangeGL_reindex_swap_ne_one`), so the law is not `b' = b` in disguise.

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
@[simp]
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

This is the non-vacuity certificate for `galoisRepMatrixTwo_conj`: without it, the conjugation law
would be consistent with `basisChangeGL` being constantly `1`, i.e. with the law saying nothing
beyond `b' = b`. -/
lemma basisChangeGL_reindex_swap_ne_one [Nontrivial R] (c : Module.Basis (Fin 2) R M) :
    basisChangeGL c (c.reindex (Equiv.swap 0 1)) ≠ 1 := by
  intro h
  have h00 := congrFun₂
    (congrArg (fun u : GL (Fin 2) R => (u : Matrix (Fin 2) (Fin 2) R)) h) 0 0
  simp [Module.Basis.toMatrix_apply] at h00

end tateModule

/-! ### The conjugation law for `ρ_{E,2}` -/

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

variable (b b' : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

open tateModule in
/-- **The matrix form of the conjugation law**: `ρ_{b'}(σ)` and `ρ_b(σ)` intertwine the change of
basis. Stated multiplicatively rather than as a conjugation because that is the form the proof
produces and the form with no inverses in it. -/
theorem coe_galoisRepMatrixTwo_mul_basisChange (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b' σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) * b'.toMatrix b
      = b'.toMatrix b * (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  obtain ⟨m, rfl⟩ : ∃ m, ⇑(b.repr m) = v :=
    ⟨b.equivFun.symm v, by rw [← Module.Basis.equivFun_apply]; exact b.equivFun.apply_symm_apply v⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Module.Basis.toMatrix_mulVec_repr,
    ← galoisRepMatrixTwo_mulVec, ← galoisRepMatrixTwo_mulVec, Module.Basis.toMatrix_mulVec_repr]

open tateModule in
/-- **`ρ_{b'}(σ) · c = c · ρ_b(σ)`** in `GL₂(ℤ_[2])`, where `c = basisChangeGL b b'`. -/
theorem galoisRepMatrixTwo_mul_basisChangeGL (σ : F ≃ₐ[S] F) :
    galoisRepMatrixTwo b' σ * basisChangeGL b b' = basisChangeGL b b' * galoisRepMatrixTwo b σ :=
  Units.ext <| by
    simpa [coe_basisChangeGL] using coe_galoisRepMatrixTwo_mul_basisChange b b' σ

open tateModule in
/-- **Changing the basis conjugates the `2`-adic representation.**

`ρ_{E,2}` depends on a choice of basis of `T₂E`, and this is exactly how: the representations
attached to two bases differ by conjugation by the change-of-basis element, uniformly in `σ`. It is
the theorem behind the classical phrase *"the `2`-adic representation attached to `E`, well defined
up to conjugation"*, and it is what makes every conjugation-invariant of `ρ_{E,2}` — its kernel,
its determinant and trace, its image up to conjugacy — independent of the choice. -/
theorem galoisRepMatrixTwo_conj (σ : F ≃ₐ[S] F) :
    galoisRepMatrixTwo b' σ
      = basisChangeGL b b' * galoisRepMatrixTwo b σ * (basisChangeGL b b')⁻¹ := by
  rw [← galoisRepMatrixTwo_mul_basisChangeGL, mul_inv_cancel_right]

open tateModule in
/-- **The conjugation law as an identity of representations**, not merely of their values: the two
monoid homomorphisms `G →* GL₂(ℤ_[2])` differ by an inner automorphism of `GL₂(ℤ_[2])`. This is the
form to quote when the point is that the *representation* is well defined up to conjugation. -/
theorem galoisRepMatrixTwo_eq_conj_comp :
    galoisRepMatrixTwo b' =
      (MulAut.conj (basisChangeGL b b')).toMonoidHom.comp (galoisRepMatrixTwo b) :=
  MonoidHom.ext fun σ => by
    simpa using galoisRepMatrixTwo_conj b b' σ

open tateModule in
/-- **The image of `ρ_{E,2}` is well defined up to conjugacy in `GL₂(ℤ_[2])`.** Not merely
isomorphic: it is carried onto the other by an inner automorphism of the ambient group. -/
theorem range_galoisRepMatrixTwo_map :
    (galoisRepMatrixTwo b').range =
      (galoisRepMatrixTwo b).range.map (MulAut.conj (basisChangeGL b b')).toMonoidHom := by
  rw [galoisRepMatrixTwo_eq_conj_comp b b', MonoidHom.range_comp]

/-- **`ker ρ_{E,2}` is closed in `G`, in every basis.**

`ker_galoisRepMatrixTwo` of `EllipticCurves.TateModule.Kernel` identifies the kernel with
`ker (galoisRep 2)`, which `isClosed_ker_galoisRepTwo` of `EllipticCurves.TateModule.OpenKernel`
shows is closed; this is the two together, in the shape a consumer of the matrix representation
wants. Note it is *closed* and not, in general, open — see `OpenKernel.lean`. -/
theorem isClosed_ker_galoisRepMatrixTwo [Algebra.IsIntegral S F] [IsAlgClosed F]
    [(W'⁄F).IsElliptic] (h2 : (2 : F) ≠ 0) :
    IsClosed ((galoisRepMatrixTwo b).ker : Set (F ≃ₐ[S] F)) := by
  rw [ker_galoisRepMatrixTwo b]
  exact isClosed_ker_galoisRepTwo h2

end WeierstrassCurve.Affine
