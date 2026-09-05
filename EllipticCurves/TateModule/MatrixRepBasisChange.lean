/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.MatrixRep
import EllipticCurves.TateModule.OpenKernel
import EllipticCurves.TateModule.PrimaryMatrixRepBasisChange

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
  (`ker_galoisRepMatrix`, and `ker_galoisRepMatrixTwo` at `ℓ = 2`) from the fact that
  `(matrixAutEquiv b).symm` is injective, which is a shorter route than conjugation and is left
  alone here; this file only adds the topological corollary `isClosed_ker_galoisRepMatrixTwo`;
* `det`, `trace` and `charpoly` do not depend on `b` — proved in
  `EllipticCurves.TateModule.Determinant`, again by a direct argument;
* **continuity** does not depend on `b` — this turned out to need no argument at all, since
  `continuous_galoisRepMatrixTwo` of `EllipticCurves.TateModule.MatrixContinuity` carries no
  hypothesis on the basis whatsoever (see the historical note below).

The conjugation law is the single statement all three are instances of, and unlike them it also
covers the invariants nobody has yet formalised (the image up to conjugacy — see
`range_galoisRepMatrixTwo_map`, the characteristic ideal, reductions mod `2^k`, …). It is stated
once so that no future file has to re-derive it.

## What is in this file, and what moved out of it

⚠️ **The argument is no longer here.** The conjugation law is proved at an arbitrary prime in
`EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`, and every theorem below is a one-line
instantiation of it at `ℓ = 2` — except `isClosed_ker_galoisRepMatrixTwo`, which is the one
statement of the file that consumes something genuinely `ℓ`-indexed
(`isClosed_ker_galoisRepTwo`, `EllipticCurves.TateModule.OpenKernel`).

⚠️ `basisChangeGL` and its seven lemmas, including the non-vacuity certificate
`tateModule.basisChangeGL_reindex_swap_ne_one`, **moved** to that file unchanged: same namespace
`WeierstrassCurve.Affine.tateModule`, same statements, same proofs. They were always stated over an
arbitrary commutative ring and an arbitrary finite-rank free module, so nothing about them became
more general; the move is forced by the import graph, since this file imports
`EllipticCurves.TateModule.OpenKernel` and an `ℓ`-generic file must not.

## A historical note, and a correction to three module docstrings

Issues `#592` (`Continuity.lean`), `#597` (`Profinite.lean`) and `#598` (`OpenKernel.lean`) each
recorded that continuity of `galoisRepMatrixTwo b` into `GL₂(ℤ_[2])` was unavailable because it
*"needs `b.repr` to be continuous, i.e. a basis compatible with the level filtration"*. That is
**false**, and `EllipticCurves.TateModule.MatrixContinuity` proves it false: `b.equivFun.symm` is
continuous for *any* basis, its source `Fin 2 → ℤ_[2]` is compact and its target is Hausdorff, so
`b.equivFun` is continuous by `Continuous.homeoOfEquivCompactToT2`. No compatibility with the level
filtration enters. The three docstrings were corrected in the same commit as this file; they are
recorded here too because the claim survived three merged pull requests and a reader who has seen
it should be able to find its refutation.

The corollary is that continuity is basis-independent for the trivial reason — every basis works —
and *not* because conjugation is a homeomorphism. The conjugation-is-a-homeomorphism argument is
still the correct one for a hypothetical `ρ` known continuous in one basis only, but it is not
needed here, so it is not stated.

## Main statements

* `WeierstrassCurve.Affine.galoisRepMatrixTwo_conj` : `ρ_{b'}(σ) = c ρ_b(σ) c⁻¹`.
* `WeierstrassCurve.Affine.galoisRepMatrixTwo_eq_conj_comp` : the same as an equality of monoid
  homomorphisms `G →* GL₂(ℤ_[2])`.
* `WeierstrassCurve.Affine.range_galoisRepMatrixTwo_map` : the image of `ρ_{E,2}` is well defined
  up to conjugacy in `GL₂(ℤ_[2])`.
* `WeierstrassCurve.Affine.isClosed_ker_galoisRepMatrixTwo` : `ker ρ_{E,2}` is closed in `G`, in
  every basis.

## Scope

`ℓ = 2` only, because the statements below are — they are the `ℓ = 2` *names*, kept because
`galoisRepMatrixTwo` predates the extraction and is consumed throughout this development. ⚠️ **The
conjugation law itself is not.**

⚠️ Three clauses this paragraph carried before that were **false** were replaced in an earlier
commit and are not re-derived here; they are recorded so the history is not lost. They were
*"a basis of `T_ℓE` is available only at `ℓ = 2`, through the `2`-primary tower"* and its
continuation *"once `T_ℓE ≅ ℤ_ℓ²` is available at odd `ℓ`"*, both false as of
`EllipticCurves.TateModule.FreeThree`; and *"[the conjugation law] will transfer verbatim as soon
as an `ℓ = 3` matrix representation is stated"*, a deadline that passed with
`EllipticCurves.TateModule.MatrixRepThree`.

What this paragraph used to end with was a clause that was **right**, and it is quoted rather than
deleted because what changed is not its truth but its tense:

> ⚠️ **So this file is `ℓ = 2` only by omission and not by obstruction.** The conjugation law is
> insensitive to `ℓ` — nothing below uses `2` for anything but the type — and extracting it to
> `PrimaryMatrixRep`-style genericity is a mechanical follow-up that nothing blocks.

The omission has stopped being one. The extraction is
`EllipticCurves.TateModule.PrimaryMatrixRepBasisChange` and the `ℓ = 3` instantiation is
`EllipticCurves.TateModule.MatrixRepBasisChangeThree`.

⚠️ **The tail of that clause still stands verbatim and is the part a reader should keep**: do not
read *"`ℓ = 2` only"* here as a claim that odd `ℓ` is gated. At `ℓ ≥ 5` the Tate module itself is
out of reach — `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)` is gated on `#E[ℓ^k]` — and **that** is the real gate,
but it is not this file's and it is not the conjugation law's.  ⚠️ This sentence used to name
`[ℓ]`-surjectivity as a second gate and to equate the pair with *"the general coordinate formula
`x(nP) = Φₙ/ΨSqₙ`"*; both are stale — surjectivity holds at every nonzero index with `(2 : F) ≠ 0`
(`nsmul_surjective_of_two_ne_zero`, `EllipticCurves.Torsion.TwoTorsionOrder`) and the formula is
proved at every index with `(2 : F) ≠ 0` (`hasXCoordFormula_of_two_ne_zero`,
`EllipticCurves.Torsion.NsmulOrder`).

Nothing here bears on **whether the conjugacy class is nontrivial**, i.e. on the image of
`ρ_{E,2}`: that is a statement about `F / S`, and `G` may be trivial for all this file knows. What
*is* discriminated is that the conjugating element is genuinely not always `1`
(`tateModule.basisChangeGL_reindex_swap_ne_one`, stated over an arbitrary `Nontrivial` commutative
ring in the generic file and **not** restated here), so the law is not `b' = b` in disguise.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

/-! ### The conjugation law for `ρ_{E,2}` -/

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

variable (b b' : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

open tateModule in
/-- **The matrix form of the conjugation law**: `ρ_{b'}(σ)` and `ρ_b(σ)` intertwine the change of
basis. Stated multiplicatively rather than as a conjugation because that is the form the proof
produces and the form with no inverses in it. `coe_galoisRepMatrix_mul_basisChange` at `ℓ = 2`. -/
theorem coe_galoisRepMatrixTwo_mul_basisChange (σ : F ≃ₐ[S] F) :
    (galoisRepMatrixTwo b' σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) * b'.toMatrix b
      = b'.toMatrix b * (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) :=
  coe_galoisRepMatrix_mul_basisChange b b' σ

open tateModule in
/-- **`ρ_{b'}(σ) · c = c · ρ_b(σ)`** in `GL₂(ℤ_[2])`, where `c = basisChangeGL b b'`. -/
theorem galoisRepMatrixTwo_mul_basisChangeGL (σ : F ≃ₐ[S] F) :
    galoisRepMatrixTwo b' σ * basisChangeGL b b' = basisChangeGL b b' * galoisRepMatrixTwo b σ :=
  galoisRepMatrix_mul_basisChangeGL b b' σ

open tateModule in
/-- **Changing the basis conjugates the `2`-adic representation.**

`ρ_{E,2}` depends on a choice of basis of `T₂E`, and this is exactly how: the representations
attached to two bases differ by conjugation by the change-of-basis element, uniformly in `σ`. It is
the theorem behind the classical phrase *"the `2`-adic representation attached to `E`, well defined
up to conjugation"*, and it is what makes every conjugation-invariant of `ρ_{E,2}` — its kernel,
its determinant and trace, its image up to conjugacy — independent of the choice. -/
theorem galoisRepMatrixTwo_conj (σ : F ≃ₐ[S] F) :
    galoisRepMatrixTwo b' σ
      = basisChangeGL b b' * galoisRepMatrixTwo b σ * (basisChangeGL b b')⁻¹ :=
  galoisRepMatrix_conj b b' σ

open tateModule in
/-- **The conjugation law as an identity of representations**, not merely of their values: the two
monoid homomorphisms `G →* GL₂(ℤ_[2])` differ by an inner automorphism of `GL₂(ℤ_[2])`. This is the
form to quote when the point is that the *representation* is well defined up to conjugation. -/
theorem galoisRepMatrixTwo_eq_conj_comp :
    galoisRepMatrixTwo b' =
      (MulAut.conj (basisChangeGL b b')).toMonoidHom.comp (galoisRepMatrixTwo b) :=
  galoisRepMatrix_eq_conj_comp b b'

open tateModule in
/-- **The image of `ρ_{E,2}` is well defined up to conjugacy in `GL₂(ℤ_[2])`.** Not merely
isomorphic: it is carried onto the other by an inner automorphism of the ambient group. -/
theorem range_galoisRepMatrixTwo_map :
    (galoisRepMatrixTwo b').range =
      (galoisRepMatrixTwo b).range.map (MulAut.conj (basisChangeGL b b')).toMonoidHom :=
  range_galoisRepMatrix_map b b'

/-- **`ker ρ_{E,2}` is closed in `G`, in every basis.**

`ker_galoisRepMatrixTwo` of `EllipticCurves.TateModule.Kernel` identifies the kernel with
`ker (galoisRep 2)`, which `isClosed_ker_galoisRepTwo` of `EllipticCurves.TateModule.OpenKernel`
shows is closed; this is the two together, in the shape a consumer of the matrix representation
wants. Note it is *closed* and not, in general, open — see `OpenKernel.lean`.

⚠️ This is the one statement of this file that is **not** an instantiation of a generic theorem:
its second input is `ℓ = 2`-specific. Its `ℓ = 3` twin is `isClosed_ker_galoisRepMatrixThree`
(`EllipticCurves.TateModule.MatrixRepBasisChangeThree`), which carries `h3` as well. -/
theorem isClosed_ker_galoisRepMatrixTwo [Algebra.IsIntegral S F] [IsAlgClosed F]
    [(W'⁄F).IsElliptic] (h2 : (2 : F) ≠ 0) :
    IsClosed ((galoisRepMatrixTwo b).ker : Set (F ≃ₐ[S] F)) := by
  rw [ker_galoisRepMatrixTwo b]
  exact isClosed_ker_galoisRepTwo h2

end WeierstrassCurve.Affine
