/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Free
import EllipticCurves.TateModule.GaloisAction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# `ρ_{E,2} : G → GL₂(ℤ₂)` : the `2`-adic representation in matrix form

Let `W'` be a Weierstrass curve over a field `S`, let `F / S` be an algebraically closed extension
with `(2 : F) ≠ 0` for which the base change `W'⁄F` is elliptic, and let `G = F ≃ₐ[S] F`. This file
turns the abstract `2`-adic Galois representation

```
galoisRep 2 : G →* (T₂E ≃ₗ[ℤ_[2]] T₂E)
```

of `EllipticCurves.TateModule.GaloisAction` into a representation by honest invertible `2 × 2`
matrices,

```
galoisRepMatrixTwo b : G →* GL (Fin 2) ℤ_[2],
```

which is what "the `ℓ`-adic representation attached to `E`" classically means (Silverman, *AEC*,
III.7 and VII.7).

The content is entirely in `EllipticCurves.TateModule.Free`: `T₂E` is a free `ℤ_[2]`-module of rank
`2`, so it has a basis indexed by `Fin 2`, and a `ℤ_[2]`-linear automorphism of it is a matrix. The
`GL₂` shape cannot even be *stated* without that rank, which is why this file could not exist
before. Nothing here is new Galois theory: it is a transport along an equivalence.

## The choice of basis, and what does not depend on it

`T₂E` has no canonical basis — one comes from a coherent system of generating pairs of the groups
`E[2^k]`, and different systems give representations differing by conjugation. So the matrix
representation takes a basis as an argument, and only its *existence* is stated choice-freely
(`exists_galoisRepMatrixTwo`). This follows the packaging already used in
`EllipticCurves.TateModule.Free`, where `padicPairEquiv` carries the basis and `Module.Free` /
`Module.finrank` do not.

## The two lemmas that make it usable

A `GL₂`-valued definition with no computation rule is worth little, so the file records how the
matrix acts:

* `galoisRepMatrixTwo_mulVec` : on coordinate vectors, `σ` acts by matrix multiplication,
  `b.repr (σ • f) = ρ σ *ᵥ b.repr f`. This is the statement that identifies `galoisRepMatrixTwo`
  with `galoisRep`, and it is the form later computations run on.
* `galoisRepMatrixTwo_apply_coe` : the entries themselves, `(ρ σ) i j = b.repr (σ • b j) i` — the
  `j`-th column of `ρ σ` is the coordinate vector of the Galois translate of the `j`-th basis
  vector, i.e. matrices act on *column* vectors here.

## Using this file

The hypotheses are on the *base-changed* curve `W'⁄F`, and `WeierstrassCurve.baseChange` is a plain
`def`, so `[(W'⁄F).IsElliptic]` is **not** found by bare `inferInstance` even when `[W'.IsElliptic]`
is available: `baseChange` does not unfold to `map`, which is where Mathlib's instance lives. Use
the incantation already standard elsewhere in this development, e.g. in
`EllipticCurves.Reduction.JInvariantGoodReductionBaseChange`:

```
haveI : (W'⁄F).IsElliptic := inferInstanceAs (W'.map (algebraMap S F)).IsElliptic
```

## Scope

Odd `ℓ` is **not** covered: `T_ℓE ≅ ℤ_ℓ²` at odd `ℓ` needs surjectivity of `[ℓ]` on `E(F̄)`, which
is not available. The `ℓ = 2` case went through the `2`-primary tower instead.

**Continuity is not asserted.** `EllipticCurves.TateModule.GaloisAction` already constructs
`galoisRep` purely as a group homomorphism, disclaiming continuity for the profinite topology on
`G` and the `2`-adic topology on `T₂E`; passing to matrices changes nothing about that, and this
file must not be read as supplying it. Also out of scope: injectivity of `ρ`, its determinant
character `det ∘ ρ : G → ℤ_[2]ˣ` and the comparison with the cyclotomic character (which needs the
Weil pairing), and any description of the image.

## Main definitions

* `WeierstrassCurve.Affine.tateModule.tateModuleBasisTwo` : the basis of `T₂E` indexed by `Fin 2`
  attached to a `ℤ_[2]`-linear equivalence `T₂E ≃ₗ ℤ_[2] × ℤ_[2]`.
* `WeierstrassCurve.Affine.galoisRepMatrixTwo` : the representation `G →* GL (Fin 2) ℤ_[2]`.

## Main statements

* `WeierstrassCurve.Affine.tateModule.nonempty_basis_tateModule_two` :
  `Nonempty (Basis (Fin 2) ℤ_[2] T₂E)`.
* `WeierstrassCurve.Affine.galoisRepMatrixTwo_mulVec`,
  `WeierstrassCurve.Affine.galoisRepMatrixTwo_apply_coe` : how the matrix acts.
* `WeierstrassCurve.Affine.exists_galoisRepMatrixTwo` : a basis and a representation
  `G →* GL (Fin 2) ℤ_[2]` computing the Galois action exist.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and VII.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

namespace tateModule

/-! ### A basis of `T₂E` indexed by `Fin 2` -/

/-- The basis of `T₂E` indexed by `Fin 2` attached to a `ℤ_[2]`-linear equivalence
`T₂E ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2]`, such as the one `padicPairEquiv` builds from a coherent system of
generating pairs.

`Fin 2 → ℤ_[2]` is preferred over `ℤ_[2] × ℤ_[2]` from here on: `Matrix`, `LinearMap.toMatrix` and
`GL` are all indexed by a `Fintype`, so it is cheaper to cross `finTwoArrow` once, here, than to
carry a `Prod` through every later statement. `Module.Free` alone would only give a basis indexed
by the opaque `Module.Free.ChooseBasisIndex`. -/
noncomputable def tateModuleBasisTwo
    (e : (W'⁄F).tateModule 2 ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2]) :
    Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2) :=
  Module.Basis.ofEquivFun (e.trans (LinearEquiv.finTwoArrow ℤ_[2] ℤ_[2]).symm)

/-- **`T₂E` has a basis indexed by `Fin 2`.** The basis itself depends on a choice of coherent
system of generating pairs of the `E[2^k]`; its existence does not. -/
theorem nonempty_basis_tateModule_two [IsAlgClosed F] [(W'⁄F).IsElliptic] (h2 : (2 : F) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :=
  (nonempty_tateModuleEquivProd h2).map tateModuleBasisTwo

end tateModule

/-! ### The matrix representation -/

variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-- The multiplicative equivalence `GL (Fin 2) ℤ_[2] ≃* Aut_{ℤ_[2]}(T₂E)` determined by a basis:
`Matrix.GeneralLinearGroup.toLin'` transports matrices to units of the endomorphism ring, and
`LinearMap.GeneralLinearGroup.generalLinearEquiv` reads those units as linear equivalences. -/
noncomputable def matrixAutEquivTwo :
    GL (Fin 2) ℤ_[2] ≃* ((W'⁄F).tateModule 2 ≃ₗ[ℤ_[2]] (W'⁄F).tateModule 2) :=
  (Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ_[2] ((W'⁄F).tateModule 2))

/-- **The `2`-adic Galois representation in matrix form**,
`ρ_{E,2} : G →* GL₂(ℤ_[2])`, obtained by reading `galoisRep 2` through a basis of `T₂E`.

Different bases give representations that differ by conjugation, so this depends on `b`; see
`exists_galoisRepMatrixTwo` for the choice-free existence statement. Continuity is not asserted:
`galoisRep` is built purely as a group homomorphism. -/
noncomputable def galoisRepMatrixTwo : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[2] :=
  (matrixAutEquivTwo b).symm.toMonoidHom.comp (galoisRep 2)

@[simp]
lemma matrixAutEquivTwo_galoisRepMatrixTwo (σ : F ≃ₐ[S] F) :
    matrixAutEquivTwo b (galoisRepMatrixTwo b σ) = galoisRep 2 σ :=
  (matrixAutEquivTwo b).apply_symm_apply _

/-- **The matrix acts on coordinate vectors exactly as `σ` acts on `T₂E`.** This is the identity
that ties `galoisRepMatrixTwo` back to `galoisRep`, and the form later computations use. -/
lemma galoisRepMatrixTwo_mulVec (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 2) :
    ⇑(b.repr (σ • f)) = (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) *ᵥ ⇑(b.repr f) := by
  have h : galoisRep 2 σ f = Fintype.linearCombination ℤ_[2] ⇑b
      ((galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) *ᵥ ⇑(b.repr f)) := by
    rw [← matrixAutEquivTwo_galoisRepMatrixTwo b σ]
    exact Matrix.GeneralLinearGroup.toLin'_apply b (galoisRepMatrixTwo b σ) f
  rw [galoisRep_apply_coe] at h
  rw [h, Fintype.linearCombination_apply, Module.Basis.repr_sum_self]

/-- **The entries of `ρ_{E,2}(σ)`.** The `j`-th column is the coordinate vector of the Galois
translate of the `j`-th basis vector; equivalently, matrices here act on column vectors. -/
lemma galoisRepMatrixTwo_apply_coe (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j = b.repr (σ • b j) i := by
  have h := congrFun (galoisRepMatrixTwo_mulVec b σ (b j)) i
  rw [h]
  simp [Module.Basis.repr_self, Finsupp.single_eq_pi_single]

/-- **`σ` translates a basis vector into the corresponding column of its matrix.** The unbundled
reading of `galoisRepMatrixTwo_apply_coe`. -/
lemma galois_smul_basis_eq_sum (σ : F ≃ₐ[S] F) (j : Fin 2) :
    σ • b j = ∑ i, (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j • b i := by
  conv_lhs => rw [← b.sum_repr (σ • b j)]
  exact Finset.sum_congr rfl fun i _ => by rw [galoisRepMatrixTwo_apply_coe]

/-- **The `2`-adic Galois representation exists**, as a matrix representation that really does
compute the Galois action: there are a basis of `T₂E` and a homomorphism
`ρ : G →* GL₂(ℤ_[2])` whose matrices act on coordinate vectors the way `G` acts on `T₂E`.

The compatibility clause is the point. `Nonempty ((F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[2])` on its own
would be vacuous — the trivial homomorphism witnesses it, and the statement would not mention the
curve at all. Both the basis and `ρ` depend on a choice of coherent system of generating pairs, and
two choices give representations differing by conjugation. -/
theorem exists_galoisRepMatrixTwo [IsAlgClosed F] [(W'⁄F).IsElliptic] (h2 : (2 : F) ≠ 0) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[2]), ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 2),
        ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) *ᵥ ⇑(b.repr f) := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_two (W' := W') (F := F) h2
  exact ⟨b, galoisRepMatrixTwo b, galoisRepMatrixTwo_mulVec b⟩

end WeierstrassCurve.Affine
