/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Free
import EllipticCurves.TateModule.PrimaryMatrixRep

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

## What this file contains, and what it does not

⚠️ **The transport is no longer here.** It is
`EllipticCurves.TateModule.PrimaryMatrixRep`, stated for an arbitrary prime `ℓ` in terms of one
input, `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`. **This file supplies that input at `ℓ = 2` and
contains no argument**: every proof below is one line, and every definition below is
*definitionally* its generic form at `ℓ = 2`. The input is `nonempty_tateModuleEquivProd`
(`EllipticCurves.TateModule.Free`).

⚠️ **Every public name and statement this file had before the extraction is unchanged.** Nine
declarations, same spellings, same types; consumers see no difference. This mirrors what
`EllipticCurves.TateModule.Free` did when `padicPairEquiv` moved to
`EllipticCurves.TateModule.PrimaryFree`.

The content is still `EllipticCurves.TateModule.Free`: `T₂E` is a free `ℤ_[2]`-module of rank `2`,
so it has a basis indexed by `Fin 2`, and a `ℤ_[2]`-linear automorphism of it is a matrix. The
`GL₂` shape cannot even be *stated* without that rank. Nothing here is new Galois theory: it is a
transport along an equivalence.

## The choice of basis, and what does not depend on it

`T₂E` has no canonical basis — one comes from a coherent system of generating pairs of the groups
`E[2^k]`, and different systems give representations differing by conjugation. So the matrix
representation takes a basis as an argument, and only its *existence* is stated choice-freely
(`exists_galoisRepMatrixTwo`). This follows the packaging already used in
`EllipticCurves.TateModule.PrimaryFree`, where `padicPairEquiv` carries the basis and `Module.Free`
/ `Module.finrank` do not. ⚠️ That reference used to name `EllipticCurves.TateModule.Free`, which
declared `padicPairEquiv` until the construction was extracted to a general `ℓ`; `Free` is now the
`ℓ = 2` list of instantiations and declares none of the `padicPair…` names.

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
`def`, so `[(W'⁄F).IsElliptic]` is **not** found by bare `inferInstance` even when
`[W'.IsElliptic]` is available: `baseChange` does not unfold to `map`, which is where Mathlib's
instance lives. Use the incantation already standard elsewhere in this development, e.g. in
`EllipticCurves.Reduction.JInvariantGoodReductionBaseChange`:

```
haveI : (W'⁄F).IsElliptic := inferInstanceAs (W'.map (algebraMap S F)).IsElliptic
```

## Scope

Odd `ℓ` is **not** covered *by this file*, and the `ℓ = 2` case went through the `2`-primary tower.
⚠️ **Three clauses this paragraph used to carry are now false and are replaced.** The first,
*"needs surjectivity of `[ℓ]` on `E(F̄)`, which is not available"*, is false at `ℓ = 3`:
`nsmul_three_surjective` (`EllipticCurves.Torsion.TriplingSurjective`) supplies it from
`(2 : F) ≠ 0` alone. The second, *"`T_ℓE ≅ ℤ_ℓ²` at odd `ℓ` is not available"* — together with
*"what is missing at `ℓ = 3` is only the transport to `T₃E`"* — is false as of
`EllipticCurves.TateModule.FreeThree`, which performs exactly that transport and delivers
`Module.Free ℤ_[3] T₃E` and `finrank ℤ_[3] T₃E = 2`. The third, *"What is missing at `ℓ = 3` is
therefore not the module but the matrix representation: `galoisRepMatrixThree` is simply not stated
below"*, is now false too: `galoisRepMatrixThree` **is** stated, in
`EllipticCurves.TateModule.MatrixRepThree`, over the `ℓ`-generic transport this file now shares
with it. ⚠️ Nothing is missing at `ℓ = 3` for the *matrix representation itself*; what remains
`ℓ = 2` only is the surrounding apparatus — continuity and the conjugation law — and each is a
separate follow-up named in `EllipticCurves.TateModule.MatrixRepThree`'s Scope. ⚠️ **This sentence
used to list "the determinant and trace characters" among them and that has gone false**:
`galoisDetThree` and `galoisTraceThree` are stated in
`EllipticCurves.TateModule.DeterminantThree`, over the `ℓ`-generic
`EllipticCurves.TateModule.PrimaryDeterminant`. At `ℓ ≥ 5` surjectivity is genuinely unavailable,
so the first clause still stands verbatim there.

**Continuity is not asserted *in this file*.** `EllipticCurves.TateModule.GaloisAction` builds
`galoisRep` purely as a group homomorphism and passing to matrices changes nothing about that, so
nothing below should be read as supplying continuity. It is supplied downstream, for an arbitrary
basis and with no compatibility hypothesis, by `continuous_galoisRepMatrixTwo` in
`EllipticCurves.TateModule.MatrixContinuity`. ⚠️ That file is `ℓ = 2` only and this file's
extraction does not change it. Also out of scope: injectivity of `ρ`, its determinant character
`det ∘ ρ : G → ℤ_[2]ˣ` and the comparison with the cyclotomic character (which needs the Weil
pairing), and any description of the image.

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

namespace tateModule

/-! ### A basis of `T₂E` indexed by `Fin 2` -/

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-- The basis of `T₂E` indexed by `Fin 2` attached to a `ℤ_[2]`-linear equivalence
`T₂E ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2]`, such as the one `padicPairEquiv` builds from a coherent system of
generating pairs. Definitionally `tateModuleBasis` at `ℓ = 2`.

`Fin 2 → ℤ_[2]` is preferred over `ℤ_[2] × ℤ_[2]` from here on: `Matrix`, `LinearMap.toMatrix` and
`GL` are all indexed by a `Fintype`, so it is cheaper to cross `finTwoArrow` once than to carry a
`Prod` through every later statement. `Module.Free` alone would only give a basis indexed by the
opaque `Module.Free.ChooseBasisIndex`. -/
noncomputable def tateModuleBasisTwo (e : W.tateModule 2 ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2]) :
    Module.Basis (Fin 2) ℤ_[2] (W.tateModule 2) :=
  tateModuleBasis e

/-- **`T₂E` has a basis indexed by `Fin 2`.** The basis itself depends on a choice of coherent
system of generating pairs of the `E[2^k]`; its existence does not. -/
theorem nonempty_basis_tateModule_two [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) ℤ_[2] (W.tateModule 2)) :=
  nonempty_basis_tateModule_of_nonempty (nonempty_tateModuleEquivProd h2)

end tateModule

/-! ### The matrix representation -/

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-- The multiplicative equivalence `GL (Fin 2) ℤ_[2] ≃* Aut_{ℤ_[2]}(T₂E)` determined by a basis:
`Matrix.GeneralLinearGroup.toLin'` transports matrices to units of the endomorphism ring, and
`LinearMap.GeneralLinearGroup.generalLinearEquiv` reads those units as linear equivalences.
Definitionally `matrixAutEquiv` at `ℓ = 2`. -/
noncomputable def matrixAutEquivTwo :
    GL (Fin 2) ℤ_[2] ≃* ((W'⁄F).tateModule 2 ≃ₗ[ℤ_[2]] (W'⁄F).tateModule 2) :=
  matrixAutEquiv b

/-- **The `2`-adic Galois representation in matrix form**,
`ρ_{E,2} : G →* GL₂(ℤ_[2])`, obtained by reading `galoisRep 2` through a basis of `T₂E`.
Definitionally `galoisRepMatrix` at `ℓ = 2`.

Different bases give representations that differ by conjugation, so this depends on `b`; see
`exists_galoisRepMatrixTwo` for the choice-free existence statement and
`galoisRepMatrixTwo_conj` in `EllipticCurves.TateModule.MatrixRepBasisChange` for the conjugation
law itself. Continuity is not asserted here, but holds — see
`continuous_galoisRepMatrixTwo` in `EllipticCurves.TateModule.MatrixContinuity`. -/
noncomputable def galoisRepMatrixTwo : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[2] :=
  galoisRepMatrix b

@[simp]
lemma matrixAutEquivTwo_galoisRepMatrixTwo (σ : F ≃ₐ[S] F) :
    matrixAutEquivTwo b (galoisRepMatrixTwo b σ) = galoisRep 2 σ :=
  matrixAutEquiv_galoisRepMatrix b σ

/-- **The matrix acts on coordinate vectors exactly as `σ` acts on `T₂E`.** This is the identity
that ties `galoisRepMatrixTwo` back to `galoisRep`, and the form later computations use. -/
lemma galoisRepMatrixTwo_mulVec (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 2) :
    ⇑(b.repr (σ • f)) = (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) *ᵥ ⇑(b.repr f) :=
  galoisRepMatrix_mulVec b σ f

/-- **The entries of `ρ_{E,2}(σ)`.** The `j`-th column is the coordinate vector of the Galois
translate of the `j`-th basis vector; equivalently, matrices here act on column vectors. -/
lemma galoisRepMatrixTwo_apply_coe (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j = b.repr (σ • b j) i :=
  galoisRepMatrix_apply_coe b σ i j

/-- **`σ` translates a basis vector into the corresponding column of its matrix.** The unbundled
reading of `galoisRepMatrixTwo_apply_coe`.

⚠️ This name carries no `Two`, which is why the `ℓ`-generic form in
`EllipticCurves.TateModule.PrimaryMatrixRep` is spelled `galoisRepMatrix_smul_basis_eq_sum` with
the head symbol first rather than by dropping a suffix that is not there. The historical spelling
is kept here so that no consumer changes. -/
lemma galois_smul_basis_eq_sum (σ : F ≃ₐ[S] F) (j : Fin 2) :
    σ • b j = ∑ i, (galoisRepMatrixTwo b σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) i j • b i :=
  galoisRepMatrix_smul_basis_eq_sum b σ j

/-- **The `2`-adic Galois representation exists**, as a matrix representation that really does
compute the Galois action: there are a basis of `T₂E` and a homomorphism
`ρ : G →* GL₂(ℤ_[2])` whose matrices act on coordinate vectors the way `G` acts on `T₂E`.

The compatibility clause is the point. `Nonempty ((F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[2])` on its own
would be vacuous — the trivial homomorphism witnesses it, and the statement would not mention the
curve at all. Both the basis and `ρ` depend on a choice of coherent system of generating pairs, and
two choices give representations differing by conjugation.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(nonempty_tateModuleEquivProd h2)` by a hole — `by refine
exists_galoisRepMatrix_of_nonempty (W' := W') (F := F) (ℓ := 2) ?_` — leaves

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁵ : Field S
inst✝⁴ : Field F
inst✝³ : DecidableEq F
inst✝² : Algebra S F
W' : Affine S
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
⊢ Nonempty (↥((W'⁄F).tateModule 2) ≃ₗ[ℤ_[2]] ℤ_[2] × ℤ_[2])
```

⚠️ `h2` **survives** in the context, so what the deletion removes is a construction and not a
hypothesis, and the residual is a **goal**, which no type mismatch could produce. It is `T₂E ≅ ℤ₂²`
itself: the `GL₂` shape cannot be produced without it. -/
theorem exists_galoisRepMatrixTwo [IsAlgClosed F] [(W'⁄F).IsElliptic] (h2 : (2 : F) ≠ 0) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[2]), ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 2),
        ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[2]) *ᵥ ⇑(b.repr f) :=
  exists_galoisRepMatrix_of_nonempty (tateModule.nonempty_tateModuleEquivProd h2)

end WeierstrassCurve.Affine
