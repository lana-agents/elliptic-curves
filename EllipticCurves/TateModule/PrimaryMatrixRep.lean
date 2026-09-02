/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.GaloisAction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# `ρ_{E,ℓ} : G → GL₂(ℤ_ℓ)` at an arbitrary prime: the matrix form of the Tate representation

Let `W'` be a Weierstrass curve over a field `S`, let `F / S` be an extension, let `G = F ≃ₐ[S] F`
and let `ℓ` be a prime. This file turns the abstract `ℓ`-adic Galois representation

```
galoisRep ℓ : G →* (T_ℓE ≃ₗ[ℤ_[ℓ]] T_ℓE)
```

of `EllipticCurves.TateModule.GaloisAction` into a representation by honest invertible `2 × 2`
matrices,

```
galoisRepMatrix b : G →* GL (Fin 2) ℤ_[ℓ],
```

for **any** prime `ℓ` and any basis `b` of `T_ℓE` indexed by `Fin 2` (Silverman, *AEC*, III.7 and
VII.7).

## What this file is, and why it is `ℓ`-generic

This is the **extraction** of `EllipticCurves.TateModule.MatrixRep` to an arbitrary prime. That
file was written at `ℓ = 2` because `T₂E ≅ ℤ₂²` was the only rank-two Tate module available; the
`GL₂` shape cannot even be *stated* without the rank. `EllipticCurves.TateModule.PrimaryFree` has
since made the rank-two construction `ℓ`-generic and `EllipticCurves.TateModule.FreeThree` has
supplied its input at `ℓ = 3`, so there is nothing `2`-specific left in the matrix transport.

⚠️ **Nothing here is new mathematics and nothing here is new Galois theory.** Seven of the nine
declarations of `MatrixRep.lean` mention `2` only in their types; this file is those seven with `ℓ`
in place of `2`, plus the two that consumed the `ℓ = 2` rank statement, restated to take it as a
**hypothesis**:

```
(h : Nonempty (W.tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ]))
```

That is exactly the shape `nonempty_tateModuleEquivProd_of_card`
(`EllipticCurves.TateModule.PrimaryFree`) produces, and exactly the shape
`nonempty_tateModuleEquivProd_three` (`EllipticCurves.TateModule.FreeThree`) produces at `ℓ = 3`.
This is the same move, one level further up the import graph, that
`EllipticCurves.Torsion.PrimaryBasis` and `EllipticCurves.TateModule.PrimaryFree` already made.

⚠️ **This file supplies no `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)` at any prime**, so on its own it produces no
matrix representation of any curve. The instances are
`EllipticCurves.TateModule.MatrixRep` (`ℓ = 2`) and
`EllipticCurves.TateModule.MatrixRepThree` (`ℓ = 3`), and at `ℓ ≥ 5` there is nothing to instantiate
with — see Scope.

## The choice of basis, and what does not depend on it

`T_ℓE` has no canonical basis — one comes from a coherent system of generating pairs of the groups
`E[ℓ^k]`, and different systems give representations differing by conjugation. So the matrix
representation takes a basis as an argument, and only its *existence* is stated choice-freely
(`exists_galoisRepMatrix_of_nonempty`). This is the packaging
`EllipticCurves.TateModule.PrimaryFree` already uses, where `padicPairEquiv` carries the basis and
`Module.Free` / `Module.finrank` do not.

## The two lemmas that make it usable

A `GL₂`-valued definition with no computation rule is worth little, so the file records how the
matrix acts:

* `galoisRepMatrix_mulVec` : on coordinate vectors, `σ` acts by matrix multiplication,
  `b.repr (σ • f) = ρ σ *ᵥ b.repr f`. This is the statement that identifies `galoisRepMatrix` with
  `galoisRep`, and it is the form later computations run on.
* `galoisRepMatrix_apply_coe` : the entries themselves, `(ρ σ) i j = b.repr (σ • b j) i` — the
  `j`-th column of `ρ σ` is the coordinate vector of the Galois translate of the `j`-th basis
  vector, i.e. matrices act on *column* vectors here.

## Naming

⚠️ The rule is `EllipticCurves.TateModule.PrimaryFree`'s, and it is settled: **the generic name is
the `ℓ = 2` name with `Two` dropped, and takes `_of_nonempty` where it takes the new hypothesis.**
So `galoisRepMatrixTwo` becomes `galoisRepMatrix`, and `exists_galoisRepMatrixTwo` becomes
`exists_galoisRepMatrix_of_nonempty`.

⚠️ **One exception, and it is a deliberate rename rather than an oversight.** `MatrixRep.lean`'s
`galois_smul_basis_eq_sum` carries no `Two` in its name even though its statement is about
`galoisRepMatrixTwo`, so dropping `Two` would collide with it. The generic form is therefore
`galoisRepMatrix_smul_basis_eq_sum`, head symbol first, which is what the two neighbouring names
(`galoisRepMatrix_mulVec`, `galoisRepMatrix_apply_coe`) already do. The `ℓ = 2` name is unchanged
and keeps its historical spelling.

⚠️ There is deliberately **no** `galoisRepMatrixThree'`-style second generic definition. A twin of
an already-generic definition is the duplication `EllipticCurves.TateModule.FreeThree` warns about
by name.

## Scope

* **No rank input.** See above: this file states the transport and not the freeness.
* **Continuity is not asserted here.** `EllipticCurves.TateModule.GaloisAction` builds `galoisRep`
  purely as a group homomorphism and passing to matrices changes nothing about that. Continuity is
  supplied downstream at `ℓ = 2` by `continuous_galoisRepMatrixTwo` in
  `EllipticCurves.TateModule.MatrixContinuity`. ⚠️ **That file is no longer `ℓ = 2` only**, and
  this bullet used to say it was: the argument is now `ℓ`-generic in
  `EllipticCurves.TateModule.PrimaryMatrixContinuity`, with instantiations at `ℓ = 2` and at
  `ℓ = 3` (`EllipticCurves.TateModule.MatrixContinuityThree`). ⚠️ What remains true is the first
  half of the bullet: *this* extraction does not supply continuity, and nothing below should be
  read as doing so.
* **The basis-change conjugation law is not here**, but it is no longer `ℓ = 2` only. ⚠️ The
  clause this bullet used to carry — *"It is `galoisRepMatrixTwo_conj` in
  `EllipticCurves.TateModule.MatrixRepBasisChange`, likewise still `ℓ = 2` only"* — is false: the
  law is proved at an arbitrary prime in
  `EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`, which imports *this* file and states
  `galoisRepMatrix_conj` about `galoisRepMatrix` below. `galoisRepMatrixTwo_conj` and
  `galoisRepMatrixThree_conj` are its two instantiations. It is out of scope here for the reason
  the rest of this file is: it is a separate module, not a separate prime.
* Also out of scope: injectivity of `ρ`, its determinant character `det ∘ ρ : G → ℤ_[ℓ]ˣ`, the
  comparison with the cyclotomic character, and any description of the image.
* ⚠️ **`ℓ ≥ 5` gains nothing from this file being generic.** Its hypothesis
  `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)` is gated at `ℓ ≥ 5` on `#E[ℓ^k]` alone.  ⚠️ This bullet used to say
  it was gated *"on `[ℓ]`-surjectivity and `#E[ℓ^k]`, both of which need the general coordinate
  formula `x(nP) = Φₙ/ΨSqₙ`, i.e. the `ωₙ` crux"*, and **all three clauses are wrong**:
  `[ℓ]`-surjectivity holds at every nonzero index (`nsmul_surjective_of_two_ne_zero`,
  `EllipticCurves.Torsion.TwoTorsionOrder`); the coordinate formula is proved at every index
  (`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`); and it is **not** the
  `ωₙ` crux — that is `#404`'s on-curve identity, closed in `EllipticCurves.Torsion.OmegaCrux`
  (PR #557), and `EllipticCurves.FunctionField.MulByNPullback` is the module that keeps the two
  apart.  ⚠️ **`#E[ℓ^k]` is no longer open at `ℓ ≥ 5`.**
  `card_torsion_pow_mul_self_of_odd` (`EllipticCurves.Torsion.PrimaryTowerOdd`) supplies it at every
  odd `ℓ` with `(ℓ : F) ≠ 0`, over `F̄` with `(2 : F) ≠ 0`, and discharges
  `EllipticCurves.Torsion.PrimaryTower`'s gate list — which this bullet used to cite as open — with
  it.  Instantiating this file at `ℓ ≥ 5` on top of that count is separate work and is not done
  here.  What being generic buys is that when the count is fed in, the
  `ℓ = 5` file is again a list of instantiations and no argument has to be written a third time.

## Using this file

The hypotheses of the instantiating files are on the *base-changed* curve `W'⁄F`, and
`WeierstrassCurve.baseChange` is a plain `def`, so `[(W'⁄F).IsElliptic]` is **not** found by bare
`inferInstance` even when `[W'.IsElliptic]` is available: `baseChange` does not unfold to `map`,
which is where Mathlib's instance lives. Use the incantation standard elsewhere in this
development:

```
haveI : (W'⁄F).IsElliptic := inferInstanceAs (W'.map (algebraMap S F)).IsElliptic
```

`Fact ℓ.Prime` is what `ℤ_[ℓ]` and `galoisRep ℓ` require. Mathlib supplies it globally at `2` and
at `3` (`Nat.fact_prime_two`, `Nat.fact_prime_three`).

## Main definitions

* `WeierstrassCurve.Affine.tateModule.tateModuleBasis` : the basis of `T_ℓE` indexed by `Fin 2`
  attached to a `ℤ_[ℓ]`-linear equivalence `T_ℓE ≃ₗ ℤ_[ℓ] × ℤ_[ℓ]`.
* `WeierstrassCurve.Affine.matrixAutEquiv` : `GL (Fin 2) ℤ_[ℓ] ≃* Aut_{ℤ_[ℓ]}(T_ℓE)`.
* `WeierstrassCurve.Affine.galoisRepMatrix` : the representation `G →* GL (Fin 2) ℤ_[ℓ]`.

## Main statements

* `WeierstrassCurve.Affine.tateModule.nonempty_basis_tateModule_of_nonempty` :
  `Nonempty (Basis (Fin 2) ℤ_[ℓ] T_ℓE)` from `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ] × ℤ_[ℓ])`.
* `WeierstrassCurve.Affine.galoisRepMatrix_mulVec`,
  `WeierstrassCurve.Affine.galoisRepMatrix_apply_coe`,
  `WeierstrassCurve.Affine.galoisRepMatrix_smul_basis_eq_sum` : how the matrix acts.
* `WeierstrassCurve.Affine.exists_galoisRepMatrix_of_nonempty` : a basis and a representation
  `G →* GL (Fin 2) ℤ_[ℓ]` computing the Galois action exist.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and VII.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

namespace tateModule

/-! ### A basis of `T_ℓE` indexed by `Fin 2` -/

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {ℓ : ℕ} [Fact ℓ.Prime]

/-- The basis of `T_ℓE` indexed by `Fin 2` attached to a `ℤ_[ℓ]`-linear equivalence
`T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ]`, such as the one `padicPairEquiv` builds from a coherent system of
generating pairs.

`Fin 2 → ℤ_[ℓ]` is preferred over `ℤ_[ℓ] × ℤ_[ℓ]` from here on: `Matrix`, `LinearMap.toMatrix` and
`GL` are all indexed by a `Fintype`, so it is cheaper to cross `finTwoArrow` once, here, than to
carry a `Prod` through every later statement. `Module.Free` alone would only give a basis indexed
by the opaque `Module.Free.ChooseBasisIndex`. -/
noncomputable def tateModuleBasis (e : W.tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ]) :
    Module.Basis (Fin 2) ℤ_[ℓ] (W.tateModule ℓ) :=
  Module.Basis.ofEquivFun (e.trans (LinearEquiv.finTwoArrow ℤ_[ℓ] ℤ_[ℓ]).symm)

/-- **`T_ℓE` has a basis indexed by `Fin 2` as soon as it is `ℤ_[ℓ]`-linearly `ℤ_[ℓ] × ℤ_[ℓ]`.**
The basis itself depends on the choice of equivalence; its existence does not.

⚠️ The hypothesis is the whole content and it is not free at any prime: it is
`nonempty_tateModuleEquivProd` at `ℓ = 2` and `nonempty_tateModuleEquivProd_three` at `ℓ = 3`, both
of which run the coherent-system construction of `EllipticCurves.TateModule.PrimaryFree`. At
`ℓ ≥ 5` nothing supplies it. -/
theorem nonempty_basis_tateModule_of_nonempty
    (h : Nonempty (W.tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) :
    Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] (W.tateModule ℓ)) :=
  h.map tateModuleBasis

end tateModule

/-! ### The matrix representation -/

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]

variable (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))

/-- The multiplicative equivalence `GL (Fin 2) ℤ_[ℓ] ≃* Aut_{ℤ_[ℓ]}(T_ℓE)` determined by a basis:
`Matrix.GeneralLinearGroup.toLin'` transports matrices to units of the endomorphism ring, and
`LinearMap.GeneralLinearGroup.generalLinearEquiv` reads those units as linear equivalences.

⚠️ Both Mathlib pieces are stated over an arbitrary `CommRing`, so neither carries a
`ℤ_[2]`-specific instance requirement. That was the one thing that could have forced this
extraction to be `ℓ = 2` only, and it does not. -/
noncomputable def matrixAutEquiv :
    GL (Fin 2) ℤ_[ℓ] ≃* ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] (W'⁄F).tateModule ℓ) :=
  (Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ_[ℓ] ((W'⁄F).tateModule ℓ))

/-- **The `ℓ`-adic Galois representation in matrix form**, `ρ_{E,ℓ} : G →* GL₂(ℤ_[ℓ])`, obtained by
reading `galoisRep ℓ` through a basis of `T_ℓE`.

Different bases give representations that differ by conjugation, so this depends on `b`; see
`exists_galoisRepMatrix_of_nonempty` for the choice-free existence statement. Continuity is not
asserted here — see the module docstring. -/
noncomputable def galoisRepMatrix : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[ℓ] :=
  (matrixAutEquiv b).symm.toMonoidHom.comp (galoisRep ℓ)

@[simp]
lemma matrixAutEquiv_galoisRepMatrix (σ : F ≃ₐ[S] F) :
    matrixAutEquiv b (galoisRepMatrix b σ) = galoisRep ℓ σ :=
  (matrixAutEquiv b).apply_symm_apply _

/-- **The matrix acts on coordinate vectors exactly as `σ` acts on `T_ℓE`.** This is the identity
that ties `galoisRepMatrix` back to `galoisRep`, and the form later computations use. -/
lemma galoisRepMatrix_mulVec (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule ℓ) :
    ⇑(b.repr (σ • f)) = (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) *ᵥ ⇑(b.repr f) := by
  have h : galoisRep ℓ σ f = Fintype.linearCombination ℤ_[ℓ] ⇑b
      ((galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) *ᵥ ⇑(b.repr f)) := by
    rw [← matrixAutEquiv_galoisRepMatrix b σ]
    exact Matrix.GeneralLinearGroup.toLin'_apply b (galoisRepMatrix b σ) f
  rw [galoisRep_apply_coe] at h
  rw [h, Fintype.linearCombination_apply, Module.Basis.repr_sum_self]

/-- **The entries of `ρ_{E,ℓ}(σ)`.** The `j`-th column is the coordinate vector of the Galois
translate of the `j`-th basis vector; equivalently, matrices here act on column vectors. -/
lemma galoisRepMatrix_apply_coe (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) i j = b.repr (σ • b j) i := by
  have h := congrFun (galoisRepMatrix_mulVec b σ (b j)) i
  rw [h]
  simp [Module.Basis.repr_self, Finsupp.single_eq_pi_single]

/-- **`σ` translates a basis vector into the corresponding column of its matrix.** The unbundled
reading of `galoisRepMatrix_apply_coe`.

⚠️ The `ℓ = 2` instance of this keeps its historical name `galois_smul_basis_eq_sum`; see the
module docstring's `## Naming` section for why the generic form is spelled with the head symbol
first. -/
lemma galoisRepMatrix_smul_basis_eq_sum (σ : F ≃ₐ[S] F) (j : Fin 2) :
    σ • b j = ∑ i, (galoisRepMatrix b σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) i j • b i := by
  conv_lhs => rw [← b.sum_repr (σ • b j)]
  exact Finset.sum_congr rfl fun i _ => by rw [galoisRepMatrix_apply_coe]

/-- **The `ℓ`-adic Galois representation exists**, as a matrix representation that really does
compute the Galois action: given `T_ℓE ≅ ℤ_[ℓ]²` there are a basis of `T_ℓE` and a homomorphism
`ρ : G →* GL₂(ℤ_[ℓ])` whose matrices act on coordinate vectors the way `G` acts on `T_ℓE`.

The compatibility clause is the point. `Nonempty ((F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[ℓ])` on its own
would be vacuous — the trivial homomorphism witnesses it, and the statement would not mention the
curve at all. Both the basis and `ρ` depend on a choice of coherent system of generating pairs, and
two choices give representations differing by conjugation.

⚠️ **Deletion test**, measured on this file as committed. Deleting the hypothesis `h` from the
statement and replacing its use in the proof by a hole leaves

```
error: don't know how to synthesize placeholder for argument `h`
context:
S : Type u_1
F : Type u_2
inst✝⁴ : Field S
inst✝³ : Field F
inst✝² : DecidableEq F
inst✝¹ : Algebra S F
W' : Affine S
ℓ : ℕ
inst✝ : Fact (Nat.Prime ℓ)
⊢ Nonempty (↥((W'⁄F).tateModule ℓ) ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])
```

⚠️ Two mechanical changes accompany the deletion and neither adds information: the use of `h`
becomes `?_` so that a hole is legal, and `ℓ` is pinned with `(ℓ := ℓ)`, without which the residual
is the unhelpful `typeclass instance problem is stuck / Fact (Nat.Prime ?m)` rather than a goal.

⚠️ The residual is a **goal** and not a type mismatch, and **nothing left in the context proves
it** — the deletion removes a hypothesis and the context has no replacement, which is the point.
It is exactly the rank-two input: with it gone there is no basis, hence no matrix, and the `GL₂`
shape cannot be produced at all. That is the sense in which this file supplies no representation of
any curve on its own. -/
theorem exists_galoisRepMatrix_of_nonempty
    (h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[ℓ]), ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule ℓ),
        ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) *ᵥ ⇑(b.repr f) := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_of_nonempty (W := W'⁄F) h
  exact ⟨b, galoisRepMatrix b, galoisRepMatrix_mulVec b⟩

end WeierstrassCurve.Affine
