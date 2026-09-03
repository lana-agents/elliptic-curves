/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.FreeThree
import EllipticCurves.TateModule.PrimaryMatrixRep

/-!
# `ρ_{E,3} : G → GL₂(ℤ_3)` : the `3`-adic representation in matrix form

For a Weierstrass curve `W'` over a field `S`, an algebraically closed extension `F / S` with
`(2 : F) ≠ 0` and `(3 : F) ≠ 0` for which `W'⁄F` is elliptic, and `G = F ≃ₐ[S] F`, the `3`-adic
Galois representation is a representation by invertible `2 × 2` matrices over `ℤ_[3]`:

```
galoisRepMatrixThree b : G →* GL (Fin 2) ℤ_[3].
```

This is the **second** prime at which the matrix form of `ρ_{E,ℓ}` is available in this
development, and the first odd one.

## What this file contains, and what it does not

The transport is in `EllipticCurves.TateModule.PrimaryMatrixRep`, stated for an arbitrary prime `ℓ`
in terms of one input: `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`. **This file supplies that input
at `ℓ = 3` and contains no argument.** The input is `nonempty_tateModuleEquivProd_three`
(`EllipticCurves.TateModule.FreeThree`, `#974`), and every proof below is one line.

⚠️ **Two hypotheses, not one.** Where the `ℓ = 2` file `EllipticCurves.TateModule.MatrixRep`
carries only `h2`, everything here carries both `h2` and `h3`, and the provenance is not
symmetric: `nsmul_three_surjective` needs **only** `(2 : F) ≠ 0`, so the coherent system's
*lifting* step is `h3`-free; `h3` enters exclusively through the counting theorem
`card_torsion_three_pow`, i.e. through `#E[3] = 9`. `EllipticCurves.TateModule.FreeThree`
documents that split for the module and this file inherits it unchanged rather than re-deriving it.

## Naming, and why there are `Three` twins of generic definitions here

⚠️ `EllipticCurves.TateModule.FreeThree` records the settled rule that a twin of an
already-generic definition is pure duplication, and declares no `padicPairEquivThree`. **The three
definitions below are a deliberate exception, and the reason is that their `ℓ = 2` twins already
exist and are consumed 100+ times.** `galoisRepMatrixTwo`, `matrixAutEquivTwo` and
`tateModuleBasisTwo` predate the extraction and cannot be removed; leaving `ℓ = 3` without the
matching spellings would put the two primes on different footings for every downstream file that
extends by pattern. ⚠️ The parenthetical this sentence used to carry — *"`MatrixRepBasisChange`,
`MatrixContinuity`, `Determinant`, `MatrixRepCompat` are all `ℓ = 2` only today"* — has since
gone false in all four of its entries: `Determinant`'s twin is
`EllipticCurves.TateModule.DeterminantThree`, `MatrixRepBasisChange`'s is
`EllipticCurves.TateModule.MatrixRepBasisChangeThree`, `MatrixContinuity`'s is
`EllipticCurves.TateModule.MatrixContinuityThree`, and `MatrixRepCompat`'s is
`EllipticCurves.TateModule.MatrixRepCompatThree` — all four over `ℓ`-generic files that import
this one. ⚠️ The clause that used to close this paragraph — *"`MatrixRepCompat` is the last of the
four still `ℓ = 2` only, and it is a separate follow-up"* — was true when it was written and is
now false: it **was** that follow-up.

Each `Three` definition is *definitionally* its generic form, so a consumer may use either
spelling and the generic lemmas apply to both. ⚠️ There is deliberately **no**
`galoisRepMatrixThree'` or second generic definition.

## Scope

* ⚠️ **This file consumes the multiplication-by-`n` coordinate formula `x(nP) = Φₙ/ΨSqₙ`**, at
  `n = 3`, through `EllipticCurves.Torsion.TriplingSurjective` and hence through
  `EllipticCurves.TateModule.FreeThree`. `EllipticCurves.TateModule.MatrixRep` says of the `ℓ = 2`
  route that it needs no such thing; **that sentence must not be read as applying here.** Ward's
  theorem and the elliptic-net recurrence remain unused at every `ℓ`.
* **Continuity is not asserted here**, and it is no longer missing at `ℓ = 3`.
  `continuous_galoisRepMatrixThree` is in `EllipticCurves.TateModule.MatrixContinuityThree`, over
  the `ℓ`-generic `EllipticCurves.TateModule.PrimaryMatrixContinuity`. ⚠️ **Two successive
  versions of this bullet were wrong and both are recorded rather than deleted.** The first gave
  the reason *"and it wants the profinite side, which is a different dependency"*:
  `EllipticCurves.TateModule.Profinite` is not a dependency of `MatrixContinuity` at all (it
  imports `Continuity`, `Determinant` and `MatrixRep`), and it is not `ℓ = 2` only either — its
  core is stated at an arbitrary `ℓ` with instantiated layers at `ℓ = 2` **and** `ℓ = 3`, five
  declarations each (`compactSpace_*`, `isCompact_coe_*`, `not_discreteTopology_tateModule_*`,
  `profiniteAddGrp*`, `coe_profiniteAddGrp*`). The second said *"all eighteen of its declarations
  have to be restated"*: ⚠️ **the number is seven.** Of `MatrixContinuity`'s eighteen, nine
  carried unsuffixed names and were generalised in place, two were already stated at an arbitrary
  prime `p` and are cited, and seven are the `Two`-suffixed statements that got twins.
  `EllipticCurves.TateModule.MatrixContinuity` records the split.
* **The basis-change conjugation law is not here.** ⚠️ Two clauses this bullet used to carry are
  false. The first, *"`galoisRepMatrixTwo_conj`
  (`EllipticCurves.TateModule.MatrixRepBasisChange`) is likewise still `ℓ = 2` only"*: the law is
  stated at an arbitrary prime in `EllipticCurves.TateModule.PrimaryMatrixRepBasisChange` and
  instantiated at `ℓ = 3` in `EllipticCurves.TateModule.MatrixRepBasisChangeThree`, which imports
  this file. The second, *"it is the next extraction after this one"*, was a prediction and it came
  true, so it is no longer a description of anything outstanding. ⚠️ The five conjugation
  statements are still not *here*, which is what this bullet is about, and the reason is unchanged:
  keeping this file to `MatrixRep.lean`'s nine names is what makes it reviewable.
* **`galoisDetThree` and `galoisTraceThree` are not here** either. ⚠️ The parenthetical this
  bullet used to carry — *"(`EllipticCurves.TateModule.Determinant`, still `ℓ = 2` only)"* — is
  false: they are stated, in `EllipticCurves.TateModule.DeterminantThree`, over the `ℓ`-generic
  invariants `EllipticCurves.TateModule.PrimaryDeterminant`. ⚠️ They are still not *here*, which is
  what this bullet is about, and the reason is unchanged: keeping this file to `MatrixRep.lean`'s
  nine names is what makes it reviewable. ⚠️ Note also that only *part* of that file needed this
  one — the definitions and `galoisTraceThree_one` needed nothing from it at all.
* ⚠️ **`det ρ_{E,3} = χ_3` `3`-adically is NOT unblocked by this file**, and `Determinant.lean`
  will look as though it just got closer. The `3`-adic identity needs the Weil pairing on `E[3^k]`
  for **every** `k`, i.e. the pairing at composite `n`. The **mod-`3`** identity is a different
  statement and landed separately as
  `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`. This rung supplies the matrices,
  not the pairing.
* **General odd `ℓ ≥ 5` stays out.** `EllipticCurves.TateModule.PrimaryMatrixRep` is already
  stated at an arbitrary prime, so the `ℓ = 5` file will again be a list of instantiations — but
  its input `Nonempty (T₅E ≃ₗ ℤ_[5]²)` is gated on `#E[5^k]`.  ⚠️ This bullet used to say it was
  gated *"on `[5]`-surjectivity and `#E[5^k]`, both of which need the general coordinate formula,
  i.e. the `ωₙ` crux"*, and all three clauses are wrong: `[5]`-surjectivity holds at every nonzero
  index (`nsmul_surjective_of_two_ne_zero`, `EllipticCurves.Torsion.TwoTorsionOrder`); the
  coordinate formula is proved at every index (`hasXCoordFormula_of_two_ne_zero`,
  `EllipticCurves.Torsion.NsmulOrder`); and it is **not** the `ωₙ` crux, which is `#404`'s on-curve
  identity, closed in `EllipticCurves.Torsion.OmegaCrux` (PR #557).
  ⚠️ **`#E[ℓ^k]` is not open at any prime `ℓ` with `(ℓ : F) ≠ 0`, and this file's generic sibling
  is now instantiated there.** The sharp count is `card_torsion_eq_sq`
  (`EllipticCurves.Torsion.StructureGeneral`, `#293`): every `n` with `(2 : F) ≠ 0` and
  `(n : F) ≠ 0`, `ℓ = 2` included, so it is sharper than the odd-`ℓ` attribution this bullet used to
  carry.  ⚠️ **`(2 : F) ≠ 0` is the second hypothesis and this bullet used to name only the index
  one** (`#1137`); it is a hypothesis of the count and of all 22 `_of_natCast_ne_zero` statements
  in the `TateModule/` directory, so none of them reaches characteristic `2`.  ⚠️ **Two entry
  points, not one, and this sentence used to say `built on it` of all 22**: eighteen take `h2`
  through the count, and the four in `EllipticCurves.TateModule.OpenKernel` and
  `EllipticCurves.TateModule.OpenKernelGeneral` take it through `finite_torsion_of_intCast_ne_zero`
  (`EllipticCurves.Torsion.XSupport`) instead — `EllipticCurves.Torsion.StructureGeneral` is not in
  `OpenKernel`'s import closure at all.
  `nonempty_tateModuleEquivProd_of_natCast_ne_zero` (`EllipticCurves.TateModule.FreeGeneral`,
  `#268`) turns that count into the rank-two input the generic layer takes as an argument, and
  **`EllipticCurves.TateModule.MatrixRepGeneral` supplies it at every prime `ℓ` with
  `(2 : F) ≠ 0` and `(ℓ : F) ≠ 0`** — so *"separate work and is not done here"* is discharged rather
  than owed. ⚠️
  `(ℓ : F) ≠ 0` is sharp: at `ℓ = char F` the conclusion is **false**, not open — `E[ℓ]` is `0` or
  `ℤ/ℓℤ`, so `T_ℓE` has rank `0` or `1`.

## Main definitions

* `WeierstrassCurve.Affine.tateModule.tateModuleBasisThree` : the basis of `T₃E` indexed by
  `Fin 2` attached to a `ℤ_[3]`-linear equivalence `T₃E ≃ₗ ℤ_[3] × ℤ_[3]`.
* `WeierstrassCurve.Affine.matrixAutEquivThree` : `GL (Fin 2) ℤ_[3] ≃* Aut_{ℤ_[3]}(T₃E)`.
* `WeierstrassCurve.Affine.galoisRepMatrixThree` : the representation `G →* GL (Fin 2) ℤ_[3]`.

## Main statements

* `WeierstrassCurve.Affine.tateModule.nonempty_basis_tateModule_three` :
  `Nonempty (Basis (Fin 2) ℤ_[3] T₃E)`.
* `WeierstrassCurve.Affine.galoisRepMatrixThree_mulVec`,
  `WeierstrassCurve.Affine.galoisRepMatrixThree_apply_coe` : how the matrix acts.
* `WeierstrassCurve.Affine.exists_galoisRepMatrixThree` : a basis and a representation
  `G →* GL (Fin 2) ℤ_[3]` computing the Galois action exist.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7 and VII.7.
-/

open Matrix

namespace WeierstrassCurve.Affine

namespace tateModule

/-! ### A basis of `T₃E` indexed by `Fin 2` -/

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-- The basis of `T₃E` indexed by `Fin 2` attached to a `ℤ_[3]`-linear equivalence
`T₃E ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3]`. Definitionally `tateModuleBasis` at `ℓ = 3`. -/
noncomputable def tateModuleBasisThree (e : W.tateModule 3 ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3]) :
    Module.Basis (Fin 2) ℤ_[3] (W.tateModule 3) :=
  tateModuleBasis e

/-- **`T₃E` has a basis indexed by `Fin 2`.** The basis itself depends on a choice of coherent
system of generating pairs of the `E[3^k]`; its existence does not.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(nonempty_tateModuleEquivProd_three h2 h3)` by a hole — `by refine
nonempty_basis_tateModule_of_nonempty (W := W) (ℓ := 3) ?_` — leaves

```
error: unsolved goals
F : Type u_1
inst✝³ : Field F
inst✝² : DecidableEq F
W : Affine F
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W
h2 : 2 ≠ 0
h3 : 3 ≠ 0
⊢ Nonempty (↥(W.tateModule 3) ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3])
```

⚠️ Two mechanical changes accompany the deletion and neither adds information: term mode becomes
`by refine … ?_` so a hole is legal, and `W` and `ℓ` are pinned, which the term-mode form infers
from the expected type. `h2` and `h3` both **survive** in the context, so what is removed is a
construction and not a hypothesis, and the residual is a **goal**, which no type mismatch could
produce. It is exactly `#974`'s theorem — the rank-two input, which is where the whole cost of
`ℓ = 3` sits. -/
theorem nonempty_basis_tateModule_three [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) ℤ_[3] (W.tateModule 3)) :=
  nonempty_basis_tateModule_of_nonempty (nonempty_tateModuleEquivProd_three h2 h3)

end tateModule

/-! ### The matrix representation at `ℓ = 3` -/

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

variable (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))

/-- The multiplicative equivalence `GL (Fin 2) ℤ_[3] ≃* Aut_{ℤ_[3]}(T₃E)` determined by a basis.
Definitionally `matrixAutEquiv` at `ℓ = 3`. -/
noncomputable def matrixAutEquivThree :
    GL (Fin 2) ℤ_[3] ≃* ((W'⁄F).tateModule 3 ≃ₗ[ℤ_[3]] (W'⁄F).tateModule 3) :=
  matrixAutEquiv b

/-- **The `3`-adic Galois representation in matrix form**, `ρ_{E,3} : G →* GL₂(ℤ_[3])`, obtained by
reading `galoisRep 3` through a basis of `T₃E`. Definitionally `galoisRepMatrix` at `ℓ = 3`.

⚠️ This is the declaration whose absence `EllipticCurves.TateModule.MatrixRep` and
`EllipticCurves.TateModule.MatrixRepBasisChange` each named, in their own words, as the only thing
missing at `ℓ = 3` after `#974`. ⚠️ The sentence that used to follow — *"Nothing else about those
files changes: continuity and the conjugation law are still stated at `ℓ = 2` only"* — is now false
in both halves: continuity is stated at `ℓ = 3` in
`EllipticCurves.TateModule.MatrixContinuityThree`, and the conjugation law is stated at every prime
(`EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`) and at `ℓ = 3`
(`EllipticCurves.TateModule.MatrixRepBasisChangeThree`). All three of those files consume this
declaration. -/
noncomputable def galoisRepMatrixThree : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[3] :=
  galoisRepMatrix b

@[simp]
lemma matrixAutEquivThree_galoisRepMatrixThree (σ : F ≃ₐ[S] F) :
    matrixAutEquivThree b (galoisRepMatrixThree b σ) = galoisRep 3 σ :=
  matrixAutEquiv_galoisRepMatrix b σ

/-- **The matrix acts on coordinate vectors exactly as `σ` acts on `T₃E`.** This is the identity
that ties `galoisRepMatrixThree` back to `galoisRep`. -/
lemma galoisRepMatrixThree_mulVec (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 3) :
    ⇑(b.repr (σ • f))
      = (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) *ᵥ ⇑(b.repr f) :=
  galoisRepMatrix_mulVec b σ f

/-- **The entries of `ρ_{E,3}(σ)`.** The `j`-th column is the coordinate vector of the Galois
translate of the `j`-th basis vector. -/
lemma galoisRepMatrixThree_apply_coe (σ : F ≃ₐ[S] F) (i j : Fin 2) :
    (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) i j = b.repr (σ • b j) i :=
  galoisRepMatrix_apply_coe b σ i j

/-- **`σ` translates a basis vector into the corresponding column of its matrix**, at `ℓ = 3`. -/
lemma galoisRepMatrixThree_smul_basis_eq_sum (σ : F ≃ₐ[S] F) (j : Fin 2) :
    σ • b j = ∑ i, (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) i j • b i :=
  galoisRepMatrix_smul_basis_eq_sum b σ j

/-- **The `3`-adic Galois representation exists**, as a matrix representation that really does
compute the Galois action: there are a basis of `T₃E` and a homomorphism `ρ : G →* GL₂(ℤ_[3])`
whose matrices act on coordinate vectors the way `G` acts on `T₃E`.

The compatibility clause is the point. `Nonempty ((F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[3])` on its own
would be vacuous — the trivial homomorphism witnesses it, and the statement would not mention the
curve at all.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(nonempty_tateModuleEquivProd_three h2 h3)` by a hole — `by refine
exists_galoisRepMatrix_of_nonempty (W' := W') (F := F) (ℓ := 3) ?_` — leaves

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
h3 : 3 ≠ 0
⊢ Nonempty (↥((W'⁄F).tateModule 3) ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3])
```

⚠️ `h2` and `h3` both **survive**, so the deletion removes a construction and not a hypothesis, and
the residual is a **goal** rather than a type mismatch. It is `T₃E ≅ ℤ₃²` itself, which is the
whole content of the `ℓ = 3` case: at `ℓ ≥ 5` this is precisely the goal nothing can discharge. -/
theorem exists_galoisRepMatrixThree [IsAlgClosed F] [(W'⁄F).IsElliptic] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[3]), ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 3),
        ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) *ᵥ ⇑(b.repr f) :=
  exists_galoisRepMatrix_of_nonempty (tateModule.nonempty_tateModuleEquivProd_three h2 h3)

/-! ### Non-vacuity

⚠️ `exists_galoisRepMatrixThree` is an **existential**, so it is the vacuity-prone kind, and the
compatibility clause is what stops it from being witnessed by the trivial homomorphism. What
remains to certify is that its hypotheses are simultaneously satisfiable on a curve that exists.

`[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` all hold for
`y² + y = x³` over `ℚ` base-changed to an algebraic closure of `ℚ`, with **`S = ℚ`** so that
`Gal(F/S)` is not the trivial group — this front's standard `n = 3` certificate curve, the same one
`EllipticCurves.TateModule.FreeThree` and `EllipticCurves.TateModule.DeterminantMod` use.
-/

section Nonvacuity

/-! The certificate curve `y² + y = x³` over `ℚ` and its base — algebraically closed so that
`Gal(F/ℚ)` is not the trivial group, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — are the
shared `EllipticCurves.Fixture.y2AddYEqX3` and `EllipticCurves.Fixture.AlgClosedQ`, which also
supply `(y2AddYEqX3 ℚ).IsElliptic` from a single `[CharZero F]` instance. The **base-changed**
`((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic` comes from the same module, via
`EllipticCurves.Fixture.instIsEllipticBaseChange`; this block declares no fixture of its own
(`#1408`). -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, `ρ_{E,3}` really is a `GL₂(ℤ_[3])`-valued representation that
computes the Galois action.

⚠️ The statement is restated in full rather than obtained-and-projected (`#916`), and the
compatibility clause `⇑(b.repr (σ • f)) = ρ σ *ᵥ ⇑(b.repr f)` is kept — without it the certificate
would be witnessed by the trivial homomorphism and would not mention the curve. -/
example : ∃ (b : Module.Basis (Fin 2) ℤ_[3] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3))
    (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) ℤ_[3]),
      ∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
        (f : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3),
        ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) *ᵥ ⇑(b.repr f) :=
  exists_galoisRepMatrixThree exampleTwo exampleThree

open Classical in
/-- **The module the matrices act on is not the zero module**, on the same curve, by a route that
never mentions the matrix representation: `T₃E` surjects onto `E[3^k]`, which has `9^k` elements.

⚠️ This is what rules out the degenerate reading of the certificate above. `GL (Fin 2) ℤ_[3]` and
the `mulVec` clause are both perfectly satisfiable over a zero module — every coordinate vector
would be `0` and the equation would hold for any `ρ` — so the certificate needs this. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3) :=
  tateModule.infinite_tateModule_three exampleTwo exampleThree

end Nonvacuity

end WeierstrassCurve.Affine
