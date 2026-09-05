/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.DeterminantThree
import EllipticCurves.TateModule.PrimaryMatrixContinuity

/-!
# `ρ_{E,3} : G → GL₂(ℤ_[3])` is continuous for the `3`-adic topology

For a Weierstrass curve `W'` over a field `S`, an algebraically closed extension `F / S` integral
over `S` with `(2 : F) ≠ 0` and `(3 : F) ≠ 0` for which `W'⁄F` is elliptic, and `G = F ≃ₐ[S] F`,
the `3`-adic Galois representation is continuous as a map into `GL₂(ℤ_[3])` with its `3`-adic
topology:

```
continuous_galoisRepMatrixThree : Continuous (galoisRepMatrixThree b).
```

This is the **second** prime at which continuity into `GL₂` is available in this development, and
the first odd one.

## What this file contains, and what it does not

The argument is in `EllipticCurves.TateModule.PrimaryMatrixContinuity`, stated for an arbitrary
prime `ℓ`. **This file supplies its one input at `ℓ = 3` and contains no argument**: every proof
below is one line. The input is `nonempty_tateModuleEquivProd_three`
(`EllipticCurves.TateModule.FreeThree`, `#974`), and it is needed only by the three basis-free
statements — the four that are handed a basis need nothing at all.

⚠️ **Two hypotheses, not one.** Where the `ℓ = 2` file `EllipticCurves.TateModule.MatrixContinuity`
carries only `h2`, the basis-free statements here carry both `h2` and `h3`, and the provenance is
not symmetric: `nsmul_three_surjective` needs **only** `(2 : F) ≠ 0`, so the coherent system's
*lifting* step is `h3`-free; `h3` enters exclusively through the counting theorem
`card_torsion_three_pow`, i.e. through `#E[3] = 9`. `EllipticCurves.TateModule.FreeThree`
documents that split and this file inherits it unchanged rather than re-deriving it.

## ⚠️ Seven declarations, not eighteen and not sixteen

⚠️ **Two sentences on `main` priced this file at eighteen** —
`EllipticCurves.TateModule.MatrixContinuity`'s own Scope paragraph and
`EllipticCurves.TateModule.MatrixRepThree`'s Continuity bullet, both repaired by this change — and
a third count, in `#1013`, cut it to sixteen. ⚠️ **The number that matters is seven.**
`EllipticCurves.TateModule.MatrixContinuity` had eighteen declarations, and they split three
ways:

* **nine** — the coordinate homeomorphism `T_ℓE ≃ₜ ℤ_[ℓ]²` and its corollaries — carried
  **unsuffixed** names in the `tateModule` namespace, so an `ℓ = 3` twin would be a name collision
  rather than a duplication. They were generalised in place and now live at the same full names in
  `EllipticCurves.TateModule.PrimaryMatrixContinuity`. ⚠️ **This file restates none of them, and
  there is deliberately no `coordHomeomorphThree`**: `coordHomeomorph b` for a basis `b` of `T₃E`
  already *is* the `ℓ = 3` statement.
* **two** — `PadicInt.not_discreteTopology` and
  `Matrix.GeneralLinearGroup.not_discreteTopology_padicInt` — were written at an arbitrary prime
  `p` from the start. ⚠️ **Cited here, in the `Non-vacuity` section, not duplicated.**
* **seven** — the `Two`-suffixed statements. These are what this file twins.

> ⚠️ **A declaration count is not a work estimate, and neither is a `variable`-block audit.** The
> first correction came from reading `variable` blocks (18 → 16); it still took reading the
> declaration *names* to see that nine more were unsuffixed and could not be twinned at all.

## Naming, and why there are `Three` twins of generic statements here

⚠️ The rule `EllipticCurves.TateModule.MatrixRepThree` records applies verbatim: a twin of an
already-generic declaration is normally pure duplication, and the seven below are the same
deliberate exception. Their `ℓ = 2` twins `continuous_galoisRepMatrixTwo`,
`continuous_galoisDetTwo` and the rest predate the extraction and cannot be removed; leaving
`ℓ = 3` without the matching spellings would put the two primes on different footings for every
downstream file that extends by pattern. ⚠️ The nine unsuffixed declarations are the *other* side
of that rule and get no twin at all — see above.

Each statement below is *definitionally* its generic form applied at `ℓ = 3`, through the
definitional identities `galoisRepMatrixThree b = galoisRepMatrix b`,
`galoisDetThree = galoisDet (ℓ := 3)` and `galoisTraceThree = galoisTrace (ℓ := 3)` of
`EllipticCurves.TateModule.MatrixRepThree` and `EllipticCurves.TateModule.DeterminantThree`.

## Non-degeneracy

⚠️ **`Continuous ρ` into a discrete codomain is free.** That is exactly the situation of
`continuous_galoisRepMod`, where `E[n]` is discrete and continuity is only levelwise local
constancy; it is *not* the situation here, and
`Matrix.GeneralLinearGroup.not_discreteTopology_padicInt 3` is the certificate, cited in the
`Non-vacuity` section below. ⚠️ It is also why `exists_continuous_galoisRepMatrixThree` keeps the
compatibility clause `⇑(b.repr (σ • f)) = ↑(ρ σ) *ᵥ ⇑(b.repr f)`: `∃ ρ, Continuous ρ` alone is
witnessed by the trivial homomorphism and mentions neither the curve nor its Tate module.

On the source side the corresponding statement is `tateModule.not_discreteTopology_tateModule_three`
(`EllipticCurves.TateModule.Profinite`), and the certificate below is the stronger
`Infinite (T₃E)`, by a route that never mentions matrices.

## Scope

* ⚠️ **This file consumes the multiplication-by-`n` coordinate formula `x(nP) = Φₙ/ΨSqₙ`**, at
  `n = 3`, through `EllipticCurves.Torsion.TriplingSurjective` and hence through
  `EllipticCurves.TateModule.FreeThree`. `EllipticCurves.TateModule.MatrixContinuity` says of the
  `ℓ = 2` route that it needs no such thing; **that sentence must not be read as applying here.**
* ⚠️ **`det ρ_{E,3} = χ_3` `3`-adically is NOT unblocked by this file**, and a module called
  `MatrixContinuityThree` landing will look like progress towards it. The `3`-adic identity needs
  the Weil pairing on `E[3^k]` for **every** `k`, i.e. the pairing at composite `n`; this
  development has the pairing at `n = 2` and `n = 3` only. The **mod-`3`** identity
  `galoisDetMod 3 = χ_3` is a *different statement about a different object* — valued in
  `(ZMod 3)ˣ`, not `ℤ_[3]ˣ` — and it landed separately as
  `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`. Continuity of a character says
  nothing about which character it is.
* **The image is not here.** ⚠️ **The clause this bullet used to carry is doubly out of date** —
  it read *"`EllipticCurves.TateModule.Image` and `EllipticCurves.TateModule.ImageProfinite` are
  `ℓ = 2` only **because their input `continuous_galoisRepMatrixTwo` is**; this file removes that
  reason and so unblocks them"*. It did, and the follow-up it predicted has now landed for **both**
  of them: `EllipticCurves.TateModule.ImageThree`, over the `ℓ`-generic
  `EllipticCurves.TateModule.PrimaryImage`, and
  `EllipticCurves.TateModule.ImageProfiniteThree`, over the `ℓ`-generic
  `EllipticCurves.TateModule.PrimaryImageProfinite`. ⚠️ A second clause of this bullet has
  therefore expired in its turn: it read *"`EllipticCurves.TateModule.ImageProfinite` is still
  `ℓ = 2` only and still ungated"*, and it was true of exactly one file until that file was
  extracted.
* **The basis-change conjugation law is not here**, and it is not missing at `ℓ = 3` either:
  `galoisRepMatrixThree_conj` is in `EllipticCurves.TateModule.MatrixRepBasisChangeThree`, over the
  `ℓ`-generic `EllipticCurves.TateModule.PrimaryMatrixRepBasisChange`. ⚠️ It is a different file,
  it consumes nothing from this one and this one consumes nothing from it — the conjugation law is
  about two bases and says nothing about any topology.
* **General odd `ℓ ≥ 5` stays out.** `EllipticCurves.TateModule.PrimaryMatrixContinuity` is already
  stated at an arbitrary prime, so the `ℓ = 5` file will again be a list of instantiations — but
  its input `Nonempty (T₅E ≃ₗ ℤ_[5]²)` is gated on `#E[5^k]`.  ⚠️ This bullet used to say it was
  gated *"on `[5]`-surjectivity and `#E[5^k]`, both of which need the general coordinate formula,
  i.e. the `ωₙ` crux"*, and all three clauses are wrong: `[5]`-surjectivity holds at every nonzero
  index with `(2 : F) ≠ 0` (`nsmul_surjective_of_two_ne_zero`,
  `EllipticCurves.Torsion.TwoTorsionOrder`); the coordinate formula is proved at every index with
  `(2 : F) ≠ 0` (`hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`); and it is
  **not** the `ωₙ` crux, which is `#404`'s on-curve identity, closed in
  `EllipticCurves.Torsion.OmegaCrux` (PR #557).  ⚠️ **`#E[ℓ^k]` is not open at any prime `ℓ` with
  `(ℓ : F) ≠ 0`, and this file's generic sibling is now instantiated there.** The sharp count is
  `card_torsion_eq_sq` (`EllipticCurves.Torsion.StructureGeneral`, `#293`): every `n` with
  `(2 : F) ≠ 0` and `(n : F) ≠ 0`, `ℓ = 2` included, so it is sharper than the odd-`ℓ` attribution
  this bullet used to carry.  ⚠️ **`(2 : F) ≠ 0` is the second hypothesis and this bullet used to
  name only the index one** (`#1137`); it is a hypothesis of the count and of all 22
  `_of_natCast_ne_zero` statements in the `TateModule/` directory, so none of them reaches
  characteristic `2`.  ⚠️ **Two entry points, not one, and this sentence used to say `built on it`
  of all 22**: eighteen take `h2` through the count, and the four in
  `EllipticCurves.TateModule.OpenKernel` and `EllipticCurves.TateModule.OpenKernelGeneral` take it
  through `finite_torsion_of_intCast_ne_zero` (`EllipticCurves.Torsion.XSupport`) instead —
  `EllipticCurves.Torsion.StructureGeneral` is not in `OpenKernel`'s import closure at all.
  `nonempty_tateModuleEquivProd_of_natCast_ne_zero` (`EllipticCurves.TateModule.FreeGeneral`,
  `#268`) turns that count into the rank-two input the generic layer takes as an argument, and
  **`EllipticCurves.TateModule.MatrixContinuityGeneral` supplies it at every prime `ℓ` with
  `(2 : F) ≠ 0` and `(ℓ : F) ≠ 0`** — so *"separate work and is not done here"* is discharged rather
  than owed.  ⚠️ The clause that followed — *"`ℓ ≥ 5` gains the generic file and nothing else"* —
  was the right diagnosis, and it is what has been answered: what was missing was a basis to feed
  the generic file, not a theorem in it.  ⚠️ `(ℓ : F) ≠ 0` is sharp: at `ℓ = char F` the conclusion
  is **false**, not open — `E[ℓ]` is `0` or `ℤ/ℓℤ`, so `T_ℓE` has rank `0` or `1`.

## Using this file

`[Algebra.IsIntegral S F]` is carried throughout, as in the `ℓ = 2` file: every statement goes
through `tateModule.continuous_galois_smul`, which needs it. ⚠️ The nine coordinate-homeomorphism
declarations in `EllipticCurves.TateModule.PrimaryMatrixContinuity` do **not** need it, so a
consumer that only wants `T₃E ≃ₜ ℤ_[3]²` should reach for that file directly rather than for this
one.

## Main statements

* `WeierstrassCurve.Affine.continuous_galoisRepMatrixThree` : `ρ_{E,3} : G →* GL₂(ℤ_[3])` is
  continuous.
* `WeierstrassCurve.Affine.continuous_galoisDetThree`,
  `WeierstrassCurve.Affine.continuous_galoisTraceThree` : the invariants are continuous.
* `WeierstrassCurve.Affine.exists_continuous_galoisRepMatrixThree` : the choice-free capstone.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}

/-! ### Continuity of the matrix representation at `ℓ = 3` -/

variable [Algebra.IsIntegral S F]
variable (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))

/-- **The matrix of `ρ_{E,3}(σ)` depends continuously on `σ`.** Entrywise: `(ρ σ) i j =
b.repr (σ • b j) i` is the composite of the continuous orbit map `σ ↦ σ • b j` with the continuous
coordinate function `tateModule.continuous_repr_apply`. Definitionally
`continuous_galoisRepMatrix_coe` at `ℓ = 3`. -/
theorem continuous_galoisRepMatrixThree_coe :
    Continuous fun σ : F ≃ₐ[S] F =>
      (galoisRepMatrixThree b σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) :=
  continuous_galoisRepMatrix_coe b

/-- **`ρ_{E,3} : G →* GL₂(ℤ_[3])` is continuous**, for the Krull topology on `G` and the `3`-adic
topology on `GL₂(ℤ_[3])`.

⚠️ This is the declaration whose absence `EllipticCurves.TateModule.MatrixRepThree`,
`EllipticCurves.TateModule.DeterminantThree` and `EllipticCurves.TateModule.MatrixContinuity` each
named, in their own words, as missing at `ℓ = 3` after `#994`. ⚠️ It was **not** the only thing
missing: the first two of those files also name the basis-change conjugation law
`galoisRepMatrixTwo_conj` (`EllipticCurves.TateModule.MatrixRepBasisChange`), which is a different
file and a different follow-up. That one has since been paid as well —
`galoisRepMatrixThree_conj`, `EllipticCurves.TateModule.MatrixRepBasisChangeThree` — so of the
apparatus those files listed, nothing is still `ℓ = 2` only. ⚠️ The clause that used to end that
sentence — *"only `EllipticCurves.TateModule.MatrixRepCompat` is still `ℓ = 2` only"* — was true
when it was written; `EllipticCurves.TateModule.MatrixRepCompatThree`, over the `ℓ`-generic
`EllipticCurves.TateModule.PrimaryMatrixRepCompat`, has since retired it. ⚠️ **The scope of the
sentence is load-bearing and must stay**: it is a claim about the apparatus *those three files
listed*, and the image (`EllipticCurves.TateModule.Image`,
`EllipticCurves.TateModule.ImageProfinite`) was never in any of their lists. Whatever is true of
the image is tracked by this file's own Scope bullet above, not here. -/
theorem continuous_galoisRepMatrixThree : Continuous (galoisRepMatrixThree b) :=
  continuous_galoisRepMatrix b

/-! ### The invariants are continuous -/

/-- **The determinant character `det ρ_{E,3} : G →* ℤ_[3]ˣ` is continuous.**

`galoisDetThree` is basis-free, but its continuity is proved through a basis, which is why one is
taken as an argument; `continuous_galoisDetThree` removes it.

⚠️ This carries neither `[IsAlgClosed F]` nor `[(W'⁄F).IsElliptic]`, and the omission is measured
rather than hopeful: it is a statement about a basis you were *handed*, so it does not care where
the basis came from. `EllipticCurves.TateModule.DeterminantThree`'s `coe_galoisDetThree` sits
outside its `Nondegenerate` section for the same reason. -/
theorem continuous_galoisDetThree_of_basis
    (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3)) :
    Continuous (galoisDetThree (W' := W') (F := F)) :=
  continuous_galoisDet_of_basis b

/-- **The trace `tr ρ_{E,3} : G → ℤ_[3]` is continuous.** Unlike the determinant this is not a
homomorphism, so there is no unit-topology bookkeeping: it is the matrix trace of a continuously
varying matrix. -/
theorem continuous_galoisTraceThree_of_basis
    (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3)) :
    Continuous (galoisTraceThree (W' := W') (F := F)) :=
  continuous_galoisTrace_of_basis b

/-! ### The unconditional `ℓ = 3` layer and the capstone -/

section Nondegenerate

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- `det ρ_{E,3}` is continuous, with no basis supplied: over an algebraically closed field in
which `2` and `3` are invertible a basis of `T₃E` exists
(`nonempty_tateModuleEquivProd_three`), and continuity is a `Prop`, so the choice can be
discharged. -/
theorem continuous_galoisDetThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Continuous (galoisDetThree (W' := W') (F := F)) :=
  continuous_galoisDet_of_nonempty (tateModule.nonempty_tateModuleEquivProd_three h2 h3)

/-- `tr ρ_{E,3}` is continuous, with no basis supplied. -/
theorem continuous_galoisTraceThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Continuous (galoisTraceThree (W' := W') (F := F)) :=
  continuous_galoisTrace_of_nonempty (tateModule.nonempty_tateModuleEquivProd_three h2 h3)

/-- **`ρ_{E,3}` is a continuous `3`-adic matrix representation.**

The continuous refinement of `exists_galoisRepMatrixThree`: there are a basis of `T₃E` and a
**continuous** homomorphism `ρ : G →* GL₂(ℤ_[3])` whose matrices compute the Galois action on
coordinate vectors.

The compatibility clause is load-bearing. `∃ ρ, Continuous ρ` alone is witnessed by the trivial
homomorphism and would mention neither the curve nor its Tate module.

⚠️ **Deletion test**, measured on this file as committed. Replacing the argument
`(tateModule.nonempty_tateModuleEquivProd_three h2 h3)` by a hole — `by refine
exists_continuous_galoisRepMatrix_of_nonempty (W' := W') (F := F) (ℓ := 3) ?_` — leaves,
copy-paste:

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁶ : Field S
inst✝⁵ : Field F
inst✝⁴ : DecidableEq F
inst✝³ : Algebra S F
W' : Affine S
inst✝² : Algebra.IsIntegral S F
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
h3 : 3 ≠ 0
⊢ Nonempty (↥((W'⁄F).tateModule 3) ≃ₗ[ℤ_[3]] ℤ_[3] × ℤ_[3])
```

⚠️ `h2` and `h3` both **survive** in the context, so what the deletion removes is a construction and
not a hypothesis, and the residual is a **goal**, which no type mismatch could produce. It is
`#974`'s theorem — the rank-two input, and the only *mathematical* input at `ℓ = 3` that costs
anything; ⚠️ `exampleIsIntegral` below is a second thing that cost something, but it is an
instance-search workaround for one certificate, not an input to any theorem. ⚠️
There is **no knock-on**: nothing below this declaration consumes it except the `Non-vacuity`
certificate, which is an `example` and closes by application. -/
theorem exists_continuous_galoisRepMatrixThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))
      (ρ : (F ≃ₐ[S] F) →* GL (Fin 2) ℤ_[3]), Continuous ρ ∧
        ∀ (σ : F ≃ₐ[S] F) (f : (W'⁄F).tateModule 3),
          ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) *ᵥ ⇑(b.repr f) :=
  exists_continuous_galoisRepMatrix_of_nonempty
    (tateModule.nonempty_tateModuleEquivProd_three h2 h3)

end Nondegenerate

/-! ### Non-vacuity

⚠️ Three risks, three certificates, following the idiom
`EllipticCurves.TateModule.MatrixRepThree` introduced and
`EllipticCurves.TateModule.DeterminantThree` extended.

1. **The statement is not trivially satisfiable.** ⚠️ `Continuous ρ` into a **discrete** codomain
   is free, which is the whole reason the two non-discreteness theorems of
   `EllipticCurves.TateModule.PrimaryMatrixContinuity` exist. They are stated at an arbitrary prime
   `p`, so `ℓ = 3` is covered **by citation** and the first certificate below is that citation.
2. **The hypothesis class is inhabited.** `[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]`,
   `[Algebra.IsIntegral S F]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` all hold simultaneously for
   `y² + y = x³` over `ℚ` base-changed to `AlgebraicClosure ℚ`, with **`S = ℚ`** so that
   `Gal(F/S)` is not the trivial group — this front's standard `n = 3` certificate curve. The
   second certificate closes **by application** of `exists_continuous_galoisRepMatrixThree`, not by
   `rfl`, `decide` or `norm_num`, so it consumes the theorem it certifies (`#944`).
3. **The target is not degenerate.** `GL (Fin 2) ℤ_[3]` and the `mulVec` clause are both
   satisfiable over a zero module — every coordinate vector would be `0` — so the third
   certificate says `T₃E` is infinite, by a route that never mentions matrices or continuity.

⚠️ **`open Classical in` is load-bearing on the last two certificates and is not optional.** The
`TateModule` family carries `[DecidableEq F]` in its `variable` blocks, but `AlgClosedQ` is
`AlgebraicClosure ℚ`, which has no decidable equality, so the section variable cannot supply one
and the block does not elaborate without it. The failure mode is a
`failed to synthesize instance of type class DecidableEq AlgClosedQ` reported at the `example`,
several lines from the `AlgClosedQ` fixture that causes it.

⚠️ Every `TateModule` certificate block now names the one shared fixture
`EllipticCurves.Fixture.y2AddYEqX3`; the `private` per-file copies this note used to describe are
gone.
-/

section Nonvacuity

/-- **⚠️ THE CERTIFICATE THAT THE STATEMENT IS NOT FREE**: `GL₂(ℤ_[3])` is not a discrete space, so
`continuous_galoisRepMatrixThree` is a constraint on `ρ_{E,3}` rather than a formality.

⚠️ This is a **citation**, not a restatement: the theorem is stated at an arbitrary prime `p` in
`EllipticCurves.TateModule.PrimaryMatrixContinuity` and needs no `ℓ = 3` twin. -/
example : ¬ DiscreteTopology (GL (Fin 2) ℤ_[3]) :=
  Matrix.GeneralLinearGroup.not_discreteTopology_padicInt 3

/-! The certificate curve `y² + y = x³` over `ℚ` and its base — algebraically closed so that
`Gal(F/ℚ)` is not the trivial group, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — are the
shared `EllipticCurves.Fixture.y2AddYEqX3` and `EllipticCurves.Fixture.AlgClosedQ`, which also
supply `(y2AddYEqX3 ℚ).IsElliptic` from a single `[CharZero F]` instance. The **base-changed**
`((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic` comes from the same module, via
`EllipticCurves.Fixture.instIsEllipticBaseChange`; this block declares no fixture of its own
(`#1408`). -/

open EllipticCurves.Fixture

/-- ⚠️ **The `ℚ`-algebra instance trap**, documented in `EllipticCurves.TateModule.Continuity` and
hit for the first time on this front here: `Algebra.IsIntegral ℚ (AlgebraicClosure ℚ)` is **not**
found by bare instance search in a file with this import closure, because
`DivisionRing.toRatAlgebra` outranks `AlgebraicClosure.instAlgebra ℚ` once `ℤ_[ℓ]` has pulled in
the analysis imports, and `AlgebraicClosure.isAlgebraic` is registered against the latter. The
failure is `failed to synthesize instance of type class Algebra.IsIntegral ℚ AlgClosedQ`,
reported at the `example`.

⚠️ It is supplied as a `private lemma` and introduced with `haveI` at the point of use rather than
as a `private instance`, so that no importing file silently acquires a `ℚ`-specific instance this
file needed only for one certificate. ⚠️ This is why
`EllipticCurves.TateModule.MatrixRepThree`'s and
`EllipticCurves.TateModule.DeterminantThree`'s certificate blocks do not carry it: neither of their
theorems takes `[Algebra.IsIntegral S F]`. ⚠️ Four other files on this front *do* carry it
(`Continuity`, `OpenKernel`, `Image`, `ImageProfinite`), so continuity is not where the hypothesis
first appears — this is merely the first place a **certificate over `ℚ`** has had to supply it. -/
private lemma exampleIsIntegral : Algebra.IsIntegral ℚ AlgClosedQ := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
        = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
    infer_instance
  infer_instance

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, `ρ_{E,3}` really is a **continuous** `GL₂(ℤ_[3])`-valued
representation that computes the Galois action.

⚠️ The statement is restated in full rather than obtained-and-projected (`#916`), and the
compatibility clause is kept — without it the certificate would be witnessed by the trivial
homomorphism and would not mention the curve. -/
example : ∃ (b : Module.Basis (Fin 2) ℤ_[3] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3))
    (ρ : (AlgClosedQ ≃ₐ[ℚ] AlgClosedQ) →* GL (Fin 2) ℤ_[3]), Continuous ρ ∧
      ∀ (σ : AlgClosedQ ≃ₐ[ℚ] AlgClosedQ)
        (f : ((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3),
        ⇑(b.repr (σ • f)) = (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[3]) *ᵥ ⇑(b.repr f) := by
  haveI := exampleIsIntegral
  exact exists_continuous_galoisRepMatrixThree exampleTwo exampleThree

open Classical in
/-- **The module the matrices act on is not the zero module**, on the same curve, by a route that
never mentions the matrix representation or continuity: `T₃E` surjects onto `E[3^k]`, which has
`9^k` elements. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3) :=
  tateModule.infinite_tateModule_three exampleTwo exampleThree

end Nonvacuity

end WeierstrassCurve.Affine
