/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.TateModule.ImageThree
import EllipticCurves.TateModule.PrimaryImageProfinite

/-!
# `im ρ_{E,3}` and `G ⧸ ker ρ_{E,3}` are profinite groups

For a Weierstrass curve `W'` over a field `S`, an extension `F / S` integral over `S` and Galois
over `S`, and `G = F ≃ₐ[S] F`, this file packages the image of the `3`-adic Galois representation,
the quotient `G ⧸ ker ρ_{E,3}`, and the image of the determinant character as objects of
`ProfiniteGrp`, and exhibits `ρ_{E,3}` itself as a **morphism of profinite groups**:

```
profiniteGrpHomGaloisRepMatrixThree :
  profiniteGrpGalois ⟶ Matrix.GeneralLinearGroup.profiniteGrpPadicInt 3 (Fin 2).
```

This is the **second** prime at which the profinite packaging is available in this development, and
the first odd one.

## What this file contains, and what it does not

The argument is in `EllipticCurves.TateModule.PrimaryImageProfinite`, stated for an arbitrary prime
`ℓ`. **This file supplies its inputs at `ℓ = 3` and contains no argument**: every proof below is
one line. The inputs are `EllipticCurves.TateModule.ImageThree`'s closedness statements, and — for
the three basis-free determinant rows only — `nonempty_tateModuleEquivProd_three`
(`EllipticCurves.TateModule.FreeThree`, `#974`).

⚠️ **Two hypotheses, not one.** Where the `ℓ = 2` file `EllipticCurves.TateModule.ImageProfinite`
carries only `h2` on its primed rows, the primed rows here carry both `h2` and `h3`, and the
provenance is not symmetric: `nsmul_three_surjective` needs **only** `(2 : F) ≠ 0`, so the coherent
system's *lifting* step is `h3`-free; `h3` enters exclusively through the counting theorem
`card_torsion_three_pow`, i.e. through `#E[3] = 9`. `EllipticCurves.TateModule.ImageThree`
documents that split and this file inherits it unchanged rather than re-deriving it.

## ⚠️ Fifteen declarations, not twenty-five

`EllipticCurves.TateModule.ImageProfinite` had **twenty-five** declarations before the extraction.
They split three ways, and ⚠️ **the group that needs nothing at all is nearly half of them**:

* **fifteen** carried a `Two` suffix. These are what this file twins, and they are the whole of it.
* **nine** were already stated at an arbitrary prime `p` — the two `MulOpposite`/`Units` gaps, the
  two `Matrix` synonym instances, `Matrix.GeneralLinearGroup.compactSpace_padicInt`,
  `…totallyDisconnectedSpace_padicInt`, `…profiniteGrpPadicInt`, `…infinite_padicInt` and
  `PadicInt.profiniteGrpUnits`. ⚠️ **Cited here, never restated.** A `…Three` twin of any of them
  would be pure duplication.
* **one** — `WeierstrassCurve.Affine.profiniteGrpGalois` — is about `F ≃ₐ[S] F` and mentions no
  prime, so a `profiniteGrpGaloisThree` would be a **name collision** rather than a duplication.
  It is cited by `profiniteGrpHomGaloisRepMatrixThree` below, exactly as at `ℓ = 2`.

All ten of the last two groups now live in `EllipticCurves.TateModule.PrimaryImageProfinite`, at
unchanged names and statements, because the generic file consumes them and cannot import the
`ℓ = 2` layer. ⚠️ *Genericity is a property of a statement; position is a property of the import
graph.* Nothing about any of them was generalised — they were already generic — and nothing about
them is this file's to twin.

## Naming, and the primed rows

The rule `EllipticCurves.TateModule.MatrixRepThree` records applies: a twin of an already-generic
declaration is normally pure duplication, and the fifteen below are the same deliberate exception —
their `ℓ = 2` twins predate the extraction and cannot be removed, and leaving `ℓ = 3` without the
matching spellings would put the two primes on different footings for every downstream file that
extends by pattern.

⚠️ **Three of the fifteen carry a `'`, and this file keeps it**:
`closedSubgroupRangeGaloisDetThree'`, `profiniteGrpRangeGaloisDetThree'` and
`coe_profiniteGrpRangeGaloisDetThree'`. Nothing on this
board had decided where a prime goes under *"drop `Two`, add `Three`"* before, so the convention is
stated here: **the prime is part of the stem and travels with it**, because a twin's job is to be
the `ℓ = 2` name at `ℓ = 3` and a reader pattern-matching from `ImageProfinite.lean` must not have
to guess. ⚠️ The **generic** file makes the opposite choice deliberately — there the two families
are `_of_basis` and `_of_nonempty`, following `EllipticCurves.TateModule.PrimaryImage`, because
generically the primed family takes `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])` rather than
`[IsAlgClosed F]` and `h2`, and a bare prime cannot say which of two hypothesis shapes is meant.

## The universe restriction

`profiniteGrpHomGaloisRepMatrixThree` and its `_apply` carry `S F : Type`, as at `ℓ = 2` and as in
the generic file: `Category ProfiniteGrp.{u}` lives at a fixed universe, so the `⟶` form needs
`F ≃ₐ[S] F` and `GL (Fin 2) ℤ_[3]` in the *same* universe. ⚠️ **The other thirteen rows are
universe-polymorphic and are stated that way here.** The restriction is the category's, not the
mathematics'; `continuousGaloisRepMatrixThree` is the universe-polymorphic carrier of the same
content.

## Non-degeneracy

⚠️ **A profinite group may be finite, and a profinite structure on the trivial group is free.**
Every statement here is true when `G` is trivial, and no theorem about `G` alone can exclude that:
it is a fact about `F / S`. The certificates offered instead are about the *ambient* group, where
the content is, and ⚠️ **all three are stated at an arbitrary prime, so `ℓ = 3` is covered by
citation and the `Non-vacuity` section below cites rather than restates:**

* `Matrix.GeneralLinearGroup.infinite_padicInt 3` — `GL₂(ℤ_[3])` is infinite.
* `Matrix.GeneralLinearGroup.not_discreteTopology_padicInt 3`
  (`EllipticCurves.TateModule.PrimaryMatrixContinuity`) — it is not discrete either. Note that
  given compactness this is now a *corollary* of infiniteness, since a compact discrete space is
  finite; the direct proof is kept deliberately, because it needs no compactness.
* `Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup 3`
  (`EllipticCurves.TateModule.PrimaryImage`) — `GL₂(ℤ_[3])` has subgroups that are not closed, so
  `ProfiniteGrp.ofClosedSubgroup` is applied to a hypothesis that is not free.

On the source side the certificate is `Infinite (T₃E)`, by a route that never mentions
profiniteness or matrices.

## Scope

* ⚠️ **Openness of `im ρ_{E,3}` is NOT proved here and is not close.** That is Serre's theorem, it
  is **false** for curves with complex multiplication, and profiniteness does not approach it.
  Compact, closed and profinite are the *hypotheses* an open-image theorem starts from.
* **Surjectivity and injectivity of `ρ_{E,3}` stay out.** An isomorphism onto `G ⧸ ker ρ` says
  nothing about whether `ker ρ` is trivial.
* ⚠️ **`det ρ_{E,3} = χ_3` `3`-adically is NOT unblocked by this file**, and
  `profiniteGrpRangeGaloisDetThree` will look exactly like progress towards it. The `3`-adic
  identity needs the Weil pairing on `E[3^k]` for **every** `k`, i.e. the pairing at composite `n`;
  this development has the pairing at `n = 2` and `n = 3` only. The **mod-`3`** identity
  `galoisDetMod 3 = χ_3` is a *different statement about a different object* — valued in
  `(ZMod 3)ˣ`, not `ℤ_[3]ˣ` — and it landed separately as
  `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`. Knowing that a character's image
  is a profinite group says nothing about which character it is.
* ⚠️ **This file consumes the multiplication-by-`n` coordinate formula `x(nP) = Φₙ/ΨSqₙ`**, at
  `n = 3`, through `EllipticCurves.Torsion.TriplingSurjective` and hence through
  `EllipticCurves.TateModule.FreeThree` — but only on the three basis-free rows. The twelve that
  are handed a basis need nothing of the sort.
* **General odd `ℓ ≥ 5` stays out.** `EllipticCurves.TateModule.PrimaryImageProfinite` is already
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
  **`EllipticCurves.TateModule.ImageProfiniteGeneral` supplies it at every prime `ℓ` with
  `(2 : F) ≠ 0` and `(ℓ : F) ≠ 0`** — so *"separate work and is not done here"* is discharged rather
  than owed. ⚠️
  The clause that followed — *"what is missing there is a basis to feed it, not a theorem"* — was
  the right diagnosis, and the basis is `tateModule.nonempty_basis_tateModule_of_natCast_ne_zero`
  (`EllipticCurves.TateModule.MatrixRepGeneral`). ⚠️ `(ℓ : F) ≠ 0` is sharp: at `ℓ = char F` the
  conclusion is **false**, not open — `E[ℓ]` is `0` or `ℤ/ℓℤ`, so `T_ℓE` has rank `0` or `1`.

## Using this file

`[IsGalois S F]` is carried throughout, as in the `ℓ = 2` file: it is what supplies compactness of
`G`, and compactness of `G` is what every statement below rests on. ⚠️ It is a hypothesis on the
extension and not on the curve, and it is **not** automatic — for `F` an algebraic closure of an
imperfect `S` the extension is normal but not separable.

## Main statements

* `WeierstrassCurve.Affine.profiniteGrpRangeGaloisRepMatrixThree`
* `WeierstrassCurve.Affine.profiniteGrpQuotientKerGaloisRepMatrixThree`
* `WeierstrassCurve.Affine.profiniteGrpHomGaloisRepMatrixThree`

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix Topology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable [Algebra.IsIntegral S F] [IsGalois S F]
variable (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))

/-! ### The image of `ρ_{E,3}` as a profinite group -/

/-- The image of `ρ_{E,3}` packaged as a `ClosedSubgroup` of `GL₂(ℤ_[3])`, which is the input
`ProfiniteGrp.ofClosedSubgroup` wants. Closedness is `isClosed_range_galoisRepMatrixThree`, and it
is not free: `Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup 3` exhibits a subgroup of
`GL₂(ℤ_[3])` that is not closed. -/
noncomputable def closedSubgroupRangeGaloisRepMatrixThree : ClosedSubgroup (GL (Fin 2) ℤ_[3]) :=
  closedSubgroupRangeGaloisRepMatrix b

/-- **The image of `ρ_{E,3}` is a profinite group.**

A closed subgroup of a profinite group is profinite, and `GL₂(ℤ_[3])` is profinite by
`Matrix.GeneralLinearGroup.profiniteGrpPadicInt 3 (Fin 2)`, which is stated at an arbitrary prime
and is reused here unchanged. -/
noncomputable def profiniteGrpRangeGaloisRepMatrixThree : ProfiniteGrp :=
  profiniteGrpRangeGaloisRepMatrix b

/-- The carrier of `profiniteGrpRangeGaloisRepMatrixThree` is the image of `ρ_{E,3}`, pinning the
object to the subgroup it is meant to be. -/
theorem coe_profiniteGrpRangeGaloisRepMatrixThree :
    (profiniteGrpRangeGaloisRepMatrixThree b : Type _) = (galoisRepMatrixThree b).range :=
  coe_profiniteGrpRangeGaloisRepMatrix b

/-- **`G ⧸ ker ρ_{E,3}` is a profinite group.**

Transported along `quotientKerContinuousMulEquivRange`
(`EllipticCurves.TateModule.PrimaryImage`, `ℓ`-generic and with no `Three` twin), used in the
`.symm` direction. The transport needs a *homeomorphism*: compactness and total disconnectedness do
not travel along a bare `MulEquiv`, and a continuous bijective homomorphism is not a homeomorphism
in general. -/
noncomputable def profiniteGrpQuotientKerGaloisRepMatrixThree : ProfiniteGrp :=
  profiniteGrpQuotientKerGaloisRepMatrix b

/-- The carrier of `profiniteGrpQuotientKerGaloisRepMatrixThree` is `G ⧸ ker ρ_{E,3}`. -/
theorem coe_profiniteGrpQuotientKerGaloisRepMatrixThree :
    (profiniteGrpQuotientKerGaloisRepMatrixThree b : Type _)
      = ((F ≃ₐ[S] F) ⧸ (galoisRepMatrixThree b).ker) :=
  coe_profiniteGrpQuotientKerGaloisRepMatrix b

/-! ### `ρ_{E,3}` as a continuous homomorphism -/

omit [IsGalois S F] in
/-- **`ρ_{E,3}` bundled as a continuous monoid homomorphism** `G →ₜ* GL₂(ℤ_[3])`.

Universe-polymorphic, and needs no `[IsGalois S F]`: continuity is
`EllipticCurves.TateModule.MatrixContinuityThree`'s `continuous_galoisRepMatrixThree`, which holds
for every basis with no hypothesis at all. Prefer this to the categorical
`profiniteGrpHomGaloisRepMatrixThree` unless the category is what is wanted. -/
noncomputable def continuousGaloisRepMatrixThree :
    ContinuousMonoidHom (F ≃ₐ[S] F) (GL (Fin 2) ℤ_[3]) :=
  continuousGaloisRepMatrix b

omit [IsGalois S F] in
@[simp]
theorem continuousGaloisRepMatrixThree_apply (σ : F ≃ₐ[S] F) :
    continuousGaloisRepMatrixThree b σ = galoisRepMatrixThree b σ :=
  continuousGaloisRepMatrix_apply b σ

/-! ### The determinant character -/

/-- The image of `det ρ_{E,3}` as a closed subgroup of `ℤ_[3]ˣ`.

Takes a basis even though `galoisDetThree` is basis-free, because continuity of `galoisDetThree` is
proved through one. See `closedSubgroupRangeGaloisDetThree'` for the form that discharges it. -/
noncomputable def closedSubgroupRangeGaloisDetThree
    (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3)) : ClosedSubgroup ℤ_[3]ˣ :=
  closedSubgroupRangeGaloisDet_of_basis b

/-- **The image of the determinant character `det ρ_{E,3} : G →* ℤ_[3]ˣ` is a profinite group.**

⚠️ **This is not progress towards `det ρ_{E,3} = χ_3`.** That identification needs the Weil pairing
on `E[3^k]` for every `k`; knowing that a character's image is a profinite group says nothing about
which character it is. -/
noncomputable def profiniteGrpRangeGaloisDetThree
    (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3)) : ProfiniteGrp :=
  profiniteGrpRangeGaloisDet_of_basis b

/-- The carrier of `profiniteGrpRangeGaloisDetThree` is the image of `det ρ_{E,3}`. -/
theorem coe_profiniteGrpRangeGaloisDetThree
    (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3)) :
    (profiniteGrpRangeGaloisDetThree b : Type _) = (galoisDetThree (W' := W') (F := F)).range :=
  coe_profiniteGrpRangeGaloisDet_of_basis b

section ThreeDet

variable (W')
variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- The image of `det ρ_{E,3}` as a closed subgroup of `ℤ_[3]ˣ`, with no basis supplied: over an
algebraically closed field in which `2` and `3` are invertible a basis of `T₃E` exists
(`nonempty_tateModuleEquivProd_three`), and `IsClosed` is a `Prop`, so the choice can be
discharged. ⚠️ Two hypotheses where `ℓ = 2` needs one; see the module docstring for the split.

⚠️ **Deletion test**, measured on this file as committed. Deleting `(h3 : (3 : F) ≠ 0)` from the
signature and replacing `h3` by a hole — `by refine closedSubgroupRangeGaloisDet_of_nonempty
(W' := W') (tateModule.nonempty_tateModuleEquivProd_three h2 ?_)` — leaves, copy-paste:

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁷ : Field S
inst✝⁶ : Field F
inst✝⁵ : DecidableEq F
inst✝⁴ : Algebra S F
W' : Affine S
inst✝³ : Algebra.IsIntegral S F
inst✝² : IsGalois S F
b : Module.Basis (Fin 2) ℤ_[3] ↥((W'⁄F).tateModule 3)
inst✝¹ : IsAlgClosed F
inst✝ : WeierstrassCurve.IsElliptic W'⁄F
h2 : 2 ≠ 0
⊢ 3 ≠ 0
```

⚠️ `h2` **survives** and `h3` is gone, so the residual is exactly the hypothesis the `ℓ = 2` file
does not have — `#E[3] = 9` through `card_torsion_three_pow`, not the lifting step, which is
`h3`-free. The residual is a **goal**, which no type mismatch could produce. One mechanical edit
accompanies it and adds no information (`:=` becomes `by refine … ?_`). ⚠️ **There is no knock-on,
and the reason is structural rather than lucky**: in this instantiation layer the three primed rows
are *siblings*, each going straight to
`EllipticCurves.TateModule.PrimaryImageProfinite`, not a chain — so deleting a hypothesis from one
of them cannot reach the other two. The chain, and therefore the knock-on, is in the generic
file. *Whether a deletion test has a knock-on is decided by what consumes the declaration and by
whether the edit touches its signature; here the signature moves and nothing consumes it.* -/
noncomputable def closedSubgroupRangeGaloisDetThree' (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ClosedSubgroup ℤ_[3]ˣ :=
  closedSubgroupRangeGaloisDet_of_nonempty (W' := W')
    (tateModule.nonempty_tateModuleEquivProd_three h2 h3)

/-- **The image of `det ρ_{E,3}` is a profinite group**, basis-free form. -/
noncomputable def profiniteGrpRangeGaloisDetThree' (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ProfiniteGrp :=
  profiniteGrpRangeGaloisDet_of_nonempty (W' := W')
    (tateModule.nonempty_tateModuleEquivProd_three h2 h3)

/-- The carrier of `profiniteGrpRangeGaloisDetThree'` is the image of `det ρ_{E,3}`. -/
theorem coe_profiniteGrpRangeGaloisDetThree' (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (profiniteGrpRangeGaloisDetThree' W' h2 h3 : Type _)
      = (galoisDetThree (W' := W') (F := F)).range :=
  coe_profiniteGrpRangeGaloisDet_of_nonempty (W' := W')
    (tateModule.nonempty_tateModuleEquivProd_three h2 h3)

end ThreeDet

/-! ### The categorical statement

`Category ProfiniteGrp.{u}` is at a fixed universe, so the morphism form needs `F ≃ₐ[S] F` and
`GL (Fin 2) ℤ_[3]` in the same universe. That forces `S F : Type`. The restriction is the
category's, not the mathematics'; `continuousGaloisRepMatrixThree` above says the same thing
without it. -/

section SmallUniverse

variable {S F : Type} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable [Algebra.IsIntegral S F] [IsGalois S F]
variable (b : Module.Basis (Fin 2) ℤ_[3] ((W'⁄F).tateModule 3))

/-- **`ρ_{E,3}` is a morphism of profinite groups** `Gal(F/S) ⟶ GL₂(ℤ_[3])`.

This is the classical statement of the `3`-adic representation at the first odd prime available
here, assembled from every piece on this front: `T₃E` free of rank `2` (`#974`), the matrix
representation (`#989`), its continuity (`#1013`), closedness of the image (`#1024`), and
compactness of `Gal(F/S)` (Mathlib, under `[IsGalois S F]`).

⚠️ Its source `profiniteGrpGalois` carries no prime and gets no `Three` twin; it is cited from
`EllipticCurves.TateModule.PrimaryImageProfinite`. It says nothing about the image beyond what
`profiniteGrpRangeGaloisRepMatrixThree` says: not surjectivity, not injectivity, and certainly not
openness. -/
noncomputable def profiniteGrpHomGaloisRepMatrixThree :
    profiniteGrpGalois (S := S) (F := F) ⟶
      Matrix.GeneralLinearGroup.profiniteGrpPadicInt 3 (Fin 2) :=
  profiniteGrpHomGaloisRepMatrix b

/-- The morphism `profiniteGrpHomGaloisRepMatrixThree` computes `ρ_{E,3}`, so it cannot drift to
some other map of profinite groups. -/
@[simp]
theorem profiniteGrpHomGaloisRepMatrixThree_apply (σ : F ≃ₐ[S] F) :
    profiniteGrpHomGaloisRepMatrixThree b σ = galoisRepMatrixThree b σ :=
  profiniteGrpHomGaloisRepMatrix_apply b σ

end SmallUniverse

/-! ### Non-vacuity

⚠️ Three risks, three certificates, following the idiom
`EllipticCurves.TateModule.MatrixRepThree` introduced and
`EllipticCurves.TateModule.ImageThree` last extended.

1. **The statement is not trivially satisfiable.** ⚠️ *Profinite* is the risk here, not `IsClosed`:
   a finite group is profinite, the trivial group is profinite, and `ProfiniteGrp.ofClosedSubgroup`
   would happily package either. Two certificates answer it and **both are citations**, because
   both are stated at an arbitrary prime `p`: `GL₂(ℤ_[3])` is infinite, and it is not discrete. ⚠️
   It is tempting to restate them at `3`; **do not** — that is the duplication
   `EllipticCurves.TateModule.FreeThree` warns about by name.
2. **The hypothesis class is inhabited.** `[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]`,
   `[Algebra.IsIntegral S F]`, **`[IsGalois S F]`**, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` all hold
   simultaneously for `y² + y = x³` over `ℚ` base-changed to `AlgebraicClosure ℚ`, with **`S = ℚ`**
   so that `Gal(F/S)` is not the trivial group. The certificate closes **by application** of
   `coe_profiniteGrpRangeGaloisRepMatrixThree` (`#944`: `rfl`, `decide` and `norm_num` consume
   nothing), so it consumes the declaration it certifies. ⚠️ It is stated with the basis
   **existentially quantified inside** the statement rather than taken as an argument, so the
   certificate is not itself conditional on a basis that might not exist — the shape
   `EllipticCurves.TateModule.MatrixRepCompatThree` uses.
3. **The target is not degenerate.** Every statement here is true over a zero Tate module, where
   the representation is trivial and its image is the trivial profinite group. The third
   certificate says `T₃E` is infinite, by a route that never mentions profiniteness or matrices.

⚠️ **Two instances have to be supplied by hand and neither is found by search**, both `ℚ`-algebra
traps of the shape `EllipticCurves.TateModule.Continuity` documents: `DivisionRing.toRatAlgebra`
outranks `AlgebraicClosure.instAlgebra ℚ` once `ℤ_[ℓ]` has pulled in the analysis imports, and the
facts one wants are registered against the latter. `Algebra.IsIntegral ℚ AlgClosedQ` is inherited
from `EllipticCurves.TateModule.MatrixContinuityThree`; `IsGalois ℚ AlgClosedQ` is inherited from
`EllipticCurves.TateModule.ImageThree`, which is the file that first hit it.

⚠️ **This file cannot use the `haveI`-at-the-point-of-use idiom that every earlier certificate
block on this front uses, and the reason is worth recording.** There the two instances were needed
only by the *proof*; here `profiniteGrpRangeGaloisRepMatrixThree` carries `[Algebra.IsIntegral S F]`
and `[IsGalois S F]` as instance arguments, so they are needed to elaborate the **statement** — and
a `haveI` inside the `by` block runs strictly too late (`failed to synthesize instance of type class
Algebra.IsIntegral ℚ AlgClosedQ`, reported at the `example` line). They are therefore registered
with `attribute [local instance]`, which is the smallest change that works: `local` attributes are
**not** exported, so no importing file acquires a `ℚ`-specific instance this file needed for one
`example`, which is exactly what the `haveI` idiom was protecting against. ⚠️ `private` in Lean 4
restricts *name resolution*, not instance search, so `private` alone would not have sufficed.

⚠️ **`open Classical in` is load-bearing on the last two certificates and is not optional.** The
`TateModule` family carries `[DecidableEq F]` in its `variable` blocks, but `AlgClosedQ` is
`AlgebraicClosure ℚ`, which has no decidable equality.

⚠️ Every `TateModule` certificate block now names the one shared fixture
`EllipticCurves.Fixture.y2AddYEqX3`; the `private` per-file copies this note used to describe are
gone. -/

section Nonvacuity

/-- **⚠️ THE FIRST CERTIFICATE THAT "PROFINITE" IS NOT A DISGUISED "FINITE"**: `GL₂(ℤ_[3])` is
infinite, so `Matrix.GeneralLinearGroup.profiniteGrpPadicInt 3 (Fin 2)` — the ambient object that
`profiniteGrpRangeGaloisRepMatrixThree` is a closed subgroup of — is not a finite group wearing a
profinite hat.

⚠️ This is a **citation**, not a restatement: the instance is stated at an arbitrary prime `p` in
`EllipticCurves.TateModule.PrimaryImageProfinite` and needs no `ℓ = 3` twin. -/
example : Infinite (GL (Fin 2) ℤ_[3]) := Matrix.GeneralLinearGroup.infinite_padicInt 3

/-- **⚠️ THE SECOND CERTIFICATE**: `GL₂(ℤ_[3])` is not discrete either, so the profinite topology
on it is not the free one that makes every subgroup closed. ⚠️ Also a citation, at an arbitrary
prime, from `EllipticCurves.TateModule.PrimaryMatrixContinuity`. -/
example : ¬ DiscreteTopology (GL (Fin 2) ℤ_[3]) :=
  Matrix.GeneralLinearGroup.not_discreteTopology_padicInt 3

/-- **⚠️ AND THE THIRD**: `GL₂(ℤ_[3])` really does have a subgroup that is not closed, namely the
integral points of the unipotent line, so `ProfiniteGrp.ofClosedSubgroup` is being applied to a
hypothesis that is not free. ⚠️ Cited at an arbitrary prime from
`EllipticCurves.TateModule.PrimaryImage`. -/
example : ¬ IsClosed
    (Matrix.GeneralLinearGroup.unipotentIntSubgroup 3 : Set (GL (Fin 2) ℤ_[3])) :=
  Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup 3

/-! The certificate curve `y² + y = x³` over `ℚ` and its base — algebraically closed so that
`Gal(F/ℚ)` is not the trivial group, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — are the
shared `EllipticCurves.Fixture.y2AddYEqX3` and `EllipticCurves.Fixture.AlgClosedQ`, which also
supply `(y2AddYEqX3 ℚ).IsElliptic` from a single `[CharZero F]` instance. The **base-changed**
`((y2AddYEqX3 ℚ)⁄AlgClosedQ).IsElliptic` comes from the same module, via
`EllipticCurves.Fixture.instIsEllipticBaseChange`; this block declares no fixture of its own
(`#1408`). -/

open EllipticCurves.Fixture

/-- The `ℚ`-algebra instance trap, as `EllipticCurves.TateModule.MatrixContinuityThree` documents
it. ⚠️ **Registered below with `attribute [local instance]`, not introduced with `haveI` at the
point of use** — that is the idiom every earlier certificate block on this front uses, and it is a
clause of `EllipticCurves.TateModule.ImageThree`'s docstring for this same lemma that does **not**
travel here. See the `Non-vacuity` section above and the note on `attribute [local instance]`
below for why the `haveI` form runs too late in this file. -/
private lemma exampleIsIntegral : Algebra.IsIntegral ℚ AlgClosedQ := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
        = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
    infer_instance
  infer_instance

/-- The same trap one class further on, as `EllipticCurves.TateModule.ImageThree` documents it:
`AlgebraicClosure`'s `Normal` and `IsSeparable` instances are registered against
`AlgebraicClosure.instAlgebra ℚ`, which `DivisionRing.toRatAlgebra` outranks. -/
private lemma exampleIsGalois : IsGalois ℚ AlgClosedQ := by
  rw [show (DivisionRing.toRatAlgebra : Algebra ℚ (AlgebraicClosure ℚ))
      = AlgebraicClosure.instAlgebra ℚ from Subsingleton.elim _ _]
  infer_instance

/-! ⚠️ **`local`, not global.** The two instances below are needed to elaborate the *statement* of
the load-bearing certificate and not merely its proof, so the `haveI`-at-the-point-of-use idiom
that `EllipticCurves.TateModule.ImageThree` uses does not apply here. `local` attributes are not
exported, so nothing an importing file sees changes. -/

attribute [local instance] exampleIsIntegral exampleIsGalois

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

open Classical in
/-- **⚠️ THE LOAD-BEARING CERTIFICATE**: on a curve that exists, over a base field `S = ℚ` whose
absolute Galois group is not trivial, there really is a basis of `T₃E`, and the profinite group
built from it really does carry the image of `ρ_{E,3}`.

⚠️ The basis is **existentially quantified inside the statement** rather than taken as an argument,
so this does not certify a family that might be empty. It closes by **application** of
`coe_profiniteGrpRangeGaloisRepMatrixThree` rather than by `rfl`, `decide` or `norm_num`, so it
consumes the declaration it certifies. -/
example : ∃ b : Module.Basis (Fin 2) ℤ_[3] (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3),
    (profiniteGrpRangeGaloisRepMatrixThree b : Type _) = (galoisRepMatrixThree b).range := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_three (W := (y2AddYEqX3 ℚ)⁄AlgClosedQ)
    exampleTwo exampleThree
  exact ⟨b, coe_profiniteGrpRangeGaloisRepMatrixThree b⟩

open Classical in
/-- **The module the representation acts on is not the zero module**, on the same curve, by a route
that never mentions profiniteness or the matrices: `T₃E` surjects onto `E[3^k]`, which has `9^k`
elements. Without this, the image would be the trivial group and profinite for free. -/
example : Infinite (((y2AddYEqX3 ℚ)⁄AlgClosedQ).tateModule 3) :=
  tateModule.infinite_tateModule_three exampleTwo exampleThree

end Nonvacuity

end WeierstrassCurve.Affine
