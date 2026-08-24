/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Image
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# `GLₙ(ℤ_[p])` is a profinite group, and so are `im ρ_{E,2}` and `G ⧸ ker ρ_{E,2}`

`EllipticCurves.TateModule.Profinite` (`#597`) packages the Tate module itself as an object of
`ProfiniteAddGrp`. This file is the multiplicative counterpart, on the other side of the
representation: it packages `GLₙ(ℤ_[p])`, the image of `ρ_{E,2}`, the quotient `G ⧸ ker ρ_{E,2}`,
and the target of the determinant character as objects of `ProfiniteGrp`, and exhibits `ρ_{E,2}`
itself as a **morphism of profinite groups**.

`EllipticCurves.TateModule.Image` (`#619`) already proved the two hard facts — that the image is
compact and closed, and that `G ⧸ ker ρ ≃ₜ* im ρ` as *topological* groups. What was missing was
nothing about elliptic curves at all, but four topological instances, three of which are gaps in
Mathlib rather than in this development. `Image.lean`'s module docstring asserts in prose that
"`GL₂(ℤ_[2])` is itself compact"; that was true and was **not a theorem** in this development
before this file. It is one now (`Matrix.GeneralLinearGroup.compactSpace_padicInt`).

## The four missing instances

The chain that fails, and where:

* `TotallyDisconnectedSpace ℤ_[p]` — **not missing**, but reachable only through
  `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated`, which nothing on this front imported.
  `ℤ_[p]` is an ultrametric metric space, hence totally separated, hence totally disconnected.
  That file states the implication as an `example`, so grepping Mathlib for an `instance` mentioning
  `PadicInt` and `TotallyDisconnectedSpace` finds nothing and invites the wrong conclusion.
* `TotallyDisconnectedSpace Mᵐᵒᵖ` — a genuine Mathlib gap. `Mathlib.Topology.Algebra.Constructions`
  has the `T2Space`, `CompactSpace` and `DiscreteTopology` siblings and not this one.
* `TotallyDisconnectedSpace Mˣ` — a genuine Mathlib gap, and it is the one that consumes the
  previous bullet: `Units.embedProduct` lands in `M × Mᵐᵒᵖ`. Mathlib does already have the
  compactness half (`CompactSpace Mˣ` for `M` compact, `T1` and with continuous multiplication).
* `CompactSpace (Matrix m n R)` and `TotallyDisconnectedSpace (Matrix m n R)` — `Matrix` is a type
  synonym for a `Pi` type and instance search does not unfold it, so `Pi.compactSpace` and
  `Pi.totallyDisconnectedSpace` never fire. This is the actual reason
  `CompactSpace (GL (Fin 2) ℤ_[2])` is not found on the pin.

All four are stated in root Mathlib namespaces and are upstreamable as written; none mentions a
curve. With them in scope, `CompactSpace`, `TotallyDisconnectedSpace`, `T2Space` and
`IsTopologicalGroup` for `GL n ℤ_[p]` are all found by instance search.

## What is proved

* `Matrix.GeneralLinearGroup.profiniteGrpPadicInt` — `GLₙ(ℤ_[p])` as an object of `ProfiniteGrp`,
  for every prime `p` and every finite index type. Nothing here is `2`-primary, so this is reusable
  verbatim when odd `ℓ` opens.
* `WeierstrassCurve.Affine.profiniteGrpRangeGaloisRepMatrixTwo` — the image of `ρ_{E,2}` as a
  profinite group, via `ProfiniteGrp.ofClosedSubgroup` and `#619`'s closedness.
* `WeierstrassCurve.Affine.profiniteGrpQuotientKerGaloisRepMatrixTwo` — `G ⧸ ker ρ_{E,2}` as a
  profinite group. This consumes `#619`'s `quotientKerContinuousMulEquivRange` in the `.symm`
  direction; a bare `MulEquiv` would not have sufficed, since transporting compactness and total
  disconnectedness needs the homeomorphism.
* `WeierstrassCurve.Affine.continuousGaloisRepMatrixTwo` and
  `WeierstrassCurve.Affine.profiniteGrpHomGaloisRepMatrixTwo` — `ρ_{E,2}` bundled as a
  `ContinuousMonoidHom`, and as a morphism in the category `ProfiniteGrp`. The latter is the
  classical statement: *the `2`-adic representation is a continuous homomorphism of profinite
  groups*.
* `PadicInt.profiniteGrpUnits` and the determinant character's image, same treatment.

## Non-degeneracy: a profinite group may be finite

Everything below is true of the trivial group, and no theorem about `G` alone can exclude that — it
is a fact about `F / S`, exactly as in `EllipticCurves.TateModule.Image` and
`EllipticCurves.TateModule.OpenKernel`. The certificates offered instead are about the *ambient*
group, where the content actually is:

* `Matrix.GeneralLinearGroup.infinite_padicInt` — `GL₂(ℤ_[p])` is infinite, so "profinite" here is
  not a disguised "finite".
* `Matrix.GeneralLinearGroup.not_discreteTopology_padicInt`
  (`EllipticCurves.TateModule.MatrixContinuity`) — it is not discrete either. Worth being precise
  about the logical relationship: `#612` proved this directly, by the unipotent line, at a point
  when compactness of `GL₂(ℤ_[p])` was not available. Now that it is, non-discreteness is a
  *corollary* of infiniteness, since a compact discrete space is finite. The direct proof is kept
  because it needs no compactness and is what a reader of `MatrixContinuity.lean` has in hand.
* `Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup`
  (`EllipticCurves.TateModule.Image`) — `GL₂(ℤ_[2])` has subgroups that are not closed, so
  `ofClosedSubgroup` is being applied to a hypothesis that is not free.

## Scope

The elliptic-curve statements are `ℓ = 2` only, because their input is. ⚠️ The reason this
paragraph used to give — *"for the usual reason: `galoisRepMatrixTwo` needs a basis of `T₂E` and
the basis comes from the `2`-primary tower"* — no longer explains the restriction, for the reason
`EllipticCurves.TateModule.Image` now records at length: `galoisRepMatrixThree` exists
(`EllipticCurves.TateModule.MatrixRepThree`) over a basis of `T₃E`, so the matrix representation
is not what confines anything to `ℓ = 2`. ⚠️ **Neither is continuity, any more, and the clause
that said so is retired**: it read *"The chain that does is `continuous_galoisRepMatrixTwo` →
`#619` → this file, and its first link is `ℓ = 2` only"*. `continuous_galoisRepMatrixThree` exists
(`EllipticCurves.TateModule.MatrixContinuityThree`), so nothing gates the `ℓ = 3` layer of this
file; it simply has not been written, and that is a follow-up. ⚠️ This
also cashes the *"reusable verbatim when odd `ℓ` opens"* promise made above about
`Matrix.GeneralLinearGroup.profiniteGrpPadicInt`: odd `ℓ` has opened at `ℓ = 3` for the matrix
representation, and that statement is indeed reusable there unchanged. The `GLₙ(ℤ_[p])` statements
are `ℓ`-free throughout.

`profiniteGrpHomGaloisRepMatrixTwo` carries a **universe restriction**, `S F : Type`, which the
other statements do not. `Category ProfiniteGrp.{u}` lives at a fixed universe, so the `⟶` form
needs `F ≃ₐ[S] F` and `GL (Fin 2) ℤ_[2]` in the *same* universe. The restriction is the category's,
not the mathematics'; `continuousGaloisRepMatrixTwo` is universe-polymorphic and carries the same
content, so reach for it unless the categorical packaging is what is wanted.

Not proved here: **openness** of the image (Serre's theorem — false for curves with complex
multiplication, and profiniteness does not approach it); **surjectivity** or **injectivity** of
`ρ_{E,2}`; the identification of `det ρ_{E,2}` with the cyclotomic character, which is Weil-pairing
gated; and odd `ℓ`.

## Main statements

* `Matrix.GeneralLinearGroup.profiniteGrpPadicInt`
* `WeierstrassCurve.Affine.profiniteGrpRangeGaloisRepMatrixTwo`
* `WeierstrassCurve.Affine.profiniteGrpQuotientKerGaloisRepMatrixTwo`
* `WeierstrassCurve.Affine.profiniteGrpHomGaloisRepMatrixTwo`

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix Topology

/-! ### Total disconnectedness of opposites and unit groups

Two Mathlib gaps. Both are one line and neither mentions a curve; they are stated here only because
`GL n R = (Matrix n n R)ˣ` needs them and Mathlib does not have them. -/

/-- **The multiplicative opposite of a totally disconnected space is totally disconnected.**

`Mathlib.Topology.Algebra.Constructions` has the `T2Space`, `CompactSpace` and `DiscreteTopology`
siblings of this instance but not this one. Upstreamable as written. -/
instance MulOpposite.instTotallyDisconnectedSpace {M : Type*} [TopologicalSpace M]
    [TotallyDisconnectedSpace M] : TotallyDisconnectedSpace Mᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.isTotallyDisconnected_range.1
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- **The unit group of a totally disconnected topological monoid is totally disconnected.**

`Units.embedProduct` is an embedding into `M × Mᵐᵒᵖ`, which is totally disconnected by
`Prod.totallyDisconnectedSpace` together with `MulOpposite.instTotallyDisconnectedSpace` above —
that is why the opposite instance has to come first.

Mathlib already has the compactness counterpart (`CompactSpace Mˣ` for `M` compact and `T1` with
continuous multiplication, `Mathlib.Topology.Algebra.Group.Basic`); this is the missing sibling. -/
instance Units.instTotallyDisconnectedSpace {M : Type*} [Monoid M] [TopologicalSpace M]
    [TotallyDisconnectedSpace M] : TotallyDisconnectedSpace Mˣ :=
  (Units.isEmbedding_embedProduct (M := M)).isTotallyDisconnected_range.1
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-! ### `Matrix` is a type synonym, and instance search does not unfold it -/

namespace Matrix

variable {m n R : Type*} [TopologicalSpace R]

/-- **A matrix space over a compact space is compact.** `Matrix m n R` is definitionally
`m → n → R`, but instance search does not unfold the synonym, so `Pi.compactSpace` never fires and
`CompactSpace (Matrix (Fin 2) (Fin 2) ℤ_[2])` is not found without this. Upstreamable. -/
instance instCompactSpace [Finite m] [Finite n] [CompactSpace R] : CompactSpace (Matrix m n R) :=
  inferInstanceAs (CompactSpace (m → n → R))

/-- **A matrix space over a totally disconnected space is totally disconnected.** Same synonym
issue as `Matrix.instCompactSpace`. Upstreamable. -/
instance instTotallyDisconnectedSpace [TotallyDisconnectedSpace R] :
    TotallyDisconnectedSpace (Matrix m n R) :=
  inferInstanceAs (TotallyDisconnectedSpace (m → n → R))

end Matrix

/-! ### `GLₙ(ℤ_[p])` as a profinite group -/

namespace Matrix.GeneralLinearGroup

variable (p : ℕ) [Fact p.Prime] (n : Type*) [Fintype n] [DecidableEq n]

/-- **`GLₙ(ℤ_[p])` is compact.** This is the statement `EllipticCurves.TateModule.Image` asserts in
prose and does not prove. It is not found by instance search on its own: it needs
`Matrix.instCompactSpace` to bridge the `Matrix` type synonym, and then Mathlib's `CompactSpace Mˣ`
does the rest. -/
instance compactSpace_padicInt : CompactSpace (GL n ℤ_[p]) := inferInstance

/-- **`GLₙ(ℤ_[p])` is totally disconnected.** Needs `Matrix.instTotallyDisconnectedSpace`,
`Units.instTotallyDisconnectedSpace` and — through the latter —
`MulOpposite.instTotallyDisconnectedSpace`, plus total disconnectedness of `ℤ_[p]` itself, which is
available only once `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated` is imported. -/
instance totallyDisconnectedSpace_padicInt : TotallyDisconnectedSpace (GL n ℤ_[p]) := inferInstance

/-- **`GLₙ(ℤ_[p])` as an object of `ProfiniteGrp`.**

The multiplicative counterpart of `EllipticCurves.TateModule.Profinite`'s `profiniteAddGrpTwo`, on
the target side of the representation rather than the source. General in `p` and in the index type:
nothing here is `2`-primary, so this is what an odd-`ℓ` development will consume unchanged.

Note this is an `abbrev`. `ProfiniteGrp.ofClosedSubgroup` below has to unify the carrier of this
object with `GL n ℤ_[p]` at reducible transparency, which a `def` would block. -/
noncomputable abbrev profiniteGrpPadicInt : ProfiniteGrp := ProfiniteGrp.of (GL n ℤ_[p])

/-- **`GL₂(ℤ_[p])` is infinite**, so `profiniteGrpPadicInt p (Fin 2)` is not a finite group wearing
a profinite hat.

The witness is Mathlib's unipotent line `x ↦ !![1, x; 0, 1]`, which is injective, applied to the
infinite `ℤ_[p]` — the same embedding `Matrix.GeneralLinearGroup.not_discreteTopology_padicInt`
uses to show `GL₂(ℤ_[p])` is not discrete.

Together with `compactSpace_padicInt` this also *reproves* non-discreteness, since a compact
discrete space is finite. That is not a reason to remove the direct proof in
`EllipticCurves.TateModule.MatrixContinuity`, which needs no compactness. -/
instance infinite_padicInt : Infinite (GL (Fin 2) ℤ_[p]) :=
  Infinite.of_injective (fun x : ℤ_[p] => upperRightHom x) injective_upperRightHom

end Matrix.GeneralLinearGroup

/-! ### `ℤ_[p]ˣ` as a profinite group -/

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

/-- **`ℤ_[p]ˣ` as an object of `ProfiniteGrp`** — the target of the determinant character. -/
noncomputable abbrev profiniteGrpUnits : ProfiniteGrp := ProfiniteGrp.of ℤ_[p]ˣ

end PadicInt

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable [Algebra.IsIntegral S F] [IsGalois S F]
variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-! ### The image of `ρ_{E,2}` as a profinite group -/

/-- The image of `ρ_{E,2}` packaged as a `ClosedSubgroup` of `GL₂(ℤ_[2])`, which is the input
`ProfiniteGrp.ofClosedSubgroup` wants. Closedness is `#619`'s
`isClosed_range_galoisRepMatrixTwo`, and it is not free: `GL₂(ℤ_[2])` has subgroups that are not
closed (`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup`). -/
noncomputable def closedSubgroupRangeGaloisRepMatrixTwo : ClosedSubgroup (GL (Fin 2) ℤ_[2]) where
  toSubgroup := (galoisRepMatrixTwo b).range
  isClosed' := isClosed_range_galoisRepMatrixTwo b

/-- **The image of `ρ_{E,2}` is a profinite group.**

A closed subgroup of a profinite group is profinite, and `GL₂(ℤ_[2])` is profinite by
`Matrix.GeneralLinearGroup.profiniteGrpPadicInt`. Together with
`WeierstrassCurve.Affine.isClosed_ker_galoisRepMatrixTwo`, this presents the `2`-adic
representation of `E` as a map of profinite groups with profinite image. -/
noncomputable def profiniteGrpRangeGaloisRepMatrixTwo : ProfiniteGrp :=
  ProfiniteGrp.ofClosedSubgroup (G := Matrix.GeneralLinearGroup.profiniteGrpPadicInt 2 (Fin 2))
    (closedSubgroupRangeGaloisRepMatrixTwo b)

/-- The carrier of `profiniteGrpRangeGaloisRepMatrixTwo` is the image of `ρ_{E,2}`, pinning the
object to the subgroup it is meant to be. -/
theorem coe_profiniteGrpRangeGaloisRepMatrixTwo :
    (profiniteGrpRangeGaloisRepMatrixTwo b : Type _) = (galoisRepMatrixTwo b).range := rfl

/-- **`G ⧸ ker ρ_{E,2}` is a profinite group.**

Transported along `#619`'s `quotientKerContinuousMulEquivRange`, used in the `.symm` direction. The
transport needs a *homeomorphism*: compactness and total disconnectedness do not travel along a
bare `MulEquiv`, and a continuous bijective homomorphism is not a homeomorphism in general. This is
where the topological first isomorphism theorem earns its keep. -/
noncomputable def profiniteGrpQuotientKerGaloisRepMatrixTwo : ProfiniteGrp :=
  ProfiniteGrp.ofContinuousMulEquiv (G := profiniteGrpRangeGaloisRepMatrixTwo b)
    (quotientKerContinuousMulEquivRange b).symm

/-- The carrier of `profiniteGrpQuotientKerGaloisRepMatrixTwo` is the quotient `G ⧸ ker ρ_{E,2}`. -/
theorem coe_profiniteGrpQuotientKerGaloisRepMatrixTwo :
    (profiniteGrpQuotientKerGaloisRepMatrixTwo b : Type _)
      = ((F ≃ₐ[S] F) ⧸ (galoisRepMatrixTwo b).ker) := rfl

/-! ### `ρ_{E,2}` as a continuous homomorphism -/

omit [IsGalois S F] in
/-- **`ρ_{E,2}` bundled as a continuous monoid homomorphism** `G →ₜ* GL₂(ℤ_[2])`.

Universe-polymorphic, and needs no `[IsGalois S F]`: continuity is
`EllipticCurves.TateModule.MatrixContinuity`'s `continuous_galoisRepMatrixTwo`, which holds for
every basis with no hypothesis at all. Prefer this to the categorical
`profiniteGrpHomGaloisRepMatrixTwo` unless the category is what is wanted. -/
noncomputable def continuousGaloisRepMatrixTwo :
    ContinuousMonoidHom (F ≃ₐ[S] F) (GL (Fin 2) ℤ_[2]) where
  __ := galoisRepMatrixTwo b
  continuous_toFun := continuous_galoisRepMatrixTwo b

omit [IsGalois S F] in
@[simp]
theorem continuousGaloisRepMatrixTwo_apply (σ : F ≃ₐ[S] F) :
    continuousGaloisRepMatrixTwo b σ = galoisRepMatrixTwo b σ := rfl

/-! ### The determinant character -/

/-- The image of `det ρ_{E,2}` as a closed subgroup of `ℤ_[2]ˣ`.

Takes a basis even though `galoisDetTwo` is basis-free, because continuity of `galoisDetTwo` is
proved through one. See `closedSubgroupRangeGaloisDetTwo'` for the form that discharges it. -/
noncomputable def closedSubgroupRangeGaloisDetTwo
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) : ClosedSubgroup ℤ_[2]ˣ where
  toSubgroup := (galoisDetTwo (W' := W') (F := F)).range
  isClosed' := isClosed_range_galoisDetTwo_of_basis b

/-- **The image of the determinant character `det ρ_{E,2} : G →* ℤ_[2]ˣ` is a profinite group.**

This is the layer the (Weil-pairing gated) identification of `det ρ_{E,2}` with the cyclotomic
character will consume. Nothing here identifies it. -/
noncomputable def profiniteGrpRangeGaloisDetTwo
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) : ProfiniteGrp :=
  ProfiniteGrp.ofClosedSubgroup (G := PadicInt.profiniteGrpUnits 2)
    (closedSubgroupRangeGaloisDetTwo b)

/-- The carrier of `profiniteGrpRangeGaloisDetTwo` is the image of `det ρ_{E,2}`. -/
theorem coe_profiniteGrpRangeGaloisDetTwo
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :
    (profiniteGrpRangeGaloisDetTwo b : Type _) = (galoisDetTwo (W' := W') (F := F)).range := rfl

section TwoDet

variable (W')
variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- The image of `det ρ_{E,2}` as a closed subgroup of `ℤ_[2]ˣ`, with no basis supplied: over an
algebraically closed field of characteristic `≠ 2` one exists, and `IsClosed` is a `Prop`. -/
noncomputable def closedSubgroupRangeGaloisDetTwo' (h2 : (2 : F) ≠ 0) : ClosedSubgroup ℤ_[2]ˣ where
  toSubgroup := (galoisDetTwo (W' := W') (F := F)).range
  isClosed' := isClosed_range_galoisDetTwo h2

/-- **The image of `det ρ_{E,2}` is a profinite group**, basis-free form. -/
noncomputable def profiniteGrpRangeGaloisDetTwo' (h2 : (2 : F) ≠ 0) : ProfiniteGrp :=
  ProfiniteGrp.ofClosedSubgroup (G := PadicInt.profiniteGrpUnits 2)
    (closedSubgroupRangeGaloisDetTwo' W' h2)

/-- The carrier of `profiniteGrpRangeGaloisDetTwo'` is the image of `det ρ_{E,2}`. -/
theorem coe_profiniteGrpRangeGaloisDetTwo' (h2 : (2 : F) ≠ 0) :
    (profiniteGrpRangeGaloisDetTwo' W' h2 : Type _)
      = (galoisDetTwo (W' := W') (F := F)).range := rfl

end TwoDet

/-! ### The categorical statement

`Category ProfiniteGrp.{u}` is at a fixed universe, so the morphism form needs `F ≃ₐ[S] F` and
`GL (Fin 2) ℤ_[2]` in the same universe. That forces `S F : Type`. The restriction is the
category's, not the mathematics'; `continuousGaloisRepMatrixTwo` above says the same thing without
it. -/

section SmallUniverse

variable {S F : Type} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable [Algebra.IsIntegral S F] [IsGalois S F]
variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

omit [Algebra.IsIntegral S F] in
/-- **`Gal(F/S)` as an object of `ProfiniteGrp`.** Mathlib already supplies every instance this
needs — `CompactSpace`, `TotallyDisconnectedSpace` and `IsTopologicalGroup` for `F ≃ₐ[S] F` under
`[IsGalois S F]` — so nothing is proved here; the point is to name the object. -/
noncomputable abbrev profiniteGrpGalois : ProfiniteGrp := ProfiniteGrp.of (F ≃ₐ[S] F)

/-- **`ρ_{E,2}` is a morphism of profinite groups** `Gal(F/S) ⟶ GL₂(ℤ_[2])`.

This is the classical statement of the `2`-adic representation, assembled from every piece on this
front: `T₂E` free of rank `2` (`#576`), the matrix representation (`#586`), its continuity
(`#612`), and compactness of `Gal(F/S)` (Mathlib, under `[IsGalois S F]`).

It says nothing about the image beyond what `profiniteGrpRangeGaloisRepMatrixTwo` says: not
surjectivity, not injectivity, and certainly not openness. -/
noncomputable def profiniteGrpHomGaloisRepMatrixTwo :
    profiniteGrpGalois (S := S) (F := F) ⟶
      Matrix.GeneralLinearGroup.profiniteGrpPadicInt 2 (Fin 2) :=
  CategoryTheory.ConcreteCategory.ofHom (continuousGaloisRepMatrixTwo b)

/-- The morphism `profiniteGrpHomGaloisRepMatrixTwo` computes `ρ_{E,2}`, so it cannot drift to some
other map of profinite groups. -/
@[simp]
theorem profiniteGrpHomGaloisRepMatrixTwo_apply (σ : F ≃ₐ[S] F) :
    profiniteGrpHomGaloisRepMatrixTwo b σ = galoisRepMatrixTwo b σ := rfl

end SmallUniverse

end WeierstrassCurve.Affine
