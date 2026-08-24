/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Image
import EllipticCurves.TateModule.PrimaryImageProfinite

/-!
# `im ρ_{E,2}` and `G ⧸ ker ρ_{E,2}` are profinite groups

`EllipticCurves.TateModule.Profinite` (`#597`) packages the Tate module itself as an object of
`ProfiniteAddGrp`. This file is the multiplicative counterpart, on the other side of the
representation: it packages the image of `ρ_{E,2}`, the quotient `G ⧸ ker ρ_{E,2}`, and the target
of the determinant character as objects of `ProfiniteGrp`, and exhibits `ρ_{E,2}` itself as a
**morphism of profinite groups**.

`EllipticCurves.TateModule.Image` (`#619`) already proved the two hard facts — that the image is
compact and closed, and that `G ⧸ ker ρ ≃ₜ* im ρ` as *topological* groups. What was missing was
nothing about elliptic curves at all, but four topological instances, three of which are gaps in
Mathlib rather than in this development.

## What this file contains, and what it does not

The argument is in `EllipticCurves.TateModule.PrimaryImageProfinite`, stated for an arbitrary prime
`ℓ`. **This file supplies its input at `ℓ = 2` and contains no argument**: every proof below is one
line. `EllipticCurves.TateModule.ImageProfiniteThree` is the `ℓ = 3` layer.

⚠️ **Ten declarations that this file used to state now live in
`EllipticCurves.TateModule.PrimaryImageProfinite`**, at the same full names, with the same
statements and the same docstrings. Nine of them were already stated at an arbitrary prime `p` and
one — `profiniteGrpGalois` — mentions no prime at all, so none of them has, or needs, a per-prime
twin. They moved because the generic file consumes them and cannot import this one, **not** because
they were generalised: nothing about any of them changed.

* `MulOpposite.instTotallyDisconnectedSpace`, `Units.instTotallyDisconnectedSpace`,
  `Matrix.instCompactSpace`, `Matrix.instTotallyDisconnectedSpace` — the four instances this file
  had to state, still upstreamable as written, together with the analysis of why Mathlib does not
  have them. ⚠️ **These four are not the same four as the *"four topological instances"* above**:
  that sentence counts the four links of the chain that fails, one of which
  (`TotallyDisconnectedSpace ℤ_[p]`) is not missing from Mathlib at all but reachable only through
  an import nothing on this front had. Hence *"three of which are gaps"* there and four
  declarations here.
* `Matrix.GeneralLinearGroup.compactSpace_padicInt`,
  `Matrix.GeneralLinearGroup.totallyDisconnectedSpace_padicInt`,
  `Matrix.GeneralLinearGroup.profiniteGrpPadicInt`, `Matrix.GeneralLinearGroup.infinite_padicInt`,
  `PadicInt.profiniteGrpUnits` — `GLₙ(ℤ_[p])` and `ℤ_[p]ˣ` as profinite groups, and the certificate
  that the former is infinite.
* `WeierstrassCurve.Affine.profiniteGrpGalois` — `Gal(F/S)` as an object of `ProfiniteGrp`.

`Image.lean`'s module docstring asserts in prose that "`GL₂(ℤ_[2])` is itself compact"; that was
true and was **not a theorem** in this development before this file was first written. It is one
now, as `Matrix.GeneralLinearGroup.compactSpace_padicInt`, and it is stated at every prime.

## What is proved here

* `WeierstrassCurve.Affine.profiniteGrpRangeGaloisRepMatrixTwo` — the image of `ρ_{E,2}` as a
  profinite group, via `ProfiniteGrp.ofClosedSubgroup` and `#619`'s closedness.
* `WeierstrassCurve.Affine.profiniteGrpQuotientKerGaloisRepMatrixTwo` — `G ⧸ ker ρ_{E,2}` as a
  profinite group. This consumes `quotientKerContinuousMulEquivRange` in the `.symm`
  direction; a bare `MulEquiv` would not have sufficed, since transporting compactness and total
  disconnectedness needs the homeomorphism.
* `WeierstrassCurve.Affine.continuousGaloisRepMatrixTwo` and
  `WeierstrassCurve.Affine.profiniteGrpHomGaloisRepMatrixTwo` — `ρ_{E,2}` bundled as a
  `ContinuousMonoidHom`, and as a morphism in the category `ProfiniteGrp`. The latter is the
  classical statement: *the `2`-adic representation is a continuous homomorphism of profinite
  groups*.
* The determinant character's image, same treatment, in a basis-taking and a basis-free form.

## Naming

All fifteen names below carry a `Two`, and all fifteen statements are byte-identical to what this
file shipped before the extraction. ⚠️ That includes the **primed** pair
`closedSubgroupRangeGaloisDetTwo'` / `profiniteGrpRangeGaloisDetTwo'`, whose prime marks the
basis-free form. `EllipticCurves.TateModule.PrimaryImageProfinite` deliberately does **not** use a
prime for the generic counterparts — generically the two families differ by taking a basis versus
taking `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`, which
`EllipticCurves.TateModule.PrimaryImage` spells `_of_basis` and `_of_nonempty` — while
`EllipticCurves.TateModule.ImageProfiniteThree` **does**, because a twin's job is to be the `ℓ = 2`
name at `ℓ = 3`. The generic file records that decision.

## Non-degeneracy: a profinite group may be finite

Everything below is true of the trivial group, and no theorem about `G` alone can exclude that — it
is a fact about `F / S`, exactly as in `EllipticCurves.TateModule.Image` and
`EllipticCurves.TateModule.OpenKernel`. The certificates offered instead are about the *ambient*
group, where the content actually is, and all three are now stated at an arbitrary prime:

* `Matrix.GeneralLinearGroup.infinite_padicInt`
  (`EllipticCurves.TateModule.PrimaryImageProfinite`) — `GL₂(ℤ_[p])` is infinite, so "profinite"
  here is not a disguised "finite".
* `Matrix.GeneralLinearGroup.not_discreteTopology_padicInt`
  (`EllipticCurves.TateModule.PrimaryMatrixContinuity`) — it is not discrete either. Worth being
  precise about the logical relationship: `#612` proved this directly, by the unipotent line, at a
  point when compactness of `GL₂(ℤ_[p])` was not available. Now that it is, non-discreteness is a
  *corollary* of infiniteness, since a compact discrete space is finite. The direct proof is kept
  because it needs no compactness and is what a reader of `MatrixContinuity.lean` has in hand.
* `Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup`
  (`EllipticCurves.TateModule.PrimaryImage`) — `GL₂(ℤ_[p])` has subgroups that are not closed, so
  `ofClosedSubgroup` is being applied to a hypothesis that is not free.

## Scope

The statements below are `ℓ = 2`, and that is now a *choice of layer* rather than a restriction on
the development: `EllipticCurves.TateModule.PrimaryImageProfinite` states all fifteen at an
arbitrary prime and `EllipticCurves.TateModule.ImageProfiniteThree` instantiates them at `ℓ = 3`.
⚠️ The clause this paragraph used to end with — *"**Nothing gates the `ℓ = 3` layer of this file;
it simply has not been written**, and that is a follow-up"* — was true when written and is retired
by the file that discharges it. So is the *"reusable verbatim when odd `ℓ` opens"* promise this
file made about `Matrix.GeneralLinearGroup.profiniteGrpPadicInt`: that statement is now literally
reused, unchanged, by both instantiation layers.

`profiniteGrpHomGaloisRepMatrixTwo` carries a **universe restriction**, `S F : Type`, which the
other statements do not. `Category ProfiniteGrp.{u}` lives at a fixed universe, so the `⟶` form
needs `F ≃ₐ[S] F` and `GL (Fin 2) ℤ_[2]` in the *same* universe. The restriction is the category's,
not the mathematics'; `continuousGaloisRepMatrixTwo` is universe-polymorphic and carries the same
content, so reach for it unless the categorical packaging is what is wanted. The generic file
inherits the restriction on exactly the same rows and no others: the two `⟶` rows, and
`profiniteGrpGalois`, which they consume.

Not proved here: **openness** of the image (Serre's theorem — false for curves with complex
multiplication, and profiniteness does not approach it); **surjectivity** or **injectivity** of
`ρ_{E,2}`; and the identification of `det ρ_{E,2}` with the cyclotomic character, which is
Weil-pairing gated. ⚠️ Odd `ℓ` is no longer on that list: `ℓ = 3` is
`EllipticCurves.TateModule.ImageProfiniteThree`, and `ℓ ≥ 5` has the generic file and lacks only a
basis to feed it.

## Main statements

* `WeierstrassCurve.Affine.profiniteGrpRangeGaloisRepMatrixTwo`
* `WeierstrassCurve.Affine.profiniteGrpQuotientKerGaloisRepMatrixTwo`
* `WeierstrassCurve.Affine.profiniteGrpHomGaloisRepMatrixTwo`

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix Topology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable [Algebra.IsIntegral S F] [IsGalois S F]
variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-! ### The image of `ρ_{E,2}` as a profinite group -/

/-- The image of `ρ_{E,2}` packaged as a `ClosedSubgroup` of `GL₂(ℤ_[2])`, which is the input
`ProfiniteGrp.ofClosedSubgroup` wants. Closedness is `#619`'s
`isClosed_range_galoisRepMatrixTwo`, and it is not free: `GL₂(ℤ_[2])` has subgroups that are not
closed (`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup`, stated at an arbitrary
prime in `EllipticCurves.TateModule.PrimaryImage`). -/
noncomputable def closedSubgroupRangeGaloisRepMatrixTwo : ClosedSubgroup (GL (Fin 2) ℤ_[2]) :=
  closedSubgroupRangeGaloisRepMatrix b

/-- **The image of `ρ_{E,2}` is a profinite group.**

A closed subgroup of a profinite group is profinite, and `GL₂(ℤ_[2])` is profinite by
`Matrix.GeneralLinearGroup.profiniteGrpPadicInt`. Together with
`WeierstrassCurve.Affine.isClosed_ker_galoisRepMatrixTwo`, this presents the `2`-adic
representation of `E` as a map of profinite groups with profinite image. -/
noncomputable def profiniteGrpRangeGaloisRepMatrixTwo : ProfiniteGrp :=
  profiniteGrpRangeGaloisRepMatrix b

/-- The carrier of `profiniteGrpRangeGaloisRepMatrixTwo` is the image of `ρ_{E,2}`, pinning the
object to the subgroup it is meant to be. -/
theorem coe_profiniteGrpRangeGaloisRepMatrixTwo :
    (profiniteGrpRangeGaloisRepMatrixTwo b : Type _) = (galoisRepMatrixTwo b).range :=
  coe_profiniteGrpRangeGaloisRepMatrix b

/-- **`G ⧸ ker ρ_{E,2}` is a profinite group.**

Transported along `quotientKerContinuousMulEquivRange`
(`EllipticCurves.TateModule.PrimaryImage`, `ℓ`-generic), used in the `.symm` direction. The
transport needs a *homeomorphism*: compactness and total disconnectedness do not travel along a
bare `MulEquiv`, and a continuous bijective homomorphism is not a homeomorphism in general. This is
where the topological first isomorphism theorem earns its keep. -/
noncomputable def profiniteGrpQuotientKerGaloisRepMatrixTwo : ProfiniteGrp :=
  profiniteGrpQuotientKerGaloisRepMatrix b

/-- The carrier of `profiniteGrpQuotientKerGaloisRepMatrixTwo` is the quotient `G ⧸ ker ρ_{E,2}`. -/
theorem coe_profiniteGrpQuotientKerGaloisRepMatrixTwo :
    (profiniteGrpQuotientKerGaloisRepMatrixTwo b : Type _)
      = ((F ≃ₐ[S] F) ⧸ (galoisRepMatrixTwo b).ker) :=
  coe_profiniteGrpQuotientKerGaloisRepMatrix b

/-! ### `ρ_{E,2}` as a continuous homomorphism -/

omit [IsGalois S F] in
/-- **`ρ_{E,2}` bundled as a continuous monoid homomorphism** `G →ₜ* GL₂(ℤ_[2])`.

Universe-polymorphic, and needs no `[IsGalois S F]`: continuity is
`EllipticCurves.TateModule.MatrixContinuity`'s `continuous_galoisRepMatrixTwo`, which holds for
every basis with no hypothesis at all. Prefer this to the categorical
`profiniteGrpHomGaloisRepMatrixTwo` unless the category is what is wanted. -/
noncomputable def continuousGaloisRepMatrixTwo :
    ContinuousMonoidHom (F ≃ₐ[S] F) (GL (Fin 2) ℤ_[2]) :=
  continuousGaloisRepMatrix b

omit [IsGalois S F] in
@[simp]
theorem continuousGaloisRepMatrixTwo_apply (σ : F ≃ₐ[S] F) :
    continuousGaloisRepMatrixTwo b σ = galoisRepMatrixTwo b σ :=
  continuousGaloisRepMatrix_apply b σ

/-! ### The determinant character -/

/-- The image of `det ρ_{E,2}` as a closed subgroup of `ℤ_[2]ˣ`.

Takes a basis even though `galoisDetTwo` is basis-free, because continuity of `galoisDetTwo` is
proved through one. See `closedSubgroupRangeGaloisDetTwo'` for the form that discharges it. -/
noncomputable def closedSubgroupRangeGaloisDetTwo
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) : ClosedSubgroup ℤ_[2]ˣ :=
  closedSubgroupRangeGaloisDet_of_basis b

/-- **The image of the determinant character `det ρ_{E,2} : G →* ℤ_[2]ˣ` is a profinite group.**

This is the layer the (Weil-pairing gated) identification of `det ρ_{E,2}` with the cyclotomic
character will consume. Nothing here identifies it. -/
noncomputable def profiniteGrpRangeGaloisDetTwo
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) : ProfiniteGrp :=
  profiniteGrpRangeGaloisDet_of_basis b

/-- The carrier of `profiniteGrpRangeGaloisDetTwo` is the image of `det ρ_{E,2}`. -/
theorem coe_profiniteGrpRangeGaloisDetTwo
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :
    (profiniteGrpRangeGaloisDetTwo b : Type _) = (galoisDetTwo (W' := W') (F := F)).range :=
  coe_profiniteGrpRangeGaloisDet_of_basis b

section TwoDet

variable (W')
variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- The image of `det ρ_{E,2}` as a closed subgroup of `ℤ_[2]ˣ`, with no basis supplied: over an
algebraically closed field of characteristic `≠ 2` one exists, and `IsClosed` is a `Prop`. -/
noncomputable def closedSubgroupRangeGaloisDetTwo' (h2 : (2 : F) ≠ 0) : ClosedSubgroup ℤ_[2]ˣ :=
  closedSubgroupRangeGaloisDet_of_nonempty (W' := W')
    (tateModule.nonempty_tateModuleEquivProd h2)

/-- **The image of `det ρ_{E,2}` is a profinite group**, basis-free form. -/
noncomputable def profiniteGrpRangeGaloisDetTwo' (h2 : (2 : F) ≠ 0) : ProfiniteGrp :=
  profiniteGrpRangeGaloisDet_of_nonempty (W' := W')
    (tateModule.nonempty_tateModuleEquivProd h2)

/-- The carrier of `profiniteGrpRangeGaloisDetTwo'` is the image of `det ρ_{E,2}`. -/
theorem coe_profiniteGrpRangeGaloisDetTwo' (h2 : (2 : F) ≠ 0) :
    (profiniteGrpRangeGaloisDetTwo' W' h2 : Type _)
      = (galoisDetTwo (W' := W') (F := F)).range :=
  coe_profiniteGrpRangeGaloisDet_of_nonempty (W' := W')
    (tateModule.nonempty_tateModuleEquivProd h2)

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

/-- **`ρ_{E,2}` is a morphism of profinite groups** `Gal(F/S) ⟶ GL₂(ℤ_[2])`.

This is the classical statement of the `2`-adic representation, assembled from every piece on this
front: `T₂E` free of rank `2` (`#576`), the matrix representation (`#586`), its continuity
(`#612`), and compactness of `Gal(F/S)` (Mathlib, under `[IsGalois S F]`).

It says nothing about the image beyond what `profiniteGrpRangeGaloisRepMatrixTwo` says: not
surjectivity, not injectivity, and certainly not openness. -/
noncomputable def profiniteGrpHomGaloisRepMatrixTwo :
    profiniteGrpGalois (S := S) (F := F) ⟶
      Matrix.GeneralLinearGroup.profiniteGrpPadicInt 2 (Fin 2) :=
  profiniteGrpHomGaloisRepMatrix b

/-- The morphism `profiniteGrpHomGaloisRepMatrixTwo` computes `ρ_{E,2}`, so it cannot drift to some
other map of profinite groups. -/
@[simp]
theorem profiniteGrpHomGaloisRepMatrixTwo_apply (σ : F ≃ₐ[S] F) :
    profiniteGrpHomGaloisRepMatrixTwo b σ = galoisRepMatrixTwo b σ :=
  profiniteGrpHomGaloisRepMatrix_apply b σ

end SmallUniverse

end WeierstrassCurve.Affine
