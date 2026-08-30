/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.PrimaryImage
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# `GLₙ(ℤ_[p])` is a profinite group, and so are `im ρ_{E,ℓ}` and `G ⧸ ker ρ_{E,ℓ}`, at every prime

This is the **extraction** of `EllipticCurves.TateModule.ImageProfinite` to an arbitrary prime
`ℓ`. It is the eighth link in the chain `EllipticCurves.Torsion.PrimaryBasis` →
`EllipticCurves.TateModule.PrimaryFree` → `EllipticCurves.TateModule.PrimaryMatrixRep` →
`EllipticCurves.TateModule.PrimaryDeterminant` →
`EllipticCurves.TateModule.PrimaryMatrixRepBasisChange` →
`EllipticCurves.TateModule.PrimaryMatrixContinuity` → `EllipticCurves.TateModule.PrimaryImage` →
here, and it contains **no new mathematics**: every proof below is the `ℓ = 2` proof with `2`
replaced by `ℓ`, or a citation of `EllipticCurves.TateModule.PrimaryImage`.

`EllipticCurves.TateModule.ImageProfinite` becomes the `ℓ = 2` instantiation, and
`EllipticCurves.TateModule.ImageProfiniteThree` is the `ℓ = 3` one.

## What moved here, and why the import graph forced it

⚠️ **Ten declarations were moved out of `EllipticCurves.TateModule.ImageProfinite` rather than
twinned**, with their statements, their proofs and their namespaces byte-identical. Nine of them
were already stated at an arbitrary prime `p` and one mentions no prime at all, so twinning them
would have been pure duplication — but *leaving* them where they stood was not an option either,
and the reason is the import graph and not their genericity:

```
PrimaryImage.lean  ←  this file  ←  ImageProfinite.lean   (ℓ = 2 instantiation)
                                 ←  ImageProfiniteThree.lean
```

The instantiation layers import this file; this file cannot import them. Every statement below
about `im ρ_{E,ℓ}` needs `Matrix.GeneralLinearGroup.profiniteGrpPadicInt` and
`PadicInt.profiniteGrpUnits` as the ambient profinite objects, so those two — and the six
instances they rest on, and `WeierstrassCurve.Affine.profiniteGrpGalois`, which the categorical
statement needs as its source — have to be *upstream* of the generic statements, not beside them.
⚠️ That argument reaches **nine** of the ten. The tenth,
`Matrix.GeneralLinearGroup.infinite_padicInt`, is consumed by no statement in this file; it moved
for the *twin's* sake, because `EllipticCurves.TateModule.ImageProfiniteThree`'s non-vacuity
certificate cites it and does not import `EllipticCurves.TateModule.ImageProfinite`.

⚠️ *Genericity is a property of a statement; position is a property of the import graph, and only
the second decides whether a generic file can reach a declaration.* The ten are:

* `_root_`: `MulOpposite.instTotallyDisconnectedSpace`, `Units.instTotallyDisconnectedSpace`;
* `Matrix`: `instCompactSpace`, `instTotallyDisconnectedSpace`;
* `Matrix.GeneralLinearGroup`: `compactSpace_padicInt`, `totallyDisconnectedSpace_padicInt`,
  `profiniteGrpPadicInt`, `infinite_padicInt`;
* `PadicInt`: `profiniteGrpUnits`;
* `WeierstrassCurve.Affine`: `profiniteGrpGalois`.

⚠️ **Eight of the ten arrived with their docstrings byte-identical as well. Two did not, and
neither change is cosmetic:**

* `Matrix.GeneralLinearGroup.profiniteGrpPadicInt` promised that *"nothing here is `2`-primary, so
  this is what an odd-`ℓ` development **will consume** unchanged"*. This file is that development,
  so the promise is written in the present tense here.
* `Matrix.GeneralLinearGroup.infinite_padicInt` cited the direct non-discreteness proof in
  `EllipticCurves.TateModule.MatrixContinuity`, which has not held it since it was extracted to
  `EllipticCurves.TateModule.PrimaryMatrixContinuity`. ⚠️ *A citation can go stale before the
  declaration carrying it moves, and a file reporting its arrivals as unchanged is the last place
  a reader would look for the repair.* Hence these two bullets rather than a bare
  *"byte-identical"*.

⚠️ The first four are **Mathlib gaps in root namespaces**, upstreamable as written. Moving them
between files of this development does not change that and does not make them this file's
mathematics. The analysis of *why* Mathlib does not have them moved with them, and is the next
section: it was written in `EllipticCurves.TateModule.ImageProfinite`, and leaving it behind would
have left a reader of these instances pointed at a file that is now downstream of them.

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
  `CompactSpace (GL (Fin 2) ℤ_[p])` is not found on the pin.

All four are stated in root Mathlib namespaces and are upstreamable as written; none mentions a
curve. With them in scope, `CompactSpace`, `TotallyDisconnectedSpace`, `T2Space` and
`IsTopologicalGroup` for `GL n ℤ_[p]` are all found by instance search.

## Naming

`EllipticCurves.TateModule.PrimaryMatrixRep`'s settled rule — *the generic name is the `ℓ = 2` name
with `Two` dropped* — is used for the **nine** rep and categorical rows (seven about
`galoisRepMatrix` and the quotient, two categorical). ⚠️ **The remaining six — the determinant rows
— are the exception, and the choice is deliberate.** At `ℓ = 2` the two determinant families are
distinguished by a **prime**: `closedSubgroupRangeGaloisDetTwo` takes a basis and
`closedSubgroupRangeGaloisDetTwo'` takes `[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]` and `h2` instead.
Dropping `Two` would give `…GaloisDet` and `…GaloisDet'`, and the prime would then be the only
thing distinguishing two hypothesis shapes that are *not* the `ℓ = 2` ones: generically the second
family takes `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`, which is what
`EllipticCurves.TateModule.PrimaryImage` spells `_of_nonempty`. So this file uses **`_of_basis` and
`_of_nonempty`**, matching the file immediately below it, whose `isClosed_range_galoisDet_of_basis`
and `isClosed_range_galoisDet_of_nonempty` are the two inputs these rows consume.

⚠️ The instantiation layers do *not* inherit that choice: `EllipticCurves.TateModule.ImageProfinite`
keeps all fifteen `Two` names and statements byte-identical, and
`EllipticCurves.TateModule.ImageProfiniteThree` twins those names with `Two` replaced by `Three`,
prime included. A twin's job is to be the `ℓ = 2` name at `ℓ = 3`; renaming it would put the two
primes on different footings for every downstream file that extends by pattern.

## The universe restriction, and it is inherited by exactly two rows

`profiniteGrpHomGaloisRepMatrix` and `profiniteGrpHomGaloisRepMatrix_apply` carry `S F : Type`, and
so does `profiniteGrpGalois`, which they consume. `Category ProfiniteGrp.{u}` lives at a fixed
universe, so the `⟶` form needs `F ≃ₐ[S] F` and `GL (Fin 2) ℤ_[ℓ]` in the *same* universe. The
restriction is the category's, not the mathematics'.

⚠️ **The other thirteen of the fifteen are universe-polymorphic and stay that way.** Dropping the
whole file to
`Type` would compile, would leave every consumer working, and would be a real weakening that no
build could see — the same shape as a namespace-preserving generalisation being indistinguishable
from a silent deletion. `continuousGaloisRepMatrix` is the universe-polymorphic carrier of the same
content; reach for it unless the categorical packaging is what is wanted.

## Hypotheses

The variable block is `EllipticCurves.TateModule.PrimaryImage`'s, unchanged:
`[Algebra.IsIntegral S F]` and `[IsGalois S F]` throughout. Neither `continuousGaloisRepMatrix`
nor `continuousGaloisRepMatrix_apply` carries `[IsGalois S F]` — continuity of `ρ_{E,ℓ}` needs no
compactness of `G` — and `profiniteGrpGalois`, which is not about the curve at all, needs no
`[Algebra.IsIntegral S F]`: `ProfiniteGrp.of (F ≃ₐ[S] F)` elaborates with `[IsGalois S F]` in
its place.

⚠️ **`profiniteGrpGalois` carries `[Algebra.IsIntegral S F]` all the same: the `omit` written
ahead of it does not remove it.** Read the signature, not the source — `#check @profiniteGrpGalois`
prints `… → [Algebra.IsIntegral S F] → [IsGalois S F] → ProfiniteGrp`. The cause is Lean's rather
than this file's: `omit … in` is applied only when the declaration that follows is a `theorem`
(`Lean.Elab.MutualDef`, `withHeaderSecVars`), so ahead of a `def`, an `abbrev` or an `instance` it
parses, is accepted and is **silently ignored** — no error, no `unusedSectionVars` report, nothing
the build can see. What such a declaration keeps is exactly the section variables its term uses,
and this term does use the binder: with the variable in scope, the `TotallyDisconnectedSpace`
argument of `ProfiniteGrp.of` is synthesised through it (visible under `pp.explicit`), whereas
with the variable out of scope the same term elaborates through `[IsGalois S F]`. Nothing
downstream pays for it, because `[IsGalois S F]` supplies `Algebra.IsIntegral S F` by instance
search, so a caller carrying the hypothesis this file assumes anyway gets the binder for free.

⚠️ The same reading is owed to the two `omit`s on the `continuousGaloisRepMatrix` rows.
`continuousGaloisRepMatrix_apply` is a `theorem`, so its `omit` is what drops `[IsGalois S F]`;
`continuousGaloisRepMatrix` is a `def`, so there the clean signature is the term's doing and the
`omit` beside it is decoration. **A prose claim about a signature is checkable by `#check @` and
by nothing else** — no build, no linter and no grep sees this class of defect, which is why this
section states what the elaborator prints rather than what the source asks for.

⚠️ `[IsAlgClosed F]`, `[(W'⁄F).IsElliptic]` and `h2` do **not** appear anywhere in this file: at an
arbitrary prime the basis-free determinant rows take `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`
directly, and it is the instantiation layers that pay for it — `h2` at `ℓ = 2` and `h2` together
with `h3` at `ℓ = 3`.

## Non-degeneracy

Every statement here is true of the trivial group, and no theorem about `G` alone can exclude that:
it is a fact about `F / S`. The certificates are about the *ambient* group, where the content is,
and two of the three are in this file:

* `Matrix.GeneralLinearGroup.infinite_padicInt` — `GL₂(ℤ_[p])` is infinite, so "profinite" here is
  not a disguised "finite".
* `Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup`
  (`EllipticCurves.TateModule.PrimaryImage`) — `GL₂(ℤ_[p])` has subgroups that are not closed, so
  `ProfiniteGrp.ofClosedSubgroup` is being applied to a hypothesis that is not free.
* `Matrix.GeneralLinearGroup.not_discreteTopology_padicInt`
  (`EllipticCurves.TateModule.PrimaryMatrixContinuity`) — it is not discrete either. Given
  `compactSpace_padicInt` below, non-discreteness is now a *corollary* of infiniteness, since a
  compact discrete space is finite; the direct proof is kept deliberately because it needs no
  compactness.

## Scope

* ⚠️ **Openness** of the image is not proved and is not approached. That is Serre's theorem, and it
  is **false** for curves with complex multiplication. Compact and closed are the *hypotheses* an
  open-image theorem starts from.
* ⚠️ **Surjectivity and injectivity of `ρ_{E,ℓ}` stay out.** An isomorphism onto `G ⧸ ker ρ` says
  nothing about whether `ker ρ` is trivial.
* ⚠️ **Nothing here identifies `det ρ_{E,ℓ}` with the cyclotomic character.**
  `profiniteGrpRangeGaloisDet_of_basis` will look exactly like progress towards it and is not:
  knowing that the image of a character is closed says nothing about *which* character it is. The
  `ℓ`-adic identification needs the Weil pairing on `E[ℓ^k]` for **every** `k`, and this
  development has the pairing at `n = 2` and `n = 3` only. The **mod-`ℓ`** identity is a different
  statement about a different object — valued in `(ZMod ℓ)ˣ`, not `ℤ_[ℓ]ˣ` — and it landed
  separately as `EllipticCurves.FunctionField.WeilPairingDeterminantCharacter`.
* ⚠️ **This file is usable at `ℓ ≥ 5` only as far as its inputs are.** Everything that takes a
  basis is available at every prime today; the two `_of_nonempty` rows need
  `Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])`, which at `ℓ ≥ 5` is gated on `[ℓ]`-surjectivity and
  `#E[ℓ^k]`, i.e. on the general multiplication-by-`n` coordinate formula. What is missing at
  `ℓ ≥ 5` is a *basis to feed this file*, not a theorem in it.

## Main statements

* `Matrix.GeneralLinearGroup.profiniteGrpPadicInt`
* `WeierstrassCurve.Affine.profiniteGrpRangeGaloisRepMatrix`
* `WeierstrassCurve.Affine.profiniteGrpQuotientKerGaloisRepMatrix`
* `WeierstrassCurve.Affine.profiniteGrpHomGaloisRepMatrix`

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
`CompactSpace (Matrix (Fin 2) (Fin 2) ℤ_[2])` is not found without this. Upstreamable.

⚠️ **This instance used to carry `[Finite m] [Finite n]` and both were dead** — neither occurred in
the remainder of the type nor in the value, measured on the elaborated environment at `2e44940`
(`#1272`).  `Pi.compactSpace` is **Tychonoff**: an arbitrary product of compact spaces is compact,
with no cardinality condition on the index. Dropping them matters for the upstream candidacy this
docstring already claims — an instance with unnecessary hypotheses simply fires less often. -/
instance instCompactSpace [CompactSpace R] : CompactSpace (Matrix m n R) :=
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
nothing here is `2`-primary, so this is what an odd-`ℓ` development consumes unchanged.

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
`EllipticCurves.TateModule.PrimaryMatrixContinuity`, which needs no compactness. -/
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
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable [Algebra.IsIntegral S F] [IsGalois S F]
variable (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))

/-! ### The image of `ρ_{E,ℓ}` as a profinite group -/

/-- The image of `ρ_{E,ℓ}` packaged as a `ClosedSubgroup` of `GL₂(ℤ_[ℓ])`, which is the input
`ProfiniteGrp.ofClosedSubgroup` wants. Closedness is `isClosed_range_galoisRepMatrix`
(`EllipticCurves.TateModule.PrimaryImage`), and it is not free: `GL₂(ℤ_[ℓ])` has subgroups that are
not closed (`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup`, stated at an arbitrary
prime in the same file).

⚠️ **Deletion test**, measured on this file as committed. Replacing the structure literal by
`by refine { toSubgroup := (galoisRepMatrix b).range, isClosed' := ?_ }` leaves, copy-paste:

```
error: unsolved goals
S : Type u_1
F : Type u_2
inst✝⁶ : Field S
inst✝⁵ : Field F
inst✝⁴ : DecidableEq F
inst✝³ : Algebra S F
W' : Affine S
ℓ : ℕ
inst✝² : Fact (Nat.Prime ℓ)
inst✝¹ : Algebra.IsIntegral S F
inst✝ : IsGalois S F
b : Module.Basis (Fin 2) ℤ_[ℓ] ↥((W'⁄F).tateModule ℓ)
⊢ IsClosed (galoisRepMatrix b).range.carrier
```

⚠️ The residual is a **goal**, not a type mismatch, and nothing in that context proves it: it is
`isClosed_range_galoisRepMatrix`, from `EllipticCurves.TateModule.PrimaryImage`. ⚠️ It is **one of
five** imported mathematical inputs, not the only one — the others are `continuous_galoisRepMatrix`,
`quotientKerContinuousMulEquivRange`, `isClosed_range_galoisDet_of_basis` and
`isClosed_range_galoisDet_of_nonempty`. One mechanical edit accompanies the deletion and adds no
information (`where` becomes `by refine { … }`, so that a hole is legal where the field was).
⚠️ **There is a knock-on and it is disclosed**: with this declaration erroring, the
`unusedSectionVars` linter then reports `[Algebra.IsIntegral S F]` and `[IsGalois S F]` as unused in
`coe_profiniteGrpRangeGaloisRepMatrix` below, because a failed declaration carries no dependencies.
That warning is **not** part of the deletion test; it is what a knock-on looks like here. -/
noncomputable def closedSubgroupRangeGaloisRepMatrix : ClosedSubgroup (GL (Fin 2) ℤ_[ℓ]) where
  toSubgroup := (galoisRepMatrix b).range
  isClosed' := isClosed_range_galoisRepMatrix b

/-- **The image of `ρ_{E,ℓ}` is a profinite group.**

A closed subgroup of a profinite group is profinite, and `GL₂(ℤ_[ℓ])` is profinite by
`Matrix.GeneralLinearGroup.profiniteGrpPadicInt`. Together with closedness of the kernel, this
presents the `ℓ`-adic representation of `E` as a map of profinite groups with profinite image.

⚠️ **Closedness of the kernel has no `ℓ`-generic form to cite**, so this docstring names no
declaration where the `ℓ = 2` one named `isClosed_ker_galoisRepMatrixTwo`: the tree has
`WeierstrassCurve.Affine.isClosed_ker_galoisRepMatrixTwo` and
`WeierstrassCurve.Affine.isClosed_ker_galoisRepMatrixThree`
(`EllipticCurves.TateModule.MatrixRepBasisChange` and
`EllipticCurves.TateModule.MatrixRepBasisChangeThree`), and no statement of either at an arbitrary
prime. *A generic file cannot cite a generic name that does not exist.*
`EllipticCurves.TateModule.ImageProfinite` names its own, at `ℓ = 2`. -/
noncomputable def profiniteGrpRangeGaloisRepMatrix : ProfiniteGrp :=
  ProfiniteGrp.ofClosedSubgroup (G := Matrix.GeneralLinearGroup.profiniteGrpPadicInt ℓ (Fin 2))
    (closedSubgroupRangeGaloisRepMatrix b)

/-- The carrier of `profiniteGrpRangeGaloisRepMatrix` is the image of `ρ_{E,ℓ}`, pinning the object
to the subgroup it is meant to be. -/
theorem coe_profiniteGrpRangeGaloisRepMatrix :
    (profiniteGrpRangeGaloisRepMatrix b : Type _) = (galoisRepMatrix b).range := rfl

/-- **`G ⧸ ker ρ_{E,ℓ}` is a profinite group.**

Transported along `quotientKerContinuousMulEquivRange`
(`EllipticCurves.TateModule.PrimaryImage`), used in the `.symm` direction. The transport needs a
*homeomorphism*: compactness and total disconnectedness do not travel along a bare `MulEquiv`, and
a continuous bijective homomorphism is not a homeomorphism in general. This is where the
topological first isomorphism theorem earns its keep. -/
noncomputable def profiniteGrpQuotientKerGaloisRepMatrix : ProfiniteGrp :=
  ProfiniteGrp.ofContinuousMulEquiv (G := profiniteGrpRangeGaloisRepMatrix b)
    (quotientKerContinuousMulEquivRange b).symm

/-- The carrier of `profiniteGrpQuotientKerGaloisRepMatrix` is the quotient `G ⧸ ker ρ_{E,ℓ}`. -/
theorem coe_profiniteGrpQuotientKerGaloisRepMatrix :
    (profiniteGrpQuotientKerGaloisRepMatrix b : Type _)
      = ((F ≃ₐ[S] F) ⧸ (galoisRepMatrix b).ker) := rfl

/-! ### `ρ_{E,ℓ}` as a continuous homomorphism -/

omit [IsGalois S F] in
/-- **`ρ_{E,ℓ}` bundled as a continuous monoid homomorphism** `G →ₜ* GL₂(ℤ_[ℓ])`.

Universe-polymorphic, and needs no `[IsGalois S F]`: continuity is
`EllipticCurves.TateModule.PrimaryMatrixContinuity`'s `continuous_galoisRepMatrix`, which holds for
every basis with no hypothesis at all. Prefer this to the categorical
`profiniteGrpHomGaloisRepMatrix` unless the category is what is wanted. -/
noncomputable def continuousGaloisRepMatrix :
    ContinuousMonoidHom (F ≃ₐ[S] F) (GL (Fin 2) ℤ_[ℓ]) where
  __ := galoisRepMatrix b
  continuous_toFun := continuous_galoisRepMatrix b

omit [IsGalois S F] in
@[simp]
theorem continuousGaloisRepMatrix_apply (σ : F ≃ₐ[S] F) :
    continuousGaloisRepMatrix b σ = galoisRepMatrix b σ := rfl

/-! ### The determinant character -/

/-- The image of `det ρ_{E,ℓ}` as a closed subgroup of `ℤ_[ℓ]ˣ`.

Takes a basis even though `galoisDet` is basis-free, because continuity of `galoisDet` is proved
through one. See `closedSubgroupRangeGaloisDet_of_nonempty` for the form that discharges it.

⚠️ `nolint defsWithUnderscore` (`#1277`): `_of_basis` names the hypothesis, exactly as the theorem
`isClosed_range_galoisDet_of_basis` this is built from does, and as the theorem
`coe_profiniteGrpRangeGaloisDet_of_basis` below does. The four `_of_basis` / `_of_nonempty` names in
this section are one naming decision, not four. -/
@[nolint defsWithUnderscore]
noncomputable def closedSubgroupRangeGaloisDet_of_basis
    (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) : ClosedSubgroup ℤ_[ℓ]ˣ where
  toSubgroup := (galoisDet (W' := W') (F := F) (ℓ := ℓ)).range
  isClosed' := isClosed_range_galoisDet_of_basis b

/-- **The image of the determinant character `det ρ_{E,ℓ} : G →* ℤ_[ℓ]ˣ` is a profinite group.**

This is the layer the (Weil-pairing gated) identification of `det ρ_{E,ℓ}` with the cyclotomic
character will consume. ⚠️ Nothing here identifies it.

⚠️ `nolint defsWithUnderscore` (`#1277`) — see `closedSubgroupRangeGaloisDet_of_basis`. -/
@[nolint defsWithUnderscore]
noncomputable def profiniteGrpRangeGaloisDet_of_basis
    (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) : ProfiniteGrp :=
  ProfiniteGrp.ofClosedSubgroup (G := PadicInt.profiniteGrpUnits ℓ)
    (closedSubgroupRangeGaloisDet_of_basis b)

/-- The carrier of `profiniteGrpRangeGaloisDet_of_basis` is the image of `det ρ_{E,ℓ}`. -/
theorem coe_profiniteGrpRangeGaloisDet_of_basis
    (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) :
    (profiniteGrpRangeGaloisDet_of_basis b : Type _)
      = (galoisDet (W' := W') (F := F) (ℓ := ℓ)).range := rfl

/-- The image of `det ρ_{E,ℓ}` as a closed subgroup of `ℤ_[ℓ]ˣ`, with no basis supplied: a basis
exists as soon as `T_ℓE` is `ℤ_[ℓ]`-linearly `ℤ_[ℓ]²`, and `IsClosed` is a `Prop`, so the choice
can be discharged. ⚠️ This is where the `ℓ = 2` and `ℓ = 3` layers pay differently: `h2` alone at
`ℓ = 2`, and `h2` together with `h3` at `ℓ = 3`.

⚠️ `nolint defsWithUnderscore` (`#1277`) — see `closedSubgroupRangeGaloisDet_of_basis`. -/
@[nolint defsWithUnderscore]
noncomputable def closedSubgroupRangeGaloisDet_of_nonempty
    (h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) : ClosedSubgroup ℤ_[ℓ]ˣ where
  toSubgroup := (galoisDet (W' := W') (F := F) (ℓ := ℓ)).range
  isClosed' := isClosed_range_galoisDet_of_nonempty h

/-- **The image of `det ρ_{E,ℓ}` is a profinite group**, basis-free form.

⚠️ `nolint defsWithUnderscore` (`#1277`) — see `closedSubgroupRangeGaloisDet_of_basis`. -/
@[nolint defsWithUnderscore]
noncomputable def profiniteGrpRangeGaloisDet_of_nonempty
    (h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) : ProfiniteGrp :=
  ProfiniteGrp.ofClosedSubgroup (G := PadicInt.profiniteGrpUnits ℓ)
    (closedSubgroupRangeGaloisDet_of_nonempty h)

/-- The carrier of `profiniteGrpRangeGaloisDet_of_nonempty` is the image of `det ρ_{E,ℓ}`. -/
theorem coe_profiniteGrpRangeGaloisDet_of_nonempty
    (h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) :
    (profiniteGrpRangeGaloisDet_of_nonempty h : Type _)
      = (galoisDet (W' := W') (F := F) (ℓ := ℓ)).range := rfl

/-! ### The categorical statement

`Category ProfiniteGrp.{u}` is at a fixed universe, so the morphism form needs `F ≃ₐ[S] F` and
`GL (Fin 2) ℤ_[ℓ]` in the same universe. That forces `S F : Type`. The restriction is the
category's, not the mathematics'; `continuousGaloisRepMatrix` above says the same thing without
it. -/

section SmallUniverse

variable {S F : Type} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable [Algebra.IsIntegral S F] [IsGalois S F]
variable (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))

omit [Algebra.IsIntegral S F] in
/-- **`Gal(F/S)` as an object of `ProfiniteGrp`.** Mathlib already supplies every instance this
needs — `CompactSpace`, `TotallyDisconnectedSpace` and `IsTopologicalGroup` for `F ≃ₐ[S] F` under
`[IsGalois S F]` — so nothing is proved here; the point is to name the object.

⚠️ **The `omit` ahead of this declaration is inert, and the signature keeps
`[Algebra.IsIntegral S F]`.** `omit … in` acts on a `theorem` and is silently ignored ahead of an
`abbrev`; `#check @profiniteGrpGalois` is the only thing that sees the difference. Harmless —
`[IsGalois S F]` supplies the binder by instance search — but do not read the `omit` as removing
it. This module's **Hypotheses** section carries the measurement and the mechanism. -/
noncomputable abbrev profiniteGrpGalois : ProfiniteGrp := ProfiniteGrp.of (F ≃ₐ[S] F)

/-- **`ρ_{E,ℓ}` is a morphism of profinite groups** `Gal(F/S) ⟶ GL₂(ℤ_[ℓ])`.

This is the classical statement of the `ℓ`-adic representation, assembled from every piece on this
front: `T_ℓE` free of rank `2`, the matrix representation, its continuity, and compactness of
`Gal(F/S)` (Mathlib, under `[IsGalois S F]`).

It says nothing about the image beyond what `profiniteGrpRangeGaloisRepMatrix` says: not
surjectivity, not injectivity, and certainly not openness. -/
noncomputable def profiniteGrpHomGaloisRepMatrix :
    profiniteGrpGalois (S := S) (F := F) ⟶
      Matrix.GeneralLinearGroup.profiniteGrpPadicInt ℓ (Fin 2) :=
  CategoryTheory.ConcreteCategory.ofHom (continuousGaloisRepMatrix b)

/-- The morphism `profiniteGrpHomGaloisRepMatrix` computes `ρ_{E,ℓ}`, so it cannot drift to some
other map of profinite groups. -/
@[simp]
theorem profiniteGrpHomGaloisRepMatrix_apply (σ : F ≃ₐ[S] F) :
    profiniteGrpHomGaloisRepMatrix b σ = galoisRepMatrix b σ := rfl

end SmallUniverse

end WeierstrassCurve.Affine
