/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.MatrixContinuity
import EllipticCurves.TateModule.OpenKernel
import EllipticCurves.TateModule.PrimaryImage

/-!
# The image of `ρ_{E,2}` is a closed subgroup of `GL₂(ℤ_[2])`

`EllipticCurves.TateModule.MatrixContinuity` proves that the `2`-adic matrix representation
`galoisRepMatrixTwo b : G →* GL₂(ℤ_[2])` is continuous, for **every** basis `b` of `T₂E`. This file
draws the consequences for its *image*, which every earlier file on this front explicitly excluded,
always with the same reason:

> "Anything about the image of `ρ_ℓ` — `G` is not known compact here."

That exclusion is discharged here, and it is worth being precise about how: **by hypothesis, not by
proof.** Mathlib's `InfiniteGalois` development supplies

```lean
instance [IsGalois k K] : CompactSpace Gal(K/k)
```

and `Gal(K/k)` is notation for `K ≃ₐ[k] K`, which is exactly the group `G` this development uses.
So the whole file costs one extra instance argument, `[IsGalois S F]`, on the existing variable
block. That is a hypothesis on the extension `F / S` — it says nothing about the curve, and it is
not automatic: for `F` an algebraic closure of an *imperfect* `S` the extension is normal but not
separable, and the instance does not apply.

## What is proved

* `isCompact_range_galoisRepMatrixTwo`, `isClosed_range_galoisRepMatrixTwo` — the image of
  `ρ_{E,2}` is a compact, hence closed, subgroup of `GL₂(ℤ_[2])`. This is the classical statement,
  and it is the hypothesis every Serre-style open-image theorem starts from.
* ⚠️ `quotientKerContinuousMulEquivRange` — the **topological** first isomorphism theorem
  `G ⧸ ker ρ ≃ₜ* im ρ` — **is no longer stated in this file**, and it never had a `Two` in its
  name. It is stated at an arbitrary prime in `EllipticCurves.TateModule.PrimaryImage`, at the same
  full name, and `quotientKerContinuousMulEquivRange b` for a basis `b` of `T₂E` is exactly what it
  always was. Note that it is *false* for a general continuous bijective homomorphism; it is
  compactness of `G` that supplies the inverse. Combined with `isClosed_ker_galoisRepTwo`
  (`EllipticCurves.TateModule.OpenKernel`), `ker ρ` is a closed normal subgroup of a compact group,
  so `G ⧸ ker ρ` — and therefore the image — is itself a compact Hausdorff group.
* `isCompact_range_galoisDetTwo`, `isClosed_range_galoisDetTwo` — the same for the determinant
  character `det ρ_{E,2} : G →* ℤ_[2]ˣ`, which is the form the (Weil-pairing-gated) comparison with
  the cyclotomic character will want.

## Non-degeneracy: why "closed" is not a formality

`GL₂(ℤ_[2])` is itself compact, so inside it *closed* and *compact* agree, and a reader may suspect
that `isClosed_range_galoisRepMatrixTwo` says nothing at all. The honest answer is a
counterexample, and it is proved rather than asserted — ⚠️ **but no longer in this file**, as the
paragraph after next records:

`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup` exhibits a subgroup of `GL₂(ℤ_[p])`
that is **not** closed — the unipotent line `n ↦ !![1, n; 0, 1]` restricted to `n : ℤ`. It is the
image of `ℤ` in `ℤ_[p]`, which is dense (`PadicInt.denseRange_intCast`) and proper
(`PadicInt.range_intCast_ne_univ`), transported along the injective continuous homomorphism
`upperRightHom`. So a subgroup of `GL₂(ℤ_[2])` given as the image of a group homomorphism is *not*
closed for free, and what makes the image of `ρ_{E,2}` closed is precisely the compactness of its
source.

⚠️ **That counterexample no longer lives in this file and is no longer about `ℤ_[2]`.** It and its
three supporting declarations are stated at an arbitrary prime `p` in
`EllipticCurves.TateModule.PrimaryImage`; this file cites them. ⚠️ **Generalising them was not
free**, and one clause of this paragraph is retired by that: it used to say
`PadicInt.range_intCast_ne_univ` was *"proved from `3` being a unit of `ℤ_[2]`"*, which was true and
`p`-specific — `3` is not a unit of `ℤ_[3]`. The generic proof uses `p + 1`.

That counterexample also isolates which hypothesis is load-bearing: `ℤ → ℤ_[p]` is an injective
continuous group homomorphism with non-closed image, and the only thing it lacks is compactness of
the source.

As in `EllipticCurves.TateModule.OpenKernel` and `EllipticCurves.TateModule.MatrixContinuity`,
every statement here about `G` remains true when `G` is trivial, and no theorem about `G` alone can
exclude that — it is a fact about `F / S`, not about the curve. The certificate offered instead is
the one above, which is about the ambient group `GL₂(ℤ_[2])`, together with
`Matrix.GeneralLinearGroup.not_discreteTopology_padicInt`.

## Scope

⚠️ **This file is the `ℓ = 2` layer, not the `ℓ = 2` case.** The ten statements below are the
`ℓ = 2` instantiations of `EllipticCurves.TateModule.PrimaryImage`, which states them at an
arbitrary prime; every proof here is one line and no argument is made twice. The `ℓ = 3`
instantiation is `EllipticCurves.TateModule.ImageThree`.

⚠️ **Two successive versions of this paragraph were wrong and both are recorded rather than
deleted.** The first read *"for the usual reason: `galoisRepMatrixTwo` needs a basis of `T₂E` and
the basis comes from the `2`-primary tower"*; both halves of it remain true of `galoisRepMatrixTwo`,
but they stopped being a *reason* once `galoisRepMatrixThree` existed
(`EllipticCurves.TateModule.MatrixRepThree`) over a basis of `T₃E`
(`EllipticCurves.TateModule.FreeThree`). The second read *"**So nothing gates the `ℓ = 3` layer of
this file; it simply has not been written**, and that is a follow-up"*: ⚠️ **it has now been
written**, and it is `EllipticCurves.TateModule.ImageThree`. The prediction was correct and has
been paid.

⚠️ At `ℓ ≥ 5` there is still a genuine gap and it is `T_ℓE ≅ ℤ_ℓ²` itself, which needs `#E[ℓ^k]` —
⚠️ a count that is no longer owed: `card_torsion_pow_mul_self_of_odd`
(`EllipticCurves.Torsion.PrimaryTowerOdd`) supplies it at every odd `ℓ` with `(ℓ : F) ≠ 0`, so what
is left is building the equivalence on top of it (`#268`), not proving a count.
⚠️ This sentence used to add *"and `[ℓ]`-surjectivity, i.e. the general coordinate formula
`x(nP) = Φₙ/ΨSqₙ`"*, and both clauses are stale: surjectivity holds at every nonzero index with
`(2 : F) ≠ 0` (`nsmul_surjective_of_two_ne_zero`, `EllipticCurves.Torsion.TwoTorsionOrder`) and the
formula is proved at every index with `(2 : F) ≠ 0` (`hasXCoordFormula_of_two_ne_zero`,
`EllipticCurves.Torsion.NsmulOrder`).  `EllipticCurves.Torsion.PrimaryTower` carries the gate list
for the count.  Everything is stated for a base change `W'⁄F`, matching
`EllipticCurves.TateModule.MatrixRep` and `EllipticCurves.TateModule.MatrixContinuity`.

Not proved here: **openness** of the image — that is Serre's theorem, it is *false* for curves with
complex multiplication, and nothing about compactness approaches it; **surjectivity** of `ρ_{E,2}`,
or any lower bound on the image; **injectivity** of `ρ_{E,2}` — an isomorphism onto `G ⧸ ker ρ`
says nothing about whether `ker ρ` is trivial; the identification of `det ρ_{E,2}` with the
cyclotomic character, which is Weil-pairing gated; and the profinite packaging, which is
`EllipticCurves.TateModule.ImageProfinite`. ⚠️ The clause that used to follow —
*"and is still `ℓ = 2` only"* — is retired: that file is now the `ℓ = 2` layer of
`EllipticCurves.TateModule.PrimaryImageProfinite`, with an `ℓ = 3` layer in
`EllipticCurves.TateModule.ImageProfiniteThree`.

## Main statements

* `WeierstrassCurve.Affine.isClosed_range_galoisRepMatrixTwo`
* `WeierstrassCurve.Affine.isClosed_range_galoisDetTwo`

⚠️ `WeierstrassCurve.Affine.quotientKerContinuousMulEquivRange` and
`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup` were listed here and are now in
`EllipticCurves.TateModule.PrimaryImage`, at the same names and covering every prime.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable [Algebra.IsIntegral S F] [IsGalois S F]
variable (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2))

/-! ### The image is compact and closed -/

omit [Algebra.IsIntegral S F] [IsGalois S F] in
/-- The underlying set of the subgroup `(galoisRepMatrixTwo b).range` is the set-theoretic range.

Purely a bridge: `MonoidHom.range` is a `Subgroup` and its coercion is not syntactically
`Set.range` of the coerced function, but every topological statement below is about the latter. -/
theorem coe_range_galoisRepMatrixTwo :
    ((galoisRepMatrixTwo b).range : Set (GL (Fin 2) ℤ_[2]))
      = Set.range (galoisRepMatrixTwo b) :=
  coe_range_galoisRepMatrix b

/-- **The image of `ρ_{E,2}` is compact.** `G = Gal(F/S)` is compact for the Krull topology
(Mathlib's `InfiniteGalois` instance, which needs `[IsGalois S F]`) and `ρ_{E,2}` is continuous
(`continuous_galoisRepMatrixTwo`, for any basis), so the image is a continuous image of a compact
space. -/
theorem isCompact_range_galoisRepMatrixTwo :
    IsCompact ((galoisRepMatrixTwo b).range : Set (GL (Fin 2) ℤ_[2])) :=
  isCompact_range_galoisRepMatrix b

/-- **The image of `ρ_{E,2}` is a closed subgroup of `GL₂(ℤ_[2])`.**

This is the classical statement, and the standing hypothesis of every theorem about the image of an
`ℓ`-adic representation. It is not a formality: `GL₂(ℤ_[2])` has subgroups that are not closed, and
`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup` exhibits one. ⚠️ That counterexample
is **not** in this file: it is stated at an arbitrary prime `p` in
`EllipticCurves.TateModule.PrimaryImage` and is cited here, exactly as
`EllipticCurves.TateModule.ImageThree` cites it at `ℓ = 3`. -/
theorem isClosed_range_galoisRepMatrixTwo :
    IsClosed ((galoisRepMatrixTwo b).range : Set (GL (Fin 2) ℤ_[2])) :=
  isClosed_range_galoisRepMatrix b

/-- The image of `ρ_{E,2}`, as a topological group in its own right, is compact. -/
instance compactSpace_range_galoisRepMatrixTwo :
    CompactSpace ((galoisRepMatrixTwo b).range) :=
  compactSpace_range_galoisRepMatrix b

/-- `ρ_{E,2}` is a closed map: it carries closed subgroups of `G` to closed subgroups of
`GL₂(ℤ_[2])`, not merely to subgroups. -/
theorem isClosedMap_galoisRepMatrixTwo : IsClosedMap (galoisRepMatrixTwo b) :=
  isClosedMap_galoisRepMatrix b

/-! ### The topological first isomorphism theorem -/

omit [IsGalois S F] in
/-- `ρ_{E,2}` corestricted to its image is continuous. -/
theorem continuous_rangeRestrict_galoisRepMatrixTwo :
    Continuous fun σ : F ≃ₐ[S] F =>
      (⟨galoisRepMatrixTwo b σ, ⟨σ, rfl⟩⟩ : (galoisRepMatrixTwo b).range) :=
  continuous_rangeRestrict_galoisRepMatrix b

/-! ### The determinant character -/

/-- The image of `det ρ_{E,2} : G →* ℤ_[2]ˣ` is compact. A basis is taken because continuity of
`galoisDetTwo` is proved through one, even though `galoisDetTwo` itself is basis-free. -/
theorem isCompact_range_galoisDetTwo_of_basis
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :
    IsCompact (Set.range (galoisDetTwo (W' := W') (F := F))) :=
  isCompact_range_galoisDet_of_basis b

/-- The image of `det ρ_{E,2}` is a closed subgroup of `ℤ_[2]ˣ`. -/
theorem isClosed_range_galoisDetTwo_of_basis
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :
    IsClosed (Set.range (galoisDetTwo (W' := W') (F := F))) :=
  isClosed_range_galoisDet_of_basis b

section Two

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- The image of `det ρ_{E,2}` is compact, with no basis supplied: over an algebraically closed
field of characteristic `≠ 2` one exists, and compactness is a `Prop`. -/
theorem isCompact_range_galoisDetTwo (h2 : (2 : F) ≠ 0) :
    IsCompact (Set.range (galoisDetTwo (W' := W') (F := F))) :=
  isCompact_range_galoisDet_of_nonempty (tateModule.nonempty_tateModuleEquivProd h2)

/-- **The image of the determinant character is a closed subgroup of `ℤ_[2]ˣ`.** This is the layer
the identification of `det ρ_{E,2}` with the cyclotomic character will consume; that identification
needs the Weil pairing and is not proved in this development. -/
theorem isClosed_range_galoisDetTwo (h2 : (2 : F) ≠ 0) :
    IsClosed (Set.range (galoisDetTwo (W' := W') (F := F))) :=
  isClosed_range_galoisDet_of_nonempty (tateModule.nonempty_tateModuleEquivProd h2)

end Two

end WeierstrassCurve.Affine
