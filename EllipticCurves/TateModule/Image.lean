/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.Determinant
import EllipticCurves.TateModule.MatrixContinuity
import EllipticCurves.TateModule.OpenKernel
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.ContinuousMonoidHom

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
* `quotientKerContinuousMulEquivRange` — the **topological** first isomorphism theorem for
  `ρ_{E,2}`: `G ⧸ ker ρ ≃ₜ* im ρ`, as topological groups. Note that this is *false* for a general
  continuous bijective homomorphism; it is compactness of `G` that supplies the inverse. Combined
  with `isClosed_ker_galoisRepTwo` (`EllipticCurves.TateModule.OpenKernel`), `ker ρ` is a closed
  normal subgroup of a compact group, so `G ⧸ ker ρ` — and therefore the image — is itself a
  compact Hausdorff group.
* `isCompact_range_galoisDetTwo`, `isClosed_range_galoisDetTwo` — the same for the determinant
  character `det ρ_{E,2} : G →* ℤ_[2]ˣ`, which is the form the (Weil-pairing-gated) comparison with
  the cyclotomic character will want.

## Non-degeneracy: why "closed" is not a formality

`GL₂(ℤ_[2])` is itself compact, so inside it *closed* and *compact* agree, and a reader may suspect
that `isClosed_range_galoisRepMatrixTwo` says nothing at all. The honest answer is a
counterexample, and it is proved below rather than asserted:

`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup` exhibits a subgroup of `GL₂(ℤ_[2])`
that is **not** closed — the unipotent line `n ↦ !![1, n; 0, 1]` restricted to `n : ℤ`. It is the
image of `ℤ` in `ℤ_[2]`, which is dense (`PadicInt.denseRange_intCast`) and proper
(`PadicInt.range_intCast_ne_univ`, proved from `3` being a unit of `ℤ_[2]`), transported along the
injective continuous homomorphism `upperRightHom`. So a subgroup of `GL₂(ℤ_[2])` given as the image
of a group homomorphism is *not* closed for free, and what makes the image of `ρ_{E,2}` closed is
precisely the compactness of its source.

That counterexample also isolates which hypothesis is load-bearing: `ℤ → ℤ_[2]` is an injective
continuous group homomorphism with non-closed image, and the only thing it lacks is compactness of
the source.

As in `EllipticCurves.TateModule.OpenKernel` and `EllipticCurves.TateModule.MatrixContinuity`,
every statement here about `G` remains true when `G` is trivial, and no theorem about `G` alone can
exclude that — it is a fact about `F / S`, not about the curve. The certificate offered instead is
the one above, which is about the ambient group `GL₂(ℤ_[2])`, together with
`Matrix.GeneralLinearGroup.not_discreteTopology_padicInt` on `main`.

## Scope

`ℓ = 2` only, for the usual reason: `galoisRepMatrixTwo` needs a basis of `T₂E` and the basis comes
from the `2`-primary tower. Everything is stated for a base change `W'⁄F`, matching
`EllipticCurves.TateModule.MatrixRep` and `EllipticCurves.TateModule.MatrixContinuity`.

Not proved here: **openness** of the image — that is Serre's theorem, it is *false* for curves with
complex multiplication, and nothing about compactness approaches it; **surjectivity** of `ρ_{E,2}`,
or any lower bound on the image; **injectivity** of `ρ_{E,2}` — an isomorphism onto `G ⧸ ker ρ`
says nothing about whether `ker ρ` is trivial; the identification of `det ρ_{E,2}` with the
cyclotomic character, which is Weil-pairing gated; and odd `ℓ`.

## Main statements

* `WeierstrassCurve.Affine.isClosed_range_galoisRepMatrixTwo`
* `WeierstrassCurve.Affine.quotientKerContinuousMulEquivRange`
* `WeierstrassCurve.Affine.isClosed_range_galoisDetTwo`
* `Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup`

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
      = Set.range (galoisRepMatrixTwo b) := by
  ext x; simp

/-- **The image of `ρ_{E,2}` is compact.** `G = Gal(F/S)` is compact for the Krull topology
(Mathlib's `InfiniteGalois` instance, which needs `[IsGalois S F]`) and `ρ_{E,2}` is continuous
(`continuous_galoisRepMatrixTwo`, for any basis), so the image is a continuous image of a compact
space. -/
theorem isCompact_range_galoisRepMatrixTwo :
    IsCompact ((galoisRepMatrixTwo b).range : Set (GL (Fin 2) ℤ_[2])) := by
  rw [coe_range_galoisRepMatrixTwo]
  exact isCompact_range (continuous_galoisRepMatrixTwo b)

/-- **The image of `ρ_{E,2}` is a closed subgroup of `GL₂(ℤ_[2])`.**

This is the classical statement, and the standing hypothesis of every theorem about the image of an
`ℓ`-adic representation. It is not a formality: `GL₂(ℤ_[2])` has subgroups that are not closed, and
`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup` below exhibits one. -/
theorem isClosed_range_galoisRepMatrixTwo :
    IsClosed ((galoisRepMatrixTwo b).range : Set (GL (Fin 2) ℤ_[2])) :=
  (isCompact_range_galoisRepMatrixTwo b).isClosed

/-- The image of `ρ_{E,2}`, as a topological group in its own right, is compact. -/
instance compactSpace_range_galoisRepMatrixTwo :
    CompactSpace ((galoisRepMatrixTwo b).range) :=
  isCompact_iff_compactSpace.mp (isCompact_range_galoisRepMatrixTwo b)

/-- `ρ_{E,2}` is a closed map: it carries closed subgroups of `G` to closed subgroups of
`GL₂(ℤ_[2])`, not merely to subgroups. -/
theorem isClosedMap_galoisRepMatrixTwo : IsClosedMap (galoisRepMatrixTwo b) :=
  (continuous_galoisRepMatrixTwo b).isClosedMap

/-! ### The topological first isomorphism theorem -/

omit [IsGalois S F] in
/-- `ρ_{E,2}` corestricted to its image is continuous. -/
theorem continuous_rangeRestrict_galoisRepMatrixTwo :
    Continuous fun σ : F ≃ₐ[S] F =>
      (⟨galoisRepMatrixTwo b σ, ⟨σ, rfl⟩⟩ : (galoisRepMatrixTwo b).range) :=
  continuous_induced_rng.2 (continuous_galoisRepMatrixTwo b)

/-- **`G ⧸ ker ρ_{E,2} ≃ₜ* im ρ_{E,2}`** — the first isomorphism theorem for `ρ_{E,2}` as an
isomorphism of *topological* groups, not merely of groups.

The forward map is continuous because `QuotientGroup.mk` is a quotient map and `ρ` is continuous.
The inverse is where compactness is spent: a continuous bijective homomorphism is **not** a
homeomorphism in general, and here it is one because `G ⧸ ker ρ` is compact (a quotient of the
compact group `G`) and the image is Hausdorff (a subspace of `GL₂(ℤ_[2])`).

Read together with `isClosed_ker_galoisRepTwo` from `EllipticCurves.TateModule.OpenKernel`: `ker ρ`
is a closed normal subgroup of a compact group, so this presents the image of the `2`-adic
representation as a compact Hausdorff group quotient of `Gal(F/S)`. -/
noncomputable def quotientKerContinuousMulEquivRange :
    ((F ≃ₐ[S] F) ⧸ (galoisRepMatrixTwo b).ker) ≃ₜ* (galoisRepMatrixTwo b).range := by
  refine ContinuousMulEquiv.mk (QuotientGroup.quotientKerEquivRange (galoisRepMatrixTwo b)) ?_ ?_
  · exact continuous_coinduced_dom.2 (continuous_rangeRestrict_galoisRepMatrixTwo b)
  · exact ((continuous_coinduced_dom.2
      (continuous_rangeRestrict_galoisRepMatrixTwo b)).homeoOfEquivCompactToT2
        (f := (QuotientGroup.quotientKerEquivRange (galoisRepMatrixTwo b)).toEquiv)).symm.continuous

/-- `quotientKerContinuousMulEquivRange` computes `ρ_{E,2}`, pinning it to the representation so it
cannot drift to some other isomorphism. -/
@[simp]
theorem quotientKerContinuousMulEquivRange_apply_mk (σ : F ≃ₐ[S] F) :
    quotientKerContinuousMulEquivRange b (QuotientGroup.mk σ)
      = ⟨galoisRepMatrixTwo b σ, ⟨σ, rfl⟩⟩ := rfl

/-! ### The determinant character -/

/-- The image of `det ρ_{E,2} : G →* ℤ_[2]ˣ` is compact. A basis is taken because continuity of
`galoisDetTwo` is proved through one, even though `galoisDetTwo` itself is basis-free. -/
theorem isCompact_range_galoisDetTwo_of_basis
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :
    IsCompact (Set.range (galoisDetTwo (W' := W') (F := F))) :=
  isCompact_range (continuous_galoisDetTwo_of_basis b)

/-- The image of `det ρ_{E,2}` is a closed subgroup of `ℤ_[2]ˣ`. -/
theorem isClosed_range_galoisDetTwo_of_basis
    (b : Module.Basis (Fin 2) ℤ_[2] ((W'⁄F).tateModule 2)) :
    IsClosed (Set.range (galoisDetTwo (W' := W') (F := F))) :=
  (isCompact_range_galoisDetTwo_of_basis b).isClosed

section Two

variable [IsAlgClosed F] [(W'⁄F).IsElliptic]

/-- The image of `det ρ_{E,2}` is compact, with no basis supplied: over an algebraically closed
field of characteristic `≠ 2` one exists, and compactness is a `Prop`. -/
theorem isCompact_range_galoisDetTwo (h2 : (2 : F) ≠ 0) :
    IsCompact (Set.range (galoisDetTwo (W' := W') (F := F))) := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_two (W := W'⁄F) h2
  exact isCompact_range_galoisDetTwo_of_basis b

/-- **The image of the determinant character is a closed subgroup of `ℤ_[2]ˣ`.** This is the layer
the identification of `det ρ_{E,2}` with the cyclotomic character will consume; that identification
needs the Weil pairing and is not proved in this development. -/
theorem isClosed_range_galoisDetTwo (h2 : (2 : F) ≠ 0) :
    IsClosed (Set.range (galoisDetTwo (W' := W') (F := F))) :=
  (isCompact_range_galoisDetTwo h2).isClosed

end Two

end WeierstrassCurve.Affine

/-! ### A subgroup of `GL₂(ℤ_[2])` that is not closed

Closedness of the image above is a real constraint and not an artefact of the ambient group being
compact. The witness is the image of `ℤ` in `ℤ_[2]`, dense and proper, pushed into `GL₂` along the
unipotent line. -/

/-- **`ℤ` is not all of `ℤ_[2]`.** `3` is a unit of `ℤ_[2]` — it has norm `1`, being prime to `2` —
and its inverse is not a rational integer, since `3 * n = 1` has no solution in `ℤ`. -/
theorem PadicInt.range_intCast_ne_univ : Set.range (Int.cast : ℤ → ℤ_[2]) ≠ Set.univ := by
  intro h
  have h3 : IsUnit ((3 : ℤ) : ℤ_[2]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd (3 : ℤ) (p := 2)).1 hlt
    omega
  obtain ⟨u, hu⟩ := h3
  obtain ⟨n, hn⟩ : (↑u⁻¹ : ℤ_[2]) ∈ Set.range (Int.cast : ℤ → ℤ_[2]) := h ▸ Set.mem_univ _
  have key : ((3 * n : ℤ) : ℤ_[2]) = ((1 : ℤ) : ℤ_[2]) := by
    rw [Int.cast_mul, hn, ← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one, Int.cast_one]
  have := (Int.cast_injective (α := ℤ_[2])) key
  omega

/-- **The additive subgroup `ℤ ⊆ ℤ_[2]` is not closed.** It is dense
(`PadicInt.denseRange_intCast`), so were it closed it would be everything, contradicting
`PadicInt.range_intCast_ne_univ`.

This is the source of the counterexample: `Int.cast : ℤ → ℤ_[2]` is an injective *continuous group
homomorphism whose image is not closed*, and the only hypothesis it lacks, compared with
`ρ_{E,2}`, is compactness of its source. -/
theorem PadicInt.not_isClosed_range_intCast :
    ¬ IsClosed (Set.range (Int.cast : ℤ → ℤ_[2])) := fun h =>
  PadicInt.range_intCast_ne_univ (h.closure_eq ▸ PadicInt.denseRange_intCast.closure_eq)

namespace Matrix.GeneralLinearGroup

/-- **The integral points of the unipotent line in `GL₂(ℤ_[2])`**: the subgroup
`{ !![1, n; 0, 1] : n : ℤ }`. It is a subgroup because `upperRightHom` is an additive character,
so it turns `+` on `ℤ_[2]` into `*` on `GL₂(ℤ_[2])`. -/
def unipotentIntSubgroup : Subgroup (GL (Fin 2) ℤ_[2]) where
  carrier := Set.range fun n : ℤ => upperRightHom ((n : ℤ_[2]))
  mul_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, by simp only [Int.cast_add, AddChar.map_add_eq_mul]⟩
  one_mem' := ⟨0, by simp only [Int.cast_zero, AddChar.map_zero_eq_one]⟩
  inv_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨-n, by simp only [Int.cast_neg, AddChar.map_neg_eq_inv]⟩

/-- **`GL₂(ℤ_[2])` has a subgroup that is not closed.**

Pulling back along the continuous injection `upperRightHom` turns a hypothetical closed
`unipotentIntSubgroup` into a closed copy of `ℤ` inside `ℤ_[2]`, which
`PadicInt.not_isClosed_range_intCast` forbids.

This is the non-degeneracy certificate for
`WeierstrassCurve.Affine.isClosed_range_galoisRepMatrixTwo`: being the image of a group
homomorphism into `GL₂(ℤ_[2])` does not make a subgroup closed, even though `GL₂(ℤ_[2])` is
compact. -/
theorem not_isClosed_unipotentIntSubgroup :
    ¬ IsClosed (unipotentIntSubgroup : Set (GL (Fin 2) ℤ_[2])) := by
  intro h
  refine PadicInt.not_isClosed_range_intCast ?_
  have hpre : (upperRightHom (R := ℤ_[2])) ⁻¹' (unipotentIntSubgroup : Set (GL (Fin 2) ℤ_[2]))
      = Set.range (Int.cast : ℤ → ℤ_[2]) := by
    ext x
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, injective_upperRightHom hn⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, rfl⟩
  rw [← hpre]
  exact h.preimage continuous_upperRightHom

end Matrix.GeneralLinearGroup
