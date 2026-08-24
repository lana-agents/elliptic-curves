/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.TateModule.PrimaryMatrixContinuity
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The image of `ρ_{E,ℓ}` is a closed subgroup of `GL₂(ℤ_[ℓ])`, at an arbitrary prime

`EllipticCurves.TateModule.PrimaryMatrixContinuity` proves that `galoisRepMatrix b : G → GL₂(ℤ_[ℓ])`
is continuous, for **every** basis `b` of `T_ℓE` and every prime `ℓ`. This file draws the
consequences for its *image*, at **any** prime.

The whole file costs one extra instance argument, `[IsGalois S F]`, which is what supplies
Mathlib's `InfiniteGalois` instance

```lean
instance [IsGalois k K] : CompactSpace Gal(K/k)
```

for `Gal(F/S) = F ≃ₐ[S] F`. That is a hypothesis on the extension `F / S` — it says nothing about
the curve, and it is not automatic: for `F` an algebraic closure of an *imperfect* `S` the
extension is normal but not separable, and the instance does not apply.

## What this file is

This is the **extraction** of `EllipticCurves.TateModule.Image` to an arbitrary prime, and it is
the sixth link in a chain that has now worked six times: `EllipticCurves.Torsion.PrimaryBasis` →
`EllipticCurves.TateModule.PrimaryFree` → `EllipticCurves.TateModule.PrimaryMatrixRep` →
`EllipticCurves.TateModule.PrimaryDeterminant` →
`EllipticCurves.TateModule.PrimaryMatrixContinuity` → here.

⚠️ **This file supplies no `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)` at any prime**, so on its own it proves
nothing non-degenerate about any curve. The instances are `EllipticCurves.TateModule.Image`
(`ℓ = 2`) and `EllipticCurves.TateModule.ImageThree` (`ℓ = 3`); at `ℓ ≥ 5` there is nothing to
instantiate with — see Scope.

## ⚠️ Where the `Two` suffix was, and where it was not

`EllipticCurves.TateModule.Image` had **sixteen** declarations. ⚠️ A `grep` for declaration
keywords at the start of a line returns **seventeen**, because that file's module docstring — and
this one's, above — quotes Mathlib's `instance [IsGalois k K] : CompactSpace Gal(K/k)` inside a
fenced ```lean block. **A fenced code block looks exactly like a declaration, because it is one —
somebody else's.**

Ten of the sixteen carried a `Two` suffix and are the ones with `ℓ = 3` twins. ⚠️ **The other six
could not be twinned and were generalised in place**, and they split into two kinds that behave
quite differently:

* `tateModule`-adjacent, unsuffixed, already `ℓ`-free in everything but the `variable` block:
  `quotientKerContinuousMulEquivRange` and `quotientKerContinuousMulEquivRange_apply_mk`.
  Generalising them was retyping `2` as `ℓ`. ⚠️ There is deliberately no
  `quotientKerContinuousMulEquivRangeThree`: `galoisRepMatrixThree b` is *definitionally*
  `galoisRepMatrix b`, so `quotientKerContinuousMulEquivRange b` for a basis `b` of `T₃E` already
  **is** the `ℓ = 3` statement.
* `_root_`-level, unsuffixed, and stated at a **hardcoded** `ℤ_[2]`:
  `PadicInt.range_intCast_ne_univ`, `PadicInt.not_isClosed_range_intCast`,
  `Matrix.GeneralLinearGroup.unipotentIntSubgroup` and
  `Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup`. ⚠️ **These were not free**, and
  the first of them needed a new proof — see the section that states it.

> ⚠️ **"Unsuffixed" tells you a twin is illegal; it does not tell you the generalisation is free.**
> In `EllipticCurves.TateModule.MatrixContinuity` the nine unsuffixed rows were already generic in
> everything but their `variable` block. Here two of the six were, and four were stated at a
> hardcoded prime with a proof that used it arithmetically. The two facts — *may this be twinned?*
> and *what does generalising cost?* — are answered by different measurements.

## The `[IsGalois S F]` split, measured

⚠️ `[IsGalois S F]` is what the whole file is for, and exactly two statements do without it.
`coe_range_galoisRepMatrix` is a pure `Subgroup`-to-`Set` bridge and needs neither section
instance; `continuous_rangeRestrict_galoisRepMatrix` needs continuity, hence
`[Algebra.IsIntegral S F]`, but not compactness. Everything else needs both, because everything
else is a consequence of `G` being compact. Both omissions are recorded with `omit … in` rather
than being left to a reader.

## Non-degeneracy: why "closed" is not a formality

`GL₂(ℤ_[p])` is itself compact, so inside it *closed* and *compact* agree, and a reader may suspect
that `isClosed_range_galoisRepMatrix` says nothing at all.
`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup` at the end of this file is the
counterexample: a subgroup of `GL₂(ℤ_[p])` that is **not** closed — the unipotent line
`n ↦ !![1, n; 0, 1]` restricted to `n : ℤ`. ⚠️ **It is stated at an arbitrary prime `p`**, so it has
no per-prime twin and needs none: the instantiating files cite it, exactly as they cite
`Matrix.GeneralLinearGroup.not_discreteTopology_padicInt`.

That counterexample also isolates which hypothesis is load-bearing: `ℤ → ℤ_[p]` is an injective
continuous group homomorphism with non-closed image, and the only thing it lacks compared with
`ρ_{E,ℓ}` is compactness of the source.

⚠️ These certificates are about the *ambient* group, not about the curve. Every statement here
about `G` remains true when `G` is trivial, and no theorem about `G` alone can exclude that — it is
a fact about `F / S`. What rules out the degenerate reading on the Tate-module side is
`Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)`, which this file takes as a hypothesis rather than proving; the
instantiating files close it separately, with `Infinite (T_ℓE)`.

## Scope

* **No rank input.** This file states the image results and takes rank two as a hypothesis exactly
  where a basis has to be produced.
* ⚠️ **Openness of the image is not here, at any prime.** That is Serre's theorem, it is *false*
  for curves with complex multiplication, and nothing about compactness approaches it.
* **Surjectivity and injectivity of `ρ_{E,ℓ}` are not here.** An isomorphism onto `G ⧸ ker ρ` says
  nothing about whether `ker ρ` is trivial.
* ⚠️ **The identification of `galoisDet` with the cyclotomic character is not proved here**, at any
  prime, and closedness of its image does not bring it closer. It needs the Weil pairing at
  **every** level `E[ℓ^k]`; see `EllipticCurves.TateModule.PrimaryDeterminant`'s Scope.
* **The profinite packaging is not here.** `EllipticCurves.TateModule.ImageProfinite` bundles the
  image, the quotient and the representation as objects and a morphism of `ProfiniteGrp`. ⚠️ **The
  clause this bullet used to end with has been paid** — it read *"it is `ℓ = 2` only and its
  `ℓ`-generic form is a separate follow-up over *this* file"*. That follow-up is
  `EllipticCurves.TateModule.PrimaryImageProfinite`, which sits over this file, with
  instantiations at `ℓ = 2` (`EllipticCurves.TateModule.ImageProfinite`) and `ℓ = 3`
  (`EllipticCurves.TateModule.ImageProfiniteThree`).
* ⚠️ **`ℓ ≥ 5` gains nothing from this file being generic.** Its hypothesis
  `Nonempty (T_ℓE ≃ₗ ℤ_[ℓ]²)` is gated at `ℓ ≥ 5` on `[ℓ]`-surjectivity and `#E[ℓ^k]`, both of
  which need the general coordinate formula `x(nP) = Φₙ/ΨSqₙ`, i.e. the `ωₙ` crux. What being
  generic buys is that when that gate is paid, the `ℓ = 5` file is a list of instantiations and no
  argument has to be written a third time.

## Using this file

Everything is stated for a base change `W'⁄F` of a curve `W' : Affine S` rather than for a bare
`W : Affine F`, matching `EllipticCurves.TateModule.PrimaryMatrixRep` and
`EllipticCurves.TateModule.PrimaryMatrixContinuity`. This is forced: the continuity inputs are
themselves stated about `(W'⁄F).tateModule ℓ`, and instance search will not unify a bare `W` with
`?W'.baseChange F`.

## Main statements

* `WeierstrassCurve.Affine.isClosed_range_galoisRepMatrix` : the image of `ρ_{E,ℓ}` is a closed
  subgroup of `GL₂(ℤ_[ℓ])`.
* `WeierstrassCurve.Affine.quotientKerContinuousMulEquivRange` : `G ⧸ ker ρ ≃ₜ* im ρ`, as
  topological groups.
* `WeierstrassCurve.Affine.isClosed_range_galoisDet_of_nonempty` : the same for the determinant
  character.
* `Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup` : `GL₂(ℤ_[p])` has a subgroup that
  is not closed, so the statements above are not formalities.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open Matrix

open scoped WeierstrassCurve.Affine.ProfiniteTopology

namespace WeierstrassCurve.Affine

variable {S F : Type*} [Field S] [Field F] [DecidableEq F] [Algebra S F] {W' : Affine S}
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable [Algebra.IsIntegral S F] [IsGalois S F]
variable (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ))

/-! ### The image is compact and closed -/

omit [Algebra.IsIntegral S F] [IsGalois S F] in
/-- The underlying set of the subgroup `(galoisRepMatrix b).range` is the set-theoretic range.

Purely a bridge: `MonoidHom.range` is a `Subgroup` and its coercion is not syntactically
`Set.range` of the coerced function, but every topological statement below is about the latter. -/
theorem coe_range_galoisRepMatrix :
    ((galoisRepMatrix b).range : Set (GL (Fin 2) ℤ_[ℓ]))
      = Set.range (galoisRepMatrix b) := by
  ext x; simp

/-- **The image of `ρ_{E,ℓ}` is compact.** `G = Gal(F/S)` is compact for the Krull topology
(Mathlib's `InfiniteGalois` instance, which needs `[IsGalois S F]`) and `ρ_{E,ℓ}` is continuous
(`continuous_galoisRepMatrix`, for any basis), so the image is a continuous image of a compact
space. -/
theorem isCompact_range_galoisRepMatrix :
    IsCompact ((galoisRepMatrix b).range : Set (GL (Fin 2) ℤ_[ℓ])) := by
  rw [coe_range_galoisRepMatrix]
  exact isCompact_range (continuous_galoisRepMatrix b)

/-- **The image of `ρ_{E,ℓ}` is a closed subgroup of `GL₂(ℤ_[ℓ])`.**

This is the classical statement, and the standing hypothesis of every theorem about the image of an
`ℓ`-adic representation. It is not a formality: `GL₂(ℤ_[ℓ])` has subgroups that are not closed, and
`Matrix.GeneralLinearGroup.not_isClosed_unipotentIntSubgroup` below exhibits one, at every
prime. -/
theorem isClosed_range_galoisRepMatrix :
    IsClosed ((galoisRepMatrix b).range : Set (GL (Fin 2) ℤ_[ℓ])) :=
  (isCompact_range_galoisRepMatrix b).isClosed

/-- The image of `ρ_{E,ℓ}`, as a topological group in its own right, is compact. -/
instance compactSpace_range_galoisRepMatrix :
    CompactSpace ((galoisRepMatrix b).range) :=
  isCompact_iff_compactSpace.mp (isCompact_range_galoisRepMatrix b)

/-- `ρ_{E,ℓ}` is a closed map: it carries closed subgroups of `G` to closed subgroups of
`GL₂(ℤ_[ℓ])`, not merely to subgroups. -/
theorem isClosedMap_galoisRepMatrix : IsClosedMap (galoisRepMatrix b) :=
  (continuous_galoisRepMatrix b).isClosedMap

/-! ### The topological first isomorphism theorem -/

omit [IsGalois S F] in
/-- `ρ_{E,ℓ}` corestricted to its image is continuous. -/
theorem continuous_rangeRestrict_galoisRepMatrix :
    Continuous fun σ : F ≃ₐ[S] F =>
      (⟨galoisRepMatrix b σ, ⟨σ, rfl⟩⟩ : (galoisRepMatrix b).range) :=
  continuous_induced_rng.2 (continuous_galoisRepMatrix b)

/-- **`G ⧸ ker ρ_{E,ℓ} ≃ₜ* im ρ_{E,ℓ}`** — the first isomorphism theorem for `ρ_{E,ℓ}` as an
isomorphism of *topological* groups, not merely of groups.

The forward map is continuous because `QuotientGroup.mk` is a quotient map and `ρ` is continuous.
The inverse is where compactness is spent: a continuous bijective homomorphism is **not** a
homeomorphism in general, and here it is one because `G ⧸ ker ρ` is compact (a quotient of the
compact group `G`) and the image is Hausdorff (a subspace of `GL₂(ℤ_[ℓ])`).

Read together with `isClosed_ker_galoisRep` from `EllipticCurves.TateModule.OpenKernel`: `ker ρ` is
a closed normal subgroup of a compact group, so this presents the image of the `ℓ`-adic
representation as a compact Hausdorff group quotient of `Gal(F/S)`.

⚠️ **This name carries no `Two`, and it gets no `Three` twin.** `galoisRepMatrixThree b` is
definitionally `galoisRepMatrix b`, so this statement applied to a basis of `T₃E` already *is* the
`ℓ = 3` statement; a `quotientKerContinuousMulEquivRangeThree` in the same namespace would be a
name collision rather than a duplication. -/
noncomputable def quotientKerContinuousMulEquivRange :
    ((F ≃ₐ[S] F) ⧸ (galoisRepMatrix b).ker) ≃ₜ* (galoisRepMatrix b).range := by
  refine ContinuousMulEquiv.mk (QuotientGroup.quotientKerEquivRange (galoisRepMatrix b)) ?_ ?_
  · exact continuous_coinduced_dom.2 (continuous_rangeRestrict_galoisRepMatrix b)
  · exact ((continuous_coinduced_dom.2
      (continuous_rangeRestrict_galoisRepMatrix b)).homeoOfEquivCompactToT2
        (f := (QuotientGroup.quotientKerEquivRange (galoisRepMatrix b)).toEquiv)).symm.continuous

/-- `quotientKerContinuousMulEquivRange` computes `ρ_{E,ℓ}`, pinning it to the representation so it
cannot drift to some other isomorphism. -/
@[simp]
theorem quotientKerContinuousMulEquivRange_apply_mk (σ : F ≃ₐ[S] F) :
    quotientKerContinuousMulEquivRange b (QuotientGroup.mk σ)
      = ⟨galoisRepMatrix b σ, ⟨σ, rfl⟩⟩ := rfl

/-! ### The determinant character -/

/-- The image of `det ρ_{E,ℓ} : G →* ℤ_[ℓ]ˣ` is compact. A basis is taken because continuity of
`galoisDet` is proved through one, even though `galoisDet` itself is basis-free. -/
theorem isCompact_range_galoisDet_of_basis
    (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) :
    IsCompact (Set.range (galoisDet (W' := W') (F := F) (ℓ := ℓ))) :=
  isCompact_range (continuous_galoisDet_of_basis b)

/-- The image of `det ρ_{E,ℓ}` is a closed subgroup of `ℤ_[ℓ]ˣ`. -/
theorem isClosed_range_galoisDet_of_basis
    (b : Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) :
    IsClosed (Set.range (galoisDet (W' := W') (F := F) (ℓ := ℓ))) :=
  (isCompact_range_galoisDet_of_basis b).isClosed

/-! ### The basis-free layer

The two statements below are the only ones in this file that take a hypothesis about the curve, and
it is the one the three earlier `Primary*` extractions on this front already take:
`Nonempty (T_ℓE ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])` — `EllipticCurves.TateModule.PrimaryMatrixRep`,
`EllipticCurves.TateModule.PrimaryDeterminant` and
`EllipticCurves.TateModule.PrimaryMatrixContinuity`, seven `_of_nonempty` declarations between
them. ⚠️ They need it to *produce* a basis rather than be handed one, which is a reason unrelated
to compactness; the non-degeneracy of the ambient group is settled unconditionally at the end of
this file. -/

/-- The image of `det ρ_{E,ℓ}` is compact, with no basis supplied: a basis exists as soon as `T_ℓE`
is `ℤ_[ℓ]`-linearly `ℤ_[ℓ]²`, and compactness is a `Prop`, so the choice can be discharged.

⚠️ **Deletion test**, measured on this file as committed. Deleting the hypothesis `h` and replacing
`obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_of_nonempty (W := W'⁄F) h` by
`obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] ((W'⁄F).tateModule ℓ)) := ?_` leaves,
copy-paste:

```
error: don't know how to synthesize placeholder
context:
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
⊢ Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] ↥((W'⁄F).tateModule ℓ))
```

⚠️ One mechanical change accompanies the deletion and it adds no information: `obtain ⟨b⟩ := …`
becomes `obtain ⟨b⟩ : Nonempty … := ?_`, so that a hole is legal where the hypothesis was, and the
type must be written out rather than left as `_` since nothing else in the goal determines it.

⚠️ The residual is a **goal** and not a type mismatch, and nothing left in the context proves it:
with `h` gone the context has no curve-theoretic content at all. ⚠️ **There IS a knock-on and it is
disclosed**: `isClosed_range_galoisDet_of_nonempty` below consumes this theorem and takes `h` only
to pass it on, so the same edit produces a second, *different* error there —
`Invalid field \`isClosed\`` on `∃ x ∈ Set.range ⇑galoisDet, ClusterPt x ?m`, because with the
hypothesis gone the elaborator can no longer see the statement as an `IsCompact`. That second error
is **not** a deletion test; it is what a knock-on looks like, and it is why the test is stated on
this declaration rather than on the one below. -/
theorem isCompact_range_galoisDet_of_nonempty
    (h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) :
    IsCompact (Set.range (galoisDet (W' := W') (F := F) (ℓ := ℓ))) := by
  obtain ⟨b⟩ := tateModule.nonempty_basis_tateModule_of_nonempty (W := W'⁄F) h
  exact isCompact_range_galoisDet_of_basis b

/-- **The image of the determinant character is a closed subgroup of `ℤ_[ℓ]ˣ`.** This is the layer
the identification of `det ρ_{E,ℓ}` with the cyclotomic character will consume; ⚠️ that
identification needs the Weil pairing at every level and is **not** proved in this development, at
either prime. ⚠️ Knowing that the image of a character is closed says nothing about *which*
character it is.

⚠️ The deletion test for the `Nonempty` hypothesis is stated on
`isCompact_range_galoisDet_of_nonempty` above, together with the knock-on this declaration
produces. -/
theorem isClosed_range_galoisDet_of_nonempty
    (h : Nonempty ((W'⁄F).tateModule ℓ ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] × ℤ_[ℓ])) :
    IsClosed (Set.range (galoisDet (W' := W') (F := F) (ℓ := ℓ))) :=
  (isCompact_range_galoisDet_of_nonempty h).isClosed

end WeierstrassCurve.Affine

/-! ### A subgroup of `GL₂(ℤ_[p])` that is not closed

Closedness of the image above is a real constraint and not an artefact of the ambient group being
compact. The witness is the image of `ℤ` in `ℤ_[p]`, dense and proper, pushed into `GL₂` along the
unipotent line.

⚠️ **All four statements below are stated at an arbitrary prime `p`**, so they have no per-prime
twins and need none: `EllipticCurves.TateModule.Image` and `EllipticCurves.TateModule.ImageThree`
cite them rather than restate them. They are `_root_`-level facts about `ℤ_[p]` and `GL₂(ℤ_[p])`
and mention no curve. ⚠️ **They were `ℓ = 2` only before this extraction, and generalising them was
not free** — see `PadicInt.range_intCast_ne_univ`. -/

/-- **`ℤ` is not all of `ℤ_[p]`.** `p + 1` is a unit of `ℤ_[p]` — it has norm `1`, being prime to
`p` — and its inverse is not a rational integer, since `(p + 1) * n = 1` has no solution in `ℤ`
for `p ≥ 2`.

⚠️ **The witness is `p`-specific and the `ℓ = 2` proof did not survive generalisation.** The
version this replaces used `3`, which is a unit of `ℤ_[2]` but *not* of `ℤ_[3]`, and nothing in its
statement or docstring flagged the constant as a choice. `p + 1` is prime to `p` at every prime and
is `≥ 3`, which is what both halves need.

⚠️ Two steps of the `ℓ = 2` proof had to be replaced, and both for the same reason — `omega` does
not reason about a variable prime. `‖((p + 1 : ℕ) : ℤ_[p])‖ < 1` gives `(p : ℤ) ∣ (p + 1 : ℤ)`,
whose refutation goes through `Int.dvd_sub` and `Int.le_of_dvd` rather than `omega`; and
`(p + 1) * n = 1` in `ℤ` is a product of two variables, closed by
`Int.eq_one_of_mul_eq_one_right` rather than by `omega`. -/
theorem PadicInt.range_intCast_ne_univ (p : ℕ) [hp : Fact p.Prime] :
    Set.range (Int.cast : ℤ → ℤ_[p]) ≠ Set.univ := by
  intro h
  have hq : IsUnit (((p + 1 : ℕ) : ℤ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_)
    have hdvd := (PadicInt.norm_int_lt_one_iff_dvd ((p + 1 : ℕ) : ℤ) (p := p)).1 hlt
    have hone : (p : ℤ) ∣ 1 := by
      have := (Int.dvd_add_right (Dvd.intro 1 (by ring))).mp (by push_cast at hdvd ⊢; exact hdvd)
      exact this
    have := Int.le_of_dvd one_pos hone
    have := hp.out.two_le
    omega
  obtain ⟨u, hu⟩ := hq
  obtain ⟨n, hn⟩ : (↑u⁻¹ : ℤ_[p]) ∈ Set.range (Int.cast : ℤ → ℤ_[p]) := h ▸ Set.mem_univ _
  have key : (((p + 1 : ℕ) * n : ℤ) : ℤ_[p]) = ((1 : ℤ) : ℤ_[p]) := by
    rw [Int.cast_mul, hn, ← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one, Int.cast_one]
  have hz := (Int.cast_injective (α := ℤ_[p])) key
  have h2 := hp.out.two_le
  have := Int.eq_one_of_mul_eq_one_right (by positivity) hz
  omega

/-- **The additive subgroup `ℤ ⊆ ℤ_[p]` is not closed.** It is dense
(`PadicInt.denseRange_intCast`), so were it closed it would be everything, contradicting
`PadicInt.range_intCast_ne_univ`.

This is the source of the counterexample: `Int.cast : ℤ → ℤ_[p]` is an injective *continuous group
homomorphism whose image is not closed*, and the only hypothesis it lacks, compared with
`ρ_{E,ℓ}`, is compactness of its source. -/
theorem PadicInt.not_isClosed_range_intCast (p : ℕ) [Fact p.Prime] :
    ¬ IsClosed (Set.range (Int.cast : ℤ → ℤ_[p])) := fun h =>
  PadicInt.range_intCast_ne_univ p (h.closure_eq ▸ PadicInt.denseRange_intCast.closure_eq)

namespace Matrix.GeneralLinearGroup

/-- **The integral points of the unipotent line in `GL₂(ℤ_[p])`**: the subgroup
`{ !![1, n; 0, 1] : n : ℤ }`. It is a subgroup because `upperRightHom` is an additive character,
so it turns `+` on `ℤ_[p]` into `*` on `GL₂(ℤ_[p])`. -/
def unipotentIntSubgroup (p : ℕ) [Fact p.Prime] : Subgroup (GL (Fin 2) ℤ_[p]) where
  carrier := Set.range fun n : ℤ => upperRightHom ((n : ℤ_[p]))
  mul_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, by simp only [Int.cast_add, AddChar.map_add_eq_mul]⟩
  one_mem' := ⟨0, by simp only [Int.cast_zero, AddChar.map_zero_eq_one]⟩
  inv_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨-n, by simp only [Int.cast_neg, AddChar.map_neg_eq_inv]⟩

/-- **`GL₂(ℤ_[p])` has a subgroup that is not closed**, at every prime `p`.

Pulling back along the continuous injection `upperRightHom` turns a hypothetical closed
`unipotentIntSubgroup` into a closed copy of `ℤ` inside `ℤ_[p]`, which
`PadicInt.not_isClosed_range_intCast` forbids.

⚠️ This is the non-vacuity certificate for
`WeierstrassCurve.Affine.isClosed_range_galoisRepMatrix`: being the image of a group homomorphism
into `GL₂(ℤ_[p])` does not make a subgroup closed, even though `GL₂(ℤ_[p])` is compact. ⚠️ **It is
`p`-generic, so it covers every prime by citation** — neither instantiating file states a copy. -/
theorem not_isClosed_unipotentIntSubgroup (p : ℕ) [Fact p.Prime] :
    ¬ IsClosed (unipotentIntSubgroup p : Set (GL (Fin 2) ℤ_[p])) := by
  intro h
  refine PadicInt.not_isClosed_range_intCast p ?_
  have hpre : (upperRightHom (R := ℤ_[p])) ⁻¹' (unipotentIntSubgroup p : Set (GL (Fin 2) ℤ_[p]))
      = Set.range (Int.cast : ℤ → ℤ_[p]) := by
    ext x
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, injective_upperRightHom hn⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, rfl⟩
  rw [← hpre]
  exact h.preimage continuous_upperRightHom

end Matrix.GeneralLinearGroup
