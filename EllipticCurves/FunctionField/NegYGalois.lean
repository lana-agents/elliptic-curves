/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoDegree
import EllipticCurves.FunctionField.NegYInvolution
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# `F(W)` is Galois over `F(x)`, in every characteristic

`EllipticCurves.FunctionField.NegYInvolution` builds the hyperelliptic involution
`ι : F(W) ≃ₐ[F] F(W)`, `x ↦ x`, `y ↦ −y − a₁x − a₃`, and proves `negYAlgEquiv_ne_one` — `ι ≠ 1` for
every elliptic curve over every field, **with no hypothesis on the characteristic**.  This file
turns that into the Galois package for the bottom of the tower:

```
F(x)  =  Fixed(⟨ι⟩)  ⊆  F(W),      [F(W) : F(x)] = 2 = |⟨ι⟩| = [F(W) : Fixed(⟨ι⟩)]
```

so `F(W) / F(x)` is **separable, normal and Galois**, again with no hypothesis on the
characteristic and — unlike `EllipticCurves.FunctionField.MulByTwoGalois` — with **no
`[IsAlgClosed F]` and no `(2 : F) ≠ 0`**.  Every result below is therefore an `instance` rather
than a `theorem` a consumer has to fire with `haveI`.

## ⚠️ This retires a merged sentence, and that is half the point of the file

`EllipticCurves.FunctionField.PlaceDegreeComparison`'s `## Scope` section used to read

> The Galois-hypothesis variant `relNorm_eq_pow_of_isPrime_isGalois` wants
> `IsGalois (RatFunc F) F(W)`, *"which a Weierstrass extension is not in general."*

**The quoted clause is false.**  `[F(W) : F(x)] = 2` is merged (`finrank_ratFuncRange`,
`EllipticCurves.FunctionField.MulByTwoDegree`), `ι` is a nontrivial `F(x)`-automorphism of it, and
Artin's theorem on fixed fields closes the sandwich — so the extension **is** Galois, over every
field and in every characteristic.  `isGalois_ratFunc` below is the statement in the exact shape
that sentence named, and the sentence is repaired in place, in the same PR that proves it.

⚠️ **This file does not close the degree comparison, and that is a statement about this file
rather than about the tree.**  `EllipticCurves.FunctionField.PlaceDegreeComparison` does close it,
over an arbitrary base field, one `haveI` away from `isGalois_fractionRing_polynomial` — see the
`## Scope` section below, whose original wording predicted otherwise and was wrong.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.negYGroup` — the subgroup `⟨ι⟩ ≤ Aut_F F(W)`, i.e.
  `Subgroup.zpowers (negYAlgEquiv W)`;
* `WeierstrassCurve.Affine.CoordinateRing.ratFuncEquivRatFuncRange` — the tautological
  `RatFunc F ≃+* ↥(ratFuncRange W)`, which is what carries the results from the intermediate field
  `F(x) ⊆ F(W)` to the abstract `RatFunc F`.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.orderOf_negYAlgEquiv` and `card_negYGroup` — `ι` has
  order `2`, so `|⟨ι⟩| = 2`;
* `WeierstrassCurve.Affine.CoordinateRing.finrank_fixedField_negYGroup` — Artin:
  `[F(W) : Fixed(⟨ι⟩)] = 2`;
* **`WeierstrassCurve.Affine.CoordinateRing.ratFuncRange_eq_fixedField_negYGroup`** — the sandwich
  `F(x) = Fixed(⟨ι⟩)`, which is the whole mathematical content;
* `WeierstrassCurve.Affine.CoordinateRing.isSeparable_ratFuncRange`,
  `normal_ratFuncRange`, **`isGalois_ratFuncRange`** — the Galois package for the intermediate
  field `F(x) ⊆ F(W)`, as instances;
* **`WeierstrassCurve.Affine.CoordinateRing.isGalois_ratFunc`** — the same for the abstract
  `RatFunc F`, which is the shape `PlaceDegreeComparison`'s Scope section names;
* `WeierstrassCurve.Affine.CoordinateRing.isGalois_fractionRing_polynomial` — and for
  `FractionRing F[X]`, which is what `Ideal.relNorm_eq_pow_of_isPrime_isGalois` literally consumes;
* the steps of the sandwich, kept public because they are what a reader checks:
  `genX_mem_fixedField_negYGroup`, `ratFuncRange_le_fixedField_negYGroup`, `finite_negYGroup` and
  `algebraMap_comp_ratFuncEquivRatFuncRange_symm`.

## The three presentations of `F(x)`, and why all three appear

| term | type | who wants it |
| --- | --- | --- |
| `ratFuncRange W` | `IntermediateField F F(W)` | `IntermediateField.eq_of_le_of_finrank_eq'` |
| `RatFunc F` | a field in its own right | `PlaceDegreeComparison`'s Scope sentence |
| `FractionRing F[X]` | a field in its own right | `Ideal.relNorm_eq_pow_of_isPrime_isGalois` |

The first is where the argument happens, because Artin's theorem produces a fixed *subfield* and
the sandwich lemma is stated for intermediate fields.  The other two are reached by
`IsGalois.of_equiv_equiv`, once each.  ⚠️ **The second hop is the one that needs care**:
`FractionRing.liftAlgebra` is a `local instance` in Mathlib —
`Mathlib.RingTheory.Ideal.Norm.RelNorm` turns it on with `attribute [local instance]`, and
`Mathlib.RingTheory.NormalClosure` records that making it global causes timeouts — so
`Algebra (FractionRing F[X]) F(W)` is **not** available by default, here or anywhere.  This
file switches it on locally for the last declaration only, exactly as `RelNorm` does, and a
consumer must do the same for `isGalois_fractionRing_polynomial` to elaborate.

## Why this needs no characteristic hypothesis, and where the input came from

Nothing below differentiates anything.  The separability comes from
`FixedPoints.isSeparable` — the fixed field of a *finite group* of automorphisms is always
separably closed below, by Artin — so the only inputs are that `⟨ι⟩` is finite of order `2` and
that `[F(W) : F(x)] = 2`.  The first is `negYAlgEquiv_ne_one` together with
`negYAlgEquiv_negYAlgEquiv`, and `negYAlgEquiv_ne_one` is where `[W.IsElliptic]` enters and where
the characteristic-`2` content lives: in the inseparable case `2 = 0`, `a₁ = 0`, `a₃ = 0` the
involution *is* the identity, and `Δ ≠ 0` is exactly what rules that out.

⚠️ So `[W.IsElliptic]` is not decoration.  For a bare Weierstrass curve over a field of
characteristic `2` with `a₁ = a₃ = 0` the extension `F(W)/F(x)` is purely inseparable and every
statement below is false.

## Scope — what is deliberately *not* claimed

* ⚠️ **Not `degPt v = residueDegreeProj W (some v)`.**  This file mentions no place, no divisor and
  no `ProjPoint`, and nothing below is a statement about either degree function.  ⚠️ **But the
  reason is scope and not difficulty**: the comparison is proved over an *arbitrary* base field in
  `EllipticCurves.FunctionField.PlaceDegreeComparison`, and `isGalois_fractionRing_polynomial` is
  the hypothesis that was missing.  ⚠️ **This bullet used to continue** *"That is
  `PlaceDegreeComparison`'s open problem and it stays open"* and then to list
  `[IsDedekindDomain F[X]]`, `[IsDedekindDomain F[W]]`, `[Module.Finite F[X] F[W]]`,
  `[IsTorsionFree F[X] F[W]]`, `P.LiesOver p` and `[p.IsMaximal]` as further obstacles.  **The
  prediction was wrong and the list was misleading**: every one of those four typeclasses is
  supplied by `inferInstance` in this tree, the last two are hypotheses of the statement rather
  than obstacles, and only the tower `[κ(v) : F] = f · [κ(p) : F]` was genuinely absent.  ⚠️ **The
  clause "none of that is done *here*" was, and remains, true of this file** — the defect was the
  generalisation to the tree, which `PlaceDegreeComparison`'s `## Scope` made and this bullet
  echoed.
* **Not a statement about `Gal(F(W)/F(x))` as a group.**  `IsGalois` is delivered;
  `ratFuncRange_eq_fixedField_negYGroup` is what an identification of the Galois group with `⟨ι⟩`
  would start from, and it is not carried out.
* **Not `mapProjPoint ι ≠ 1`.**  `NegYInvolution`'s `## Scope` is explicit that `ι ≠ 1` is a
  statement about the automorphism and not about the permutation of `ProjPoint W` it induces, and
  nothing here changes that.
* **Not a statement about `[2]∗F(W)`.**  `MulByTwoGalois` is the *template* followed here;
  `F(W)/[2]∗F(W)` is a different extension, is already merged, and keeps its `[IsAlgClosed F]` and
  `(2 : F) ≠ 0` — those hypotheses come from `#E[2] = 4` and are not removed by anything below.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.2.
* [H. Stichtenoth, *Algebraic function fields and codes*][stichtenoth2009], I.1–I.4, III.7.
* Artin's theorem on fixed fields, [stacks 09I3].
-/

open Module Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The group `⟨ι⟩` and its order -/

variable (W) in
/-- **The group generated by the hyperelliptic involution**, `⟨ι⟩ ≤ Aut_F F(W)`.

It is a `Subgroup` rather than a bespoke type, so `Subgroup.mulSemiringAction` supplies the action
on `F(W)` and `Subgroup.instFaithfulSMulSubtypeMem` its faithfulness — both of which Artin's
theorem needs and neither of which has to be built here. -/
noncomputable abbrev negYGroup (W : Affine F) [W.IsElliptic] :
    Subgroup (W.FunctionField ≃ₐ[F] W.FunctionField) :=
  Subgroup.zpowers (negYAlgEquiv W)

/-- **`ι` has order exactly `2`.**  `orderOf_eq_prime` needs `ι ^ 2 = 1` and `ι ≠ 1`; the first is
`negYAlgEquiv_negYAlgEquiv` and the second is `negYAlgEquiv_ne_one`, which is where
`[W.IsElliptic]` and the whole characteristic-`2` argument of `NegYInvolution` are spent. -/
theorem orderOf_negYAlgEquiv : orderOf (negYAlgEquiv W) = 2 := by
  refine orderOf_eq_prime ?_ (negYAlgEquiv_ne_one W)
  ext f
  simp [negYAlgEquiv_negYAlgEquiv]

/-- **`|⟨ι⟩| = 2`**, by `Nat.card_zpowers` off `orderOf_negYAlgEquiv`. -/
theorem card_negYGroup : Nat.card ↥(negYGroup W) = 2 := by
  rw [negYGroup, Nat.card_zpowers, orderOf_negYAlgEquiv]

instance finite_negYGroup : Finite ↥(negYGroup W) :=
  Nat.finite_of_card_ne_zero (by rw [card_negYGroup]; norm_num)

/-! ### Artin's theorem -/

/-- **Artin: `[F(W) : Fixed(⟨ι⟩)] = |⟨ι⟩| = 2`.**

`FixedPoints.finrank_eq_card` is stated for `FixedPoints.subfield G F(W)`, a `Subfield`;
`IntermediateField.fixedField` is the same subset presented as an `IntermediateField F F(W)`, and
the two coercions to a type agree definitionally, so the `Subfield`-level statement is `exact`ed
into the `IntermediateField`-level one.

⚠️ Mathlib's `IntermediateField.finrank_fixedField_eq_card` is **not** usable here: it assumes
`[FiniteDimensional F E]`, and `F(W)` is infinite-dimensional over `F`.  The finiteness that
Artin's theorem actually needs is that of the *group*, which is `finite_negYGroup`. -/
theorem finrank_fixedField_negYGroup :
    finrank ↥(IntermediateField.fixedField (negYGroup W)) W.FunctionField = 2 := by
  haveI : Fintype ↥(negYGroup W) := Fintype.ofFinite _
  have h : finrank ↥(FixedPoints.subfield ↥(negYGroup W) W.FunctionField) W.FunctionField = 2 := by
    rw [FixedPoints.finrank_eq_card, ← Nat.card_eq_fintype_card, card_negYGroup]
  exact h

/-! ### The sandwich `F(x) = Fixed(⟨ι⟩)` -/

/-- **`ι` fixes the generic `x`-coordinate, and so does every power of it.**

The quantifier in `IntermediateField.mem_fixedField_iff` ranges over all of `⟨ι⟩`, not just over
`ι`, so the statement is routed through `MulAction.stabilizer`: the automorphisms fixing `genX W`
form a subgroup, `ι` is in it by `negYAlgEquiv_genX`, hence `⟨ι⟩ ≤ it` by `Subgroup.zpowers_le`. -/
theorem genX_mem_fixedField_negYGroup :
    genX W ∈ IntermediateField.fixedField (negYGroup W) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro f hf
  exact (Subgroup.zpowers_le.mpr (negYAlgEquiv_genX W) hf :
    f ∈ MulAction.stabilizer (W.FunctionField ≃ₐ[F] W.FunctionField) (genX W))

/-- **`F(x) ⊆ Fixed(⟨ι⟩)`.**  `ratFuncRange_eq_adjoin` presents `F(x)` as `F⟮genX W⟯`, and an
adjunction is contained in an intermediate field as soon as its generator is. -/
theorem ratFuncRange_le_fixedField_negYGroup :
    ratFuncRange W ≤ IntermediateField.fixedField (negYGroup W) := by
  rw [ratFuncRange_eq_adjoin]
  exact IntermediateField.adjoin_le_iff.mpr (by simpa using genX_mem_fixedField_negYGroup)

/-- **`F(x) = Fixed(⟨ι⟩)`** — the whole mathematical content of this file.

Both outer degrees are `2`: `finrank_ratFuncRange` (`EllipticCurves.FunctionField.MulByTwoDegree`)
on the left and `finrank_fixedField_negYGroup` on the right.  The inclusion
`ratFuncRange_le_fixedField_negYGroup` therefore has index one, and
`IntermediateField.eq_of_le_of_finrank_eq'` closes it.  Everything after this is transport. -/
theorem ratFuncRange_eq_fixedField_negYGroup :
    ratFuncRange W = IntermediateField.fixedField (negYGroup W) := by
  haveI : FiniteDimensional ↥(ratFuncRange W) W.FunctionField :=
    Module.finite_of_finrank_pos (by rw [finrank_ratFuncRange]; norm_num)
  exact IntermediateField.eq_of_le_of_finrank_eq' ratFuncRange_le_fixedField_negYGroup
    (by rw [finrank_ratFuncRange, finrank_fixedField_negYGroup])

/-! ### The Galois package over the intermediate field `F(x)` -/

/-- **`F(W)` is separable over `F(x)`, in every characteristic and over every field.**

`FixedPoints.isSeparable` is an unconditional instance for the fixed field of a finite group, and
the sandwich identifies that fixed field with `F(x)`.  ⚠️ This is *not* the argument "a quadratic
extension with a nontrivial automorphism is separable" — separability is Artin's, and the only
role of `ι ≠ 1` is to make the group have order `2` rather than `1`.

Unlike `isSeparable_mulByTwoFieldRange_of_isAlgClosed` this is an `instance`: it has no hypothesis
that is not a typeclass. -/
instance isSeparable_ratFuncRange : Algebra.IsSeparable ↥(ratFuncRange W) W.FunctionField := by
  haveI : Algebra.IsSeparable ↥(IntermediateField.fixedField (negYGroup W)) W.FunctionField :=
    inferInstanceAs (Algebra.IsSeparable
      ↥(FixedPoints.subfield ↥(negYGroup W) W.FunctionField) W.FunctionField)
  rw [ratFuncRange_eq_fixedField_negYGroup]
  infer_instance

/-- **`F(W)` is normal over `F(x)`**, by the same route off `FixedPoints.normal`. -/
instance normal_ratFuncRange : Normal ↥(ratFuncRange W) W.FunctionField := by
  haveI : Normal ↥(IntermediateField.fixedField (negYGroup W)) W.FunctionField :=
    inferInstanceAs (Normal ↥(FixedPoints.subfield ↥(negYGroup W) W.FunctionField) W.FunctionField)
  rw [ratFuncRange_eq_fixedField_negYGroup]
  infer_instance

/-- **`F(W) / F(x)` is Galois.**  `IsGalois` is separable plus normal, and both halves are
`isSeparable_ratFuncRange` and `normal_ratFuncRange`. -/
instance isGalois_ratFuncRange : IsGalois ↥(ratFuncRange W) W.FunctionField := ⟨⟩

/-! ### Transport to `RatFunc F` and to `FractionRing F[X]` -/

/-- The tautological isomorphism `RatFunc F ≃+* F(x)`: `ratFuncRange W` is by definition the field
range of `RatFunc F → F(W)`, and that map is injective.  This is the same equivalence
`finrank_ratFuncRange` uses to move the degree across, restated as a `RingEquiv` because
`IsGalois.of_equiv_equiv` consumes one. -/
noncomputable def ratFuncEquivRatFuncRange (W : Affine F) :
    RatFunc F ≃+* ↥(ratFuncRange W) :=
  (AlgHom.equivFieldRange (IsScalarTower.toAlgHom F (RatFunc F) W.FunctionField)).toRingEquiv

/-- The commuting square `IsGalois.of_equiv_equiv` needs: `F(x) → F(W)` is the inclusion, and
composing it with `ratFuncEquivRatFuncRange⁻¹` is the algebra map of `RatFunc F`.

⚠️ Stated for an arbitrary Weierstrass curve: it is the tautology that the field range of an
injection is its image, and `[W.IsElliptic]` plays no part in it. -/
theorem algebraMap_comp_ratFuncEquivRatFuncRange_symm (W : Affine F) :
    (algebraMap (RatFunc F) W.FunctionField).comp
        ((ratFuncEquivRatFuncRange W).symm : ↥(ratFuncRange W) →+* RatFunc F)
      = ((RingEquiv.refl W.FunctionField) : W.FunctionField →+* W.FunctionField).comp
        (algebraMap ↥(ratFuncRange W) W.FunctionField) := by
  ext f
  exact congrArg Subtype.val ((ratFuncEquivRatFuncRange W).apply_symm_apply f)

/-- **`F(W)` is Galois over `RatFunc F`.**

⚠️ This is the statement `EllipticCurves.FunctionField.PlaceDegreeComparison`'s `## Scope` section
used to deny.  It is the same extension as `isGalois_ratFuncRange` — `RatFunc F` and
`ratFuncRange W` are isomorphic as `F`-algebras over `F(W)` — carried across by
`IsGalois.of_equiv_equiv`. -/
instance isGalois_ratFunc : IsGalois (RatFunc F) W.FunctionField :=
  IsGalois.of_equiv_equiv (algebraMap_comp_ratFuncEquivRatFuncRange_symm W)

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **`F(W)` is Galois over `FractionRing F[X]`** — the shape
`Ideal.relNorm_eq_pow_of_isPrime_isGalois` literally consumes, since `F(W)` is by definition
`FractionRing F[W]`.

⚠️ **This is a `theorem` and cannot be an `instance`**, because the algebra structure
`Algebra (FractionRing F[X]) F(W)` it is stated against comes from
`FractionRing.liftAlgebra`, which Mathlib deliberately keeps
`local` (`Mathlib.RingTheory.NormalClosure` records that making it global causes timeouts).  A
consumer writes `attribute [local instance] FractionRing.liftAlgebra` — exactly as
`Mathlib.RingTheory.Ideal.Norm.RelNorm` does — and then this fires.

⚠️ **It does not on its own give the degree comparison** — that is a statement about places and
degree functions, and this file mentions neither.  It is the *hypothesis* the comparison consumes:
`degPt_eq_residueDegreeProj` (`EllipticCurves.FunctionField.PlaceDegreeComparison`) fires this
theorem with `haveI`, its projective form is `degProjPt_eq_residueDegreeProj`, and both hold over
an arbitrary base field.

⚠️ **This paragraph used to continue** *"see the `## Scope` section of the module docstring for the
hypotheses of `relNorm_eq_pow_of_isPrime_isGalois` that remain undischarged"*.  **That forward
reference is retired**: the `## Scope` section now records that there are none — all four
typeclasses are supplied by `inferInstance` in this tree — so it promised the reader a list the
section it points at says does not exist.

The proof is `IsGalois.of_equiv_equiv` along `FractionRing.algEquiv F[X] (RatFunc F)`, whose
commuting square is checked on `F[X]` by `IsLocalization.ringHom_ext` — two ring homomorphisms out
of a localisation agreeing on the base are equal — and then by `AlgEquiv.commutes` and the two
scalar towers. -/
theorem isGalois_fractionRing_polynomial : IsGalois (FractionRing F[X]) W.FunctionField := by
  refine IsGalois.of_equiv_equiv (F := RatFunc F) (E := W.FunctionField)
    (f := (FractionRing.algEquiv F[X] (RatFunc F)).symm.toRingEquiv)
    (g := RingEquiv.refl W.FunctionField) ?_
  refine IsLocalization.ringHom_ext (nonZeroDivisors F[X]) (RingHom.ext fun p => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_ringEquiv, RingEquiv.coe_refl, id_eq]
  rw [(FractionRing.algEquiv F[X] (RatFunc F)).symm.commutes p,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-! ### Non-vacuity

Every result in this file needs `[W.IsElliptic]` and nothing else, so a curve over `ℚ` certifies
that the hypothesis class is inhabited.  ⚠️ But `ℚ` certifies only the *easy* half: over a field of
characteristic zero `Algebra.IsSeparable.of_integral` already gives separability, and it is
characteristic `2` where these results say something the `CharZero` instances did not.  So the
characteristic-`2` curve `y² + y = x³` over `ZMod 2` — the same one `NegYInvolution` commits, and
the one with `a₁ = 0`, so that `a₃ = 1` is the only reason `ι ≠ 1` — is committed as well. -/

section Nonvacuity

/-- The curve `y² = x³ − x` over `ℚ`, of discriminant `64`. -/
private def exampleCurveRat : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurveRat.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveRat, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

example : IsGalois (RatFunc ℚ) exampleCurveRat.FunctionField := isGalois_ratFunc

/-- The supersingular curve `y² + y = x³` over `ZMod 2`, of discriminant `−27 = 1`. -/
private def exampleCurveChar2 : Affine (ZMod 2) := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveChar2.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide +kernel

/-- ⚠️ The certificate that matters: the base field has characteristic `2`, and `F(W)` is still
separable — indeed Galois — over `F(x)`. -/
example : (2 : ZMod 2) = 0 ∧ Algebra.IsSeparable ↥(ratFuncRange exampleCurveChar2)
    exampleCurveChar2.FunctionField ∧
    IsGalois (RatFunc (ZMod 2)) exampleCurveChar2.FunctionField :=
  ⟨by decide, isSeparable_ratFuncRange, isGalois_ratFunc⟩

/-- The sandwich, on a curve that exists. -/
example : ratFuncRange exampleCurveChar2
    = IntermediateField.fixedField (negYGroup exampleCurveChar2) :=
  ratFuncRange_eq_fixedField_negYGroup

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
