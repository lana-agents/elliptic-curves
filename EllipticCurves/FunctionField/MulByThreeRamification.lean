/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByThreeGalois
import EllipticCurves.FunctionField.MulByThreePlacePullback
import EllipticCurves.FunctionField.PlaceRamificationInertia

/-!
# The fundamental identity for `[3]`: `∑_{p ↦ q} e_p = 9`

`MulByThreePlacePullback` (`#814`) instantiates `PlacePullback` and `PullbackDivisor` at
`φ = mulByThreeEndo h2 h3`, giving `comapProjPointThree`, `ramificationIdxThree` and
`pullbackDivisorThree`.  What it does not give is the **arithmetic** those indices satisfy.  This
file supplies it:

```
∑_{p ↦ q} e_p = 9 = deg [3]
```

over an algebraically closed base field of characteristic `≠ 2, 3` — the `n = 3` analogue of
`#763`'s `sum_ramificationIdxTwo_eq_four`, which is what made `#774`'s `[2]`-fibre description
cheap.

Like its predecessor this file adds no place theory.  `PlaceBelowIntegralClosure`,
`PlacePrimesOverFibre` and `PlaceRamificationInertia` state everything for an **arbitrary** `φ`
fixing `F` with `F(W)` integral over its image, and each records a `[2]∗` instantiation in a final
section; `PlaceRamificationInertia` says in its own voice that *"`[3]∗` and general `[n]∗` will use
it unchanged"*.  Every declaration below is one of those general theorems applied to `[3]∗`.

## What the `9` comes from, and why it is not a transcription of the `4`

`sum_ramificationIdxTwo_eq_four` reads its right-hand side off
`finrank_integralClosure_placeBelowTwo`, which reads it off `#682`'s `[F(W) : [2]∗F(W)] = 4`.  The
`n = 3` chain is the same three links, but the bottom one is a **different theorem**:
`finrank_mulByThreeFieldRange` (`MulByThreeDegree`), whose proof needs
`isCoprime_Φ_three_ΨSq_three` — a congruence argument, because the `n = 2` route's explicit Bézout
certificate is a `17 × 17` Sylvester determinant at `n = 3` and is not viable.  That theorem is
merged; this file consumes it and does not redo it.

The separability that `#754`/`#755` carry as a hypothesis is likewise supplied by a merged `n = 3`
theorem and not by an analogy: `isSeparable_mulByThreeEndoFieldRange_of_isAlgClosed`
(`MulByThreeGalois`, `#784`), which comes from `F(W)/[3]∗F(W)` being Galois with group `E[3]`.

So the three inputs that are `n`-dependent are all merged, and the work here is their assembly.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.finrank_mulByThreeEndoFieldRange` — `[F(W) : [3]∗F(W)]
  = 9` in the `Subfield` presentation `ValuationSubring` needs, and
  `module_finite_mulByThreeEndoFieldRange`;
* `WeierstrassCurve.Affine.CoordinateRing.placeBelowThree` — the place of `[3]∗F(W)` below `q`,
  with its `IsDiscreteValuationRing` and `Module.IsTorsionFree` instances;
* `WeierstrassCurve.Affine.CoordinateRing.finrank_integralClosure_placeBelowThree` — the rank `9`
  of its integral closure, the right-hand side of the identity at the ring level;
* `WeierstrassCurve.Affine.CoordinateRing.primesOverEquivFibreThree` and
  `nonempty_fibre_comapProjPointThree` — the `primesOver` ↔ fibre dictionary, and the surjectivity
  of `[3]` on places that follows from it without any of the identity;
* **`WeierstrassCurve.Affine.CoordinateRing.sum_ramificationIdxThree_eq_nine`** — the fundamental
  identity, over `[IsAlgClosed F]`;
* `WeierstrassCurve.Affine.CoordinateRing.card_fibre_comapProjPointThree_le_nine` — hence at most
  nine places above a place, and with `nonempty_fibre_comapProjPointThree` at least one.  That pair
  is what `#774` consumed at `n = 2`.

## What is **not** here

* **The place calculus itself.**  `comapProjPointThree`, `ramificationIdxThree`,
  `pullbackDivisorThree`, `divisorProj_mulByThreeEndo` and the behaviour at `O` are
  `MulByThreePlacePullback` (`#814`), which this file imports and does not restate.
* **Any value of `comapProjPointThree` at an affine point.**  `#814` computes it at `O`; this file
  supplies the *arithmetic* a fibre description counts against, and not one value of the map.  That
  description is `EllipticCurves.FunctionField.MulByThreeFibre`, the `n = 3` mirror of
  `MulByTwoFibreInfinity` and `MulByTwoFibreAffine`, which consumes both this file and
  `Torsion.TriplingCoords` (`#811`).
* **`hprin` at `n = 3`, and therefore `#418`.**  Two rungs above this one, in
  `EllipticCurves.FunctionField.PullbackPrincipalityThree`, via
  `EllipticCurves.FunctionField.MulByThreeFibre`.  Do not read
  `sum_ramificationIdxThree_eq_nine` as saying anything about `E[3]`: what is counted here is
  *places of `F(W)`*, and the passage to points runs through "a separable isogeny has `#ker = deg`",
  which is nowhere in this tree.  The merged count `#E[3] = 9` (`card_torsion_three`,
  `Torsion.ThreeTorsionStructure`) is an independent theorem and is **not** used here.
  `PlaceRamificationInertia` carries the same warning at `n = 2`.
* **A residue-degree companion.**  ⚠️ **The clause this bullet used to carry has been paid** — it
  read *"`sum_ramificationIdxTwo_mul_residueDegreeTwo` has no mirror below, because
  `residueDegreeThree` does not exist; the identity it decorates is the one proved here, and adding
  the decoration is a separate, purely notational step"*.  It was a correct prediction: the step is
  `EllipticCurves.FunctionField.MulByThreeResidueDegree`, which defines `residueDegreeThree` off
  `#744`'s `φ`-generic `residueDegreeComap` and derives
  `sum_ramificationIdxThree_mul_residueDegreeThree` from `sum_ramificationIdxThree_eq_nine` below in
  three lines.  ⚠️ It is still not *here*, and cannot be: that file imports this one.
* **General `n`.**  ⚠️ **The clause this bullet used to carry has been paid** — it read
  *"`mulByNEndo` does not exist; `[2]∗` and `[3]∗` are the two concrete endomorphisms this tree
  has"*.  `[n]∗` at every `n` is `mulByNEndo`,
  `EllipticCurves.FunctionField.MulByNPullback`, with its place layer in
  `EllipticCurves.FunctionField.MulByNPlacePullback`.  ⚠️ The `9` is `[3]`-specific and nothing
  general-`n` is attempted here.
-/

open Module IsDedekindDomain

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

variable [IsDedekindDomain W.CoordinateRing]

/-! ### The degree of `[3]∗` in the `Subfield` presentation

`MulByThreeDegree` states `[F(W) : [3]∗F(W)] = 9` for the `AlgHom.fieldRange` (an
`IntermediateField`) and for the `RingHom.range` (a `Subring`).  `ValuationSubring L` needs `L` to
be a `Field` *type*, which the `Subfield` coercion is and the `Subring` coercion is not, so the
result has to be carried across.  `rangeEquivFieldRangeThree` is that transport and is the identity
on elements — the `n = 3` twin of `rangeEquivFieldRangeTwo`. -/

/-- The identity map, read as an isomorphism from the `RingHom.range` of `[3]∗` to its
`fieldRange`.  Both are the same subset of `F(W)`, but they live in different subobject
lattices. -/
def rangeEquivFieldRangeThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ↥(mulByThreeEndo (W := W) h2 h3).range ≃+* ↥(mulByThreeEndo (W := W) h2 h3).fieldRange where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`[F(W) : [3]∗F(W)] = 9`, for the subfield.**  `finrank_mulByThreeRange_functionField`
(`MulByThreeDegree`) in the `Subfield` presentation this file needs. -/
theorem finrank_mulByThreeEndoFieldRange [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    finrank ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField = 9 := by
  letI : Algebra ↥(mulByThreeEndo (W := W) h2 h3).range W.FunctionField :=
    ((mulByThreeEndo (W := W) h2 h3).range.subtype).toAlgebra
  rw [← Algebra.finrank_eq_of_equiv_equiv (rangeEquivFieldRangeThree h2 h3)
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)]
  exact finrank_mulByThreeRange_functionField h2 h3

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`F(W)` is a finite extension of the subfield `[3]∗F(W)`**, off the degree being `9 ≠ 0`. -/
theorem module_finite_mulByThreeEndoFieldRange [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    Module.Finite ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField :=
  Module.finite_of_finrank_pos (by rw [finrank_mulByThreeEndoFieldRange h2 h3]; norm_num)

/-! ### The place below, and the rank of its integral closure -/

variable (W) in
/-- **The valuation ring of the place of `[3]∗F(W)` below `q`.** -/
noncomputable def placeBelowThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (q : ProjPoint W) :
    ValuationSubring ↥(mulByThreeEndo (W := W) h2 h3).fieldRange :=
  placeBelow (mulByThreeEndo h2 h3) q

/-- **A place of `[3]∗F(W)` is a discrete valuation ring.**  Restated at the `[3]∗` layer because
`placeBelowThree` is a `def`, not an `abbrev`, and so is opaque to instance search — the same
reason `instIsDiscreteValuationRingPlaceBelowTwo` is restated at the `[2]∗` layer. -/
instance instIsDiscreteValuationRingPlaceBelowThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (q : ProjPoint W) : IsDiscreteValuationRing ↥(placeBelowThree W h2 h3 q) :=
  instIsDiscreteValuationRingPlaceBelow q

/-- **`F(W)` is torsion-free over a place of `[3]∗F(W)`.** -/
instance instIsTorsionFreePlaceBelowThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (q : ProjPoint W) : Module.IsTorsionFree ↥(placeBelowThree W h2 h3 q) W.FunctionField :=
  instIsTorsionFreePlaceBelow q

/-- The `[3]∗` form of `placeBelow_comapProjPoint`: the place of `[3]∗F(W)` below a place `p` of
`F(W)` is the intersection of `[3]∗F(W)` with `placeOf W p`. -/
theorem placeBelowThree_comapProjPointThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (p : ProjPoint W) :
    placeBelowThree W h2 h3 (comapProjPointThree h2 h3 p)
      = (placeOf W p).comap ((mulByThreeEndo (W := W) h2 h3).fieldRange.subtype) :=
  placeBelow_comapProjPoint _ _ p

/-- **The integral closure of a place of `[3]∗F(W)` is flat over it.**  No hypothesis on the
characteristic and none on `F`. -/
theorem module_flat_integralClosure_placeBelowThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (q : ProjPoint W) :
    Module.Flat ↥(placeBelowThree W h2 h3 q)
      ↥(integralClosure ↥(placeBelowThree W h2 h3 q) W.FunctionField) :=
  module_flat_integralClosure_placeBelow q

/-- **`F(W)` is module-finite over a place of `[3]∗F(W)`, given separability.** -/
theorem module_finite_integralClosure_placeBelowThree [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    Module.Finite ↥(placeBelowThree W h2 h3 q)
      ↥(integralClosure ↥(placeBelowThree W h2 h3 q) W.FunctionField) := by
  haveI := module_finite_mulByThreeEndoFieldRange (W := W) h2 h3
  haveI := hsep
  exact module_finite_integralClosure_placeBelow q

/-- **The integral closure of a place of `[3]∗F(W)` has rank `9` over it**, given separability.

The right-hand side of the fundamental identity, at the ring level: `finrank_mulByThreeFieldRange`
gives `[F(W) : [3]∗F(W)] = 9` for the *fields*, and `finrank_integralClosure_placeBelow` carries it
down to the local rings. -/
theorem finrank_integralClosure_placeBelowThree [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0)
    (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    finrank ↥(placeBelowThree W h2 h3 q)
      ↥(integralClosure ↥(placeBelowThree W h2 h3 q) W.FunctionField) = 9 := by
  haveI := module_finite_mulByThreeEndoFieldRange (W := W) h2 h3
  haveI := hsep
  exact (finrank_integralClosure_placeBelow (φ := mulByThreeEndo h2 h3) q).trans
    (finrank_mulByThreeEndoFieldRange h2 h3)

/-! ### The `primesOver` ↔ fibre dictionary -/

section Fibre

variable [W.IsElliptic] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
  (hsep : Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField)
  (q : ProjPoint W)

include hsep in
/-- **The `primesOver` ↔ fibre dictionary for `[3]∗`.** -/
noncomputable def primesOverEquivFibreThree :
    ↥((IsLocalRing.maximalIdeal ↥(placeBelowThree W h2 h3 q)).primesOver
        ↥(integralClosure ↥(placeBelowThree W h2 h3 q) W.FunctionField))
      ≃ ↥(comapProjPointThree h2 h3 ⁻¹' {q}) :=
  haveI := module_finite_mulByThreeEndoFieldRange (W := W) h2 h3
  haveI := hsep
  primesOverEquivFibre (mulByThreeEndo_algebraMap_base h2 h3)
    (mulByThreeEndo_isIntegralElem h2 h3)

include hsep in
/-- **The fibre of `[3]` over a place is nonempty** — classically, `[3]` is surjective on places.
This is the consequence of the dictionary that needs no part of the fundamental identity. -/
theorem nonempty_fibre_comapProjPointThree :
    ((comapProjPointThree (W := W) h2 h3) ⁻¹' {q}).Nonempty :=
  haveI := module_finite_mulByThreeEndoFieldRange (W := W) h2 h3
  haveI := hsep
  nonempty_fibre_comapProjPoint (mulByThreeEndo_algebraMap_base h2 h3)
    (mulByThreeEndo_isIntegralElem h2 h3)

include hsep in
/-- **Finitely many primes lie over the maximal ideal of a place of `[3]∗F(W)`.**  The `Fintype`
`Ideal.sum_ramification_inertia_eq_finrank` asks for is `Fintype.ofFinite` of this, and is
noncomputable — keep it in a `haveI` at the use site. -/
theorem finite_primesOver_maximalIdeal_placeBelowThree :
    Finite ↥((IsLocalRing.maximalIdeal ↥(placeBelowThree W h2 h3 q)).primesOver
      ↥(integralClosure ↥(placeBelowThree W h2 h3 q) W.FunctionField)) :=
  haveI := module_finite_mulByThreeEndoFieldRange (W := W) h2 h3
  haveI := hsep
  finite_primesOver_maximalIdeal_placeBelow (mulByThreeEndo_algebraMap_base h2 h3)
    (mulByThreeEndo_isIntegralElem h2 h3)

end Fibre

/-! ### The unconditional companions over an algebraically closed base field

`MulByThreeGalois` (`#784`) discharges the separability hypothesis over `[IsAlgClosed F]`, which is
the hypothesis the `#418`/`#465` front carries.  These are the resulting hypothesis-free forms. -/

section IsAlgClosed

variable [W.IsElliptic] [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (q : ProjPoint W)

/-- **The integral closure of a place of `[3]∗F(W)` is module-finite over it**, over an
algebraically closed base field. -/
theorem module_finite_integralClosure_placeBelowThree_of_isAlgClosed :
    Module.Finite ↥(placeBelowThree W h2 h3 q)
      ↥(integralClosure ↥(placeBelowThree W h2 h3 q) W.FunctionField) :=
  module_finite_integralClosure_placeBelowThree h2 h3
    (isSeparable_mulByThreeEndoFieldRange_of_isAlgClosed h2 h3) q

/-- **The rank is `9`**, over an algebraically closed base field. -/
theorem finrank_integralClosure_placeBelowThree_of_isAlgClosed :
    finrank ↥(placeBelowThree W h2 h3 q)
      ↥(integralClosure ↥(placeBelowThree W h2 h3 q) W.FunctionField) = 9 :=
  finrank_integralClosure_placeBelowThree h2 h3
    (isSeparable_mulByThreeEndoFieldRange_of_isAlgClosed h2 h3) q

/-- **The `primesOver` ↔ fibre dictionary**, over an algebraically closed base field.

⚠️ `nolint defsWithUnderscore` (`#1277`): the `_of_isAlgClosed` suffix is the hypothesis-naming
convention this file's theorems use — `finrank_integralClosure_placeBelowThree_of_isAlgClosed`
directly above is the same name for the same hypothesis — and renaming the `def` alone would break
that pairing to satisfy a linter that flags underscores in `def` names. -/
@[nolint defsWithUnderscore]
noncomputable def primesOverEquivFibreThree_of_isAlgClosed :
    ↥((IsLocalRing.maximalIdeal ↥(placeBelowThree W h2 h3 q)).primesOver
        ↥(integralClosure ↥(placeBelowThree W h2 h3 q) W.FunctionField))
      ≃ ↥(comapProjPointThree h2 h3 ⁻¹' {q}) :=
  primesOverEquivFibreThree h2 h3 (isSeparable_mulByThreeEndoFieldRange_of_isAlgClosed h2 h3) q

/-- **The fibre of `[3]` over a place is nonempty**, over an algebraically closed base field. -/
theorem nonempty_fibre_comapProjPointThree_of_isAlgClosed :
    ((comapProjPointThree (W := W) h2 h3) ⁻¹' {q}).Nonempty :=
  nonempty_fibre_comapProjPointThree h2 h3
    (isSeparable_mulByThreeEndoFieldRange_of_isAlgClosed h2 h3) q

/-- **Finitely many primes lie over the maximal ideal of a place of `[3]∗F(W)`**, over an
algebraically closed base field. -/
theorem finite_primesOver_maximalIdeal_placeBelowThree_of_isAlgClosed :
    Finite ↥((IsLocalRing.maximalIdeal ↥(placeBelowThree W h2 h3 q)).primesOver
      ↥(integralClosure ↥(placeBelowThree W h2 h3 q) W.FunctionField)) :=
  finite_primesOver_maximalIdeal_placeBelowThree h2 h3
    (isSeparable_mulByThreeEndoFieldRange_of_isAlgClosed h2 h3) q

/-! #### The identity -/

/-- **The fundamental identity for `[3]`**: over an algebraically closed base field of
characteristic `≠ 2, 3`, the ramification indices of the places above a place of `[3]∗F(W)` sum to
`9`.

This is `∑_{p ↦ q} e_p = deg [3]` for the *projective* curve, and it is the `n = 3` analogue of
`#763`'s `sum_ramificationIdxTwo_eq_four` — the arithmetic that made `#774`'s fibre description
cheap at `n = 2`.

⚠️ It does **not** say `#E[3] = 9`.  What is counted here is places of `F(W)`; the link from the
degree of the extension to a count of `3`-torsion points runs through "a separable isogeny has
`#ker = deg`", which is nowhere in this tree.  The merged `card_torsion_three` is a genuinely
independent theorem and is not used above. -/
theorem sum_ramificationIdxThree_eq_nine :
    ∑ p ∈ (finite_comapProjPointThree_preimage_singleton h2 h3 q).toFinset,
      (ramificationIdxThree h2 h3 p).toNat = 9 := by
  haveI := module_finite_mulByThreeEndoFieldRange (W := W) h2 h3
  haveI := isSeparable_mulByThreeEndoFieldRange_of_isAlgClosed (W := W) h2 h3
  rw [show (9 : ℕ) = finrank ↥(placeBelowThree W h2 h3 q)
      ↥(integralClosure ↥(placeBelowThree W h2 h3 q) W.FunctionField) from
    (finrank_integralClosure_placeBelowThree_of_isAlgClosed h2 h3 q).symm]
  exact sum_toNat_ramificationIdx_fibre (mulByThreeEndo_algebraMap_base h2 h3)
    (mulByThreeEndo_isIntegralElem h2 h3)

/-- **A place of `[3]∗F(W)` has at most nine places above it.**  Each ramification index is at least
`1` and they sum to `9`.

With `nonempty_fibre_comapProjPointThree_of_isAlgClosed` this pins the fibre between `1` and `9`
elements, which is the shape the `n = 3` fibre description will consume — the analogue of what
`card_fibre_comapProjPointTwo_le_four` does for `#774`. -/
theorem card_fibre_comapProjPointThree_le_nine :
    (finite_comapProjPointThree_preimage_singleton h2 h3 q).toFinset.card ≤ 9 := by
  rw [Finset.card_eq_sum_ones, ← sum_ramificationIdxThree_eq_nine h2 h3 q]
  exact Finset.sum_le_sum fun p _ => by have := ramificationIdxThree_pos h2 h3 p; omega

end IsAlgClosed

/-! ### Non-vacuity

The headline needs `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` at once, and
every step runs through instance searches on the `ValuationSubring`-of-a-`Subfield` stack that
`#754` found delicate.  A curve on which the whole chain elaborates with nothing supplied by hand is
therefore committed rather than quoted.

`y² + y = x³` over `AlgebraicClosure ℚ` is the `n = 3` certificate curve of this tree, used by
`TranslationActionThree` and `MulByThreeGalois` — the `n = 2` curve `y² = x³ − x` has no rational
`3`-torsion point, and the `ℚ` curve of `MulByThreeDegree` cannot witness a statement that needs an
algebraically closed base field. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`. -/
private noncomputable def exampleCurveThree : Affine exampleField := ⟨0, 0, 1, 0, 0⟩

private instance : exampleCurveThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveThree, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- Hoisted rather than written inline: an inline `by norm_num` for `(2 : exampleField) ≠ 0` is
postponed and leaves the curve a metavariable at the use site. -/
private lemma exampleTwo : (2 : exampleField) ≠ 0 := by norm_num

private lemma exampleThree : (3 : exampleField) ≠ 0 := by norm_num

example : IsDedekindDomain exampleCurveThree.CoordinateRing := inferInstance

/-- **The divisor-level functoriality on a curve that exists.** -/
example {f : exampleCurveThree.FunctionField} (hf : f ≠ 0) :
    divisorProj exampleCurveThree (mulByThreeEndo exampleTwo exampleThree f)
      = pullbackDivisorThree exampleTwo exampleThree (divisorProj exampleCurveThree f) :=
  divisorProj_mulByThreeEndo _ _ hf

/-- **`[F(W) : [3]∗F(W)] = 9` in the `Subfield` presentation**, on the same curve. -/
example : finrank
    ↑(mulByThreeEndo (W := exampleCurveThree) exampleTwo exampleThree).fieldRange
    exampleCurveThree.FunctionField = 9 :=
  finrank_mulByThreeEndoFieldRange exampleTwo exampleThree

/-- **The rank of the integral closure of a place below is `9`**, on the same curve. -/
example (q : ProjPoint exampleCurveThree) :
    finrank ↑(placeBelowThree exampleCurveThree exampleTwo exampleThree q)
      ↑(integralClosure ↑(placeBelowThree exampleCurveThree exampleTwo exampleThree q)
        exampleCurveThree.FunctionField) = 9 :=
  finrank_integralClosure_placeBelowThree_of_isAlgClosed exampleTwo exampleThree q

/-- **The fundamental identity on a curve that exists.** -/
example (q : ProjPoint exampleCurveThree) :
    ∑ p ∈ (finite_comapProjPointThree_preimage_singleton exampleTwo exampleThree q).toFinset,
      (ramificationIdxThree exampleTwo exampleThree p).toNat = 9 :=
  sum_ramificationIdxThree_eq_nine exampleTwo exampleThree q

/-- The fibre is nonempty and has at most nine elements, on the same curve. -/
example (q : ProjPoint exampleCurveThree) :
    ((comapProjPointThree (W := exampleCurveThree) exampleTwo exampleThree) ⁻¹' {q}).Nonempty
      ∧ (finite_comapProjPointThree_preimage_singleton exampleTwo exampleThree q).toFinset.card
          ≤ 9 :=
  ⟨nonempty_fibre_comapProjPointThree_of_isAlgClosed exampleTwo exampleThree q,
    card_fibre_comapProjPointThree_le_nine exampleTwo exampleThree q⟩

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
