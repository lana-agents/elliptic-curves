/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNPlaceComposition
import EllipticCurves.FunctionField.MulByNResidueDegree
import EllipticCurves.FunctionField.MulByNSeparable
import EllipticCurves.FunctionField.PlaceInertiaGeneral

/-!
# The fundamental identity for `[n]∗`: `∑_{p ↦ q} e_p · f_p = [F(W) : [n]∗F(W)]`

`EllipticCurves.FunctionField.PlaceInertiaGeneral` proves the fundamental identity at an
**arbitrary** ring endomorphism `φ` of `F(W)`, over an arbitrary base field:

```
∑_{p ↦ q} e_p · f_p = finrank (placeBelow φ q) (integralClosure (placeBelow φ q) F(W))
```

under `hφF` (`φ` fixes `F`), `hφint` (`φ` is integral), `[Module.Finite ↥φ.fieldRange F(W)]` and
`[Algebra.IsSeparable ↥φ.fieldRange F(W)]`.  Until now it was instantiated at `φ = [2]∗` only.
This file instantiates it at `φ = [n]∗`, and supplies the two instance hypotheses:

* `Module.Finite` is `module_finite_mulByNEndoFieldRange`
  (`EllipticCurves.FunctionField.MulByNIntegral`) at **every** `n` at which `[n]` is non-constant;
* `Algebra.IsSeparable` is `isSeparable_mulByNEndoFieldRange_of_smooth`
  (`EllipticCurves.FunctionField.MulByNSeparable`, `#1219`) at every `3`-smooth `n` over `F̄`, and
  — `isSeparable_mulByNEndoFieldRange_of_charZero` below — at **every** `n` in characteristic zero.

## ⚠️ The identity and the value `n²` are two different theorems, and they have different ranges

The identity's own right-hand side is a `finrank` of an integral closure, not `n²`; turning it into
`n²` is a separate step, and the two do not reach the same indices.

* **The identity** holds at every `n` at which `[n]` is non-constant and `F(W) / [n]∗F(W)` is
  separable — in particular, by the characteristic-zero route, at **every** `n` over `ℚ` or any
  other field of characteristic zero, with no `3`-smoothness and no algebraic closure.  That is
  `sum_ramificationIdxN_mul_residueDegreeN_finrank_of_charZero`.
* **The value `n²`** needs `[F(W) : [n]∗F(W)] = n²`, which
  `EllipticCurves.FunctionField.MulByNComposition` (`#1213`) proves at `3`-smooth `n` and nowhere
  else, so `sum_… = n ^ 2` carries `3`-smoothness even in characteristic zero.

⚠️ Read the `finrank` forms as the theorems and the `n ^ 2` forms as their corollaries at the
indices where the degree is known, not the other way round.  The general-`n` characteristic-zero
identity is strictly the wider statement and is lost if only the `n ^ 2` shape is remembered.

## The chain, and where each link comes from

```
sum_toNat_ramificationIdx_mul_residueDegreeComap_fibre    (PlaceInertiaGeneral, arbitrary φ)
  ⟹ ∑ e_p · f_p = finrank (placeBelowN) (integralClosure …)
finrank_integralClosure_placeBelow                        (#754, arbitrary φ)
  ⟹                = finrank ([n]∗F(W)) F(W)
finrank_mulByNFieldRange_of_smooth                        (#1213, 3-smooth n)
  ⟹                = n²
```

⚠️ There is a presentation mismatch in the middle link and it is the one mechanical obstacle in the
file.  `#1213`'s degree is stated for `mulByNEndoAlgHom` — the `IntermediateField` `fieldRange` —
while the place machinery runs on `mulByNEndo`, the `RingHom` one, because `ValuationSubring ↥L`
needs `L` to be a `Field` type and only the `Subfield` coercion is one.  `#1219`'s
`mulByNFieldRangeEquivSubfield` is the identity map between them;
`finrank_mulByNEndoFieldRange_of_smooth` below is the crossing, and it is the exact general-`n`
analogue of the merged `finrank_mulByTwoEndoFieldRange` and `finrank_mulByThreeEndoFieldRange`.

## What was already there at `n = 2` and `n = 3`, and what is genuinely new

⚠️ `#1221` was filed saying *"there is no `n = 3` instantiation at all"*.  **That is wrong**, and
the record should say so: `sum_ramificationIdxThree_mul_residueDegreeThree`
(`EllipticCurves.FunctionField.MulByThreeResidueDegree`) has been merged for months.  What is true
is narrower and still worth having:

* that theorem carries `[IsAlgClosed F]` and is proved by *collapsing* — it rewrites every `f_p` to
  `1` and quotes `sum_ramificationIdxThree_eq_nine` — so it says nothing over a base field that is
  not algebraically closed.  The `_of_isSeparable` and `_of_charZero` forms below **are** new at
  `n = 3`, and over `ℚ` the identity at `n = 3` was not available in any form;
* it is stated in the `[3]`-indexing, not the `[n]`-indexing, so no consumer holding an
  `n` can use it.  `residueDegreeN_three` (`EllipticCurves.FunctionField.MulByNResidueDegree`) and
  `sum_ramificationIdxN_mul_residueDegreeN_three` below are the bridge, and
  `sum_ramificationIdxThree_mul_residueDegreeThree_of_charZero` is the
  `[3]`-indexed statement they buy — which is, verbatim, what `MulByThreeResidueDegree`'s `## Scope`
  section **used to say** is still absent.  ⚠️ **It no longer does, and the section is `## Scope`
  and never was a `## What is not here`.**  That bullet was retired in the same commit that created
  this file (`4a30e82`, `#1221`) and now names
  `sum_ramificationIdxThree_mul_residueDegreeThree_of_charZero` — i.e. this file — as exactly what
  supplies it.  The citation is kept because it is the *reason* the statement below is written in
  the `[3]`-indexing at all; it is not a live gap.

At `n = 2`, `sum_ramificationIdxTwo_mul_residueDegreeTwo_of_isSeparable` and `…_of_charZero`
(`PlaceInertiaGeneral`) already say everything below at that index; the content there is the bridge
`sum_ramificationIdxN_mul_residueDegreeN_two`, nothing more.

## Main results

⚠️ Every public declaration of this file is listed, and all are in namespace
`WeierstrassCurve.Affine.CoordinateRing`.  ⚠️ `residueDegreeN` itself is **not** among them: it,
its tower formula, `residueDegreeN_none_eq_one` and the consistency pair `residueDegreeN_two` /
`residueDegreeN_three` are `EllipticCurves.FunctionField.MulByNResidueDegree` (`#1225`), and this
file consumes them rather than restating them.

* `placeBelowN`, with its `IsDiscreteValuationRing` and `Module.IsTorsionFree` instances, and
  `placeBelowN_comapProjPointN` — the place of `[n]∗F(W)` below `q`;
* `finrank_mulByNEndoFieldRange_of_smooth` — `[F(W) : [n]∗F(W)] = n²` in the `Subfield`
  presentation.  ⚠️ **No `[IsAlgClosed F]`**: this is `#1213`'s degree, which needs none;
* `isSeparable_mulByNEndoFieldRange_of_charZero` — separability at **every** `n` in characteristic
  zero, the general-`n` form of the merged `isSeparable_mulByTwoEndoFieldRange`.  ⚠️ Incomparable
  with `#1219`'s: neither `[CharZero F]` nor `[IsAlgClosed F]` implies the other, and this one is
  not restricted to `3`-smooth `n`;
* `module_finite_integralClosure_placeBelowN_of_isSeparable` and
  `finrank_integralClosure_placeBelowN_of_smooth` — the right-hand side at the ring level;
* **`sum_ramificationIdxN_mul_residueDegreeN_finrank`** and
  **`…_finrank_of_charZero`** — **the identity**, `∑_{p ↦ q} e_p · f_p = [F(W) : [n]∗F(W)]`, at
  every `n` at which `[n]∗F(W)` is separably closed below and at every `n` in characteristic zero;
* **`sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable`**, **`…_of_smooth`** and
  **`…_of_charZero`** — the same with the right-hand side evaluated, `= n ^ 2`, at `3`-smooth `n`;
* `sum_ramificationIdxN_of_smooth` — the collapsed form `∑_{p ↦ q} e_p = n²` over `F̄`, the
  general-`n` shape of `sum_ramificationIdxTwo_eq_four` and `sum_ramificationIdxThree_eq_nine`;
* `sum_ramificationIdxN_mul_residueDegreeN_two` and `…_three` — the sum-level consistency with the
  two merged instantiations;
* **`sum_ramificationIdxThree_mul_residueDegreeThree_of_charZero`** — `∑_{p ↦ q} e_p · f_p = 9` in
  the `[3]`-indexing with **no `[IsAlgClosed F]`**, which `MulByThreeResidueDegree` names as what is
  still absent.

## ⚠️ What this does *not* give

* **Not `#E[n] = n²`.**  `EllipticCurves.FunctionField.PlaceRamificationInertia`,
  `EllipticCurves.FunctionField.PlacePullback` and
  `EllipticCurves.FunctionField.MulByTwoFibreInfinity` all record that the counting step *"a
  separable isogeny has as many points in its kernel as its degree"* is nowhere in this tree.
  Widening the fundamental identity does not add it.  What is counted below is **places of `F(W)`
  in a fibre**, weighted by ramification and residue degree; the passage to points is a different
  theorem.
* **Nothing at `n = 5` with the value `n²`**, because `#1213`'s degree stops there.  The identity
  itself does reach `n = 5` in characteristic zero — with `[F(W) : [5]∗F(W)]` on the right, which
  this tree cannot yet evaluate.
* **Not `hprin`** (`#962`).  `PlaceInertiaGeneral`'s `## Scope` records that it removes one of three
  `[IsAlgClosed F]` inputs to `exists_nsmul_divisor_eq_divisor_mulByTwoEndo` and not the other two;
  that accounting is unchanged at general `n`, and nothing below touches `card_torsion_two` or
  `exists_nsmul_two_eq`.
* **No value for any individual `e_p` or `f_p`.**  `ramificationIdxN_none_of_smooth`
  (`MulByNPlaceComposition`) gives `e_∞ = 1` and `residueDegreeN_none_eq_one`
  (`MulByNResidueDegree`) gives `f_∞ = 1`; at every other place both are left as they are, exactly
  as at `n = 2`.
* **No place with `f_p > 1` exhibited.**  As `PlaceInertiaGeneral` says of itself: the
  characteristic-zero statements are strictly stronger than their `[IsAlgClosed F]` siblings
  because they *apply* over a field that is not algebraically closed, which is what the certificate
  below shows; producing a closed point of degree `2` on a named curve is a different piece of work.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, III.1.11.
-/

open Module IsDedekindDomain

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-! ### The relative residue degree of `[n]∗`

⚠️ Not defined here.  `residueDegreeN`, its tower formula
`residueDegreeProj_mul_residueDegreeN`, `residueDegreeN_none_eq_one` (`f_∞ = 1` at **every** `n`)
and the consistency pair `residueDegreeN_two` / `residueDegreeN_three` are
`EllipticCurves.FunctionField.MulByNResidueDegree` (`#1225`), which this file imports; the
`φ`-congruence they are proved by is `residueDegreeComap_congr`
(`EllipticCurves.FunctionField.PlaceResidueComap`).  Everything below consumes them. -/

namespace CoordinateRing

variable [W.IsElliptic]

/-! ### The place of `[n]∗F(W)` below a place of `F(W)` -/

variable (W) in
/-- **The valuation ring of the place of `[n]∗F(W)` below `q`.**  The `[n]∗` instantiation of
`placeBelow` (`#754`), and the general-`n` form of the merged `placeBelowTwo` and
`placeBelowThree`. -/
noncomputable def placeBelowN (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ValuationSubring ↥(mulByNEndo n h).fieldRange :=
  placeBelow (mulByNEndo n h) q

/-- **A place of `[n]∗F(W)` is a discrete valuation ring.**  Restated at the `[n]∗` layer for the
reason `placeBelowTwo` restates it: `placeBelowN` is a `def` rather than an `abbrev`, so search
does not see through it to the general instance.  `IsNoetherianRing` and `IsPrincipalIdealRing`
follow from this one. -/
instance instIsDiscreteValuationRingPlaceBelowN (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    IsDiscreteValuationRing ↥(placeBelowN W n h q) :=
  instIsDiscreteValuationRingPlaceBelow q

/-- **`F(W)` is torsion-free over a place of `[n]∗F(W)`**, restated at the `[n]∗` layer for the same
reason. -/
instance instIsTorsionFreePlaceBelowN (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    Module.IsTorsionFree ↥(placeBelowN W n h q) W.FunctionField :=
  instIsTorsionFreePlaceBelow q

/-- **The place of `[n]∗F(W)` below `p` is `[n]∗F(W) ∩ placeOf W p`**, the classical description.
The `[n]∗` form of `placeBelow_comapProjPoint`. -/
theorem placeBelowN_comapProjPointN (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    placeBelowN W n h (comapProjPointN n h p)
      = (placeOf W p).comap ((mulByNEndo n h).fieldRange.subtype) :=
  placeBelow_comapProjPoint _ _ p

/-! ### The two hypotheses of the identity, at `[n]∗` -/

omit [IsDedekindDomain W.CoordinateRing] in
/-- **`[F(W) : [n]∗F(W)] = n²` at every `3`-smooth `n ≠ 0`, for the subfield.**
`finrank_mulByNFieldRange_of_smooth` (`#1213`) in the `Subfield` presentation the place machinery
needs, crossed along `#1219`'s `mulByNFieldRangeEquivSubfield`.

⚠️ **No `[IsAlgClosed F]` and no separability.**  This is the degree, which needs neither; only the
statements below it that consume `Algebra.IsSeparable` do.  The general-`n` form of the merged
`finrank_mulByTwoEndoFieldRange` and `finrank_mulByThreeEndoFieldRange`, and their proof verbatim
with a different equiv. -/
theorem finrank_mulByNEndoFieldRange_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    finrank ↥(mulByNEndo n h).fieldRange W.FunctionField = n ^ 2 := by
  rw [← Algebra.finrank_eq_of_equiv_equiv (mulByNFieldRangeEquivSubfield n h)
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)]
  exact finrank_mulByNFieldRange_of_smooth h2 h3 hn hfac h

omit [IsDedekindDomain W.CoordinateRing] in
/-- **In characteristic zero, `F(W)` is separable over `[n]∗F(W)` at every `n` at which `[n]` is
non-constant.**

The extension is finite (`module_finite_mulByNEndoFieldRange`, general `n`), hence integral, and
`Algebra.IsSeparable.of_integral` is an instance over a characteristic-zero base.  `CharZero` is
transported twice, from `F` to `F(W)` along the injective structure map and from `F(W)` down to the
subfield — the merged `isSeparable_mulByTwoEndoFieldRange` verbatim, with `n` in place of `2`.

⚠️ **This is not weaker than `#1219`'s `isSeparable_mulByNEndoFieldRange_of_smooth`, and not
stronger: the two are incomparable.**  `[CharZero F]` and `[IsAlgClosed F]` neither implies the
other, as `#754` records; but this one carries **no `3`-smoothness**, because it never touches the
composition law — so in characteristic zero the separability, and with it the fundamental identity,
holds at every `n`, `n = 5` included.  What remains `3`-smooth there is only the *value* `n²`. -/
theorem isSeparable_mulByNEndoFieldRange_of_charZero [CharZero F] (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) :
    Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField := by
  haveI : CharZero W.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F W.FunctionField).injective
  haveI : CharZero ↥(mulByNEndo n h).fieldRange :=
    ((mulByNEndo n h).fieldRange.subtype).charZero
  haveI := module_finite_mulByNEndoFieldRange n h
  haveI : Algebra.IsIntegral ↥(mulByNEndo n h).fieldRange W.FunctionField :=
    Algebra.IsIntegral.of_finite _ _
  infer_instance

/-! ### The right-hand side, at the ring level -/

/-- **The integral closure of a place of `[n]∗F(W)` is module-finite over it**, given separability.
`IsIntegralClosure.finite` through `module_finite_integralClosure_placeBelow` (`#754`), with
`Module.Finite` of the field extension supplied at **general** `n`. -/
theorem module_finite_integralClosure_placeBelowN_of_isSeparable (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    Module.Finite ↥(placeBelowN W n h q)
      ↥(integralClosure ↥(placeBelowN W n h q) W.FunctionField) := by
  haveI := module_finite_mulByNEndoFieldRange n h
  haveI := hsep
  exact module_finite_integralClosure_placeBelow q

/-- **The integral closure of a place of `[n]∗F(W)` has rank `n²` over it** at every `3`-smooth
`n ≠ 0`, given separability — the right-hand side of the fundamental identity at the ring level, so
that the identity below never descends from the field degree by hand.

The general-`n` form of `finrank_integralClosure_placeBelowTwo` and
`finrank_integralClosure_placeBelowThree`. -/
theorem finrank_integralClosure_placeBelowN_of_smooth (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    finrank ↥(placeBelowN W n h q)
      ↥(integralClosure ↥(placeBelowN W n h q) W.FunctionField) = n ^ 2 := by
  haveI := module_finite_mulByNEndoFieldRange n h
  haveI := hsep
  exact (finrank_integralClosure_placeBelow (φ := mulByNEndo n h) q).trans
    (finrank_mulByNEndoFieldRange_of_smooth h2 h3 hn hfac h)

/-! ### The fundamental identity

⚠️ The two statements in this section are the theorems; everything in the next one is a corollary at
the indices where `[F(W) : [n]∗F(W)]` is known.  See the module docstring. -/

/-- **`∑_{p ↦ q} e_p · f_p = [F(W) : [n]∗F(W)]` for `[n]∗`, over an arbitrary field**, at every `n`
at which `[n]` is non-constant, with separability carried as a hypothesis exactly as `#754` carries
it.

⚠️ **No `3`-smoothness anywhere in this statement.**  What `3`-smoothness buys is the *value* of the
right-hand side, and that is the next section. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_finrank (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
        (ramificationIdxN n h p).toNat * residueDegreeN n h p
      = finrank ↥(mulByNEndo n h).fieldRange W.FunctionField := by
  haveI := module_finite_mulByNEndoFieldRange n h
  haveI := hsep
  rw [← finrank_integralClosure_placeBelow (φ := mulByNEndo n h) q]
  exact sum_toNat_ramificationIdx_mul_residueDegreeComap_fibre
    (mulByNEndo_algebraMap_base n h) (mulByNEndo_isIntegralElem n h)

/-- **`∑_{p ↦ q} e_p · f_p = [F(W) : [n]∗F(W)]` in characteristic zero, at every `n`.**

The widest statement in this file: over `ℚ`, or any characteristic-zero field, the fundamental
identity for `[n]∗` holds at **every** `n` at which `[n]` is non-constant — no `3`-smoothness, no
algebraic closure, `n = 5` included.  Separability is discharged by
`isSeparable_mulByNEndoFieldRange_of_charZero`.

⚠️ The right-hand side cannot be evaluated at a general `n`: `[F(W) : [n]∗F(W)] = n²` is `#1213`,
which stops at `3`-smooth `n`.  Leaving it as a `finrank` is what makes the statement true at every
`n`, and replacing it by `n ^ 2` would be a *narrower* theorem, not a sharper one. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_finrank_of_charZero [CharZero F] (n : ℕ)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
        (ramificationIdxN n h p).toNat * residueDegreeN n h p
      = finrank ↥(mulByNEndo n h).fieldRange W.FunctionField :=
  sum_ramificationIdxN_mul_residueDegreeN_finrank n h
    (isSeparable_mulByNEndoFieldRange_of_charZero n h) q

/-! ### The right-hand side evaluated: `= n²` at every `3`-smooth `n` -/

/-- **`∑_{p ↦ q} e_p · f_p = n²` for `[n]∗` at every `3`-smooth `n ≠ 0`, over an arbitrary field**,
with separability carried as a hypothesis.

The general-`n` form of `sum_ramificationIdxTwo_mul_residueDegreeTwo_of_isSeparable`
(`EllipticCurves.FunctionField.PlaceInertiaGeneral`).  ⚠️ It does **not** say `#E[n] = n²`: what is
counted is places of `F(W)` in a fibre, and the passage to points needs the separable-isogeny count
this tree does not have.  See the module docstring. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord)
    (hsep : Algebra.IsSeparable ↥(mulByNEndo n h).fieldRange W.FunctionField)
    (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat * residueDegreeN n h p = n ^ 2 :=
  (sum_ramificationIdxN_mul_residueDegreeN_finrank n h hsep q).trans
    (finrank_mulByNEndoFieldRange_of_smooth h2 h3 hn hfac h)

/-- **`∑_{p ↦ q} e_p · f_p = n²` at every `3`-smooth `n ≠ 0`, over `F̄`** — separability discharged
by `#1219`.  This is what `#1221` was filed for. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_of_smooth [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat * residueDegreeN n h p = n ^ 2 :=
  sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable h2 h3 hn hfac h
    (isSeparable_mulByNEndoFieldRange_of_smooth h2 h3 hn hfac h) q

/-- **`∑_{p ↦ q} e_p · f_p = n²` at every `3`-smooth `n ≠ 0`, in characteristic zero** — the form
available over `ℚ`, where `sum_ramificationIdxN_of_smooth` is not. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_of_charZero [CharZero F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat * residueDegreeN n h p = n ^ 2 :=
  sum_ramificationIdxN_mul_residueDegreeN_of_isSeparable h2 h3 hn hfac h
    (isSeparable_mulByNEndoFieldRange_of_charZero n h) q

/-- **The collapsed form `∑_{p ↦ q} e_p = n²` over `F̄`**, at every `3`-smooth `n ≠ 0`.

Over an algebraically closed base field every place is rational, so every `f_p` is `1`.  The
general-`n` shape of `sum_ramificationIdxTwo_eq_four`
(`EllipticCurves.FunctionField.PlaceRamificationInertia`) and `sum_ramificationIdxThree_eq_nine`
(`EllipticCurves.FunctionField.MulByThreeRamification`), neither of which had a general-`n` form.

⚠️ `[IsAlgClosed F]` is **not** removable here, and not merely unproved: `residueDegreeProj_eq_one`
is equivalent to the base field being algebraically closed, and over `ℚ` the statement is false
as soon as some place in the fibre has residue degree `2`.  The weighted form above is what
generalises; see `PlaceInertiaGeneral`'s docstring on exactly this point. -/
theorem sum_ramificationIdxN_of_smooth [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {n : ℕ} (hn : n ≠ 0) (hfac : ∀ p ∈ n.primeFactors, p = 2 ∨ p = 3)
    (h : Transcendental F (n • genericPoint (W := W)).xCoord) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton n h q).toFinset,
      (ramificationIdxN n h p).toNat = n ^ 2 := by
  rw [← sum_ramificationIdxN_mul_residueDegreeN_of_smooth h2 h3 hn hfac h q]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [residueDegreeN_eq_one_of_residueDegreeProj_eq_one n h (residueDegreeProj_eq_one p), mul_one]

/-! ### The identity is the merged one at `n = 2` and at `n = 3`

Stated as a check that nothing drifted between the `[n]`-indexing and the two merged
instantiations, and because a consumer holding an `n` cannot otherwise use them.  ⚠️ At `n = 3`
this is also the only bridge: `sum_ramificationIdxThree_mul_residueDegreeThree` carries
`[IsAlgClosed F]`, so the `_of_isSeparable` and `_of_charZero` forms above are new there. -/

/-- **At `n = 2` the identity is `sum_ramificationIdxTwo_mul_residueDegreeTwo`.**  The two fibres
are the same set by `comapProjPointN_two`, and the two summands agree by `ramificationIdxN_two` and
`residueDegreeN_two`. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_two (h2 : (2 : F) ≠ 0) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton 2
        (transcendental_xCoord_two_nsmul (W := W) h2) q).toFinset,
        (ramificationIdxN 2 (transcendental_xCoord_two_nsmul (W := W) h2) p).toNat
          * residueDegreeN 2 (transcendental_xCoord_two_nsmul (W := W) h2) p
      = ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset,
        (ramificationIdxTwo h2 p).toNat * residueDegreeTwo h2 p := by
  have hset : (finite_comapProjPointN_preimage_singleton 2
      (transcendental_xCoord_two_nsmul (W := W) h2) q).toFinset
        = (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
      comapProjPointN_two h2 p]
  rw [hset]
  exact Finset.sum_congr rfl fun p _ => by
    rw [ramificationIdxN_two h2 p, residueDegreeN_two h2 p]

/-- **At `n = 3` the identity is `sum_ramificationIdxThree_mul_residueDegreeThree`.**  The `n = 3`
mirror of the previous statement, through `comapProjPointN_three`, `ramificationIdxN_three` and
`residueDegreeN_three`. -/
theorem sum_ramificationIdxN_mul_residueDegreeN_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointN_preimage_singleton 3
        (transcendental_xCoord_three_nsmul (W := W) h2 h3) q).toFinset,
        (ramificationIdxN 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) p).toNat
          * residueDegreeN 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) p
      = ∑ p ∈ (finite_comapProjPointThree_preimage_singleton h2 h3 q).toFinset,
        (ramificationIdxThree h2 h3 p).toNat * residueDegreeThree h2 h3 p := by
  have hset : (finite_comapProjPointN_preimage_singleton 3
      (transcendental_xCoord_three_nsmul (W := W) h2 h3) q).toFinset
        = (finite_comapProjPointThree_preimage_singleton h2 h3 q).toFinset := by
    ext p
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
      comapProjPointN_three h2 h3 p]
  rw [hset]
  exact Finset.sum_congr rfl fun p _ => by
    rw [ramificationIdxN_three h2 h3 p, residueDegreeN_three h2 h3 p]

/-- **`∑_{p ↦ q} e_p · f_p = 9` for `[3]∗` in characteristic zero** — the `[3]`-indexed weighted
identity **without** `[IsAlgClosed F]`.

⚠️ `EllipticCurves.FunctionField.MulByThreeResidueDegree` **named** exactly this as what was
still absent, in what is its `## Scope` section (not a `## What is not here` — that file has no such
heading): *"what is still absent *here* is a `[3]` weighted identity without `[IsAlgClosed F]`"*.
It is the previous bridge composed with `sum_ramificationIdxN_mul_residueDegreeN_of_charZero` at
`n = 3`, and it is stated here rather than left as a two-step so that the bullet could be retired
against a name.  ⚠️ **It was — in the same commit (`4a30e82`) that added this file, which is why
the quotation above is historical from the moment it was written.**  That bullet now reads *"the
clause this bullet used to carry said it was absent, full stop, and that is now false of the
tree"*, and names this declaration.  Do not go looking for the quoted sentence.

The `n = 3` mirror of `sum_ramificationIdxTwo_mul_residueDegreeTwo_of_charZero`
(`EllipticCurves.FunctionField.PlaceInertiaGeneral`), which had none. -/
theorem sum_ramificationIdxThree_mul_residueDegreeThree_of_charZero [CharZero F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (q : ProjPoint W) :
    ∑ p ∈ (finite_comapProjPointThree_preimage_singleton h2 h3 q).toFinset,
      (ramificationIdxThree h2 h3 p).toNat * residueDegreeThree h2 h3 p = 9 := by
  have hsmooth : ∀ p ∈ Nat.primeFactors 3, p = 2 ∨ p = 3 := by
    intro p hp
    exact Or.inr (Finset.mem_singleton.mp (Nat.prime_three.primeFactors ▸ hp))
  rw [← sum_ramificationIdxN_mul_residueDegreeN_three h2 h3 q]
  exact sum_ramificationIdxN_mul_residueDegreeN_of_charZero h2 h3 (by norm_num) hsmooth _ q

/-! ### Non-vacuity

Every statement above carries `[IsDedekindDomain W.CoordinateRing]` and `[W.IsElliptic]` on top of a
non-constancy hypothesis; `comapProjPointN`, `ramificationIdxN` and `residueDegreeN` are all
extracted from existence statements by choice, and `↥(placeBelowN W n h q)` carries five instances
found by search.  Curves on which the whole chain elaborates with nothing supplied by hand are
therefore committed rather than quoted.

⚠️ **Two curves are needed and neither will do alone.**  The `_of_smooth` statements want
`[IsAlgClosed F]`, which the `ℚ` curve of most of `FunctionField/` cannot supply; the `_of_charZero`
statements are interesting *only* over a field that is not algebraically closed, so a certificate
over `AlgebraicClosure ℚ` would certify the wrong thing.  `y² = x³ − x` over `ℚ` and `y² + y = x³`
over `AlgebraicClosure ℚ` are the two curves the merged layers already use, and they are used here
for the same reasons.

⚠️ The non-constancy hypothesis is **produced** at every index below, never assumed:
`transcendental_xCoord_nsmul_of_smooth` at `n = 12` and — this is what makes the `n = 5` certificate
possible — `transcendental_xCoord_nsmul_of_isAlgClosed`, which gives it at **every** `n ≠ 0` over an
algebraically closed base field. -/

section Nonvacuity

/-! The certificate curves `y² = x³ − x` and `y² + y = x³` are the shared
`EllipticCurves.Fixture.y2EqX3SubX` and `EllipticCurves.Fixture.y2AddYEqX3`, and the base —
algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here.  ⚠️ `y2EqX3SubX ℚ` is deliberately over `ℚ`, a base field that is **not**
algebraically closed — that is the point of the characteristic-zero statements; and
`y2AddYEqX3 AlgClosedQ` is the curve `#1219` certifies separability on, hence the one on which the
`_of_smooth` chain closes. -/

open EllipticCurves.Fixture

private lemma exampleQTwo : (2 : ℚ) ≠ 0 := by norm_num

private lemma exampleQThree : (3 : ℚ) ≠ 0 := by norm_num

/-- ⚠️ `decide` does **not** close this: `Nat.primeFactors` goes through `Nat.primeFactorsList`,
whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded recursion.  Bounding `p` and
case-splitting is what works — the same note `#1219` records. -/
private lemma smoothTwelve : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

/-- **The identity at `n = 12` over `ℚ`, committed** — `∑_{p ↦ ∞} e_p · f_p = 144` on a genuine
curve over a base field that is not algebraically closed, where the collapsed form
`sum_ramificationIdxN_of_smooth` does not apply. -/
example : ∑ p ∈ (finite_comapProjPointN_preimage_singleton (W := y2EqX3SubX ℚ) 12
      (transcendental_xCoord_nsmul_of_smooth exampleQTwo exampleQThree (by norm_num) smoothTwelve)
      (none : ProjPoint (y2EqX3SubX ℚ))).toFinset,
      (ramificationIdxN 12 (transcendental_xCoord_nsmul_of_smooth exampleQTwo exampleQThree
          (by norm_num) smoothTwelve) p).toNat
        * residueDegreeN 12 (transcendental_xCoord_nsmul_of_smooth exampleQTwo exampleQThree
          (by norm_num) smoothTwelve) p = 144 :=
  sum_ramificationIdxN_mul_residueDegreeN_of_charZero exampleQTwo exampleQThree (by norm_num)
    smoothTwelve _ _

/-- **`f_∞ = 1` over `ℚ`**, at an index at which nothing merged says anything — and with no
`[IsAlgClosed F]`, which is what distinguishes this from *"every place is rational"*. -/
example : residueDegreeN (W := y2EqX3SubX ℚ) 12
    (transcendental_xCoord_nsmul_of_smooth exampleQTwo exampleQThree (by norm_num) smoothTwelve)
    (none : ProjPoint (y2EqX3SubX ℚ)) = 1 :=
  residueDegreeN_none_eq_one _ _

private lemma exampleBarTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

private lemma exampleBarThree : (3 : AlgClosedQ) ≠ 0 := three_ne_zero_of_charZero _

/-- **The collapsed identity at `n = 12` over `F̄`, committed** — `∑_{p ↦ ∞} e_p = 144`, the
general-`n` shape of `sum_ramificationIdxTwo_eq_four` at an index at which neither merged
instantiation says anything. -/
example : ∑ p ∈ (finite_comapProjPointN_preimage_singleton (W := y2AddYEqX3 AlgClosedQ) 12
      (transcendental_xCoord_nsmul_of_smooth exampleBarTwo exampleBarThree (by norm_num)
        smoothTwelve) (none : ProjPoint (y2AddYEqX3 AlgClosedQ))).toFinset,
      (ramificationIdxN 12 (transcendental_xCoord_nsmul_of_smooth exampleBarTwo exampleBarThree
        (by norm_num) smoothTwelve) p).toNat = 144 :=
  sum_ramificationIdxN_of_smooth exampleBarTwo exampleBarThree (by norm_num) smoothTwelve _ _

/-- **The identity at `n = 5`, committed** — the index this tree reaches in no other statement about
`[n]∗`.

⚠️ The right-hand side is `[F(W) : [5]∗F(W)]` and **stays** a `finrank`: `#1213`'s degree `n²` is
`3`-smooth and `5` is not, so nothing here evaluates it to `25`.  That is exactly the distinction
the module docstring draws — the identity is wider than the value — and this certificate is what
makes it concrete rather than a claim.  The non-constancy of `[5]` comes from
`transcendental_xCoord_nsmul_of_isAlgClosed`, which is the only route to it at a non-`3`-smooth
index in this tree. -/
example : ∑ p ∈ (finite_comapProjPointN_preimage_singleton (W := y2AddYEqX3 AlgClosedQ) 5
      (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num))
      (none : ProjPoint (y2AddYEqX3 AlgClosedQ))).toFinset,
        (ramificationIdxN 5
          (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num)) p).toNat
          * residueDegreeN 5
            (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num)) p
      = finrank ↥(mulByNEndo (W := y2AddYEqX3 AlgClosedQ) 5
          (transcendental_xCoord_nsmul_of_isAlgClosed exampleBarTwo (by norm_num))).fieldRange
        (y2AddYEqX3 AlgClosedQ).FunctionField :=
  sum_ramificationIdxN_mul_residueDegreeN_finrank_of_charZero _ _ _

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
