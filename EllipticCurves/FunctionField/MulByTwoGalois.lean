/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByTwoDegree
import EllipticCurves.FunctionField.TranslationAction
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# `F(W)` is Galois over `[2]∗F(W)`, with group `E[2]`

`EllipticCurves.FunctionField.TranslationAction` (`#758`) builds the group `G = E[2]` of
translations by `2`-torsion points, acting faithfully on `F(W)` by `F`-algebra automorphisms, with
`Nat.card G = 4` over an algebraically closed base field of characteristic `≠ 2`, and proves the
inclusion `[2]∗F(W) ⊆ Fixed(G)`.  This file closes the sandwich:

```
[2]∗F(W)  ⊆  Fixed(G)  ⊆  F(W),      [F(W) : [2]∗F(W)] = 4 = |G| = [F(W) : Fixed(G)]
```

so `Fixed(G) = [2]∗F(W)` exactly, whence `F(W) / [2]∗F(W)` is **Galois** — and in particular
**separable, in every characteristic `≠ 2`**, with no `CharZero` anywhere.

## Why this matters, and what it replaces

`#744`'s route decision for the fundamental identity `∑_{p ↦ q} e_p · f_p = 4` reaches
`Module.Finite` for an integral closure through `IsIntegralClosure.finite`, whose one hypothesis
about the extension is `Algebra.IsSeparable ([2]∗F(W)) F(W)`.  Until now the only route to that in
this tree was `Algebra.IsSeparable.of_integral`, an instance under `[CharZero F]`.  That route stays
true and stays useful — it needs no algebraic closure, so it covers `ℚ` and number fields — but it
is no longer the only one: this file trades `[CharZero F]` for `[IsAlgClosed F]`, which is the
hypothesis the Weil-pairing front carries anyway.

Nothing here is an isogeny-theoretic argument.  The classical proof that `[2]` is separable away
from characteristic `2` differentiates the invariant differential; this one is Artin's theorem
against a degree already known (`finrank_mulByTwoFieldRange`, `#682`), and every input is merged.

## The three presentations of `[2]∗F(W)`, and which one carries what

The subset `[2]∗F(W) ⊆ F(W)` appears in this tree as three different objects:

| term | type |
| --- | --- |
| `(mulByTwoEndoAlgHom h2).fieldRange` | `IntermediateField F F(W)` |
| `(mulByTwoEndo h2).fieldRange` | `Subfield F(W)` |
| `(mulByTwoEndo h2).range` | `Subring F(W)` |

Membership in any two of them is `Iff.rfl`, and `#682` proves the degree for the first and (through
an explicit `RingEquiv`) the third.

**The headline is stated for the `IntermediateField`**, because that is the only one of the three
for which Mathlib has the tool the argument needs — `IntermediateField.eq_of_le_of_finrank_eq'`,
"two intermediate fields with `F ≤ E` and `[L : F] = [L : E]` finite are equal", which is exactly
the sandwich.  `FixedPoints.subfield G F(W)` is a `Subfield`, so it is promoted with
`Subfield.toIntermediateField`; the promotion is legitimate because the group acts by *`F`-algebra*
automorphisms, so `AlgEquiv.commutes` puts every constant in the fixed field.

**Separability is exported for the first two only, and that is not an oversight.**
`Algebra.IsSeparable.of_equiv_equiv` — the transport along a ring isomorphism — is stated for
*fields*, and `↥(mulByTwoEndo h2).range` is a `Subring`, so it carries no `Field` instance:
`isField_mulByTwoRange` is an `IsField` *proposition*, and `.toField` would produce a structure that
is not the instance any statement is elaborated against.  There is no transportable
`Algebra.IsSeparable ↥(mulByTwoEndo h2).range F(W)` to be had.  This is the concrete reason a
consumer should state its hypotheses for the `Subfield` presentation.

⚠️ **That paragraph is about the `Subring`, and it used to be everything this file said about the
`Subfield` column.**  Every word of it stays — there is no `Subring` version of anything, at any
`n`, and there will not be — but it was read as covering the second presentation too, and it never
did.  Until `#1244` the `Subfield` column really did hold separability alone:
`normal_mulByTwoEndoFieldRange_of_isAlgClosed` and `isGalois_mulByTwoEndoFieldRange_of_isAlgClosed`
simply did not exist, even though `↥(mulByTwoEndo h2).fieldRange` *is* a `Field` type and the
declaration crossing separability into it sits two lines away.  `#1233` found the gap while
mirroring this file at general `n` and left it deliberately open; it is closed below, by
`Normal.of_equiv_equiv` along the same `mulByTwoFieldRangeEquivSubfield`.  What blocks the `Subring`
is the missing `Field` instance; nothing blocked the `Subfield`.

## Main results

Every public declaration of this file is listed, and all are in namespace
`WeierstrassCurve.Affine.CoordinateRing`.

* **`fixedFieldTwo`** — `Fixed(E[2])` as an `IntermediateField F F(W)`, with
  `mem_fixedFieldTwo_iff`, and `finrank_fixedFieldTwo`: it has index `4`, by Artin;
* **`fixedFieldTwo_eq_mulByTwoFieldRange`** — the sandwich, `Fixed(E[2]) = [2]∗F(W)`, and
  `fixedPoints_subfield_eq_mulByTwoEndoFieldRange` at the `Subfield` level;
* `mulByTwoFieldRangeEquivSubfield` — the identity map read as a `RingEquiv` between the
  `IntermediateField` and `Subfield` presentations, along which everything below is transported;
* **`isSeparable_mulByTwoFieldRange_of_isAlgClosed`** and
  **`isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed`** — separability in the two field
  presentations, with **no hypothesis on the characteristic beyond `(2 : F) ≠ 0`**;
* `normal_mulByTwoFieldRange_of_isAlgClosed` and `isGalois_mulByTwoFieldRange_of_isAlgClosed` — the
  rest of the Galois package, which comes with it;
* `normal_mulByTwoEndoFieldRange_of_isAlgClosed` and
  `isGalois_mulByTwoEndoFieldRange_of_isAlgClosed` (`#1244`) — that rest in the `Subfield`
  presentation as well, so both field presentations now carry the whole package and not just
  separability.

## How to fire these

`(2 : F) ≠ 0` is a hypothesis rather than a typeclass, so none of the results below can be an
`instance`; a consumer writes

```lean
haveI := isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed (W := W) h2
```

and then applies whatever wanted `[Algebra.IsSeparable ↥(mulByTwoEndo h2).fieldRange F(W)]`.  Same
shape as `finite_torsionTwoMul` in `TranslationAction`, and for the same reason.

## What is *not* here

* `[3]∗` and general `[n]∗`: `#682`'s degree `4` is `[2]`-specific and `card_torsion_two` is the
  `n = 2` count, so nothing below is proved at any other index.  ⚠️ That is a statement about *this
  file*, not about the tree: `EllipticCurves.FunctionField.MulByThreeGalois` has the `n = 3`
  package, and `EllipticCurves.FunctionField.MulByNSeparable` (`#1219`) composes the two along
  `[m · n]∗ = [m]∗ ∘ [n]∗` (`#1213`) to get separability at every `3`-smooth `n`.  ⚠️ **This bullet
  used to end *"Only the separability half generalises that way — normality is not transitive"*, and
  the second clause is still true while the conclusion no longer is.**  Normality is indeed not
  transitive, so it does not travel up *that* tower; but `EllipticCurves.FunctionField.MulByNGalois`
  (`#1233`) reaches `Normal` and `IsGalois` at every `3`-smooth `n` by a route that is not a tower —
  Artin's theorem against the `E[n]` translation action of
  `EllipticCurves.FunctionField.TranslationActionN` (`#1232`), the general-`n` mirror of this file's
  own argument.  ⚠️ At `n = 2` it is **this file's** package that is the sharp one: the general-`n`
  statements carry `(3 : F) ≠ 0` as well, because their right-hand side runs through
  `card_torsion_eq_sq_of_smooth`.  Keep using the names below at `n = 2`.
* The fundamental identity (`#755`), and the module-finiteness of an integral closure that consumes
  this (`#754`).  Nothing below mentions places, divisors or `ProjPoint`.
* ⚠️ Any statement about `Gal(F(W) / [2]∗F(W))` as a group — **RETIRED, it landed.**  This bullet
  used to read *"`IsGalois` is delivered, its Galois *group* is not identified with `E[2]` here,
  though `fixedFieldTwo_eq_mulByTwoFieldRange` is what such an identification would start from."*
  It is `torsionTwoMulGaloisEquiv` in `EllipticCurves.FunctionField.MulByNGaloisGroup`, built on
  `fixedPoints_subfield_eq_mulByTwoEndoFieldRange` below rather than on the `IntermediateField`
  form the bullet nominated.  ⚠️ **Still `n = 2`-specific, and for the reason above**: the
  general-`n` equivalence carries `(3 : F) ≠ 0` as well, so it does not subsume the `n = 2` one and
  this file's inputs remain the sharp ones at this index.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
* Artin's theorem on fixed fields, [stacks 09I3].
-/

open Module Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The fixed field as an intermediate field -/

open Classical in
/-- **The fixed field of `E[2]`, as an intermediate field of `F(W) / F`.**

`FixedPoints.subfield` produces a `Subfield F(W)`; the promotion to an `IntermediateField F F(W)`
is legitimate because `E[2]` acts by *`F`-algebra* automorphisms, so `AlgEquiv.commutes` puts every
constant in the fixed field.  The promotion is what makes
`IntermediateField.eq_of_le_of_finrank_eq'` — the sandwich lemma — applicable. -/
noncomputable def fixedFieldTwo (W : Affine F) [W.IsElliptic] :
    IntermediateField F W.FunctionField :=
  (FixedPoints.subfield (TorsionTwoMul W) W.FunctionField).toIntermediateField
    fun c T => (translateAut (T.toAdd : W.Point)).commutes c

open Classical in
@[simp] lemma mem_fixedFieldTwo_iff {g : W.FunctionField} :
    g ∈ fixedFieldTwo W ↔ ∀ T : TorsionTwoMul W, T • g = g := Iff.rfl

open Classical in
/-- **Artin's theorem for the translation action**: `[F(W) : Fixed(E[2])] = |E[2]| = 4`.

`FixedPoints.finrank_eq_card` wants `[Fintype G]` and `[FaithfulSMul G F(W)]`.  The second is an
unconditional instance from `#758`; the first is not, because finiteness of `E[2]` rests on the
*hypothesis* `(2 : F) ≠ 0` — so it is manufactured here inside the proof, as
`Fintype.ofFinite` of `finite_torsionTwoMul`, and never appears in a statement. -/
theorem finrank_fixedFieldTwo [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    finrank ↥(fixedFieldTwo W) W.FunctionField = 4 := by
  haveI := finite_torsionTwoMul (W := W) h2
  haveI : Fintype (TorsionTwoMul W) := Fintype.ofFinite _
  have h : finrank ↥(FixedPoints.subfield (TorsionTwoMul W) W.FunctionField) W.FunctionField
      = 4 := by
    rw [FixedPoints.finrank_eq_card (TorsionTwoMul W) W.FunctionField, ← Nat.card_eq_fintype_card,
      card_torsionTwoMul h2]
  exact h

/-! ### The sandwich -/

open Classical in
/-- **`Fixed(E[2]) = [2]∗F(W)`.**

Both outer degrees are `4` — `finrank_fixedFieldTwo` by Artin, `finrank_mulByTwoFieldRange` by
`#682` — and `[2]∗F(W) ⊆ Fixed(E[2])` by `#758`, so the middle inclusion has index one and
`IntermediateField.eq_of_le_of_finrank_eq'` closes it.

This is the whole mathematical content of the file; everything after it is transport. -/
theorem fixedFieldTwo_eq_mulByTwoFieldRange [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    (mulByTwoEndoAlgHom (W := W) h2).fieldRange = fixedFieldTwo W := by
  have hdeg : finrank ↥(mulByTwoEndoAlgHom (W := W) h2).fieldRange W.FunctionField = 4 :=
    finrank_mulByTwoFieldRange h2
  haveI : FiniteDimensional ↥(mulByTwoEndoAlgHom (W := W) h2).fieldRange W.FunctionField :=
    Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  refine IntermediateField.eq_of_le_of_finrank_eq' ?_ (by rw [hdeg, finrank_fixedFieldTwo h2])
  rintro _ ⟨f, rfl⟩
  exact mulByTwoEndo_mem_fixedPoints h2 f

open Classical in
/-- The `Subfield`-level form of the sandwich: `Fixed(E[2])` and `[2]∗F(W)` are the same subfield of
`F(W)`.  Membership on both sides is unchanged, so this is `SetLike.ext` off the headline. -/
theorem fixedPoints_subfield_eq_mulByTwoEndoFieldRange [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    FixedPoints.subfield (TorsionTwoMul W) W.FunctionField
      = (mulByTwoEndo (W := W) h2).fieldRange := by
  refine SetLike.ext fun g => ?_
  have h : g ∈ fixedFieldTwo W ↔ g ∈ (mulByTwoEndo (W := W) h2).fieldRange := by
    rw [← fixedFieldTwo_eq_mulByTwoFieldRange h2]
    exact Iff.rfl
  exact h

/-! ### Separability, normality, and the Galois package -/

/-- The identity map, read as an isomorphism from the `IntermediateField` presentation of
`[2]∗F(W)` to the `Subfield` one.  Both are the same subset — `mem_fieldRange` twice — but they
live in different subobject lattices, and separability has to be carried across. -/
def mulByTwoFieldRangeEquivSubfield (h2 : (2 : F) ≠ 0) :
    ↥(mulByTwoEndoAlgHom (W := W) h2).fieldRange ≃+* ↥(mulByTwoEndo (W := W) h2).fieldRange where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

open Classical in
/-- **`F(W)` is separable over `[2]∗F(W)`**, over an algebraically closed base field of
characteristic `≠ 2` — with **no** `CharZero`.

`FixedPoints.isSeparable` is an instance for the fixed field of any finite group, and the sandwich
identifies that fixed field with `[2]∗F(W)`.

This is a `theorem` and not an `instance` because `(2 : F) ≠ 0` is a hypothesis; fire it with
`haveI`.  The characteristic-zero route (`Algebra.IsSeparable.of_integral`) remains available and is
the one to use when `F` is not algebraically closed. -/
theorem isSeparable_mulByTwoFieldRange_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    Algebra.IsSeparable ↥(mulByTwoEndoAlgHom (W := W) h2).fieldRange W.FunctionField := by
  haveI := finite_torsionTwoMul (W := W) h2
  haveI : Algebra.IsSeparable ↥(fixedFieldTwo W) W.FunctionField := inferInstanceAs
    (Algebra.IsSeparable ↥(FixedPoints.subfield (TorsionTwoMul W) W.FunctionField) W.FunctionField)
  rw [fixedFieldTwo_eq_mulByTwoFieldRange h2]
  infer_instance

open Classical in
/-- **`F(W)` is normal over `[2]∗F(W)`**, by the same route off `FixedPoints.normal`. -/
theorem normal_mulByTwoFieldRange_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    Normal ↥(mulByTwoEndoAlgHom (W := W) h2).fieldRange W.FunctionField := by
  haveI := finite_torsionTwoMul (W := W) h2
  haveI : Normal ↥(fixedFieldTwo W) W.FunctionField := inferInstanceAs
    (Normal ↥(FixedPoints.subfield (TorsionTwoMul W) W.FunctionField) W.FunctionField)
  rw [fixedFieldTwo_eq_mulByTwoFieldRange h2]
  infer_instance

open Classical in
/-- **`F(W) / [2]∗F(W)` is Galois.**  `IsGalois` is separable plus normal, and both halves are
above. -/
theorem isGalois_mulByTwoFieldRange_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    IsGalois ↥(mulByTwoEndoAlgHom (W := W) h2).fieldRange W.FunctionField :=
  haveI := isSeparable_mulByTwoFieldRange_of_isAlgClosed (W := W) h2
  haveI := normal_mulByTwoFieldRange_of_isAlgClosed (W := W) h2
  ⟨⟩

open Classical in
/-- **Separability in the `Subfield` presentation** — the form a consumer that has to write
`ValuationSubring ↥L` wants, since `ValuationSubring` needs `L` to be a `Field` type and the
`Subfield` coercion is one.  Carried across `mulByTwoFieldRangeEquivSubfield`, which is the identity
on elements.

There is deliberately no `Subring` version: see the module docstring. -/
theorem isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    Algebra.IsSeparable ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField := by
  haveI := isSeparable_mulByTwoFieldRange_of_isAlgClosed (W := W) h2
  exact Algebra.IsSeparable.of_equiv_equiv (mulByTwoFieldRangeEquivSubfield h2)
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)

open Classical in
/-- **Normality in the `Subfield` presentation**, the companion of the separability crossing
directly above and carried across the same `mulByTwoFieldRangeEquivSubfield`, which is the identity
on elements.

⚠️ `Normal.of_equiv_equiv` takes its two ring isomorphisms **implicitly** and only `hcomp`
explicitly, unlike `Algebra.IsSeparable.of_equiv_equiv` above, which takes all three positionally;
hence the named arguments.  The `hcomp` goal is the same in both.

There is deliberately no `Subring` version: see the module docstring. -/
theorem normal_mulByTwoEndoFieldRange_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    Normal ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField := by
  haveI := normal_mulByTwoFieldRange_of_isAlgClosed (W := W) h2
  exact Normal.of_equiv_equiv (f := mulByTwoFieldRangeEquivSubfield h2)
    (g := RingEquiv.refl W.FunctionField) (by ext a; rfl)

open Classical in
/-- **`F(W) / [2]∗F(W)` is Galois, in the `Subfield` presentation.**  Separability and normality are
both above, so this is `⟨⟩` off the two — the same shape as
`isGalois_mulByTwoFieldRange_of_isAlgClosed` uses in the `IntermediateField` presentation, and as
`isGalois_mulByNEndoFieldRange_of_smooth` uses at general `n`.  `IsGalois.of_equiv_equiv` would
prove it in one step instead, but it re-does the separability transport that the declaration two
above has already done. -/
theorem isGalois_mulByTwoEndoFieldRange_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    IsGalois ↥(mulByTwoEndo (W := W) h2).fieldRange W.FunctionField :=
  haveI := isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed (W := W) h2
  haveI := normal_mulByTwoEndoFieldRange_of_isAlgClosed (W := W) h2
  ⟨⟩

/-! ### Non-vacuity

The headline needs `[IsAlgClosed F]`, `[W.IsElliptic]` and `(2 : F) ≠ 0` at once, and rests on a
group whose order is computed rather than assumed — so a curve on which the whole chain elaborates
is committed rather than quoted.  `y² = x³ − x` over `AlgebraicClosure ℚ` is the curve
`TranslationAction.lean` uses, for the same reason: the `ℚ` curve of the rest of `FunctionField/`
cannot witness a statement that needs an algebraically closed base field, and faking one by
weakening the statement would defeat the point of the file. -/

section Nonvacuity

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

/-- **The sandwich, on a curve that exists.** -/
example : (mulByTwoEndoAlgHom (W := y2EqX3SubX AlgClosedQ) exampleTwo).fieldRange
    = fixedFieldTwo (y2EqX3SubX AlgClosedQ) :=
  fixedFieldTwo_eq_mulByTwoFieldRange exampleTwo

/-- Artin's degree on the same curve: the fixed field has index `4`. -/
example : finrank ↥(fixedFieldTwo (y2EqX3SubX AlgClosedQ))
    (y2EqX3SubX AlgClosedQ).FunctionField = 4 :=
  finrank_fixedFieldTwo exampleTwo

/-- **The headline, committed**: `F(W)` is separable over `[2]∗F(W)` on a genuine curve, in the
presentation `#754` consumes. -/
example : Algebra.IsSeparable ↥(mulByTwoEndo (W := y2EqX3SubX AlgClosedQ) exampleTwo).fieldRange
    (y2EqX3SubX AlgClosedQ).FunctionField :=
  isSeparable_mulByTwoEndoFieldRange_of_isAlgClosed exampleTwo

/-- And the whole Galois package. -/
example : IsGalois ↥(mulByTwoEndoAlgHom (W := y2EqX3SubX AlgClosedQ) exampleTwo).fieldRange
    (y2EqX3SubX AlgClosedQ).FunctionField :=
  isGalois_mulByTwoFieldRange_of_isAlgClosed exampleTwo

/-- Normality in the `Subfield` presentation, on the same curve. -/
example : Normal ↥(mulByTwoEndo (W := y2EqX3SubX AlgClosedQ) exampleTwo).fieldRange
    (y2EqX3SubX AlgClosedQ).FunctionField :=
  normal_mulByTwoEndoFieldRange_of_isAlgClosed exampleTwo

/-- And the whole Galois package in that presentation too — the statement `#1244` was filed for. -/
example : IsGalois ↥(mulByTwoEndo (W := y2EqX3SubX AlgClosedQ) exampleTwo).fieldRange
    (y2EqX3SubX AlgClosedQ).FunctionField :=
  isGalois_mulByTwoEndoFieldRange_of_isAlgClosed exampleTwo

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
