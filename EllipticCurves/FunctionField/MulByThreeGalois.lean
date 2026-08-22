/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByThreeDegree
import EllipticCurves.FunctionField.TranslationActionThree
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# `F(W)` is Galois over `[3]∗F(W)`, with group `E[3]`

`EllipticCurves.FunctionField.TranslationActionThree` builds the group `G = E[3]` of translations by
`3`-torsion points, acting faithfully on `F(W)` by `F`-algebra automorphisms, with
`Nat.card G = 9` over an algebraically closed base field of characteristic `≠ 2, 3`, and proves the
inclusion `[3]∗F(W) ⊆ Fixed(G)`.  This file closes the sandwich:

```
[3]∗F(W)  ⊆  Fixed(G)  ⊆  F(W),      [F(W) : [3]∗F(W)] = 9 = |G| = [F(W) : Fixed(G)]
```

so `Fixed(G) = [3]∗F(W)` exactly, whence `F(W) / [3]∗F(W)` is **Galois** — and in particular
**separable, in every characteristic `≠ 2, 3`**, with no `CharZero` anywhere.

It is the `n = 3` mirror of `EllipticCurves.FunctionField.MulByTwoGalois` (`#759`), and it completes
the `n = 3` side of Artin's theorem: the left-hand degree is `#775`'s
`finrank_mulByThreeFieldRange`, the right-hand count is the merged `card_torsion_three`.

## What made this possible, and what it is not

Until `#775` there was no lower bound on `deg [3]` in this tree at all — the `MulByThree*` files
stopped at `module_finite_mulByThreeRange`, "finite, of degree `≤ 9`".  `#759` recorded a warning
that the `[3]∗` extension is not a copy-paste of `[2]∗`; that warning was about the *degree*, and
with the degree merged the remainder transposes.

⚠️ This is **not** a route to `#E[3] = 9`, and `IsGalois` below must not be read as one.  The count
is an *input* here (`card_torsion_three`, over an algebraically closed base, proved by a completely
different argument), and the step that would connect a field degree to a kernel count — a separable
isogeny has as many points in its kernel as its degree — is still nowhere in this tree.  Now that
both facts sit in one file the temptation to read one off the other is real; do not.  Nothing below
re-proves the count, and the count shortens nothing below.

## The three presentations of `[3]∗F(W)`, and which one carries what

The subset `[3]∗F(W) ⊆ F(W)` appears in this tree as three different objects:

| term | type |
| --- | --- |
| `(mulByThreeEndoAlgHom h2 h3).fieldRange` | `IntermediateField F F(W)` |
| `(mulByThreeEndo h2 h3).fieldRange` | `Subfield F(W)` |
| `(mulByThreeEndo h2 h3).range` | `Subring F(W)` |

Membership in any two of them is `Iff.rfl`, and `#775` proves the degree for the first and (through
an explicit `RingEquiv`) the third.

**The headline is stated for the `IntermediateField`**, because that is the only one of the three
for which Mathlib has the tool the argument needs — `IntermediateField.eq_of_le_of_finrank_eq'`,
"two intermediate fields with `F ≤ E` and `[L : F] = [L : E]` finite are equal", which is exactly
the sandwich.  `FixedPoints.subfield G F(W)` is a `Subfield`, so it is promoted with
`Subfield.toIntermediateField`; the promotion is legitimate because the group acts by *`F`-algebra*
automorphisms, so `AlgEquiv.commutes` puts every constant in the fixed field.

**Separability is exported for the first two only, and that is not an oversight.**
`Algebra.IsSeparable.of_equiv_equiv` — the transport along a ring isomorphism — is stated for
*fields*, and `↥(mulByThreeEndo h2 h3).range` is a `Subring`, so it carries no `Field` instance:
`isField_mulByThreeRange` is an `IsField` *proposition*, and `.toField` would produce a structure
that is not the instance any statement is elaborated against.  There is no transportable
`Algebra.IsSeparable ↥(mulByThreeEndo h2 h3).range F(W)` to be had.  This is the concrete reason a
consumer should state its hypotheses for the `Subfield` presentation.  `#759` established both
halves of this at `n = 2`, against its own issue's guess; nothing about it is `n`-dependent.

## Main results

* **`WeierstrassCurve.Affine.CoordinateRing.fixedFieldThree`** — `Fixed(E[3])` as an
  `IntermediateField F F(W)`, and `finrank_fixedFieldThree`: it has index `9`, by Artin;
* **`WeierstrassCurve.Affine.CoordinateRing.fixedFieldThree_eq_mulByThreeFieldRange`** — the
  sandwich, `Fixed(E[3]) = [3]∗F(W)`, and `fixedPoints_subfield_eq_mulByThreeEndoFieldRange` at the
  `Subfield` level;
* **`isSeparable_mulByThreeFieldRange_of_isAlgClosed`** and
  **`isSeparable_mulByThreeEndoFieldRange_of_isAlgClosed`** — separability in the two field
  presentations, with **no hypothesis on the characteristic beyond `(2 : F) ≠ 0` and
  `(3 : F) ≠ 0`**;
* `normal_mulByThreeFieldRange_of_isAlgClosed` and `isGalois_mulByThreeFieldRange_of_isAlgClosed` —
  the rest of the Galois package, which comes with it.

## How to fire these

`(2 : F) ≠ 0` and `(3 : F) ≠ 0` are hypotheses rather than typeclasses, so none of the results below
can be an `instance`; a consumer writes

```lean
haveI := isSeparable_mulByThreeEndoFieldRange_of_isAlgClosed (W := W) h2 h3
```

and then applies whatever wanted `[Algebra.IsSeparable ↥(mulByThreeEndo h2 h3).fieldRange F(W)]`.
Same shape as `finite_torsionThreeMul` in `TranslationActionThree`, and for the same reason.

## What is *not* here

* General `[n]∗`: `#775`'s degree `9` is `[3]`-specific and `card_torsion_three` is the `n = 3`
  count.  The general case waits on `#E[n] = n²` and on `#403`/`#404`/`#405`.
* Non-degeneracy of `e_3` (`#419`), which is what consumes this.  Nothing below mentions the
  Weil pairing, places, divisors or `ProjPoint`.
* Any statement about `Gal(F(W) / [3]∗F(W))` as a group — `IsGalois` is delivered, its Galois
  *group* is not identified with `E[3]` here, though `fixedFieldThree_eq_mulByThreeFieldRange` is
  what such an identification would start from.

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
/-- **The fixed field of `E[3]`, as an intermediate field of `F(W) / F`.**

`FixedPoints.subfield` produces a `Subfield F(W)`; the promotion to an `IntermediateField F F(W)`
is legitimate because `E[3]` acts by *`F`-algebra* automorphisms, so `AlgEquiv.commutes` puts every
constant in the fixed field.  The promotion is what makes
`IntermediateField.eq_of_le_of_finrank_eq'` — the sandwich lemma — applicable. -/
noncomputable def fixedFieldThree (W : Affine F) [W.IsElliptic] :
    IntermediateField F W.FunctionField :=
  (FixedPoints.subfield (TorsionThreeMul W) W.FunctionField).toIntermediateField
    fun c T => (translateAut (T.toAdd : W.Point)).commutes c

open Classical in
@[simp] lemma mem_fixedFieldThree_iff {g : W.FunctionField} :
    g ∈ fixedFieldThree W ↔ ∀ T : TorsionThreeMul W, T • g = g := Iff.rfl

open Classical in
/-- **Artin's theorem for the translation action**: `[F(W) : Fixed(E[3])] = |E[3]| = 9`.

`FixedPoints.finrank_eq_card` wants `[Fintype G]` and `[FaithfulSMul G F(W)]`.  The second is an
unconditional instance from `TranslationActionThree`; the first is not, because finiteness of `E[3]`
rests on the *hypotheses* `(2 : F) ≠ 0` and `(3 : F) ≠ 0` — so it is manufactured here inside the
proof, as `Fintype.ofFinite` of `finite_torsionThreeMul`, and never appears in a statement. -/
theorem finrank_fixedFieldThree [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    finrank ↥(fixedFieldThree W) W.FunctionField = 9 := by
  haveI := finite_torsionThreeMul (W := W) h2 h3
  haveI : Fintype (TorsionThreeMul W) := Fintype.ofFinite _
  have h : finrank ↥(FixedPoints.subfield (TorsionThreeMul W) W.FunctionField) W.FunctionField
      = 9 := by
    rw [FixedPoints.finrank_eq_card (TorsionThreeMul W) W.FunctionField,
      ← Nat.card_eq_fintype_card, card_torsionThreeMul h2 h3]
  exact h

/-! ### The sandwich -/

open Classical in
/-- **`Fixed(E[3]) = [3]∗F(W)`.**

Both outer degrees are `9` — `finrank_fixedFieldThree` by Artin, `finrank_mulByThreeFieldRange` by
`#775` — and `[3]∗F(W) ⊆ Fixed(E[3])` by `TranslationActionThree`, so the middle inclusion has index
one and `IntermediateField.eq_of_le_of_finrank_eq'` closes it.

⚠️ The **prime** on `eq_of_le_of_finrank_eq'` is load-bearing: that variant assumes
finite-dimensionality of the top field over the smaller one and compares the two *outer* degrees
`finrank F L` and `finrank E L`, which is what a sandwich of outer degrees supplies.  The unprimed
`eq_of_le_of_finrank_eq` compares degrees over the *base* and does not close this goal.

This is the whole mathematical content of the file; everything after it is transport. -/
theorem fixedFieldThree_eq_mulByThreeFieldRange [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    (mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange = fixedFieldThree W := by
  have hdeg : finrank ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange W.FunctionField = 9 :=
    finrank_mulByThreeFieldRange h2 h3
  haveI : FiniteDimensional ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange W.FunctionField :=
    Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  refine IntermediateField.eq_of_le_of_finrank_eq' ?_
    (by rw [hdeg, finrank_fixedFieldThree h2 h3])
  rintro _ ⟨f, rfl⟩
  exact mulByThreeEndo_mem_fixedPoints h2 h3 f

open Classical in
/-- The `Subfield`-level form of the sandwich: `Fixed(E[3])` and `[3]∗F(W)` are the same subfield of
`F(W)`.  Membership on both sides is unchanged, so this is `SetLike.ext` off the headline. -/
theorem fixedPoints_subfield_eq_mulByThreeEndoFieldRange [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    FixedPoints.subfield (TorsionThreeMul W) W.FunctionField
      = (mulByThreeEndo (W := W) h2 h3).fieldRange := by
  refine SetLike.ext fun g => ?_
  have h : g ∈ fixedFieldThree W ↔ g ∈ (mulByThreeEndo (W := W) h2 h3).fieldRange := by
    rw [← fixedFieldThree_eq_mulByThreeFieldRange h2 h3]
    exact Iff.rfl
  exact h

/-! ### Separability, normality, and the Galois package -/

/-- The identity map, read as an isomorphism from the `IntermediateField` presentation of
`[3]∗F(W)` to the `Subfield` one.  Both are the same subset — `mem_fieldRange` twice — but they
live in different subobject lattices, and separability has to be carried across. -/
def mulByThreeFieldRangeEquivSubfield (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange ≃+*
      ↥(mulByThreeEndo (W := W) h2 h3).fieldRange where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

open Classical in
/-- **`F(W)` is separable over `[3]∗F(W)`**, over an algebraically closed base field of
characteristic `≠ 2, 3` — with **no** `CharZero`.

`FixedPoints.isSeparable` is an instance for the fixed field of any finite group, and the sandwich
identifies that fixed field with `[3]∗F(W)`.

This is a `theorem` and not an `instance` because `(2 : F) ≠ 0` and `(3 : F) ≠ 0` are hypotheses;
fire it with `haveI`.  The characteristic-zero route (`Algebra.IsSeparable.of_integral`) remains
available and is the one to use when `F` is not algebraically closed. -/
theorem isSeparable_mulByThreeFieldRange_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    Algebra.IsSeparable ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange W.FunctionField := by
  haveI := finite_torsionThreeMul (W := W) h2 h3
  haveI : Algebra.IsSeparable ↥(fixedFieldThree W) W.FunctionField := inferInstanceAs
    (Algebra.IsSeparable ↥(FixedPoints.subfield (TorsionThreeMul W) W.FunctionField)
      W.FunctionField)
  rw [fixedFieldThree_eq_mulByThreeFieldRange h2 h3]
  infer_instance

open Classical in
/-- **`F(W)` is normal over `[3]∗F(W)`**, by the same route off `FixedPoints.normal`. -/
theorem normal_mulByThreeFieldRange_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    Normal ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange W.FunctionField := by
  haveI := finite_torsionThreeMul (W := W) h2 h3
  haveI : Normal ↥(fixedFieldThree W) W.FunctionField := inferInstanceAs
    (Normal ↥(FixedPoints.subfield (TorsionThreeMul W) W.FunctionField) W.FunctionField)
  rw [fixedFieldThree_eq_mulByThreeFieldRange h2 h3]
  infer_instance

open Classical in
/-- **`F(W) / [3]∗F(W)` is Galois.**  `IsGalois` is separable plus normal, and both halves are
above. -/
theorem isGalois_mulByThreeFieldRange_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    IsGalois ↥(mulByThreeEndoAlgHom (W := W) h2 h3).fieldRange W.FunctionField :=
  haveI := isSeparable_mulByThreeFieldRange_of_isAlgClosed (W := W) h2 h3
  haveI := normal_mulByThreeFieldRange_of_isAlgClosed (W := W) h2 h3
  ⟨⟩

open Classical in
/-- **Separability in the `Subfield` presentation** — the form a consumer that has to write
`ValuationSubring ↥L` wants, since `ValuationSubring` needs `L` to be a `Field` type and the
`Subfield` coercion is one.  Carried across `mulByThreeFieldRangeEquivSubfield`, which is the
identity on elements.

There is deliberately no `Subring` version: see the module docstring. -/
theorem isSeparable_mulByThreeEndoFieldRange_of_isAlgClosed [IsAlgClosed F] (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) :
    Algebra.IsSeparable ↥(mulByThreeEndo (W := W) h2 h3).fieldRange W.FunctionField := by
  haveI := isSeparable_mulByThreeFieldRange_of_isAlgClosed (W := W) h2 h3
  exact Algebra.IsSeparable.of_equiv_equiv (mulByThreeFieldRangeEquivSubfield h2 h3)
    (RingEquiv.refl W.FunctionField) (by ext a; rfl)

/-! ### Non-vacuity

The headline needs `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0` and `(3 : F) ≠ 0` at once, and
rests on a group whose order is computed rather than assumed — so a curve on which the whole chain
elaborates is committed rather than quoted.  `y² + y = x³` over `AlgebraicClosure ℚ` is the curve
`TranslationActionThree.lean` uses, and for the same reason: it is the `n = 3` certificate curve of
this tree, carrying a rational `3`-torsion point `T = (0, 0)`, whereas `y² = x³ − x` — the `n = 2`
curve — has none.  The `ℚ` curve of `MulByThreeDegree.lean` cannot witness a statement that needs an
algebraically closed base field, and faking one by weakening the statement would defeat the point of
the file. -/

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

open Classical in
/-- **The sandwich, on a curve that exists.** -/
example : (mulByThreeEndoAlgHom (W := exampleCurveThree) exampleTwo exampleThree).fieldRange
    = fixedFieldThree exampleCurveThree :=
  fixedFieldThree_eq_mulByThreeFieldRange exampleTwo exampleThree

open Classical in
/-- Artin's degree on the same curve: the fixed field has index `9`. -/
example : finrank ↥(fixedFieldThree exampleCurveThree) exampleCurveThree.FunctionField = 9 :=
  finrank_fixedFieldThree exampleTwo exampleThree

open Classical in
/-- **The headline, committed**: `F(W)` is separable over `[3]∗F(W)` on a genuine curve, in the
presentation a place-theoretic consumer would state its hypotheses for. -/
example : Algebra.IsSeparable
    ↥(mulByThreeEndo (W := exampleCurveThree) exampleTwo exampleThree).fieldRange
    exampleCurveThree.FunctionField :=
  isSeparable_mulByThreeEndoFieldRange_of_isAlgClosed exampleTwo exampleThree

open Classical in
/-- And the whole Galois package. -/
example : IsGalois
    ↥(mulByThreeEndoAlgHom (W := exampleCurveThree) exampleTwo exampleThree).fieldRange
    exampleCurveThree.FunctionField :=
  isGalois_mulByThreeFieldRange_of_isAlgClosed exampleTwo exampleThree

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
