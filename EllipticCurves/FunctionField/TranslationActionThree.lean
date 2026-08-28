/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationAction
import EllipticCurves.FunctionField.TranslationTriplingComm
import EllipticCurves.Torsion.ThreeTorsionStructure

/-!
# The translation action of `E[3]` on the function field

For `G := Multiplicative ↥(W.torsion 3)` — the group `E[3]` written multiplicatively — this file
builds a faithful `MulSemiringAction G F(W)` by translation, computes `Nat.card G = 9` over an
algebraically closed base field of characteristic `≠ 2, 3`, and proves the inclusion

```
[3]∗F(W) ⊆ Fixed(G).
```

It is the `n = 3` mirror of `EllipticCurves.FunctionField.TranslationAction` (`#758`), and the
sandwich that turns the inclusion into an equality is the sibling file
`MulByThreeGalois` and is deliberately **not** here.

## What this file does *not* rebuild, and why it is short

`TranslationAction` builds `translateAut : W.Point → (F(W) ≃ₐ[F] F(W))` — the identity at the point
at infinity, `translateAlgEquiv` at an affine point — together with the homomorphism law
`translateAut_add`, the faithfulness criterion `translateAut_eq_one_iff`, the injectivity
`translateAut_injective` and the bundled `translateAutHom`.  **All of that is stated for an
arbitrary `W.Point` and is `n`-agnostic**: the hard case analysis, including the `O` corner that a
group homomorphism out of `W.Point` has to name, was done once and is reused verbatim here.  So is
the torsion transport `translatePoint_add_add_self` (`TranslationTorsionMap`), which is *already*
written in the `n = 3` form for this consumer.

What is genuinely `n = 3` is therefore only: the restriction of `translateAutHom` to `E[3]`, the two
instances, the count, and the inclusion.

The one input that has no `n`-agnostic form is
`translateEndo_mulByThreeEndo_apply` (`TranslationTriplingComm`, the `n = 3` twin of
`translateEndo_mulByTwoEndo_apply`, PR #164): it says `[3] ∘ τ_T = [3]` when `T ⊕ T ⊕ T = O`, and
it is merged and unconditional.  There is no missing ingredient of that kind at `n = 3`; if this
argument looks harder than the `n = 2` one, that lemma is the first thing to check.

## Why: Artin's theorem at `n = 3`

`F(W)` is a degree-`9` extension of `[3]∗F(W)` (`finrank_mulByThreeFieldRange`, `#775`), and `E[3]`
has exactly nine elements over an algebraically closed field of characteristic `≠ 2, 3`
(`card_torsion_three`).  Translation by a `3`-torsion point fixes `[3]∗f` pointwise, so
`[3]∗F(W) ⊆ Fixed(E[3])`, and `FixedPoints.finrank_eq_card` gives `[F(W) : Fixed(E[3])] = 9`.  Both
outer degrees being `9`, the sandwich closes and `Fixed(E[3]) = [3]∗F(W)` exactly — whence
separability, normality and `IsGalois`, in **every characteristic `≠ 2, 3`** and with no `CharZero`.
This file is the first half of that argument: everything up to and including the inclusion.

## The `DecidableEq F` convention

The group law on `W.Point` is data-dependent on a `DecidableEq F` instance (Mathlib's `Point.add`
branches on `x₁ = x₂`), and this tree uses two conventions for supplying it:
`EllipticCurves/Torsion/` carries `[DecidableEq F]` as an instance argument, while
`EllipticCurves/FunctionField/Translation*.lean` writes `open Classical in`.  A statement of the
first kind can be instantiated at the classical instance but not conversely, so this file — which
consumes both layers, `card_torsion_three` from one and `translateAut` from the other — follows the
`open Classical in` convention throughout, exactly as `TranslationAction` does.

## `Finite`, not `Fintype`

`FixedPoints.finrank_eq_card` asks for `[Fintype G]`, but the finiteness of `E[3]` rests on the
*hypotheses* `(2 : F) ≠ 0` and `(3 : F) ≠ 0` rather than on typeclasses, so it cannot be an instance
here.  What this file exports is the theorem `finite_torsionThreeMul`; the consumer writes

```lean
haveI := finite_torsionThreeMul (W := W) h2 h3
```

and then obtains the `Fintype` as `Fintype.ofFinite _`, which is noncomputable and should stay
inside that `haveI` rather than appearing in any statement.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.TorsionThreeMul` — `E[3]` written multiplicatively;
* `WeierstrassCurve.Affine.CoordinateRing.translateAutThreeHom` — the restriction of
  `translateAutHom` to `E[3]`, which is what the `MulSemiringAction` instance is built from.

## Main statements

* `translateAutThreeHom_injective`, and the `MulSemiringAction` / `FaithfulSMul` instances — `E[3]`
  acts faithfully on `F(W)` by `F`-algebra automorphisms;
* `card_torsionThreeMul` — `|E[3]| = 9` over `[IsAlgClosed F]` with `(2 : F) ≠ 0`, `(3 : F) ≠ 0`, in
  the multiplicative packaging Artin's theorem consumes, and `finite_torsionThreeMul`;
* `mulByThreeEndo_mem_fixedPoints` and `mulByThreeRange_le_fixedPoints` — `[3]∗F(W) ⊆ Fixed(E[3])`.

## Scope

The sandwich `Fixed(E[3]) = [3]∗F(W)`, Artin's degree `finrank_fixedFieldThree = 9`, `IsGalois` and
the separability package are **not** here: they are the sibling issue `#784`, merged as
`EllipticCurves.FunctionField.MulByThreeGalois`, which imports this file.  Nothing here mentions
divisors, places or `ProjPoint`, and nothing here is `[2]`- or general-`[n]`-flavoured:
`card_torsion_three` is the `n = 3` count and `#775`'s degree `9` is `[3]`-specific.

This is also **not** a route to `#E[3] = 9` — that count is an *input* here, merged separately as
`card_torsion_three` — and it supplies no kernel count for `[3]` as an isogeny.

`TranslationAction`'s own Scope sentence, that nothing in *that* file is `[3]`-flavoured, is a
statement about its contents and stays true; it is deliberately left untouched.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4.
* Artin's theorem on fixed fields, [stacks 09I3].
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### The group `E[3]` acting on `F(W)` -/

open Classical in
/-- **The `3`-torsion group `E[3]`, written multiplicatively.**  This is the group that acts on
`F(W)` by translation and whose fixed field is `[3]∗F(W)`; the `Multiplicative` wrapper exists only
because `MulSemiringAction` and `FixedPoints.subfield` are stated for monoids.

The classical `DecidableEq F` instance is baked in here, which is what pins the convention of this
file (see the module docstring) for every statement below. -/
abbrev TorsionThreeMul (W : Affine F) : Type _ := Multiplicative ↥(W.torsion 3)

open Classical in
/-- **The translation homomorphism restricted to `E[3]`.**  Injective, being the composite of the
injective `translateAutHom` with the inclusion of a subgroup. -/
noncomputable def translateAutThreeHom :
    TorsionThreeMul W →* (W.FunctionField ≃ₐ[F] W.FunctionField) :=
  translateAutHom.comp (AddMonoidHom.toMultiplicative (W.torsion 3).subtype)

open Classical in
@[simp] lemma translateAutThreeHom_apply (T : TorsionThreeMul W) :
    translateAutThreeHom T = translateAut (T.toAdd : W.Point) := rfl

open Classical in
theorem translateAutThreeHom_injective :
    Function.Injective (translateAutThreeHom (F := F) (W := W)) := by
  intro S T h
  simp only [translateAutThreeHom_apply] at h
  exact Multiplicative.toAdd.injective (Subtype.ext (translateAut_injective h))

open Classical in
/-- **`E[3]` acts on `F(W)` by ring automorphisms**, through `translateAutThreeHom` and the
tautological action of `Aut_F F(W)` on `F(W)`.

`MulSemiringAction.compHom` is an `abbrev` and not an instance — it would loop — so the composite is
declared as an instance here, at the concrete head `Multiplicative ↥(W.torsion 3)`.  A global
instance keyed on a concrete head is preferable to a `letI`: downstream files get the action from
instance search with nothing to import but this module. -/
noncomputable instance : MulSemiringAction (TorsionThreeMul W) W.FunctionField :=
  MulSemiringAction.compHom _ translateAutThreeHom

open Classical in
@[simp] lemma torsionThreeMul_smul_def (T : TorsionThreeMul W) (g : W.FunctionField) :
    T • g = translateAut (T.toAdd : W.Point) g := rfl

open Classical in
/-- **The action is faithful**, which is the hypothesis Artin's theorem
(`FixedPoints.finrank_eq_card`) carries alongside finiteness. -/
instance : FaithfulSMul (TorsionThreeMul W) W.FunctionField where
  eq_of_smul_eq_smul h := translateAutThreeHom_injective (AlgEquiv.ext h)

/-! ### The order of `E[3]` -/

open Classical in
/-- **`|E[3]| = 9`**, in the multiplicative packaging.  This is `card_torsion_three`
(`EllipticCurves.Torsion.ThreeTorsionStructure`) read through the type synonym; it is the
right-hand side of Artin's theorem for the translation action.

`card_torsion_three` is stated with `[DecidableEq F]` as an instance argument, so it applies
verbatim at the classical instance this file works with; no `Subsingleton (Decidable _)` transport
is involved. -/
theorem card_torsionThreeMul [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Nat.card (TorsionThreeMul W) = 9 :=
  (Nat.card_congr Multiplicative.toAdd).trans (card_torsion_three h2 h3)

open Classical in
/-- `E[3]` is finite over an algebraically closed field of characteristic `≠ 2, 3`, since it has
exactly nine elements.

This is a `theorem`, not an `instance`, because it rests on the *hypotheses* `h2` and `h3` rather
than on typeclasses.  Downstream, fire it as `haveI := finite_torsionThreeMul (W := W) h2 h3`; the
`Fintype` that `FixedPoints.finrank_eq_card` asks for is then `Fintype.ofFinite _`, which is
noncomputable and should be kept inside a `haveI` at the use site rather than named in a
statement. -/
theorem finite_torsionThreeMul [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Finite (TorsionThreeMul W) :=
  Nat.finite_of_card_ne_zero (by rw [card_torsionThreeMul h2 h3]; omega)

/-! ### `[3]∗F(W)` is fixed by the action -/

open Classical in
/-- The `F(W)`-level `3`-torsion datum that `translateEndo_mulByThreeEndo_apply` consumes, read off
membership in `E[3]`.

There is no `three_nsmul`, so `3 • P = 0` has to be unfolded as `add_smul` at `3 = 2 + 1` followed
by `two_nsmul` and `one_nsmul`; that is done once and for all in
`add_add_self_eq_zero_of_mem_torsion_three` (`EllipticCurves.Torsion.Defs`).
`translatePoint_add_add_self` then transports the relation to the constant point over `F(W)`. -/
lemma translatePoint_add_add_self_of_mem_torsion_three {x y : F} (h : W.Nonsingular x y)
    (hT : (.some x y h : W.Point) ∈ W.torsion 3) :
    translatePoint h.left + translatePoint h.left + translatePoint h.left = 0 :=
  translatePoint_add_add_self h.left (add_add_self_eq_zero_of_mem_torsion_three hT)

open Classical in
/-- **Translation by a `3`-torsion point fixes `[3]∗f`.**  The affine case is the merged
`translateEndo_mulByThreeEndo_apply`, which says `[3] ∘ τ_T = [3]` when `T ⊕ T ⊕ T = O`; the point
at infinity acts as the identity by construction. -/
theorem translateAut_mulByThreeEndo (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {P : W.Point}
    (hP : P ∈ W.torsion 3) (f : W.FunctionField) :
    translateAut P (mulByThreeEndo h2 h3 f) = mulByThreeEndo h2 h3 f := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, translateAut_zero, AlgEquiv.one_apply]
  · rw [translateAut_apply_some]
    exact translateEndo_mulByThreeEndo_apply h.left h2 h3
      (translatePoint_add_add_self_of_mem_torsion_three h hP) f

open Classical in
/-- **Every `[3]∗f` lies in the fixed field of `E[3]`.** -/
theorem mulByThreeEndo_mem_fixedPoints (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (f : W.FunctionField) :
    mulByThreeEndo h2 h3 f ∈ FixedPoints.subfield (TorsionThreeMul W) W.FunctionField := fun T =>
  translateAut_mulByThreeEndo h2 h3 T.toAdd.2 f

open Classical in
/-- **`[3]∗F(W) ⊆ Fixed(E[3])`**, the inclusion half of the sandwich that identifies the two.  The
reverse inclusion is a degree count (Artin's theorem against `#775`) and is not proved here. -/
theorem mulByThreeRange_le_fixedPoints (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (mulByThreeEndo (W := W) h2 h3).range
      ≤ (FixedPoints.subfield (TorsionThreeMul W) W.FunctionField).toSubring := by
  rintro _ ⟨f, rfl⟩
  exact mulByThreeEndo_mem_fixedPoints h2 h3 f

/-! ### Non-vacuity

`card_torsionThreeMul` needs `[IsAlgClosed F]`, so the `ℚ` curve of `MulByThreeDegree.lean` cannot
witness it, and `y² = x³ − x` — the curve the `n = 2` files certify on — has **no** affine
`3`-torsion point with rational coordinates, so exhibiting a nonidentity element of `E[3]` on it
would mean naming a root of `3X⁴ − 6X² − 1`.

The curve used instead is `y² + y = x³` over `AlgebraicClosure ℚ`, of discriminant `−27`, on which
`T = (0, 0)` has order exactly `3`.  It is the same curve, under the same name, that
`WeilPairingTelescopeThree.lean` and `WeilPairingAntisymmetricMu.lean` certify their `n = 3`
statements on, and for the same reason. -/

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

/-- `T = (0, 0)` lies on `y² + y = x³` and is nonsingular. -/
private lemma exampleNonsingular : exampleCurveThree.Nonsingular 0 0 :=
  exampleCurveThree.equation_iff_nonsingular.mp (by
    norm_num [exampleCurveThree, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `T = (0, 0)` is `3`-torsion: `Ψ₃ = 3X⁴ + 3b₆X` vanishes at `0`, and the side condition of
`mem_torsion_three_some_iff` is automatic. -/
private lemma exampleTorsionThree :
    Point.some (0 : exampleField) 0 exampleNonsingular ∈ exampleCurveThree.torsion 3 :=
  mem_torsion_three_some_iff'.mpr (by
    norm_num [exampleCurveThree, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])

open Classical in
/-- The action is by a group with more than one element, so the fixed field is not all of `F(W)`
for a trivial reason. -/
example : Nontrivial (TorsionThreeMul exampleCurveThree) :=
  ⟨⟨Multiplicative.ofAdd ⟨_, exampleTorsionThree⟩, 1, by
    simp only [ne_eq, ← Multiplicative.toAdd.injective.eq_iff, Subtype.ext_iff]
    exact Point.some_ne_zero exampleNonsingular⟩⟩

open Classical in
noncomputable example :
    MulSemiringAction (TorsionThreeMul exampleCurveThree) exampleCurveThree.FunctionField :=
  inferInstance

open Classical in
example : FaithfulSMul (TorsionThreeMul exampleCurveThree) exampleCurveThree.FunctionField :=
  inferInstance

open Classical in
example : Nat.card (TorsionThreeMul exampleCurveThree) = 9 :=
  card_torsionThreeMul exampleTwo exampleThree

open Classical in
example : Finite (TorsionThreeMul exampleCurveThree) :=
  finite_torsionThreeMul exampleTwo exampleThree

open Classical in
example (f : exampleCurveThree.FunctionField) :
    mulByThreeEndo exampleTwo exampleThree f
      ∈ FixedPoints.subfield (TorsionThreeMul exampleCurveThree)
        exampleCurveThree.FunctionField :=
  mulByThreeEndo_mem_fixedPoints exampleTwo exampleThree f

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
