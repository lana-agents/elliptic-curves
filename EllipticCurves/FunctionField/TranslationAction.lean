/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.TranslationAutomorphism
import EllipticCurves.FunctionField.TranslationTorsionMap
import EllipticCurves.Torsion.TwoTorsion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The translation action of `W.Point` on the function field

For an elliptic curve `W` over a field `F`, translation by an **affine** point `T = (x, y)` is an
`F`-algebra automorphism `translateAlgEquiv h : F(W) ≃ₐ[F] F(W)`
(`EllipticCurves.FunctionField.TranslationAutomorphism`), and the two composition laws

* `translateEndo_comp` (`TranslationComposition.lean`), for `P ⊕ Q` again affine, and
* `translateEndo_comp_zero` (`TranslationAutomorphism.lean`), for `P ⊕ Q = O`

say between them that the assignment is compatible with the group law in *every* case.  What is
missing is the assignment itself at the point at infinity, and the bundling that lets Mathlib's
`FixedPoints` machinery see it as a group acting on `F(W)`.  This file supplies both:

```lean
translateAut : W.Point → (F(W) ≃ₐ[F] F(W))          -- `1` at `O`, `translateAlgEquiv` elsewhere
translateAut_add : translateAut (P + Q) = translateAut P * translateAut Q
translateAut_injective
```

and then, for `G := Multiplicative ↥(W.torsion 2)` — the group `E[2]` written multiplicatively —
a faithful `MulSemiringAction G F(W)` together with `Nat.card G = 4` over an algebraically closed
base field of characteristic `≠ 2`, and the inclusion `[2]∗F(W) ⊆ Fixed(G)`.

## Why: Artin's theorem, and separability of `[2]` away from characteristic `2`

`F(W)` is a degree-`4` extension of `[2]∗F(W)` (`finrank_mulByTwoRange_functionField`, `#682`), and
`Ideal.sum_ramification_inertia_eq_finrank` — the route the fundamental identity
`∑_{p ↦ q} e_p · f_p = 4` goes through — needs `Module.Finite` for an integral closure, hence
`Algebra.IsSeparable ([2]∗F(W)) F(W)`.  ⚠️ **When this file was written that had exactly one route
in the tree**, `Algebra.IsSeparable.of_integral`, which wants characteristic zero — and the sentence
saying so outlived the fact, because the `CharZero`-free route described next is now merged
(`EllipticCurves.FunctionField.MulByTwoGalois`, `#759`), with the `3`-smooth `n` generalisation in
`EllipticCurves.FunctionField.MulByNSeparable` (`#1219`).  What follows is the motivation this file
was built from, not a current inventory.

The `CharZero`-free route is Artin's theorem: translation by a `2`-torsion point fixes `[2]∗f`
pointwise (`translateEndo_mulByTwoEndo_apply`, PR #164), so `[2]∗F(W) ⊆ Fixed(G)`, and
`FixedPoints.finrank_eq_card` gives `[F(W) : Fixed(G)] = |G| = 4`.  Both outer degrees being `4`,
the sandwich `[2]∗F(W) ⊆ Fixed(G) ⊆ F(W)` closes and `Fixed(G) = [2]∗F(W)` exactly — whence
separability and normality for free, from Mathlib's `FixedPoints.isSeparable` and
`FixedPoints.normal`.  This file is the first half of that argument: everything up to and including
`[2]∗F(W) ⊆ Fixed(G)`.  Closing the sandwich is deliberately **not** done here.

## The `DecidableEq F` convention

The group law on `W.Point` is data-dependent on a `DecidableEq F` instance (Mathlib's
`Point.add` branches on `x₁ = x₂`), and this tree uses *two* conventions for supplying it:
`EllipticCurves/Torsion/` carries `[DecidableEq F]` as an instance argument, while
`EllipticCurves/FunctionField/Translation*.lean` writes `open Classical in`.  A statement of the
first kind can be instantiated at the classical instance, but not conversely, so this file — which
must consume both — follows the `open Classical in` convention throughout.  `card_torsion_two` is
applied at the classical instance; no `Subsingleton (Decidable _)` transport is needed anywhere.

## `Finite`, not `Fintype`

`FixedPoints.finrank_eq_card` asks for `[Fintype G]`, but the finiteness of `E[2]` rests on the
*hypothesis* `(2 : F) ≠ 0` rather than on a typeclass, so it cannot be an instance here.  What this
file exports is the theorem `finite_torsionTwoMul`; the consumer writes
`haveI := finite_torsionTwoMul (W := W) h2` and then obtains the `Fintype` as `Fintype.ofFinite _`,
which is noncomputable and should stay inside that `haveI` rather than appearing in a statement.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.translateAut` — translation by an arbitrary point of `W`,
  as an `F`-algebra automorphism of `F(W)`;
* `WeierstrassCurve.Affine.CoordinateRing.translateAutHom` — its bundled form
  `Multiplicative W.Point →* (F(W) ≃ₐ[F] F(W))`;
* `WeierstrassCurve.Affine.CoordinateRing.translateAutTwoHom` — the restriction to `E[2]`, which is
  what the `MulSemiringAction` instance is built from.

## Main statements

* `translateAut_add` — the homomorphism law, in all four cases of `(P, Q)`;
* `translateAut_eq_one_iff` and `translateAut_injective` — the action of `W.Point` on `F(W)` is
  faithful, so `E[2]` embeds in `Aut_F F(W)`;
* `card_torsionTwoMul` — `|E[2]| = 4` over `[IsAlgClosed F]` with `(2 : F) ≠ 0`, in the
  multiplicative packaging Artin's theorem consumes;
* `mulByTwoEndo_mem_fixedPoints` and `mulByTwoRange_le_fixedPoints` — `[2]∗F(W) ⊆ Fixed(E[2])`.

## Scope

The sandwich `Fixed(E[2]) = [2]∗F(W)`, Artin's degree `finrank_fixedFieldTwo = 4`, `IsGalois` and
the separability package are **not** here: they are the sibling issue `#759`, merged as
`EllipticCurves.FunctionField.MulByTwoGalois`, which imports this file.  ⚠️ Those statements carry
`[IsAlgClosed F]`; `mulByTwoRange_le_fixedPoints` does not — it needs only `[W.IsElliptic]` and
`(2 : F) ≠ 0`.  Nothing here mentions divisors, places, or `ProjPoint`, and nothing here is
`[3]`- or general-`[n]`-flavoured: `card_torsion_two` is the `n = 2` computation, and `#682`'s
degree `4` is `[2]`-specific.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4.
* Artin's theorem on fixed fields, [stacks 09I3].
-/

open Polynomial

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-! ### Translation by an arbitrary point -/

/-- **Translation by an arbitrary point of `W`, as an `F`-algebra automorphism of `F(W)`.**  The
identity at the point at infinity, and `translateAlgEquiv` at an affine point.

`translateAlgEquiv` is indexed by an `Equation`, so it can only describe translation by an affine
point; the group law on `W.Point`, however, leaves the affine chart, and the `O` corner is exactly
what a *group homomorphism* out of `W.Point` has to name.  That is the whole reason this definition
exists. -/
noncomputable def translateAut : W.Point → (W.FunctionField ≃ₐ[F] W.FunctionField)
  | 0 => 1
  | .some _ _ h => translateAlgEquiv h.left

@[simp] lemma translateAut_zero : translateAut (0 : W.Point) = 1 := rfl

@[simp] lemma translateAut_some {x y : F} (h : W.Nonsingular x y) :
    translateAut (.some x y h) = translateAlgEquiv h.left := rfl

lemma translateAut_apply_some {x y : F} (h : W.Nonsingular x y) (g : W.FunctionField) :
    translateAut (.some x y h) g = translateEndo h.left g := rfl

/-- The base-change point homomorphism on an affine point, in the form the composition laws want.
Both sides are `Point.some` at the base-changed coordinates; `rfl` because the `Nonsingular`
arguments are propositions. -/
lemma torsionPointMap_some {x y : F} (h : W.Nonsingular x y) :
    torsionPointMap (.some x y h) = translatePoint h.left := rfl

/-! ### The homomorphism law -/

open Classical in
/-- **Translation is a homomorphism from the group of points to `Aut_F F(W)`.**

The four cases are: `P = O`, `Q = O`, and — for `P`, `Q` both affine — whether `P ⊕ Q` is affine or
`O`.  The last two are the merged composition laws `translateEndo_comp` and
`translateEndo_comp_zero`, whose hypothesis `𝒯_P + 𝒯_Q = 𝒯_R` is obtained by pushing the `F`-level
identity `P + Q = R` through the base-change homomorphism `torsionPointMap`.

Note the variance: Mathlib's group structure on `A ≃ₐ[R] A` has `(f * g) x = f (g x)`
(`AlgEquiv.mul_apply`), and the composition laws read
`(translateEndo hP).comp (translateEndo hQ) = translateEndo hR` for `P ⊕ Q = R`, so `translateAut`
is a genuine homomorphism and no `MulOpposite` is needed. -/
theorem translateAut_add (P Q : W.Point) :
    translateAut (P + Q) = translateAut P * translateAut Q := by
  rcases P with _ | ⟨xP, yP, hP⟩
  · rw [← Point.zero_def, zero_add, translateAut_zero, one_mul]
  rcases Q with _ | ⟨xQ, yQ, hQ⟩
  · rw [← Point.zero_def, add_zero, translateAut_zero, mul_one]
  -- The `F(W)`-level sum of the two constant points, from the `F`-level sum of the points.
  have hmap : translatePoint hP.left + translatePoint hQ.left
      = torsionPointMap (Point.some xP yP hP + Point.some xQ yQ hQ) := by
    rw [map_add, torsionPointMap_some, torsionPointMap_some]
  -- Split on whether the sum is affine or the point at infinity.
  rcases hsum : (Point.some xP yP hP + Point.some xQ yQ hQ : W.Point) with _ | ⟨xR, yR, hR⟩
  · rw [hsum, ← Point.zero_def, map_zero] at hmap
    rw [← Point.zero_def, translateAut_zero]
    refine AlgEquiv.ext fun g => ?_
    rw [AlgEquiv.mul_apply, translateAut_apply_some, translateAut_apply_some,
      translateEndo_translateEndo_apply_zero hP.left hQ.left hmap g, AlgEquiv.one_apply]
  · rw [hsum, torsionPointMap_some] at hmap
    refine AlgEquiv.ext fun g => ?_
    rw [AlgEquiv.mul_apply, translateAut_apply_some, translateAut_apply_some,
      translateAut_apply_some, translateEndo_translateEndo_apply hP.left hQ.left hR.left hmap g]

/-! ### Faithfulness -/

/-- **The translation action is faithful**: only the point at infinity acts as the identity.
The affine case is `translateAlgEquiv_ne_one`, which is unconditional on `T`. -/
theorem translateAut_eq_one_iff {P : W.Point} : translateAut P = 1 ↔ P = 0 := by
  constructor
  · intro h
    rcases P with _ | ⟨x, y, hP⟩
    · rfl
    · exact absurd h (translateAlgEquiv_ne_one hP.left)
  · rintro rfl
    exact translateAut_zero

open Classical in
/-- **The bundled translation homomorphism** `E ≃ Multiplicative W.Point → Aut_F F(W)`.  The
`Multiplicative` wrapper is what `MulSemiringAction` and `FixedPoints` consume; the underlying
function is `translateAut`. -/
noncomputable def translateAutHom :
    Multiplicative W.Point →* (W.FunctionField ≃ₐ[F] W.FunctionField) where
  toFun P := translateAut P.toAdd
  map_one' := translateAut_zero
  map_mul' P Q := translateAut_add P.toAdd Q.toAdd

open Classical in
@[simp] lemma translateAutHom_apply (P : Multiplicative W.Point) :
    translateAutHom P = translateAut P.toAdd := rfl

open Classical in
theorem translateAutHom_injective :
    Function.Injective (translateAutHom (F := F) (W := W)) :=
  (injective_iff_map_eq_one _).mpr fun _ h => translateAut_eq_one_iff.mp h

open Classical in
/-- `translateAut` itself is injective — the `Multiplicative`-free form of
`translateAutHom_injective`. -/
theorem translateAut_injective : Function.Injective (translateAut (F := F) (W := W)) :=
  translateAutHom_injective

/-! ### The group `E[2]` acting on `F(W)` -/

open Classical in
/-- **The `2`-torsion group `E[2]`, written multiplicatively.**  This is the group that acts on
`F(W)` by translation and whose fixed field is `[2]∗F(W)`; the `Multiplicative` wrapper exists only
because `MulSemiringAction` and `FixedPoints.subfield` are stated for monoids.

The classical `DecidableEq F` instance is baked in here, which is what pins the convention of this
file (see the module docstring) for every statement below. -/
abbrev TorsionTwoMul (W : Affine F) : Type _ := Multiplicative ↥(W.torsion 2)

open Classical in
/-- **The translation homomorphism restricted to `E[2]`.**  Injective, being the composite of the
injective `translateAutHom` with the inclusion of a subgroup. -/
noncomputable def translateAutTwoHom :
    TorsionTwoMul W →* (W.FunctionField ≃ₐ[F] W.FunctionField) :=
  translateAutHom.comp (AddMonoidHom.toMultiplicative (W.torsion 2).subtype)

open Classical in
@[simp] lemma translateAutTwoHom_apply (T : TorsionTwoMul W) :
    translateAutTwoHom T = translateAut (T.toAdd : W.Point) := rfl

open Classical in
theorem translateAutTwoHom_injective :
    Function.Injective (translateAutTwoHom (F := F) (W := W)) := by
  intro S T h
  simp only [translateAutTwoHom_apply] at h
  exact Multiplicative.toAdd.injective (Subtype.ext (translateAut_injective h))

open Classical in
/-- **`E[2]` acts on `F(W)` by ring automorphisms**, through `translateAutTwoHom` and the
tautological action of `Aut_F F(W)` on `F(W)`.

`MulSemiringAction.compHom` is an `abbrev` and not an instance — it would loop — so the composite is
declared as an instance here, at the concrete head `Multiplicative ↥(W.torsion 2)`.  A global
instance keyed on a concrete head is preferable to a `letI`: downstream files get the action from
instance search with nothing to import but this module. -/
noncomputable instance : MulSemiringAction (TorsionTwoMul W) W.FunctionField :=
  MulSemiringAction.compHom _ translateAutTwoHom

open Classical in
@[simp] lemma torsionTwoMul_smul_def (T : TorsionTwoMul W) (g : W.FunctionField) :
    T • g = translateAut (T.toAdd : W.Point) g := rfl

open Classical in
/-- **The action is faithful**, which is the hypothesis Artin's theorem
(`FixedPoints.finrank_eq_card`) carries alongside finiteness. -/
instance : FaithfulSMul (TorsionTwoMul W) W.FunctionField where
  eq_of_smul_eq_smul h := translateAutTwoHom_injective (AlgEquiv.ext h)

/-! ### The order of `E[2]` -/

open Classical in
/-- **`|E[2]| = 4`**, in the multiplicative packaging.  This is `card_torsion_two`
(`EllipticCurves.Torsion.TwoTorsion`) read through the type synonym; it is the right-hand side of
Artin's theorem for the translation action.

`card_torsion_two` is stated with `[DecidableEq F]` as an instance argument, so it applies verbatim
at the classical instance this file works with; no `Subsingleton (Decidable _)` transport is
involved. -/
theorem card_torsionTwoMul [IsAlgClosed F] (h2 : (2 : F) ≠ 0) :
    Nat.card (TorsionTwoMul W) = 4 :=
  (Nat.card_congr Multiplicative.toAdd).trans (card_torsion_two h2)

open Classical in
/-- `E[2]` is finite over an algebraically closed field of characteristic `≠ 2`, since it has
exactly four elements.

This is a `theorem`, not an `instance`, because it rests on the *hypothesis* `h2` rather than on a
typeclass.  Downstream, fire it as `haveI := finite_torsionTwoMul (W := W) h2`; the `Fintype` that
`FixedPoints.finrank_eq_card` asks for is then `Fintype.ofFinite _`, which is noncomputable and
should be kept inside a `haveI` at the use site rather than named in a statement. -/
theorem finite_torsionTwoMul [IsAlgClosed F] (h2 : (2 : F) ≠ 0) : Finite (TorsionTwoMul W) :=
  Nat.finite_of_card_ne_zero (by rw [card_torsionTwoMul h2]; omega)

/-! ### `[2]∗F(W)` is fixed by the action -/

open Classical in
/-- The `F(W)`-level `2`-torsion datum that `translateEndo_mulByTwoEndo_apply` consumes, read off
membership in `E[2]`.  `add_self_eq_zero_of_mem_torsion_two` (`EllipticCurves.Torsion.Defs`) turns
the membership into `P + P = 0`, and `translatePoint_add_self` transports that to the constant
point over `F(W)`. -/
lemma translatePoint_add_self_of_mem_torsion_two {x y : F} (h : W.Nonsingular x y)
    (hT : (.some x y h : W.Point) ∈ W.torsion 2) :
    translatePoint h.left + translatePoint h.left = 0 :=
  translatePoint_add_self h.left (add_self_eq_zero_of_mem_torsion_two hT)

open Classical in
/-- **Translation by a `2`-torsion point fixes `[2]∗f`.**  The affine case is the merged
`translateEndo_mulByTwoEndo_apply` (PR #164), which says `[2] ∘ τ_T = [2]` when `T + T = O`; the
point at infinity acts as the identity by construction. -/
theorem translateAut_mulByTwoEndo (h2 : (2 : F) ≠ 0) {P : W.Point} (hP : P ∈ W.torsion 2)
    (f : W.FunctionField) : translateAut P (mulByTwoEndo h2 f) = mulByTwoEndo h2 f := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Point.zero_def, translateAut_zero, AlgEquiv.one_apply]
  · rw [translateAut_apply_some]
    exact translateEndo_mulByTwoEndo_apply h.left h2
      (translatePoint_add_self_of_mem_torsion_two h hP) f

open Classical in
/-- **Every `[2]∗f` lies in the fixed field of `E[2]`.** -/
theorem mulByTwoEndo_mem_fixedPoints (h2 : (2 : F) ≠ 0) (f : W.FunctionField) :
    mulByTwoEndo h2 f ∈ FixedPoints.subfield (TorsionTwoMul W) W.FunctionField := fun T =>
  translateAut_mulByTwoEndo h2 T.toAdd.2 f

open Classical in
/-- **`[2]∗F(W) ⊆ Fixed(E[2])`**, the inclusion half of the sandwich that identifies the two.  The
reverse inclusion is a degree count (Artin's theorem against `#682`) and is not proved here: it is
`fixedPoints_subfield_eq_mulByTwoEndoFieldRange`
(`EllipticCurves.FunctionField.MulByTwoGalois`, downstream of this file), which states the
corresponding equality of subfields and carries `[IsAlgClosed F]` — a hypothesis absent from this
statement's own signature. -/
theorem mulByTwoRange_le_fixedPoints (h2 : (2 : F) ≠ 0) :
    (mulByTwoEndo (W := W) h2).range
      ≤ (FixedPoints.subfield (TorsionTwoMul W) W.FunctionField).toSubring := by
  rintro _ ⟨f, rfl⟩
  exact mulByTwoEndo_mem_fixedPoints h2 f

/-! ### Non-vacuity

Everything above is stated for an arbitrary elliptic curve, and the two headline facts about the
group — `Nat.card = 4` and faithfulness — would be worth nothing if the hypotheses could not be met
at once.  They can: on `y² = x³ − x` over `AlgebraicClosure ℚ` (discriminant `64`, characteristic
zero, algebraically closed) the `MulSemiringAction` and `FaithfulSMul` instances are found by
instance search, the group has four elements, and `T = (0, 0)` exhibits a nonidentity one — so the
action is not by a trivial group and Artin's theorem will not be reading `[F(W) : F(W)] = 1`.

The same curve over `ℚ` is the one `PlacePullback.lean`, `PullbackDivisor.lean`,
`PlaceResidueField.lean` and `PlaceResidueComap.lean` certify against; the base field is enlarged to
its algebraic closure here only because `card_torsionTwoMul` needs `[IsAlgClosed F]`.  The
certificates that do not need the closure hold over `ℚ` unchanged. -/

section Nonvacuity

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

/-- Hoisted rather than written inline: an inline `by norm_num` for `(2 : AlgClosedQ) ≠ 0` is
postponed and leaves the curve a metavariable at the use site. -/
private lemma exampleTwo : (2 : AlgClosedQ) ≠ 0 := two_ne_zero

/-- `T = (0, 0)` lies on `y² = x³ − x` and is nonsingular. -/
private lemma exampleNonsingular : (y2EqX3SubX AlgClosedQ).Nonsingular 0 0 :=
  (y2EqX3SubX AlgClosedQ).equation_iff_nonsingular.mp (by
    norm_num [y2EqX3SubX, WeierstrassCurve.Affine.equation_iff])

open Classical in
/-- `T = (0, 0)` is `2`-torsion: `2y + a₁x + a₃ = 0` reads `0 = 0`. -/
private lemma exampleTorsion :
    Point.some (0 : AlgClosedQ) 0 exampleNonsingular ∈ (y2EqX3SubX AlgClosedQ).torsion 2 :=
  (mem_torsion_two_some_iff exampleNonsingular).mpr (by norm_num [y2EqX3SubX])

open Classical in
/-- The action is by a group with more than one element, so the fixed field is not all of `F(W)`
for a trivial reason. -/
example : Nontrivial (TorsionTwoMul (y2EqX3SubX AlgClosedQ)) :=
  ⟨⟨Multiplicative.ofAdd ⟨_, exampleTorsion⟩, 1, by
    simp only [ne_eq, ← Multiplicative.toAdd.injective.eq_iff, Subtype.ext_iff]
    exact Point.some_ne_zero exampleNonsingular⟩⟩

open Classical in
noncomputable example :
    MulSemiringAction (TorsionTwoMul (y2EqX3SubX AlgClosedQ))
        (y2EqX3SubX AlgClosedQ).FunctionField := inferInstance

open Classical in
example : FaithfulSMul (TorsionTwoMul (y2EqX3SubX AlgClosedQ))
    (y2EqX3SubX AlgClosedQ).FunctionField := inferInstance

open Classical in
example (P Q : (y2EqX3SubX AlgClosedQ).Point) :
    translateAut (P + Q) = translateAut P * translateAut Q :=
  translateAut_add P Q

open Classical in
example : Function.Injective (translateAut (W := y2EqX3SubX AlgClosedQ)) := translateAut_injective

open Classical in
example : Nat.card (TorsionTwoMul (y2EqX3SubX AlgClosedQ)) = 4 := card_torsionTwoMul exampleTwo

open Classical in
example : Finite (TorsionTwoMul (y2EqX3SubX AlgClosedQ)) := finite_torsionTwoMul exampleTwo

open Classical in
example (f : (y2EqX3SubX AlgClosedQ).FunctionField) :
    mulByTwoEndo exampleTwo f
      ∈ FixedPoints.subfield (TorsionTwoMul (y2EqX3SubX AlgClosedQ))
          (y2EqX3SubX AlgClosedQ).FunctionField :=
  mulByTwoEndo_mem_fixedPoints exampleTwo f

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
