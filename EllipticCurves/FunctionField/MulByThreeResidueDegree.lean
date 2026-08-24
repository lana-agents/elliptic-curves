/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByThreeRamification

/-!
# The relative residue degree of `[3]∗`, and the weighted identity `∑_{p ↦ q} e_p · f_p = 9`

`EllipticCurves.FunctionField.MulByThreeRamification` proves the **unweighted** fundamental
identity `∑_{p ↦ q} e_p = 9` for `[3]∗`, and said of itself — ⚠️ **in text this change retires in
place, so do not expect to find the quotation there** —

> **A residue-degree companion.**  `sum_ramificationIdxTwo_mul_residueDegreeTwo` has no mirror
> below, because `residueDegreeThree` does not exist; the identity it decorates is the one proved
> here, and adding the decoration is a separate, purely notational step.

⚠️ **Two further files said the same thing** — `MulByThreePlacePullback`'s *"the weighted form still
has no `n = 3` case"* and `MulByThreeFibre`'s *"`residueDegreeThree` does not exist, so
`sum_ramificationIdxTwo_mul_residueDegreeTwo` still has no `n = 3` mirror"*.  This file is that
step; all three clauses are retired in the same change, and none of the three files consumes it.

⚠️ Both of those two wrote the weight as `deg p`, and `MulByThreePlacePullback`'s opening sentence
still does.  What the identity below carries is the **relative** residue degree
`f_p = [κ(p) : κ([3]⁻¹ p)]`, not `[κ(p) : F]` (`residueDegreeProj`).  The two agree here only
because the base field is algebraically closed, and it is the relative one that survives when it is
not — the same choice `sum_ramificationIdxTwo_mul_residueDegreeTwo` made at `n = 2`.  Both
retirements record the correction next to the sentence that carries it.

## What is here, and why it is short

The generic machinery is already generic in the embedding `φ`, in
`EllipticCurves.FunctionField.PlaceResidueComap`: `residueDegreeComap` is the definition,
`residueDegreeProj_mul_residueDegreeComap` the tower formula, and
`residueDegreeComap_eq_one_of_residueDegreeProj_eq_one` the collapse at a rational place.  Every
declaration below is the `[2]∗` instantiation of one of those three with `mulByTwoEndo_*` replaced
by `mulByThreeEndo_*` and `h3` threaded — ⚠️ **no property of `[3]` beyond
`mulByThreeEndo_algebraMap_base` and `mulByThreeEndo_isIntegralElem` is used**, and both have been
merged since `MulByThreeFinite` and `MulByThreePlacePullback` respectively.

## ⚠️ Why this is one new module and not two edits, which is *not* how `n = 2` is arranged

At `n = 2` the layer is split: `residueDegreeTwo` and its first three lemmas live in
`EllipticCurves.FunctionField.PlaceResidueComap`, and the unconditional value at infinity and the
weighted identity live in `EllipticCurves.FunctionField.PlaceRamificationInertia`.  **That split
cannot be mirrored.**  `PlaceResidueComap` is upstream of every `MulByThree*` module — it imports
`MulByTwoPlaceAtInfinity` and `PlaceResidueField` and nothing else — so it cannot mention
`comapProjPointThree`, and `PlaceRamificationInertia` cannot either.  The `n = 2` split is an
artefact of the order `#744` and `#763` landed in, not a design to be copied; one module downstream
of `MulByThreeRamification` is the only placement available.

## ⚠️ One shape at `n = 2` that is a fossil and should not be mirrored

`residueDegreeTwo_none_eq_one_of_ne_zero` (`PlaceResidueComap`) takes
`residueDegreeProj W none ≠ 0` as a hypothesis, and `residueDegreeTwo_none_eq_one`
(`PlaceRamificationInertia`) discharges it from `residueDegreeProj_none_eq_one` — which is
unconditional and was merged in between.  So the hypothesis-taking form exists only because it was
written before its own hypothesis became free.  `residueDegreeThree_none_eq_one` below is stated
once, unconditionally, and reaches it by the *rational-place* route
(`residueDegreeThree_eq_one_of_residueDegreeProj_eq_one`) rather than by the tower formula and
`Nat.mul_eq_left`: with `residueDegreeProj_none_eq_one` in hand the collapse lemma applies directly,
and the two-step at `n = 2` is a second fossil of the same ordering.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.residueDegreeThree` — the relative residue degree
  `f_p = [κ(p) : κ([3]⁻¹ p)]` of `[3]∗` at a place of the projective curve.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.residueDegreeProj_mul_residueDegreeThree` — the tower
  formula `[κ([3]⁻¹ p) : F] · f_p = [κ(p) : F]`.
* `WeierstrassCurve.Affine.CoordinateRing.residueDegreeThree_eq_one_of_residueDegreeProj_eq_one` —
  at a place rational over `F`, `[3]∗` is residually trivial.
* `WeierstrassCurve.Affine.CoordinateRing.residueDegreeThree_none_eq_one` — `[3]∗` is residually
  trivial at the point at infinity, unconditionally.
* `WeierstrassCurve.Affine.CoordinateRing.sum_ramificationIdxThree_mul_residueDegreeThree` — **the
  weighted fundamental identity** `∑_{p ↦ q} e_p · f_p = 9`, over an algebraically closed base
  field.

## Scope

⚠️ **This is not `#E[3] = 9`, and nothing below is a step towards it.**  What is counted here is
*places of `F(W)`*; the passage to a count of `3`-torsion points runs through *"a separable isogeny
has `#ker = deg`"*, which no file in this tree contains.  The merged `card_torsion_three`
(`EllipticCurves.Torsion.ThreeTorsionStructure`) is an independent theorem, is **not** used below,
and is not reproved.  `MulByThreeRamification`, `MulByThreeFibre` and `PlaceRamificationInertia` all
carry this warning; it is repeated rather than cross-referenced because the weighted form is the one
that most looks like a count.

⚠️ **`[IsAlgClosed F]` is carried by the headline and by nothing else below**, and it is not a gap.
Over a base field that is not algebraically closed `f_p = 1` fails in general — an affine closed
point of a curve over `ℚ` can have a number field as residue field
(`residueDegreeProj_some_eq_one`'s own warning) — so the weighted identity is the *only* true form
there, and the closure is exactly what collapses it to `sum_ramificationIdxThree_eq_nine`.  ⚠️ By
`#899`'s test the hypothesis is not removable by base change either: it is consumed to produce
`residueDegreeProj_eq_one`, and what it produces is used as an equation, but the *general* weighted
identity is a different theorem rather than a descent of this one.

* **The general (non-closed-field) weighted identity stays out.**
  `sum_ramificationIdxTwo_mul_residueDegreeTwo`'s docstring records that it *"would need the
  inertia compatibility unconditionally — [and] is what a later issue owes"*.  That debt is
  `n`-independent, it is unchanged by this file, and nothing below pays any part of it.
* **General `n` stays out.**  `mulByNEndo` does not exist; `[2]∗` and `[3]∗` are the two concrete
  endomorphisms this tree has, and `#404`'s general `ωₙ` is untouched.
* **The ramification side is not re-examined.**  `ramificationIdxThree_none` (`[3]` is unramified at
  infinity) is merged and is not consumed below: the residue degree at infinity is `1` for a reason
  that has nothing to do with ramification, namely that `[0 : 1 : 0]` is a rational point of every
  Weierstrass curve.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, III.1.11 — the shape `∑ e_p · f_p = deg`.
-/

open Module IsDedekindDomain

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing]

/-! ### The relative residue degree of `[3]∗` -/

/-- **The relative residue degree of `[3]∗`**, `f_p = [κ(p) : κ([3]⁻¹ p)]`.

Together with `ramificationIdxThree` this is the pair of local invariants of the degree-nine
extension `F(W) / [3]∗F(W)` at a place.  Their fundamental identity `∑_{p ↦ q} e_p · f_p = 9` is
`sum_ramificationIdxThree_mul_residueDegreeThree` below, over an algebraically closed base field.

⚠️ Nothing here shows this is nonzero: `Module.finrank` is `0` on an infinite-dimensional module,
and `residueDegreeProj_mul_residueDegreeThree` is the tool for ruling that out. -/
noncomputable def residueDegreeThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (p : ProjPoint W) : ℕ :=
  residueDegreeComap (mulByThreeEndo_algebraMap_base h2 h3) (mulByThreeEndo_isIntegralElem h2 h3) p

/-- The tower formula for `[3]∗`: `[κ([3]⁻¹ p) : F] · f_p = [κ(p) : F]`.

`Module.finrank_mul_finrank` on `F → κ([3]⁻¹ p) → κ(p)`, with no finiteness hypothesis: both sides
are `0` when `κ(p)` is infinite over `F`. -/
theorem residueDegreeProj_mul_residueDegreeThree (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (p : ProjPoint W) :
    residueDegreeProj W (comapProjPointThree h2 h3 p) * residueDegreeThree h2 h3 p
      = residueDegreeProj W p :=
  residueDegreeProj_mul_residueDegreeComap _ _ p

/-- **At a place rational over `F`, `[3]∗` is residually trivial.**

The `n = 3` mirror of `residueDegreeTwo_eq_one_of_residueDegreeProj_eq_one`: if `κ(p) = F` then
every intermediate field is `F`, so `f_p = 1`.  Over an algebraically closed base field the
hypothesis holds at every place (`residueDegreeProj_eq_one`), which is what collapses the weighted
identity below to `sum_ramificationIdxThree_eq_nine`. -/
theorem residueDegreeThree_eq_one_of_residueDegreeProj_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {p : ProjPoint W} (hp : residueDegreeProj W p = 1) : residueDegreeThree h2 h3 p = 1 :=
  (residueDegreeComap_eq_one_of_residueDegreeProj_eq_one _ _ hp).2

/-- **`[3]∗` is residually trivial at the point at infinity**, unconditionally.

⚠️ No hypothesis on `F` beyond `(2 : F) ≠ 0` and `(3 : F) ≠ 0`, and in particular no algebraic
closedness: `[0 : 1 : 0]` is a rational point of every Weierstrass curve, so
`residueDegreeProj_none_eq_one` needs none either and this is the previous lemma applied to it.

⚠️ The `n = 2` layer reaches the same statement in two steps — a hypothesis-taking
`residueDegreeTwo_none_eq_one_of_ne_zero` and then `residueDegreeTwo_none_eq_one` discharging it
through the tower formula — because it was written before `residueDegreeProj_none_eq_one` existed.
That is a fossil of the merge order, not a design; see the module docstring. -/
theorem residueDegreeThree_none_eq_one (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    residueDegreeThree h2 h3 (none : ProjPoint W) = 1 :=
  residueDegreeThree_eq_one_of_residueDegreeProj_eq_one h2 h3 (residueDegreeProj_none_eq_one W)

/-! ### The weighted fundamental identity -/

section IsAlgClosed

variable [W.IsElliptic] [IsAlgClosed F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (q : ProjPoint W)

/-- **The fundamental identity for `[3]` with the residue degrees**, `∑_{p ↦ q} e_p · f_p = 9`.

Over an algebraically closed base field `f_p = 1` at every place, so this is
`sum_ramificationIdxThree_eq_nine`.  It is stated separately because it is the shape Silverman II.2
and Stichtenoth III.1.11 record, and it is the `n = 3` mirror of
`sum_ramificationIdxTwo_mul_residueDegreeTwo` that three merged docstrings named as missing.

⚠️ It does **not** say `#E[3] = 9`: what is counted is places of `F(W)`, and the passage to points
needs the separable-isogeny count that this tree does not have. -/
theorem sum_ramificationIdxThree_mul_residueDegreeThree :
    ∑ p ∈ (finite_comapProjPointThree_preimage_singleton h2 h3 q).toFinset,
      (ramificationIdxThree h2 h3 p).toNat * residueDegreeThree h2 h3 p = 9 := by
  rw [← sum_ramificationIdxThree_eq_nine h2 h3 q]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [residueDegreeThree_eq_one_of_residueDegreeProj_eq_one h2 h3 (residueDegreeProj_eq_one p),
    mul_one]

end IsAlgClosed

/-! ### Non-vacuity

The headline needs `[IsAlgClosed F]`, `[W.IsElliptic]`, `(2 : F) ≠ 0`, `(3 : F) ≠ 0` and the
`IsDedekindDomain W.CoordinateRing` instance at once, and `residueDegreeThree` is itself a
`Module.finrank` of residue fields extracted from `comapProjPoint` by choice.  A curve on which the
whole chain elaborates with nothing supplied by hand is therefore committed rather than quoted, and
every example below closes **by application** of a statement above rather than by `rfl` or
`norm_num`.

`y² + y = x³` over `AlgebraicClosure ℚ` is this tree's `n = 3` certificate curve
(`TranslationActionThree`, `MulByThreeGalois`, `MulByThreeRamification`): the `n = 2` curve
`y² = x³ − x` has no rational `3`-torsion point, and a curve over `ℚ` cannot witness a statement
that needs an algebraically closed base field.

⚠️ **`residueDegreeThree` is not definitionally `1`.**  It is a `Module.finrank`, and the honest
demonstration of that is the third example below: the value `1` is obtained from
`residueDegreeProj_eq_one`, which carries `[IsAlgClosed F]`, and not from unfolding. -/

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

/-- **The tower formula on a curve that exists.** -/
example (p : ProjPoint exampleCurveThree) :
    residueDegreeProj exampleCurveThree
        (comapProjPointThree exampleTwo exampleThree p)
      * residueDegreeThree exampleTwo exampleThree p
      = residueDegreeProj exampleCurveThree p :=
  residueDegreeProj_mul_residueDegreeThree exampleTwo exampleThree p

/-- **`[3]∗` is residually trivial at infinity**, on the same curve. -/
example : residueDegreeThree exampleTwo exampleThree (none : ProjPoint exampleCurveThree) = 1 :=
  residueDegreeThree_none_eq_one exampleTwo exampleThree

/-- **The residue degree is `1` at *every* place of this curve** — and it is read off
`residueDegreeProj_eq_one`, which needs the algebraic closedness, rather than off the definition. -/
example (p : ProjPoint exampleCurveThree) : residueDegreeThree exampleTwo exampleThree p = 1 :=
  residueDegreeThree_eq_one_of_residueDegreeProj_eq_one exampleTwo exampleThree
    (residueDegreeProj_eq_one p)

/-- **The weighted fundamental identity on a curve that exists.** -/
example (q : ProjPoint exampleCurveThree) :
    ∑ p ∈ (finite_comapProjPointThree_preimage_singleton exampleTwo exampleThree q).toFinset,
      (ramificationIdxThree exampleTwo exampleThree p).toNat
        * residueDegreeThree exampleTwo exampleThree p = 9 :=
  sum_ramificationIdxThree_mul_residueDegreeThree exampleTwo exampleThree q

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
