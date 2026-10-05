/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.ThreeDivisionField
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.NormNum.IsSquare

/-!
# Layer two of the `3`-division tower is PROPER at `y² = x³ + 2`

`EllipticCurves.Torsion.ThreeDivisionField` builds the `3`-division field as a two-layer tower
`F ⊆ L₁ ⊆ L₂`, and its `## What is *not* here` records that nothing there says the tower is
**proper** at layer two.  This file closes the positive half of that gap over `ℚ`, by exhibiting
one curve at which layer two does adjoin something:

`(⊤ : Subalgebra L₁ (threeDivisionField (y2EqX3AddTwo))) ≠ ⊥`.

⚠️ **This is the opposite direction from the certificate curve.** At `y2AddYEqX3` layer two is
`⊤ = ⊥`, so properness there is **false** and no work at that fixture could ever discharge the
bullet.  ⚠️ **That is not hand arithmetic here: it is a landed theorem**,
`top_eq_bot_threeDivisionField_y2AddYEqX3` of `EllipticCurves.Torsion.ThreeDivisionField`, which
this file imports.  ⚠️ **It is `private` there, so grep for the name and do NOT `#check` it from an
importing file**; nothing below uses it, this file proving nothing about that curve.  The two
statements together turn the bullet from one about emptiness into one about generality.

## The mechanism

`Ψ₂Sq_eval_eq_sq` (`EllipticCurves.Torsion.TwoTorsion`) gives `W.Ψ₂Sq.eval x = (2y + a₁x + a₃) ^ 2`
at any point `(x, y)` of `W`, so `Ψ₂Sq.eval x₀` is a square in exactly the fields carrying a
`y`-coordinate above `x₀`.  **Layer two is proper precisely when some value `Ψ₂Sq` takes at a root
of `Ψ₃` is not already a square at layer one**, and that is the single inequality this file proves.

For `y² = x³ + 2` the invariants are `b₂ = b₄ = b₈ = 0` and `b₆ = 8`, so

```
Ψ₂Sq = 4X³ + 8        Ψ₃ = 3X⁴ + 24X = 3X(X + 2)(X² - 2X + 4)
```

and `x = 0` is a root of `Ψ₃` at which `Ψ₂Sq` takes the value `8`.

## ⚠️ Why the degree of `L₁` is never computed, and the curve that makes that possible

⚠️ **The one structural idea here is that a minimal field needs no degree.** `L₁` is *a splitting
field* of `Ψ₃`, so `Polynomial.IsSplittingField.lift` maps it into **any** field over which `Ψ₃`
splits, and a field map is injective — so a value that fails to be a square downstream cannot have
been a square in `L₁`.  It is therefore enough to name **one** concrete field where `Ψ₃` splits and
`8` is not a square, and the abstract `L₁` is bounded by it for free.  ⚠️ **No `[L₁ : ℚ]`, no
`IntermediateField`, no tower law, and no `abbrev`/diamond hazard.**

That reduces the whole problem to choosing a curve whose `Ψ₃` splits over a field small enough to
compute in.  ⚠️ **`ζ₃ ∈ L₁` for every curve over `ℚ`** — an automorphism fixing every `x`-coordinate
of `E[3]` acts as `±1`, both of determinant `1`, so the cyclotomic character is trivial on
`Gal(ℚ̄/L₁)` — hence `ℚ(√-3) ⊆ L₁` always and `ℚ(√-3)` is the smallest `L₁` available.  The curve
below attains it: `X³ + 8` has the rational root `-2`, so

`Ψ₃ = 3X(X + 2)(X² - 2X + 4)` splits over `ℚ(√-3)`, whose elements are `a + b√-3` with `a b : ℚ`.

⚠️ **`8` is not a square there, and both cases of the check are elementary**: `(a + b√-3)² = 8`
forces `2ab = 0` and `a² - 3b² = 8`, and then `b = 0` gives `a² = 8` — not a rational square — while
`a = 0` gives `-3b² = 8`, impossible by positivity alone.

## Why not `y² = x³ - 1`

⚠️ **`y² = x³ - 1` is a witness too and it is the expensive one.** There `Ψ₃ = 3X(X³ - 4)` with
`X³ - 4` irreducible, so `L₁ = ℚ(∛4, ζ₃)` has degree `6`, the value at `x = 0` is `-4`, and the
argument is that `√-4 ∈ L₁` would put the biquadratic `ℚ(i, ζ₃)` of degree `4` inside a field of
degree `6`.  **That route needs `[L₁ : ℚ] = 6`, a cube-root radical extension and the tower law.**
Adding a rational root to the cubic removes all three, which is the whole reason `y² = x³ + 2` is
the curve here.  The tree's two rational fixtures are **not** available either: layer two collapses
at `y2AddYEqX3` and at `y2EqX3AddOne`, because at both of them every value `Ψ₂Sq` takes at a root of
`Ψ₃` is already a square at layer one — `1` and `-3` at the first, `4` and `-12` at the second, and
`√-3 ∈ L₁` in each case.

## ⚠️ What is *not* proved here

Three things said above are **prose**, and ⚠️ **nothing below depends on any of them**:

* **The floor argument** — *"`ζ₃ ∈ L₁` for every curve over `ℚ`, so `ℚ(√-3)` is the smallest `L₁`
  available"*.  It is a statement about the Galois action on `E[3]`, formalised nowhere in this
  repository.  It records why this curve was chosen; no proof below uses it.
* **The `y² = x³ - 1` account** — its `Ψ₃`, the irreducibility of `X³ - 4`, the degree `6` and the
  biquadratic obstruction.  Hand arithmetic, kept because it is the reason that curve is the dearer
  witness and this one the cheaper.
* **The collapse at the two fixtures** — the values `1`, `-3`, `4` and `-12` in the paragraph above.
  Hand arithmetic as well, and deliberately given with no citation: this file proves nothing about
  either of those two curves, and a pointer to a section elsewhere would be a claim about a ref.

⚠️ **The two public theorems below rest on `splits_Ψ₃_QSqrtNegThree`, on `not_isSquare_eight` and
on `Polynomial.IsSplittingField.lift`, and on none of the three.**

## The curve is local to this file

`y2EqX3AddTwo` is a `def` in this module's own namespace and **not** a `EllipticCurves.Fixtures`
entry.  `Fixtures.lean` carries a census of which fixture is used where and a shared `IsElliptic`
convention, and adding a row to it is a tree-wide act that one single-file consumer does not earn;
this file is that one consumer.

⚠️ **It is a `def` and not a `private def`, and the ground for keeping it here is therefore "no
`Fixtures` row, one consumer" and not visibility.**  Both public theorems below name the curve in
their own statements, so a private curve would give them types mentioning a constant no importing
file can write.  A public `def` *is* importable, so *"local to this file"* is a claim about today's
consumers rather than about reachability — which is exactly what a `Fixtures` row, with its census,
would be the honest way to record if a second consumer ever appeared.

⚠️ **If a second file ever wants this curve, promote it then**: the `IsElliptic` instance below is
the tactic block `Fixtures.lean` prescribes for its rows, without the `private` those rows carry, so
promoting it is a move and not a rewrite.
-/

open Polynomial

namespace EllipticCurves.ThreeDivisionFieldProper

/-! ## `ℚ(√-3)`, as a concrete field in which `8` is not a square -/

/-- The minimal polynomial of `√-3` over `ℚ`. -/
private noncomputable abbrev sqrtNegThreePoly : ℚ[X] := X ^ 2 + C 3

private theorem sqrtNegThreePoly_monic : sqrtNegThreePoly.Monic := by
  unfold sqrtNegThreePoly; monicity!

private theorem sqrtNegThreePoly_natDegree : sqrtNegThreePoly.natDegree = 2 := by
  unfold sqrtNegThreePoly; compute_degree!

/-- `X² + 3` is irreducible over `ℚ`: it is monic of degree `2`, so it is irreducible as soon as it
has no rational root, and `a² + 3 = 0` fails by positivity. -/
private theorem irreducible_sqrtNegThreePoly : Irreducible sqrtNegThreePoly := by
  rw [Monic.irreducible_iff_roots_eq_zero_of_degree_le_three sqrtNegThreePoly_monic
    (by rw [sqrtNegThreePoly_natDegree]) (by rw [sqrtNegThreePoly_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun a ha => ?_
  rw [mem_roots (Monic.ne_zero sqrtNegThreePoly_monic), IsRoot.def] at ha
  simp only [sqrtNegThreePoly, eval_add, eval_pow, eval_X, eval_C] at ha
  nlinarith [sq_nonneg a]

private noncomputable instance : Fact (Irreducible sqrtNegThreePoly) :=
  ⟨irreducible_sqrtNegThreePoly⟩

/-- **`ℚ(√-3)`**, presented as `ℚ[X]/(X² + 3)`.  ⚠️ This is the *smallest* field that can serve as
layer one for any curve over `ℚ`, and `sqrtNegThree` below is the adjoined root. -/
private noncomputable abbrev QSqrtNegThree : Type := AdjoinRoot sqrtNegThreePoly

private noncomputable instance : CharZero QSqrtNegThree :=
  charZero_of_injective_algebraMap (algebraMap ℚ QSqrtNegThree).injective

/-- The adjoined square root of `-3`. -/
private noncomputable abbrev sqrtNegThree : QSqrtNegThree := AdjoinRoot.root sqrtNegThreePoly

private theorem sqrtNegThree_sq : sqrtNegThree ^ 2 = -3 := by
  have h : sqrtNegThreePoly.eval₂ (AdjoinRoot.of sqrtNegThreePoly)
      (AdjoinRoot.root sqrtNegThreePoly) = 0 := AdjoinRoot.eval₂_root sqrtNegThreePoly
  simp only [sqrtNegThreePoly, eval₂_add, eval₂_pow, eval₂_X, map_ofNat, eval₂_ofNat] at h
  linear_combination h

/-- **`1` and `√-3` are linearly independent over `ℚ`** — ⚠️ proved by POSITIVITY and not from a
basis: `x + y√-3 = 0` squares to `x² + 3y² = 0`, and over `ℚ` that forces both. -/
private theorem eq_zero_of_add_mul_sqrtNegThree_eq_zero {x y : ℚ}
    (h : (x : QSqrtNegThree) + (y : QSqrtNegThree) * sqrtNegThree = 0) : x = 0 ∧ y = 0 := by
  have key : x ^ 2 + 3 * y ^ 2 = 0 := by
    have hK : ((x ^ 2 + 3 * y ^ 2 : ℚ) : QSqrtNegThree) = 0 := by
      push_cast
      linear_combination ((x : QSqrtNegThree) - (y : QSqrtNegThree) * sqrtNegThree) * h
        + (y : QSqrtNegThree) ^ 2 * sqrtNegThree_sq
    exact_mod_cast hK
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

/-- **Every element of `ℚ(√-3)` is `a + b√-3`.**  `AdjoinRoot.powerBasis` writes it as `aeval` of a
polynomial of degree `< 2`, and `Polynomial.eq_X_add_C_of_natDegree_le_one` names the two
coefficients. -/
private theorem exists_eq_add_mul_sqrtNegThree (z : QSqrtNegThree) :
    ∃ a b : ℚ, z = (a : QSqrtNegThree) + (b : QSqrtNegThree) * sqrtNegThree := by
  obtain ⟨p, hp, rfl⟩ := (AdjoinRoot.powerBasis (f := sqrtNegThreePoly)
    (Monic.ne_zero sqrtNegThreePoly_monic)).exists_eq_aeval z
  rw [AdjoinRoot.powerBasis_dim, sqrtNegThreePoly_natDegree] at hp
  have hpe := eq_X_add_C_of_natDegree_le_one (p := p) (by omega)
  refine ⟨p.coeff 0, p.coeff 1, ?_⟩
  rw [AdjoinRoot.powerBasis_gen]
  conv_lhs => rw [hpe]
  simp only [map_add, map_mul, aeval_C, aeval_X, eq_ratCast]
  ring

/-- **⚠️ `8` is not a square in `ℚ(√-3)`** — the one inequality this file turns on.

`(a + b√-3)² = 8` gives `a² - 3b² = 8` and `2ab = 0`.  With `a = 0` the first reads `-3b² = 8`,
refuted by positivity with no irrationality input at all; with `b = 0` it reads `a² = 8`, refuted
because `8` is not a square in `ℚ`. -/
private theorem not_isSquare_eight : ¬ IsSquare (8 : QSqrtNegThree) := by
  have hQ : ¬ IsSquare (8 : ℚ) := by norm_num
  rintro ⟨z, hz⟩
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_sqrtNegThree z
  have h : ((a ^ 2 - 3 * b ^ 2 - 8 : ℚ) : QSqrtNegThree)
      + ((2 * a * b : ℚ) : QSqrtNegThree) * sqrtNegThree = 0 := by
    push_cast
    linear_combination -hz - (b : QSqrtNegThree) ^ 2 * sqrtNegThree_sq
  obtain ⟨h1, h2⟩ := eq_zero_of_add_mul_sqrtNegThree_eq_zero h
  rcases mul_eq_zero.mp h2 with hh | hh
  · have ha : a = 0 := by linarith
    subst ha; nlinarith [sq_nonneg b]
  · subst hh; exact hQ ⟨a, by nlinarith⟩

/-! ## The curve `y² = x³ + 2` -/

open WeierstrassCurve WeierstrassCurve.Affine

/-- **`y² = x³ + 2`**, of discriminant `-1728`.  ⚠️ Local to this file on purpose; see the module
docstring's *"The curve is local to this file"*. -/
def y2EqX3AddTwo : Affine ℚ := ⟨0, 0, 0, 0, 2⟩

/-- `Δ = -432a₆² = -1728 ≠ 0`. -/
instance : y2EqX3AddTwo.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  decide +kernel

/-- `b₂ = a₁² + 4a₂ = 0`, `b₄ = 2a₄ + a₁a₃ = 0` and `b₆ = a₃² + 4a₆ = 8`. -/
private lemma Ψ₂Sq_y2EqX3AddTwo : y2EqX3AddTwo.Ψ₂Sq = C 4 * X ^ 3 + C 8 := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    y2EqX3AddTwo]
  norm_num only
  simp only [map_ofNat, Polynomial.C_0]
  ring

/-- **⚠️ The cubic has a RATIONAL root.**  `Ψ₃ = 3X⁴ + 3b₆X = 3X(X³ + 8)` and `X³ + 8` factors as
`(X + 2)(X² - 2X + 4)` over `ℚ` — which is the whole reason this curve is cheap and
`y² = x³ - 1`, whose `X³ - 4` is irreducible, is not. -/
private lemma Ψ₃_y2EqX3AddTwo :
    y2EqX3AddTwo.Ψ₃ = C 3 * X * ((X + C 2) * (X ^ 2 - C 2 * X + C 4)) := by
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, y2EqX3AddTwo]
  norm_num only
  simp only [map_ofNat, Polynomial.C_0]
  ring

/-- Both factorisations survive every base change out of `ℚ`: the coefficients are integers. -/
private lemma Ψ₂Sq_baseChange_y2EqX3AddTwo (K : Type*) [Field K] [Algebra ℚ K] :
    (y2EqX3AddTwo⁄K).Ψ₂Sq = C 4 * X ^ 3 + C 8 := by
  rw [show (y2EqX3AddTwo⁄K).Ψ₂Sq = y2EqX3AddTwo.Ψ₂Sq.map (algebraMap ℚ K) from
      WeierstrassCurve.map_Ψ₂Sq .., Ψ₂Sq_y2EqX3AddTwo]
  simp [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow]

private lemma Ψ₃_baseChange_y2EqX3AddTwo (K : Type*) [Field K] [Algebra ℚ K] :
    (y2EqX3AddTwo⁄K).Ψ₃ = C 3 * X * ((X + C 2) * (X ^ 2 - C 2 * X + C 4)) := by
  rw [show (y2EqX3AddTwo⁄K).Ψ₃ = y2EqX3AddTwo.Ψ₃.map (algebraMap ℚ K) from
      WeierstrassCurve.map_Ψ₃ .., Ψ₃_y2EqX3AddTwo]
  simp [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow]

/-! ## `Ψ₃` splits over `ℚ(√-3)`, so layer one embeds there -/

/-- `X² - 2X + 4 = (X - (1 + √-3))(X - (1 - √-3))`, because the product of the two roots is
`1 - (√-3)² = 4`. -/
private lemma quadratic_factor_eq :
    (X ^ 2 - C 2 * X + C 4 : QSqrtNegThree[X])
      = (X - C (1 + sqrtNegThree)) * (X - C (1 - sqrtNegThree)) := by
  have hC : (C sqrtNegThree : QSqrtNegThree[X]) ^ 2 = -3 := by
    rw [← map_pow, sqrtNegThree_sq, map_neg, map_ofNat]
  simp only [map_add, map_sub, map_one, map_ofNat]
  linear_combination hC

/-- **`Ψ₃` splits over `ℚ(√-3)`**: it is `3 · X · (X + 2) · (X - (1 + √-3)) · (X - (1 - √-3))`. -/
private theorem splits_Ψ₃_QSqrtNegThree : (y2EqX3AddTwo⁄QSqrtNegThree).Ψ₃.Splits := by
  rw [Ψ₃_baseChange_y2EqX3AddTwo, quadratic_factor_eq]
  refine Splits.mul (Splits.mul (Splits.C _) Splits.X) (Splits.mul ?_ (Splits.mul ?_ ?_))
  · exact Splits.X_add_C _
  · exact Splits.X_sub_C _
  · exact Splits.X_sub_C _

/-! ## Layer two is proper -/

/-- ⚠️ **Layer one embeds in `ℚ(√-3)` — and this is the step that replaces the degree argument.**

`Polynomial.IsSplittingField.lift`: a splitting field of `Ψ₃` maps into **every** field over which
`Ψ₃` splits, and `splits_Ψ₃_QSqrtNegThree` says `ℚ(√-3)` is one.  Since a field map is injective,
anything that fails to be a square in `ℚ(√-3)` was not a square upstairs either — so `[L₁ : ℚ]` is
never computed and no `IntermediateField` is ever formed. -/
private noncomputable def liftToQSqrtNegThree :
    y2EqX3AddTwo.Ψ₃.SplittingField →ₐ[ℚ] QSqrtNegThree :=
  IsSplittingField.lift (F := QSqrtNegThree) y2EqX3AddTwo.Ψ₃.SplittingField y2EqX3AddTwo.Ψ₃
    (by rw [← WeierstrassCurve.map_Ψ₃]; exact splits_Ψ₃_QSqrtNegThree)

/-- **`8` is not a square at layer one**, pulled back along the embedding above. -/
private theorem not_isSquare_eight_splittingField :
    ¬ IsSquare (8 : y2EqX3AddTwo.Ψ₃.SplittingField) := fun h => by
  refine not_isSquare_eight ?_
  simpa [map_ofNat] using h.map liftToQSqrtNegThree.toRingHom.toMonoidHom

private lemma Ψ₃_eval_zero :
    ((y2EqX3AddTwo⁄y2EqX3AddTwo.Ψ₃.SplittingField).Ψ₃).eval 0 = 0 := by
  rw [Ψ₃_baseChange_y2EqX3AddTwo]; simp

private lemma Ψ₂Sq_eval_zero :
    ((y2EqX3AddTwo⁄y2EqX3AddTwo.Ψ₃.SplittingField).Ψ₂Sq).eval 0 = 8 := by
  rw [Ψ₂Sq_baseChange_y2EqX3AddTwo]; simp

/-- **⚠️ The single inequality the whole file turns on**: `x = 0` is a root of `Ψ₃`, the value of
`Ψ₂Sq` there is `8`, and `8` is not a square at layer one.  By `Ψ₂Sq_eval_eq_sq` that says exactly
that the `3`-torsion points above `x = 0` have no `y`-coordinate in `L₁`. -/
private theorem not_isSquare_Ψ₂Sq_eval_zero :
    ¬ IsSquare (((y2EqX3AddTwo⁄y2EqX3AddTwo.Ψ₃.SplittingField).Ψ₂Sq).eval 0) := by
  rw [Ψ₂Sq_eval_zero]; exact not_isSquare_eight_splittingField

/-- **⚠️ Layer two's polynomial does NOT split over layer one** at `y² = x³ + 2`.

If it did, then `X² - C 8` — which divides it, because `8` is the value `Ψ₂Sq` takes at the root
`0` of `Ψ₃` — would split too and hand over a square root of `8` in `L₁`. -/
theorem not_splits_Ψ₂SqRootPoly_y2EqX3AddTwo :
    ¬ (Ψ₂SqRootPoly y2EqX3AddTwo y2EqX3AddTwo.Ψ₃.SplittingField).Splits := by
  intro hs
  have h3 : (3 : y2EqX3AddTwo.Ψ₃.SplittingField) ≠ 0 := by norm_num
  have hdvd := dvd_Ψ₂SqRootPoly (W := y2EqX3AddTwo) Ψ₃_eval_zero h3
  have hdeg : (X ^ 2 -
      C (((y2EqX3AddTwo⁄y2EqX3AddTwo.Ψ₃.SplittingField).Ψ₂Sq).eval 0) :
        y2EqX3AddTwo.Ψ₃.SplittingField[X]).degree = 2 := by
    compute_degree!
  obtain ⟨s, hsv⟩ :=
    (hs.of_dvd Ψ₂SqRootPoly_ne_zero hdvd).exists_eval_eq_zero (by rw [hdeg]; decide)
  simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hsv
  exact not_isSquare_Ψ₂Sq_eval_zero ⟨s, by rw [← hsv]; ring⟩

/-- **⚠️ LAYER TWO OF THE `3`-DIVISION TOWER IS PROPER AT `y² = x³ + 2`.**

The `3`-division field is **not** generated over layer one by the empty set, so the tower really is
two steps at this curve.  `Polynomial.IsSplittingField.splits_iff` at layer two's polynomial,
contraposed against the theorem above.

⚠️ **This is `top_eq_bot_threeDivisionField_y2AddYEqX3` with the curve and the verdict both
changed** — that theorem, `private` in `EllipticCurves.Torsion.ThreeDivisionField` and named here
because it is now in the tree, says layer two adjoins nothing at the certificate curve
`y2AddYEqX3`; this one says it adjoins something at `y² = x³ + 2`.  ⚠️ **Neither is the negation of
the other, and neither is the other's converse**: they are one predicate at two different curves,
and that is precisely why the pair turns `ThreeDivisionField`'s `## What is *not* here` bullet
about `[L₂ : F]` from a statement about emptiness into one about generality.  Properness at layer
two is **false** at the certificate curve and **true** here.

⚠️ **It still computes no degree: no statement in this file names `[L₁ : ℚ]`, `[L₂ : L₁]` or
`[L₂ : ℚ]`, and the prose above names the first of the three, three times.**  ⚠️ **Say it that way
and not *named anywhere in this file*, which is false of all three** — the paragraph under
`` ## ⚠️ Why the degree of `L₁` is never computed, and the curve that makes that possible `` names
`[L₁ : ℚ]`, so does the `y² = x³ - 1` account, and so does `liftToQSqrtNegThree`, while the only
occurrence of either of the other two is this sentence itself.  The widest reading of the old
words was refuted by the text carrying them.  Nothing here says `L₂ / ℚ` is normal either — so
`ThreeDivisionField`'s *"the case `threeDivisionGaloisField W = threeDivisionField W` is not
excluded"* is untouched by this, exactly as it is by the collapse at the certificate curve. -/
theorem top_ne_bot_threeDivisionField_y2EqX3AddTwo :
    (⊤ : Subalgebra y2EqX3AddTwo.Ψ₃.SplittingField (threeDivisionField y2EqX3AddTwo)) ≠ ⊥ :=
  fun h => not_splits_Ψ₂SqRootPoly_y2EqX3AddTwo
    ((IsSplittingField.splits_iff (threeDivisionField y2EqX3AddTwo)
      (Ψ₂SqRootPoly y2EqX3AddTwo y2EqX3AddTwo.Ψ₃.SplittingField)).mpr h)

end EllipticCurves.ThreeDivisionFieldProper
