/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.ProjectiveDivisor
import EllipticCurves.FunctionField.CoordinateRingNormalAlgClosed
import EllipticCurves.FunctionField.MulByThreeResidueDegree

/-!
# The two degree functions on places agree over an algebraically closed base field

This tree carries **two** notions of the degree of a place, defined by different routes and never
compared:

* `WeierstrassCurve.Affine.degPt v = Ideal.natDegreeGenerator (Ideal.relNorm F[X] v.asIdeal)`
  (`EllipticCurves.FunctionField.DivisorDegree`) — a *relative ideal norm to `F[X]`*, which is what
  the degree-zero theorem `degDiv (div f) + ordInfty f = 0` weights its divisors by;
* `WeierstrassCurve.Affine.CoordinateRing.residueDegreeProj W p`, which is
  `Module.finrank F (residueFieldProj W p)`
  (`EllipticCurves.FunctionField.PlaceResidueField`) — the *residue-field degree over `F`*, which is
  what the fundamental identity `∑_{p ↦ q} e_p · f_p = 4` weights its ramification indices by.

Two merged module docstrings asserted, in the indicative and without proof, that the two agree.
This file proves it over an algebraically closed base field, which is where every consumer of
either function lives, and records why the general case is a different problem rather than a longer
one.

## Main results

* `WeierstrassCurve.Affine.degPt_eq_one` — every affine closed point has degree `1`;
* `WeierstrassCurve.Affine.degProjPt_eq_one` — and so does the point at infinity;
* `WeierstrassCurve.Affine.degPt_eq_residueDegreeProj` — the affine comparison;
* **`WeierstrassCurve.Affine.degProjPt_eq_residueDegreeProj`** — the headline: the two degree
  functions on `ProjPoint W` are equal;
* `WeierstrassCurve.Affine.degProj_eq_sum` / `degDiv_eq_sum` — a divisor's degree is the plain sum
  of its coefficients, so the degree-zero theorem reads *"as many zeros as poles"*;
* `WeierstrassCurve.Affine.CoordinateRing.sum_ramificationIdxTwo_mul_degProjPt` and
  `sum_ramificationIdxThree_mul_degProjPt` — the fundamental identity in the `∑ e_p · deg p`
  spelling, at `n = 2` and `n = 3`.

## The proof, and the two halves that were already merged

The residue-degree half has been available since `#749`: `residueDegreeProj_eq_one` holds for
*every* place, with no classification of ideals behind it — Zariski's lemma makes
`algebraMap F (residueFieldProj W p)` surjective and
`residueDegreeProj_eq_one_iff_surjective` converts that to the degree.

So the whole comparison reduces to `degPt v = 1`, and both inputs for that are merged too:

* `exists_equation_and_eq_XYIdeal_of_isMaximal`
  (`EllipticCurves.FunctionField.CoordinateRingNormalAlgClosed`, `#396`/`#469`) — over an
  algebraically closed field every maximal ideal of `F[W]` is `XYIdeal W a (C b)` for a point
  `(a, b)` on the curve;
* `degPt_pointClosedPoint` (`EllipticCurves.FunctionField.RationalPointDegree`) — `degPt` is `1` at
  the closed point of a rational point, because `v_{-P} · v_P = ⟨x - x₀⟩` has norm `(X - x₀)²`.

The bridge between them is that a height-one prime of a Dedekind domain is maximal, so the
classification applies to *every* `v` and not only to those already presented as a point; Mathlib's
`equation_iff_nonsingular` upgrades the `W.Equation a b` it returns to the `W.Nonsingular a b` that
`degPt_pointClosedPoint` consumes.  That is the entire content of `degPt_eq_one`, and it is the
reason this identification is three lines rather than the relative-ideal-norm computation the
general case needs.

## What the `none` branch is worth

`degProjPt W none = 1` is a *definitional choice*
(`EllipticCurves.FunctionField.ProjectiveDivisor`), while `residueDegreeProj_none_eq_one` is a
*theorem*, and one that needs no hypothesis on `F` at
all.  `degProjPt_none_unique` separately shows the choice is forced: no other weight makes the
degree-zero theorem hold.  `degProjPt_eq_residueDegreeProj` is what ties the three together — the
convention, the theorem it had to match, and the uniqueness that says it had no freedom.

## ⚠️ Nothing here is new mathematics about `[2]` or `[3]`

`sum_ramificationIdxTwo_mul_degProjPt` is `sum_ramificationIdxTwo_eq_four` with a weight that
`degProjPt_eq_one` shows is `1`, and the `n = 3` statement is the same sentence off
`sum_ramificationIdxThree_eq_nine`.  **A reader who sees `∑_{p ↦ q} e_p · deg p = 4` land will read
it as progress on `[2]`; it is not.**  Five merged docstrings write the fundamental identity in that
spelling, and until now the tree proved only the `f_p` one — so what changes is that a spelling
already in use becomes *statable*, exactly as `#1046` made `∑ e_p · f_p = 9` statable at `n = 3`
without proving anything about `[3]`.

⚠️ In particular this is **not** `#E[n] = n²`.  What is counted is places of `F(W)`; the passage to
a count of torsion points runs through *"a separable isogeny has `#ker = deg`"*, which no file in
this tree contains.  `PlaceRamificationInertia`, `MulByThreeResidueDegree` and `MulByTwoDegree` all
carry the same warning and all three are right.

## Scope — ⚠️ the general base field is open, and every hypothesis of the route is discharged

Everything below carries `[IsAlgClosed F]`, and **that is not a convenience**: over a general field
`degPt v = residueDegreeProj W (some v)` is not proved here and does not follow from anything below.

The classical route is `Ideal.relNorm F[X] v.asIdeal = p ^ f` for `p` the prime of `F[X]` below `v`
and `f` the relative residue degree, together with the tower `[κ(v) : F] = f · [κ(p) : F]` and the
multiplicativity of `Ideal.natDegreeGenerator`.  Mathlib proves the first step as
`Ideal.relNorm_eq_pow_of_isMaximal` — ⚠️ **but under `[PerfectField (FractionRing R)]`**, and here
`R = F[X]`, whose fraction field is `RatFunc F`, which is **not perfect in characteristic `p`**:
`X` has no `p`-th root in it.

⚠️ **This paragraph used to continue** *"The Galois-hypothesis variant
`relNorm_eq_pow_of_isPrime_isGalois` wants `IsGalois (RatFunc F) F(W)`, which a Weierstrass
extension is not in general."*  **The quoted clause is false and the number of hypotheses it
saved was zero.**  `EllipticCurves.FunctionField.NegYGalois` proves
`WeierstrassCurve.Affine.CoordinateRing.isGalois_ratFunc` — `IsGalois (RatFunc F) F(W)` for every
elliptic curve over every field, in **every** characteristic — off the hyperelliptic involution
`ι` of `EllipticCurves.FunctionField.NegYInvolution` and Artin's theorem on fixed fields, against
the merged degree `[F(W) : F(x)] = 2`.  It also proves
`isGalois_fractionRing_polynomial`, which is the `FractionRing F[X]` spelling
`relNorm_eq_pow_of_isPrime_isGalois` literally consumes.

⚠️ **The Galois hypothesis is discharged, and so is every other typeclass hypothesis of that
lemma.**  Besides `IsGalois`, `relNorm_eq_pow_of_isPrime_isGalois` wants `[IsDedekindDomain F[X]]`,
`[IsDedekindDomain F[W]]`, `[Module.Finite F[X] F[W]]` and `[Module.IsTorsionFree F[X] F[W]]`, and
— checked by elaboration, not by reading — **all four already hold for an elliptic curve over an
arbitrary field**: the two `F[X]`-side ones and the torsion-freeness from Mathlib's generic
instances, `[IsDedekindDomain F[W]]` from
`EllipticCurves.FunctionField.CoordinateRingNormalGeneral.instIsDedekindDomain`, and
`[Module.Finite F[X] F[W]]` from
`EllipticCurves.FunctionField.DivisorDegree.instModuleFiniteCoordinateRing`.  So for a prime `P`
of `F[W]` lying over a maximal `p` of `F[X]`,
`Ideal.relNorm F[X] P = p ^ P.inertiaDeg F[X]` **is now available over a general base field**: the
first step of the classical route is unblocked, and `[PerfectField (RatFunc F)]` is not needed for
it after all.

⚠️ **The second step is what is still missing, and it is now the only thing missing.**  That
`relNorm` value has to be combined with the tower `[κ(v) : F] = f · [κ(p) : F]` and the
multiplicativity of `Ideal.natDegreeGenerator` before it becomes
`degPt v = residueDegreeProj W (some v)`.  ⚠️ **Both of those ingredients also already exist** —
the tower is Mathlib's `Module.finrank_mul_finrank`, and the multiplicativity is
`Ideal.natDegreeGenerator_mul` of `EllipticCurves.FunctionField.DivisorDegree`, which this file
transitively imports — so naming them is naming what the assembly *consumes*, not what it lacks.
**What is absent is the assembly itself**, which is written nowhere in this tree, and until it is
written every statement below keeps `[IsAlgClosed F]` and the general comparison stays open.

⚠️ So the remaining obstruction is a computation rather than a missing hypothesis — which is the
opposite of what the retired clause said, and this paragraph is deliberately not predicting the
price of that computation.  Four sweeps of this tree have been spent retiring sentences that named
a route and got it wrong; the clause retired just above was one of them, and a replacement that
over-states what is left would be another.

## What is deliberately *not* changed

* **No consumer is re-plumbed.**  Both stale docstrings said *"nothing below assumes it"*, and that
  was true and stays true: this file adds a bridge and crosses nothing over it.  Rewriting the
  `f_p`-weighted statements to use `degPt`, or the reverse, is a separate and reviewable decision.
* **`residueDegreeProj`'s defining docstring still says it is *not* `degPt`**, and that sentence is
  correct: the two are different definitions, and over a general field they are not known to be
  equal.  What is proved below is an equality of *values* over `F̄`, not an identification of
  notions.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2.
* [H. Stichtenoth, *Algebraic function fields and codes*][stichtenoth2009], I.4 (the degree of a
  place) and III.1.11 (the fundamental identity).
-/

open Polynomial Polynomial.Bivariate IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [IsAlgClosed F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing]

/-! ### Every place has degree one -/

/-- **Every affine closed point of a curve over an algebraically closed field has degree `1`.**

A height-one prime of a Dedekind domain is maximal, so
`exists_equation_and_eq_XYIdeal_of_isMaximal` presents `v` as the closed point of an on-curve point
`(a, b)`, and `degPt_pointClosedPoint` computes the degree there. -/
theorem degPt_eq_one (v : HeightOneSpectrum W.CoordinateRing) : degPt v = 1 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨a, b, hab, hv⟩ :=
    CoordinateRing.exists_equation_and_eq_XYIdeal_of_isMaximal (W := W) v.asIdeal
  have hns : W.Nonsingular a b := equation_iff_nonsingular.mp hab
  have hveq : v = CoordinateRing.pointClosedPoint hns.left :=
    HeightOneSpectrum.ext (by simpa using hv)
  rw [hveq]
  exact degPt_pointClosedPoint hns

variable (W) in
/-- **Every place of the projective curve has degree `1`.**  At infinity this is the definitional
weight of `degProjPt`; at an affine place it is `degPt_eq_one`. -/
theorem degProjPt_eq_one (p : ProjPoint W) : degProjPt W p = 1 := by
  cases p with
  | none => exact degProjPt_none
  | some v => exact degPt_eq_one v

/-! ### The comparison -/

/-- **The relative ideal norm and the residue-field degree agree at an affine closed point**, over
an algebraically closed base field. -/
theorem degPt_eq_residueDegreeProj (v : HeightOneSpectrum W.CoordinateRing) :
    degPt v = residueDegreeProj W (some v) := by
  rw [degPt_eq_one, residueDegreeProj_eq_one]

variable (W) in
/-- **The two degree functions on places of the projective curve are equal**, over an algebraically
closed base field.

This is the statement `EllipticCurves.FunctionField.PlaceResidueField` and
`EllipticCurves.FunctionField.PlaceResidueDegree` both asserted without proof.  At the point at
infinity it says the definitional weight `degProjPt W none = 1` agrees with the theorem
`residueDegreeProj_none_eq_one`; `degProjPt_none_unique` says that weight was forced anyway. -/
theorem degProjPt_eq_residueDegreeProj (p : ProjPoint W) :
    degProjPt W p = residueDegreeProj W p := by
  rw [degProjPt_eq_one, residueDegreeProj_eq_one]

/-! ### Divisor degrees are coefficient sums -/

variable (W) in
/-- **The degree of a projective divisor is the sum of its coefficients**, over an algebraically
closed base field.  With `degProj_divisorProj` this is the statement that a rational function has as
many zeros as poles, counted with multiplicity. -/
theorem degProj_eq_sum (D : ProjPoint W →₀ ℤ) : degProj W D = D.sum fun _ n => n := by
  simp [degProj, degProjPt_eq_one]

variable (W) in
/-- **The degree of an affine divisor is the sum of its coefficients**, over an algebraically closed
base field. -/
theorem degDiv_eq_sum (D : HeightOneSpectrum W.CoordinateRing →₀ ℤ) :
    degDiv W D = D.sum fun _ n => n := by
  simp [degDiv, degPt_eq_one]

/-! ### The fundamental identity in the `∑ e_p · deg p` spelling -/

namespace CoordinateRing

variable (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (q : ProjPoint W)

/-- **The fundamental identity for `[2]` with the point degrees**, `∑_{p ↦ q} e_p · deg p = 4`.

⚠️ This proves nothing new about `[2]`: over an algebraically closed base field `deg p = 1` at every
place (`degProjPt_eq_one`), so this is `sum_ramificationIdxTwo_eq_four` reweighted.  It is stated
because it is the spelling five merged docstrings of this subtree use, and until now the tree proved
only the `f_p`-weighted `sum_ramificationIdxTwo_mul_residueDegreeTwo`.  Over a general base field
the two weights are different quantities and only the relative one is expected to survive. -/
theorem sum_ramificationIdxTwo_mul_degProjPt :
    ∑ p ∈ (finite_comapProjPointTwo_preimage_singleton h2 q).toFinset,
      (ramificationIdxTwo h2 p).toNat * degProjPt W p = 4 := by
  rw [← sum_ramificationIdxTwo_eq_four h2 q]
  exact Finset.sum_congr rfl fun p _ => by rw [degProjPt_eq_one, mul_one]

/-- **The fundamental identity for `[3]` with the point degrees**, `∑_{p ↦ q} e_p · deg p = 9`.

The `n = 3` mirror of `sum_ramificationIdxTwo_mul_degProjPt`, off `#1046`'s
`sum_ramificationIdxThree_eq_nine`, and equally free of new content about `[3]`. -/
theorem sum_ramificationIdxThree_mul_degProjPt :
    ∑ p ∈ (finite_comapProjPointThree_preimage_singleton h2 h3 q).toFinset,
      (ramificationIdxThree h2 h3 p).toNat * degProjPt W p = 9 := by
  rw [← sum_ramificationIdxThree_eq_nine h2 h3 q]
  exact Finset.sum_congr rfl fun p _ => by rw [degProjPt_eq_one, mul_one]

end CoordinateRing

/-! ### Non-vacuity

Every statement above carries `[IsAlgClosed F]`, `[W.IsElliptic]` and
`[IsDedekindDomain W.CoordinateRing]` at once, and the two fundamental identities add `(2 : F) ≠ 0`
and `(3 : F) ≠ 0`.  That instance set is strictly stronger than the one
`EllipticCurves.FunctionField.PlaceResidueDegree` certifies, so its `ℚ`-rational curve does not
serve here and a curve over an algebraically closed field is committed instead.

`y² = x³ - x` over `AlgebraicClosure ℚ` is the same equation that file uses for its own headline;
characteristic zero discharges both nonvanishing hypotheses, and both fundamental identities are
committed on it, at `n = 2` and at `n = 3`. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² = x³ - x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **The headline, committed**: on a named curve over a named algebraically closed field, the
relative ideal norm and the residue-field degree agree at every place. -/
example (p : ProjPoint exampleCurve) :
    degProjPt exampleCurve p = residueDegreeProj exampleCurve p :=
  degProjPt_eq_residueDegreeProj exampleCurve p

/-- The degree-zero theorem, read as *"as many zeros as poles"* on the same curve. -/
example {f : exampleCurve.FunctionField} (hf : f ≠ 0) :
    (divisorProj exampleCurve f).sum (fun _ n => n) = 0 := by
  rw [← degProj_eq_sum, degProj_divisorProj hf]

/-- The `n = 2` fundamental identity in the `∑ e_p · deg p` spelling, committed and not merely
stated: characteristic zero discharges `(2 : F) ≠ 0`. -/
example (q : ProjPoint exampleCurve) :
    ∑ p ∈ (CoordinateRing.finite_comapProjPointTwo_preimage_singleton
        (W := exampleCurve) two_ne_zero q).toFinset,
      (CoordinateRing.ramificationIdxTwo two_ne_zero p).toNat * degProjPt exampleCurve p = 4 :=
  CoordinateRing.sum_ramificationIdxTwo_mul_degProjPt two_ne_zero q

/-- The `n = 3` mirror, committed on the same curve: characteristic zero discharges `(3 : F) ≠ 0`
as well, so *both* nonvanishing hypotheses of the two fundamental identities are met.

⚠️ This example is also the regression test for the binder order of
`sum_ramificationIdxThree_mul_degProjPt`.  It is applied here as `h2 h3 q`, which is the order
`sum_ramificationIdxThree_eq_nine`, `sum_ramificationIdxThree_mul_residueDegreeThree` and
`finite_comapProjPointThree_preimage_singleton` all use; an `h2 q h3` signature fails to elaborate
against it. -/
example (q : ProjPoint exampleCurve) :
    ∑ p ∈ (CoordinateRing.finite_comapProjPointThree_preimage_singleton
        (W := exampleCurve) two_ne_zero (by norm_num) q).toFinset,
      (CoordinateRing.ramificationIdxThree two_ne_zero (by norm_num) p).toNat
        * degProjPt exampleCurve p = 9 :=
  CoordinateRing.sum_ramificationIdxThree_mul_degProjPt two_ne_zero (by norm_num) q

end Nonvacuity

end WeierstrassCurve.Affine
