/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Fixtures
import EllipticCurves.FunctionField.MulByNComposition
import EllipticCurves.FunctionField.MulByNPlacePullback
import EllipticCurves.FunctionField.MulByThreeResidueDegree

/-!
# The relative residue degree of `[n]∗`, and `f_∞ = 1` at every `n`

`EllipticCurves.FunctionField.PlaceResidueComap` defines the relative residue degree
`f_p = [κ(p) : κ(q)]` of a contraction `q = comapProjPoint φ p` for an arbitrary `F`-fixing
endomorphism `φ` of `F(W)` over which `F(W)` is integral, and
`EllipticCurves.FunctionField.MulByThreeResidueDegree` instantiates it at `[3]∗`, `[2]∗` having
been done earlier.  This file is the `[n]∗` instantiation, on `mulByNEndo`.

## ⚠️ The residue degree at infinity is *not* in the composition class

`#1214` proved `comapProjPointN … none = none` and `e_∞ = 1` at every `3`-smooth `n` by composing
the merged `n = 2` and `n = 3` computations, and asked whether the residue degree goes the same
way.  **It does not, and it does not have to.**  `residueDegreeN_none_eq_one` below holds at
*every* `n` at which `[n]` is non-constant, with no `3`-smoothness, no `(2 : F) ≠ 0`, no
`(3 : F) ≠ 0`, no `[IsAlgClosed F]` — and it does not consume `#1214` at all.

The reason is `n`-free and this tree already wrote it down, in `MulByThreeResidueDegree`'s own
*"What is not here"*:

> the residue degree at infinity is `1` for a reason that has nothing to do with ramification,
> namely that `[0 : 1 : 0]` is a rational point of every Weierstrass curve.

Formally: `residueDegreeProj_none_eq_one` is unconditional, and the tower formula
`[κ(q) : F] · f_∞ = [κ(∞) : F]` then reads `d · f_∞ = 1` in `ℕ`, which forces both factors to be
`1`.  That argument is uniform in `φ`, so it is made once, for an arbitrary `φ`, in
`EllipticCurves.FunctionField.PlaceRamificationInertia` (`residueDegreeComap_none_eq_one`); every
declaration below is that lemma or one of `PlaceResidueComap`'s three general ones, applied to
`mulByNEndo`.

⚠️ **So the two local invariants of `[n]∗` at infinity have genuinely different hypothesis sets**,
and that is the interesting thing about them: `e_∞ = 1` is `3`-smooth-only and is *false* at general
`n` (`EllipticCurves.FunctionField.MulByNPlacePullback`'s characteristic-`p` argument), while
`f_∞ = 1` is free.  Do not let the two be quoted together as *"`[n]` is unramified and residually
trivial at infinity, at `3`-smooth `n`"*: the second half is true much more widely.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.residueDegreeN` — the relative residue degree
  `f_p = [κ(p) : κ([n]⁻¹ p)]` of `[n]∗` at a place of the projective curve.

## Main statements

⚠️ Every public declaration of this file is listed.

* `…residueDegreeProj_mul_residueDegreeN` — the tower formula `[κ([n]⁻¹ p) : F] · f_p = [κ(p) : F]`;
* `…residueDegreeN_eq_one_of_residueDegreeProj_eq_one` — at a place rational over `F`, `[n]∗` is
  residually trivial;
* **`…residueDegreeN_none_eq_one`** — `f_∞ = 1`, at every `n`, unconditionally, together with its
  companion `…residueDegreeProj_comapProjPointN_none_eq_one` for the place below;
* `…residueDegreeN_eq_one` — over an algebraically closed base field, `f_p = 1` at *every* place and
  every `n`;
* `…residueDegreeN_two` and `…residueDegreeN_three` — the general-`n` layer agrees with the merged
  `residueDegreeTwo` and `residueDegreeThree`.

## What is *not* here

* **Not the fundamental identity at general `n`.**  `#701` and `#1046` are the *fibre sums*
  `∑_{p ↦ q} e_p · f_p = deg`, not the value of `f` at one place.  The general-`n` form of those is
  `#1221`; it is gated on separability of `F(W) / [n]∗F(W)` and its right-hand side is an
  integral-closure rank, not `n²`.  This file supplies one of its inputs and closes none of it.
* **Nothing new about places.**  As `MulByNPlacePullback` says of itself, the content is the merged
  general-`φ` machinery applied to `mulByNEndo`; the only thing proved here that is about `[n]` is
  the pair of consistency lemmas at `n = 2` and `n = 3`.
* **No `f_p = 1` at an affine place over a general field.**  `residueDegreeProj_some_eq_one` needs
  `[IsAlgClosed F]` and genuinely so — an affine closed point of a curve over `ℚ` can have a number
  field as its residue field.  Only the point at infinity is unconditional.
* **No ramification.**  `ramificationIdxN` is untouched; see the second warning above.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, III.1.11.
-/

open IsDedekindDomain

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [IsDedekindDomain W.CoordinateRing] [W.IsElliptic]

/-! ### The definition and the two general consequences -/

/-- **The relative residue degree of `[n]∗`**, `f_p = [κ(p) : κ([n]⁻¹ p)]`.

Together with `ramificationIdxN` this is the pair of local invariants of the extension
`F(W) / [n]∗F(W)` at a place.  ⚠️ As at `n = 2` and `n = 3`, nothing here shows it is nonzero:
`Module.finrank` is `0` on an infinite-dimensional module, and the tower formula below is the tool
for ruling that out. -/
noncomputable def residueDegreeN (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) : ℕ :=
  residueDegreeComap (mulByNEndo_algebraMap_base n hn) (mulByNEndo_isIntegralElem n hn) p

/-- The tower formula for `[n]∗`: `[κ([n]⁻¹ p) : F] · f_p = [κ(p) : F]`.

`Module.finrank_mul_finrank` on `F → κ([n]⁻¹ p) → κ(p)`, with no finiteness hypothesis: both sides
are `0` when `κ(p)` is infinite over `F`. -/
theorem residueDegreeProj_mul_residueDegreeN (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    residueDegreeProj W (comapProjPointN n hn p) * residueDegreeN n hn p = residueDegreeProj W p :=
  residueDegreeProj_mul_residueDegreeComap _ _ p

/-- **At a place rational over `F`, `[n]∗` is residually trivial.**  If `κ(p) = F` then every
intermediate field is `F`, so `f_p = 1`; the `n`-indexed mirror of
`residueDegreeTwo_eq_one_of_residueDegreeProj_eq_one` and its `n = 3` twin. -/
theorem residueDegreeN_eq_one_of_residueDegreeProj_eq_one (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) {p : ProjPoint W}
    (hp : residueDegreeProj W p = 1) : residueDegreeN n hn p = 1 :=
  (residueDegreeComap_eq_one_of_residueDegreeProj_eq_one _ _ hp).2

/-! ### The point at infinity, at every `n` -/

/-- **`[n]∗` is residually trivial at the point at infinity, at every `n`**: `f_∞ = 1`.

⚠️ **Read the hypotheses.**  There is no `3`-smoothness, no `(2 : F) ≠ 0`, no `(3 : F) ≠ 0` and no
`[IsAlgClosed F]`; the only thing `n` is asked for is the non-constancy that `mulByNEndo` needs in
order to exist at all.  This is the `φ = [n]∗` instance of `residueDegreeComap_none_eq_one`
(`EllipticCurves.FunctionField.PlaceRamificationInertia`), and nothing about `[n]` is used.

⚠️ In particular this does **not** go through `comapProjPointN … none = none` — `[n]` fixing the
point at infinity is `#1214`, holds only at `3`-smooth `n`, and is not needed: the tower formula
collapses `d · f_∞ = 1` wherever the contracted place happens to be. -/
theorem residueDegreeN_none_eq_one (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    residueDegreeN n hn (none : ProjPoint W) = 1 :=
  residueDegreeComap_none_eq_one _ _

/-- **The place of `[n]∗F(W)` below the point at infinity is rational**, the other half of the same
collapse: `[κ([n]⁻¹ ∞) : F] = 1`, at every `n`.

⚠️ This says nothing about *which* place that is.  At `3`-smooth `n` it is the point at infinity
(`#1214`); at a general `n` the tree does not know, and does not need to know, because a degree-one
extension of `F` sits under nothing but `F` wherever it is. -/
theorem residueDegreeProj_comapProjPointN_none_eq_one (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) :
    residueDegreeProj W (comapProjPointN n hn (none : ProjPoint W)) = 1 :=
  residueDegreeProj_comapProjPoint_none_eq_one _ _

/-- **Over an algebraically closed base field `[n]∗` is residually trivial at every place**, at
every `n`.  `residueDegreeProj_eq_one` supplies the hypothesis of
`residueDegreeN_eq_one_of_residueDegreeProj_eq_one` everywhere; this is what would collapse a
weighted fibre sum `∑_{p ↦ q} e_p · f_p` to `∑_{p ↦ q} e_p`.  ⚠️ No such sum is stated here — see
*"What is not here"* in the module docstring. -/
theorem residueDegreeN_eq_one [IsAlgClosed F] (n : ℕ)
    (hn : Transcendental F (n • genericPoint (W := W)).xCoord) (p : ProjPoint W) :
    residueDegreeN n hn p = 1 :=
  residueDegreeN_eq_one_of_residueDegreeProj_eq_one n hn (residueDegreeProj_eq_one p)

/-! ### Consistency with the merged `n = 2` and `n = 3` layers

⚠️ These are not restatements, for the reason `MulByNPlacePullback` gives about
`comapProjPointN_two`: `mulByNEndo 2 h` and `mulByTwoEndo h2` are equal by `mulByNEndo_two` but not
definitionally, and `residueDegreeComap` is a `Module.finrank` whose `Algebra` instance is built
from the endomorphism itself.  The crossing is `residueDegreeComap_congr`
(`EllipticCurves.FunctionField.PlaceResidueComap`), which is where the `subst` happens. -/

/-- **The `[n]∗` residue degree at `n = 2` is the merged `[2]∗` residue degree.** -/
theorem residueDegreeN_two (h2 : (2 : F) ≠ 0) (p : ProjPoint W) :
    residueDegreeN 2 (transcendental_xCoord_two_nsmul (W := W) h2) p = residueDegreeTwo h2 p :=
  residueDegreeComap_congr _ _ _ _ (mulByNEndo_two h2) p

/-- **The `[n]∗` residue degree at `n = 3` is the merged `[3]∗` residue degree.** -/
theorem residueDegreeN_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (p : ProjPoint W) :
    residueDegreeN 3 (transcendental_xCoord_three_nsmul (W := W) h2 h3) p
      = residueDegreeThree h2 h3 p :=
  residueDegreeComap_congr _ _ _ _ (mulByNEndo_three h2 h3) p

/-! ### Non-vacuity: the statements have content on real curves

Everything above carries `[IsDedekindDomain W.CoordinateRing]` and `[W.IsElliptic]`, and
`residueDegreeN` is a `Module.finrank` of residue fields of a place extracted by choice, so the
chain is committed on curves rather than quoted.  Two are used, for two reasons.

`y² = x³ - x` over `ℚ` is the certificate curve of `MulByNPlaceComposition`, `PlaceResidueDegree`
and `MulByTwoPlaceAtInfinity`; it witnesses the unconditional statements at `n = 12`, and the
rational base field is the point — `f_∞ = 1` is about as far from needing algebraic closedness as a
statement in this file gets.  The same curve over `AlgebraicClosure ℚ` — the pairing
`PlaceResidueDegree`'s own non-vacuity section uses — witnesses `residueDegreeN_eq_one`, which is
the one statement above that carries `[IsAlgClosed F]`.

⚠️ The non-constancy hypothesis is **produced** by `transcendental_xCoord_nsmul_of_smooth` rather
than assumed, on both curves: a statement whose hypothesis could not be met would be vacuous. -/

section Nonvacuity

/-! The certificate curve `y² = x³ − x` is the shared `EllipticCurves.Fixture.y2EqX3SubX`, and the
base — algebraically closed, and of characteristic `0` so that `2 ≠ 0` and `3 ≠ 0` — is
`EllipticCurves.Fixture.AlgClosedQ`, whose single `[CharZero F]` instance also supplies
`IsElliptic` here. -/

open EllipticCurves.Fixture

/-- ⚠️ `decide` does **not** close this: `Nat.primeFactors` goes through `Nat.primeFactorsList`,
whose `Decidable` instance gets stuck on `Nat.minFac`'s well-founded recursion. -/
private lemma exampleSmoothTwelveRes : ∀ p ∈ Nat.primeFactors 12, p = 2 ∨ p = 3 := by
  intro p hp
  obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hp2
  interval_cases p <;> revert hp1 hp2 <;> decide

example : IsDedekindDomain (y2EqX3SubX ℚ).CoordinateRing := inferInstance

/-- **The headline, committed over `ℚ`.**  `f_∞ = 1` for `[12]` on a genuine curve over a field
that is not algebraically closed. -/
example : residueDegreeN (W := y2EqX3SubX ℚ) 12
      (transcendental_xCoord_nsmul_of_smooth (by norm_num) (by norm_num) (by norm_num)
        exampleSmoothTwelveRes) (none : ProjPoint (y2EqX3SubX ℚ)) = 1 :=
  residueDegreeN_none_eq_one _ _

/-- The companion at the place below, on the same curve. -/
example : residueDegreeProj (y2EqX3SubX ℚ) (comapProjPointN (W := y2EqX3SubX ℚ) 12
      (transcendental_xCoord_nsmul_of_smooth (by norm_num) (by norm_num) (by norm_num)
        exampleSmoothTwelveRes) (none : ProjPoint (y2EqX3SubX ℚ))) = 1 :=
  residueDegreeProj_comapProjPointN_none_eq_one _ _

/-- The tower formula, on a curve, at an index outside `{2, 3}`. -/
example (p : ProjPoint (y2EqX3SubX ℚ)) :
    residueDegreeProj (y2EqX3SubX ℚ) (comapProjPointN (W := y2EqX3SubX ℚ) 12
        (transcendental_xCoord_nsmul_of_smooth (by norm_num) (by norm_num) (by norm_num)
          exampleSmoothTwelveRes) p)
        * residueDegreeN (W := y2EqX3SubX ℚ) 12
          (transcendental_xCoord_nsmul_of_smooth (by norm_num) (by norm_num) (by norm_num)
            exampleSmoothTwelveRes) p
      = residueDegreeProj (y2EqX3SubX ℚ) p :=
  residueDegreeProj_mul_residueDegreeN _ _ p

/-- The `n = 2` consistency lemma, on a curve. -/
example (p : ProjPoint (y2EqX3SubX ℚ)) :
    residueDegreeN (W := y2EqX3SubX ℚ) 2 (transcendental_xCoord_two_nsmul (by norm_num)) p
      = residueDegreeTwo (by norm_num) p :=
  residueDegreeN_two _ p

/-- **The `[IsAlgClosed F]` statement, committed**: over `AlgebraicClosure ℚ`, `[12]∗` is residually
trivial at *every* place of the curve, the point at infinity and the affine closed points alike. -/
example (p : ProjPoint (y2EqX3SubX AlgClosedQ)) : residueDegreeN (W := y2EqX3SubX AlgClosedQ) 12
    (transcendental_xCoord_nsmul_of_smooth (by norm_num) (by norm_num) (by norm_num)
      exampleSmoothTwelveRes) p = 1 :=
  residueDegreeN_eq_one _ _ p

/-- There is at least one affine closed point on that curve to say it about. -/
example : Nonempty (HeightOneSpectrum (y2EqX3SubX AlgClosedQ).CoordinateRing) :=
  nonempty_heightOneSpectrum

end Nonvacuity

end CoordinateRing

end WeierstrassCurve.Affine
