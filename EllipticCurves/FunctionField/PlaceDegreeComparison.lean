/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.ProjectiveDivisor
import EllipticCurves.FunctionField.CoordinateRingNormalAlgClosed
import EllipticCurves.FunctionField.MulByThreeResidueDegree
import EllipticCurves.FunctionField.NegYGalois

/-!
# The two degree functions on places agree, over an arbitrary base field

This tree carries **two** notions of the degree of a place, defined by different routes and
compared nowhere until this file:

* `WeierstrassCurve.Affine.degPt v = Ideal.natDegreeGenerator (Ideal.relNorm F[X] v.asIdeal)`
  (`EllipticCurves.FunctionField.DivisorDegree`) — a *relative ideal norm to `F[X]`*, which is what
  the degree-zero theorem `degDiv (div f) + ordInfty f = 0` weights its divisors by;
* `WeierstrassCurve.Affine.CoordinateRing.residueDegreeProj W p`, which is
  `Module.finrank F (residueFieldProj W p)`
  (`EllipticCurves.FunctionField.PlaceResidueField`) — the *residue-field degree over `F`*, which is
  what the fundamental identity `∑_{p ↦ q} e_p · f_p = 4` weights its ramification indices by.

Two merged module docstrings asserted, in the indicative and without proof, that the two agree.
**This file proves it, for every elliptic curve over every field.**

⚠️ **The two routes below are different theorems and only one of them generalises.** Over an
algebraically closed field the comparison is a *corollary of a stronger fact*, `deg p = 1` at every
place; over `ℚ` that fact is false — an affine closed point can have a number field as residue
field — and the comparison is proved instead by computing the relative norm. Both are kept: the
`[IsAlgClosed F]` statements say strictly more where they apply, and merged docstrings across the
`MulByTwo*` and `MulByThree*` front point at them by name.

## Main results

Over an **arbitrary** base field, with no hypothesis on the characteristic:

* `WeierstrassCurve.Affine.degPt_eq_residueDegreeProj` — the affine comparison;
* **`WeierstrassCurve.Affine.degProjPt_eq_residueDegreeProj`** — the headline: the two degree
  functions on `ProjPoint W` are equal.

Over an algebraically closed base field, where more is true:

* `WeierstrassCurve.Affine.degPt_eq_one` — every affine closed point has degree `1`;
* `WeierstrassCurve.Affine.degProjPt_eq_one` — and so does the point at infinity;
* `WeierstrassCurve.Affine.degProj_eq_sum` / `degDiv_eq_sum` — a divisor's degree is the plain sum
  of its coefficients, so the degree-zero theorem reads *"as many zeros as poles"*;
* `WeierstrassCurve.Affine.CoordinateRing.sum_ramificationIdxTwo_mul_degProjPt` and
  `sum_ramificationIdxThree_mul_degProjPt` — the fundamental identity in the `∑ e_p · deg p`
  spelling, at `n = 2` and `n = 3`.

## The general comparison, step by step

Write `P = v.asIdeal`, `p = P ∩ F[X]` (`Ideal.under`) and `f = P.inertiaDeg F[X]`.

| step | by |
| --- | --- |
| `degPt v = deg (relNorm F[X] P)` | the definition, `EllipticCurves.FunctionField.DivisorDegree` |
| `relNorm F[X] P = p ^ f` | `Ideal.relNorm_eq_pow_of_isPrime_isGalois` |
| `deg (p ^ f) = f · deg p` | `Ideal.natDegreeGenerator_pow` |
| `deg p = [F[X]⧸p : F]` | `Ideal.natDegreeGenerator_eq_finrank_quotient` |
| `f = [F[W]⧸P : F[X]⧸p]` | `Ideal.inertiaDeg_eq_of_isMaximal` |
| `[F[X]⧸p : F] · [F[W]⧸P : F[X]⧸p] = [F[W]⧸P : F]` | `Module.finrank_mul_finrank` |
| `[F[W]⧸P : F] = residueDegreeProj W (some v)` | `residueFieldProjSomeEquiv`, merged |

⚠️ **The only step that was missing is the second**, and it is the one `## Scope` below used to
record as unavailable. Its Galois hypothesis `IsGalois (FractionRing F[X]) F(W)` is
`WeierstrassCurve.Affine.CoordinateRing.isGalois_fractionRing_polynomial`
(`EllipticCurves.FunctionField.NegYGalois`, `#1086`), off the hyperelliptic involution and Artin's
theorem on fixed fields. Everything else in the table was already merged or is Mathlib:
`natDegreeGenerator_pow` and `natDegreeGenerator_eq_finrank_quotient` are added by this change to
`EllipticCurves.FunctionField.DivisorDegree`, beside the additivity they are built from, and
`residueFieldProjSomeEquiv` — the first-isomorphism-theorem identification
`κ(some v) ≃ₐ[F] F[W] ⧸ v.asIdeal` — is `EllipticCurves.FunctionField.PlaceResidueDegree`'s.

The side conditions are standard and all discharged inside the proof: `P` is maximal because a
height-one prime of a Dedekind domain is (`HeightOneSpectrum.isMaximal`); `p` is maximal because
`F[W]` is integral over `F[X]` (`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`, off the merged
`Module.Finite F[X] F[W]`); `P.LiesOver p` is `rfl` because `p` is *defined* as `P.under F[X]`; and
`p ≠ 0` because a maximal ideal of a non-field is nonzero.

## The `F̄` route, which is now a different theorem

⚠️ **The comparison above does not go this way.**  The route survives in the file as
`degPt_eq_one`, which computes the common *value* and therefore says strictly more than the
comparison wherever it applies; it is described here because it is what a reader arriving from
`PlaceResidueField` or `PlaceResidueDegree` will be looking for.

Over an algebraically closed base field the residue-degree half has been available since `#749`:
`residueDegreeProj_eq_one` holds for *every* place, with no classification of ideals behind it —
Zariski's lemma makes `algebraMap F (residueFieldProj W p)` surjective and
`residueDegreeProj_eq_one_iff_surjective` converts that to the degree.  So over `F̄` the comparison
reduces to `degPt v = 1`, and both inputs for that are merged too:

* `exists_equation_and_eq_XYIdeal_of_isMaximal`
  (`EllipticCurves.FunctionField.CoordinateRingNormalAlgClosed`, `#396`/`#469`) — over an
  algebraically closed field every maximal ideal of `F[W]` is `XYIdeal W a (C b)` for a point
  `(a, b)` on the curve;
* `degPt_pointClosedPoint` (`EllipticCurves.FunctionField.RationalPointDegree`) — `degPt` is `1` at
  the closed point of a rational point, because `v_{-P} · v_P = ⟨x - x₀⟩` has norm `(X - x₀)²`.

The bridge between them is that a height-one prime of a Dedekind domain is maximal, so the
classification applies to *every* `v` and not only to those already presented as a point; Mathlib's
`equation_iff_nonsingular` upgrades the `W.Equation a b` it returns to the `W.Nonsingular a b` that
`degPt_pointClosedPoint` consumes.  That is the entire content of `degPt_eq_one`.

⚠️ **`degPt_eq_one` is not a corollary of the general comparison and is not superseded by it.**  It
computes the common *value*; the general comparison only says the two functions agree.  Over `ℚ`
the value is not `1` in general — a closed point can have a number field as residue field, which is
classical and is **not proved here** — and that is why `degProj_eq_sum` and the two fundamental
identities below keep `[IsAlgClosed F]`.

## What the `none` branch is worth

`degProjPt W none = 1` is a *definitional choice*
(`EllipticCurves.FunctionField.ProjectiveDivisor`), while `residueDegreeProj_none_eq_one` is a
*theorem*, and one that needs no hypothesis on `F` at
all.  `degProjPt_none_unique` separately shows the choice is forced: no other weight makes the
degree-zero theorem hold.  `degProjPt_eq_residueDegreeProj` is what ties the three together — the
convention, the theorem it had to match, and the uniqueness that says it had no freedom.  ⚠️ This
branch was never the obstruction to the general statement: `[0 : 1 : 0]` is a rational point of
every Weierstrass curve, and `residueDegreeProj_none_eq_one` never carried `[IsAlgClosed F]`.

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

⚠️ **The general comparison does not change this.**  It removes `[IsAlgClosed F]` from the
*comparison*, not from the two identities: those are reweightings of `∑ e_p · f_p`, and the
reweighting is `deg p = 1`, which is genuinely an `F̄` fact.

## Scope — ⚠️ a merged paragraph of this section said the general case was out of reach

⚠️ **This section's heading used to read** *"Scope — ⚠️ the general base field is open, and the
obstruction is a hypothesis, not an effort"*, over an opening sentence *"Everything below carries
`[IsAlgClosed F]`, and that is not a convenience: over a general field
`degPt v = residueDegreeProj W (some v)` is not proved here and does not follow from anything
below."*  **That is retired by
`degPt_eq_residueDegreeProj` above**, which carries no hypothesis on `F` beyond `[Field F]`.

The half of it that survives, and is worth keeping: Mathlib's hypothesis-free route
`Ideal.relNorm_eq_pow_of_isMaximal` is ⚠️ **stated under `[PerfectField (FractionRing R)]`**, and
here `R = F[X]`, whose fraction field is `RatFunc F`, which is **not perfect in characteristic
`p`**: `X` has no `p`-th root in it.  So the perfect-field route really is unavailable, and the
Galois-hypothesis variant really is the one that works.

⚠️ **And a paragraph added by `#1086` — the PR that removed the *previous* wrong sentence from this
same section — was wrong in the other direction.** It read:

> `relNorm_eq_pow_of_isPrime_isGalois` also wants `[IsDedekindDomain F[X]]`,
> `[IsDedekindDomain F[W]]`, `[Module.Finite F[X] F[W]]`, `[IsTorsionFree F[X] F[W]]` and
> `P.LiesOver p` with `[p.IsMaximal]`, and then its output still has to be combined with the tower
> `[κ(v) : F] = f · [κ(p) : F]` and the multiplicativity of `Ideal.natDegreeGenerator`.
> **None of that is done anywhere in this tree.**

**The bolded sentence was false of five of the seven things it ranged over**, measured with one
`example : C := inferInstance` per hypothesis under this file's own `variable` line:

* `[IsDedekindDomain F[X]]` — automatic; `F[X]` is a PID.
* `[IsDedekindDomain F[W]]` — `WeierstrassCurve.Affine.CoordinateRing.instIsDedekindDomain`
  (`EllipticCurves.FunctionField.CoordinateRingNormalGeneral`), a **global** instance for
  `[W.IsElliptic]` over any field.
* `[Module.Finite F[X] F[W]]` — `WeierstrassCurve.Affine.instModuleFiniteCoordinateRing`
  (`EllipticCurves.FunctionField.DivisorDegree`), and registered a second time in
  `EllipticCurves.Torsion.CoordinateRingDedekind`.
* `[IsTorsionFree F[X] F[W]]` — automatic; ⚠️ and the spelling was wrong, the class being
  `Module.IsTorsionFree`.
* `P.LiesOver p` and `[p.IsMaximal]` — not obstructions at all: hypotheses of the *statement*,
  chosen by whoever applies it.
* the multiplicativity of `Ideal.natDegreeGenerator` — merged as `Ideal.natDegreeGenerator_mul`.
* the tower `[κ(v) : F] = f · [κ(p) : F]` — ✅ **the one genuinely absent item**, and it is
  `Module.finrank_mul_finrank`, supplied above.

> ⚠️ **The generalisable point, because this is the second wrong sentence retired from this one
> section and the two failed in opposite directions.**  A hypothesis list copied from a Mathlib
> signature is a list of what the theorem *asks for*, not a list of what is *missing*; every clause
> in it is individually true of Mathlib, so a falsity check, an identifier-existence check and a
> capability sweep are all blind to it.  The detector is one line per hypothesis —
> `example : C := inferInstance` under the file's own `variable` line — and it costs the same ten
> seconds as the declaration-count grep.

## What is deliberately *not* changed

* **No consumer is re-plumbed.**  Both stale docstrings said *"nothing below assumes it"*, and that
  was true and stays true: this file adds a bridge and crosses nothing over it.  Rewriting the
  `f_p`-weighted statements to use `degPt`, or the reverse, is a separate and reviewable decision.
* **Neither degree function is rephrased in terms of the other**, and both defining docstrings now
  name this comparison.  ⚠️ This bullet used to read that `residueDegreeProj`'s docstring *"still
  says it is **not** `degPt`"*, and stop there because that sentence is *"correct as a statement
  about definitions"*.  The ground was right — the two are different constructions, and what is
  proved here is an equality of *values*, not an identification of notions — but it stopped one file
  short: `degPt`'s own docstring (`EllipticCurves.FunctionField.DivisorDegree`) carried the
  **mirror** gloss, *"its residue degree over `F`"*, which is that same equality asserted in the
  positive, seven days before this file proved it.  Read side by side, one denied a *definitional*
  identity and the other asserted the equality outright, and neither named a theorem.  Both now
  point here; the parenthetical
  *"which is a relative ideal norm to `F[X]`"* is still right, and what is no longer right anywhere
  in this tree is any claim that the two are **only** known to agree over `F̄`.
* **No binder is removed anywhere else.**  `[IsAlgClosed F]` stays on `degPt_eq_one`,
  `degProjPt_eq_one`, `degProj_eq_sum`, `degDiv_eq_sum` and the two fundamental identities, where it
  is load-bearing.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], II.2.
* [H. Stichtenoth, *Algebraic function fields and codes*][stichtenoth2009], I.4 (the degree of a
  place) and III.1.11 (the fundamental identity).
-/

open Polynomial Polynomial.Bivariate IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]
  [IsDedekindDomain W.CoordinateRing]

/-! ### The comparison over an arbitrary base field -/

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/-- **The relative ideal norm and the residue-field degree agree at every affine closed point**, of
every elliptic curve, over **every** field — no algebraic closedness, no hypothesis on the
characteristic.

Write `P = v.asIdeal`, `p = P ∩ F[X]` and `f = P.inertiaDeg F[X]`.  The chain is

```
degPt v = deg (relNorm F[X] P) = deg (p ^ f) = f · deg p
        = [F[W]⧸P : F[X]⧸p] · [F[X]⧸p : F] = [F[W]⧸P : F] = residueDegreeProj W (some v)
```

and each step is named in the module docstring's `## The general comparison` section.  The one
that used to be missing is `Ideal.relNorm_eq_pow_of_isPrime_isGalois`, whose Galois hypothesis is
`isGalois_fractionRing_polynomial` (`EllipticCurves.FunctionField.NegYGalois`, `#1086`).

⚠️ `isGalois_fractionRing_polynomial` is a `theorem` and **cannot** be an `instance` — the algebra
structure it is stated against comes from `FractionRing.liftAlgebra`, which Mathlib keeps `local`
because making it global causes timeouts.  That is why the proof fires it with `haveI` and why the
`attribute [local instance] … in` is scoped to this declaration alone rather than to the file. -/
theorem degPt_eq_residueDegreeProj (v : HeightOneSpectrum W.CoordinateRing) :
    degPt v = residueDegreeProj W (some v) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI hpmax : (v.asIdeal.under F[X]).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
  haveI : v.asIdeal.LiesOver (v.asIdeal.under F[X]) := ⟨rfl⟩
  haveI : IsGalois (FractionRing F[X]) W.FunctionField := isGalois_fractionRing_polynomial
  have hp0 : v.asIdeal.under F[X] ≠ 0 :=
    Ring.ne_bot_of_isMaximal_of_not_isField hpmax (Polynomial.not_isField F)
  rw [degPt, Ideal.relNorm_eq_pow_of_isPrime_isGalois v.asIdeal (v.asIdeal.under F[X]),
    Ideal.natDegreeGenerator_pow hp0, Ideal.natDegreeGenerator_eq_finrank_quotient,
    Ideal.inertiaDeg_eq_of_isMaximal (v.asIdeal.under F[X]) v.asIdeal, residueDegreeProj,
    (residueFieldProjSomeEquiv v).toLinearEquiv.finrank_eq, mul_comm]
  letI : Field (F[X] ⧸ v.asIdeal.under F[X]) := Ideal.Quotient.field _
  exact Module.finrank_mul_finrank F (F[X] ⧸ v.asIdeal.under F[X]) (W.CoordinateRing ⧸ v.asIdeal)

variable (W) in
/-- **The two degree functions on places of the projective curve are equal, over an arbitrary base
field.**

This is the statement `EllipticCurves.FunctionField.PlaceResidueField` and
`EllipticCurves.FunctionField.PlaceResidueDegree` both asserted without proof, and the one
`## Scope` below used to record as open beyond `[IsAlgClosed F]`.

The two branches are different theorems and neither needs algebraic closedness: at infinity the
definitional weight `degProjPt W none = 1` meets `residueDegreeProj_none_eq_one` (`[0 : 1 : 0]` is
rational on every Weierstrass curve, so that branch was never the obstruction), and
`degProjPt_none_unique` says the weight was forced anyway.  ⚠️ At an affine place the *values* are
**not** `1` in general — over `ℚ` a closed point can have a number field as residue field — and
that is exactly the content `degPt_eq_one` cannot supply. -/
theorem degProjPt_eq_residueDegreeProj (p : ProjPoint W) :
    degProjPt W p = residueDegreeProj W p := by
  cases p with
  | none => rw [degProjPt_none, residueDegreeProj_none_eq_one]
  | some v => exact degPt_eq_residueDegreeProj v

section IsAlgClosed

variable [IsAlgClosed F]

/-! ### Every place has degree one, over an algebraically closed field -/

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

end IsAlgClosed

/-! ### Non-vacuity

⚠️ **Two hypothesis sets are certified here, not one, and they need different curves.**  The two
comparisons of the `## The general comparison, step by step` section carry `[W.IsElliptic]` and
`[IsDedekindDomain W.CoordinateRing]` and **no hypothesis on `F` beyond `[Field F]`**; everything
inside `section IsAlgClosed` adds `[IsAlgClosed F]`, and the two fundamental identities add
`(2 : F) ≠ 0` and `(3 : F) ≠ 0` on top of that.  So a single curve cannot serve: an algebraically
closed base is *required* by the second set and *invisible* to the first.

⚠️ **This paragraph used to read** *"Every statement above carries `[IsAlgClosed F]`,
`[W.IsElliptic]` and `[IsDedekindDomain W.CoordinateRing]` at once … That instance set is strictly
stronger than the one `EllipticCurves.FunctionField.PlaceResidueDegree` certifies, so its
`ℚ`-rational curve does not serve here and a curve over an algebraically closed field is committed
instead."*  **The first clause stopped being true when `[IsAlgClosed F]` left
`degPt_eq_residueDegreeProj` and `degProjPt_eq_residueDegreeProj`**, and with it the conclusion:
a `ℚ`-rational curve is now exactly what the general comparison needs, and `exampleCurveRat` is one.
The comparison with `EllipticCurves.FunctionField.PlaceResidueDegree` survives for the
`section IsAlgClosed` half, which is what it was written about.

The same equation `y² = x³ - x` is committed twice, once over each kind of base field:

* over `AlgebraicClosure ℚ` (`exampleCurve`) — the equation that
  `EllipticCurves.FunctionField.PlaceResidueDegree` uses for its own headline; characteristic zero
  discharges both nonvanishing hypotheses, and both fundamental identities are committed on it, at
  `n = 2` and at `n = 3`;
* over `ℚ` (`exampleCurveRat`) — ⚠️ **the certificate for the general comparison**, since over `F̄`
  that comparison is the merged `degPt_eq_one` reweighted and says nothing new.
  `not_isAlgClosed_rat` commits *"`ℚ` is not algebraically closed"* as a theorem rather than
  asserting it in prose beside the example.  ⚠️ What is **not** certified there is the common
  *value*: `degPt_eq_one` is false over `ℚ` and nothing here computes what replaces it. -/

section Nonvacuity

/-- An algebraically closed field of characteristic zero. -/
private abbrev exampleField : Type := AlgebraicClosure ℚ

/-- The curve `y² = x³ - x` over `AlgebraicClosure ℚ`, of discriminant `64`. -/
private noncomputable def exampleCurve : Affine exampleField := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **The comparison on a named curve over a named algebraically closed field**: the relative ideal
norm and the residue-field degree agree at every place.

⚠️ This is the weaker of the two certificates and is kept for the `section IsAlgClosed` statements
that follow it, which need this base field.  Over `F̄` the comparison is `degPt_eq_one` reweighted;
the certificate for the general statement is the `exampleCurveRat` one. -/
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

/-! ⚠️ **The certificate that matters for the general comparison**: a base field that is *not*
algebraically closed.  Over `AlgebraicClosure ℚ` the comparison is the merged `deg = 1` statement
reweighted and says nothing new; the content of `degProjPt_eq_residueDegreeProj` is precisely that
it survives when `degPt_eq_one` fails, and `ℚ` is where it fails.  `not_isAlgClosed_rat` commits
the second fact as a theorem rather than asserting it in prose beside the example. -/

/-- The same equation `y² = x³ − x` over `ℚ`, of discriminant `64`. -/
private def exampleCurveRat : Affine ℚ := ⟨0, 0, 0, -1, 0⟩

private instance : exampleCurveRat.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurveRat, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- ⚠️ **`ℚ` is not algebraically closed** — the hypothesis this file used to carry everywhere, and
the reason the `exampleCurveRat` example is not a restatement of the `exampleCurve` one.  If `ℚ`
were algebraically closed, `-1` would have a square root in it. -/
private theorem not_isAlgClosed_rat : ¬ IsAlgClosed ℚ := fun h => by
  obtain ⟨z, hz⟩ := @IsAlgClosed.exists_pow_nat_eq ℚ _ h (-1) 2 two_pos
  nlinarith [sq_nonneg z]

/-- **The general comparison, committed on a curve over a field that is not algebraically closed.**

⚠️ Note what is *not* claimed: the common value is **not** asserted to be `1`.  Over `ℚ` an affine
closed point can have a number field as its residue field, `degPt_eq_one` is false, and this
example is exactly the statement that the two degree functions agree anyway. -/
example (p : ProjPoint exampleCurveRat) :
    degProjPt exampleCurveRat p = residueDegreeProj exampleCurveRat p :=
  degProjPt_eq_residueDegreeProj exampleCurveRat p

end Nonvacuity

end WeierstrassCurve.Affine
