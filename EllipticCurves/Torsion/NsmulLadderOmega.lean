/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.DoublingOmega

/-!
# The ladder's predicted `y`-coordinate with no `(2 : F) ≠ 0`, and both base cases

`EllipticCurves.Torsion.NsmulLadder` runs the `n • P` induction on a pair of predicted
coordinates, `divX x n = Φₙ(x)/ΨSqₙ(x)` and

```
divY x y n = (Tₙ - a₁·divX x n - a₃) / 2,      Tₙ = divT x y n = ψ₂ₙ(x, y)/ψₙ(x, y)⁴,
```

and every rung of it binds `(2 : F) ≠ 0`.  ⚠️ **That hypothesis is not a group-law fact: it is the
`/ 2` in `divY`'s own definition.**  `divT` has no `2` in it at all; the `2` appears when `divT` is
converted from *"the value of `ψ₂ = 2Y + a₁X + a₃`"* to *"the value of `Y`"*, and that conversion
is the division.  This file is the `2`-free companion of that datum:

```
divYω x y n = ωNumₙ(x, y) / ψₙ(x, y)³
```

together with the predicate `NsmulEqDivω` stated in it, and **both** of the ladder's base cases
proved in it with **no `(2 : F) ≠ 0`**.

## ⚠️ Why the halved datum cannot simply be reinterpreted, and why `divT` is not the fix

The obvious repair is *"carry `(divX, divT)`, which has no `2`, and convert to `y` only at the
end"*.  ⚠️ **It cannot work, and the reason is sharp enough to state as a theorem about this
file's own vocabulary.**  `NsmulLadder` needs a datum that distinguishes `n • P` from `−n • P`;
`divT` is built from `ψ`, and in characteristic `2`

* `ψ₂ = 2Y + a₁X + a₃ ≡ a₁X + a₃` while `negY x y ≡ y + a₁x + a₃`, so `ψ₂(x, negY x y) = ψ₂(x, y)`
  — **the two points above `x` give the same value**;
* and `OmegaIntegral`'s `ψ_eq_C` says `ψₙ` has no `Y` at all there, **at every index**, so
  `divT n = ψ₂ₙ/ψₙ⁴` is a function of `x` alone.

So `divT` carries exactly zero sign information where `2 = 0`, and the datum that does carry it is
the `y`-coordinate itself.  ⚠️ **`divY` is not merely unavailable there — it is identically `0`,
at every index and at every point, which `divY_eq_zero_of_two_eq_zero` records in one line.**
`divYω` is the `2`-free name for the same coordinate, and `ωNumₙ` is an honest polynomial over
every commutative ring (`OmegaIntegral`'s `two_mul_ωNum`), so the quotient is honest in
characteristic `2` as well.

## ⚠️ Nothing landed is re-proved, and nothing landed is edited

Everything here is **additive**.  `divY_eq_divYω` identifies the two data wherever the halved one
means anything, so the `ω`-flavoured predicate is the halved one restated rather than a rival to
it, and `nsmulEqDiv_iff_nsmulEqDivω` says so at the point level.  ⚠️ **`divY`, `divT`,
`NsmulEqDiv` and every rung of `NsmulLadder` are untouched** — re-normalising `divY` would re-prove
its every consumer, which is the cost `#2248` priced at `152` tree-wide mentions for the analogous
move on `omegaY`.

⚠️ **The word *restatement* does two jobs in this file, and mixing them is how the round-1 text got
the predicate relation wrong.**  *Under* `(2 : F) ≠ 0` and the two non-vanishing hypotheses,
`divY_eq_divYω` and `nsmulEqDiv_iff_nsmulEqDivω` make the `ω`-flavoured ladder a **restatement** of
the landed one — that is the sense of the paragraph above and of
`nsmulEqDiv_iff_nsmulEqDivω`'s own docstring.  *Without* them the two predicates are not
interchangeable in either direction — `NsmulEqDivω` holds at a characteristic-`2` point where
`NsmulEqDiv` is false, and `NsmulEqDiv.divY_eq_divYω` says at most one of them can hold wherever
the two data differ — which is the sense in which `NsmulEqDivω`'s docstring and the `Nonvacuity`
bullet below say it is **not** a restatement.  Every *"is"* is scoped to those hypotheses and every
*"is not"* to their absence; neither is a claim about the other's scope.

## Main results

* `WeierstrassCurve.Affine.divY_eq_zero_of_two_eq_zero` — ⚠️ **`divY x y n = 0` for every index
  and every point whenever `(2 : F) = 0`**, so the halved datum is not a weak prediction in
  characteristic `2` but no prediction at all.  No point hypothesis and no index restriction;
* `WeierstrassCurve.Affine.divYω` — the predicted `y`-coordinate as `ωNumₙ(x, y)/ψₙ(x, y)³`;
* `WeierstrassCurve.Affine.divYω_one` — ⚠️ **`divYω x y 1 = y`, with no `(2 : F) ≠ 0`**.  This is
  the `h2`-free counterpart of `divY_one`, whose `h2` exists only to undo the halving;
* `WeierstrassCurve.Affine.divY_eq_divYω` — the bridge, `divY x y n = divYω x y n`, under the
  hypotheses `divY_eq_omegaY` already asks for.  ⚠️ **It is `divY_eq_omegaY` composed with
  `OmegaIntegral`'s `omegaY_eq` and it proves nothing new** — it is here so that nothing stated
  with `divY` has to be re-proved;
* `WeierstrassCurve.Affine.divYω_two_eq_addY_self` — `divYω x y 2` is the group-law double's
  `y`-coordinate.  ⚠️ This is `DoublingOmega`'s `addY_self_eq_div_ωNum` read in this file's
  vocabulary and is not a second proof of it;
* `WeierstrassCurve.Affine.NsmulEqDivω` — the ladder predicate with `divYω` in place of `divY`;
* **`WeierstrassCurve.Affine.nsmulEqDivω_one`** and **`WeierstrassCurve.Affine.nsmulEqDivω_two`** —
  ⚠️ **both base cases of the ladder, over an arbitrary field, with no `(2 : F) ≠ 0`.**  The `n = 2`
  rung is where the doubling formula enters and the only place it does;
* `WeierstrassCurve.Affine.nsmulEqDiv_iff_nsmulEqDivω` — the two predicates agree wherever the
  halved one is meaningful;
* `WeierstrassCurve.Affine.NsmulEqDiv.divY_eq_divYω` — ⚠️ **and where it is not, at most one of
  them can hold**: both predicates name the single point `n • P`, so both holding forces
  `divY x y n = divYω x y n`.  No hypothesis on `2`, on the curve or on `ψ`.  This is the
  mechanism, and it is why the two predicates are **not ordered** in either direction at a point
  where the two data differ.

The `Nonvacuity` section is one curve and one point, reusing `DoublingOmega`'s witness rather than
building another: `curveCharTwoOne`, the curve `y² + xy = x³ + 1` over `ZMod 2`, at `(1, 0)`.
⚠️ **Every declaration in it takes no hypotheses at all.**

* `divY_two_curveCharTwoOne`, `divYω_two_curveCharTwoOne` — the halved datum is `0` there and the
  `ω`-quotient is `1`;
* `divYω_two_ne_divY_two_curveCharTwoOne` — so the two data **differ** at this point, which is what
  makes `divY_eq_divYω`'s hypotheses necessary rather than decorative;
* ⚠️⚠️ **`nsmulEqDivω_two_curveCharTwoOne` and `not_nsmulEqDiv_two_curveCharTwoOne` — the pair that
  decides whether this file is worth anything.  `NsmulEqDivω` HOLDS at `(1, 0)` on
  `curveCharTwoOne` and `NsmulEqDiv` is FALSE there.**  The true value `y(2 • (1, 0))` is `1`
  (`DoublingOmega`'s `addY_self_curveCharTwoOne`) while `divY 1 0 2` is `0`, so the halved
  predicate's conclusion is refuted at this point and not merely unproved;
* ⚠️⚠️ **`not_forall_nsmulEqDivω_imp_nsmulEqDiv_curveCharTwoOne` — and what that pair refutes is
  the ordering it looks like it supports.**  *"A is stronger than B"* asserts `A → B`, and the pair
  is a **counterexample** to `NsmulEqDivω → NsmulEqDiv`: the `ω` predicate holds at `n = 2` there
  and the halved one is false, so the two predicates are **not ordered** and *stronger* is the one
  word this datum rules out.  ⚠️ **The relation that IS an ordering is between the THEOREMS**:
  `nsmulEqDivω_two` has strictly fewer hypotheses than `NsmulLadder`'s `nsmulEqDiv_two` — `h2`
  alone — and under `h2` it gives that theorem's conclusion back through
  `nsmulEqDiv_iff_nsmulEqDivω`;
* `nsmulEqDiv_one_curveCharTwoOne` — ⚠️ **`NsmulEqDiv` itself HOLDS at `n = 1` on this same curve
  and point**, `divY 1 0 1` and `y` both being `0`.  So the halved predicate is not globally
  unavailable in characteristic `2`: *"every rung of the halved ladder is unavailable"* is a claim
  about the THEOREMS, each of which binds `(2 : F) ≠ 0`, and must never be read of the predicate.

## What is *not* here

* **The ladder step.**  `nsmul_step`, `nsmulEqDiv_step` and `nsmulEqDiv_pair` are not re-run on
  `NsmulEqDivω`.  ⚠️ **That is `#2250`'s route step 3 and it is the expensive rung** — the step
  consumes two consecutive rungs, so a single-rung induction does not carry, and
  `nsmulEqDiv_pair`'s own docstring says so.  This file is route steps 1 and 2 and deliberately
  only those.
* **`HasXCoordFormula` at a general index**, which is `#2250`'s target.  Nothing here approaches
  it, and the four `h2` consumers inside `hasXCoordFormula_of_two_ne_zero` are untouched.  ⚠️ Three
  of those four are `NsmulOrder` lemmas about `ψ`-vanishing and divisibility rather than about
  coordinates, and whether each one's `h2` is a halving is **not** settled here.
* **Any `(2 : F) ≠ 0` sweep.**  No consumer of `divY`, `NsmulEqDiv` or
  `hasXCoordFormula_of_two_ne_zero` is edited.
* **An ordering of the two predicates, in either direction.**
  `not_forall_nsmulEqDivω_imp_nsmulEqDiv_curveCharTwoOne` refutes `NsmulEqDivω → NsmulEqDiv`, and
  `NsmulEqDiv.divY_eq_divYω` says why no implication can survive at a point where the two data
  differ.  ⚠️ **The reverse implication is neither proved nor refuted here**: at `n = 1` on the
  witness curve **both** predicates hold (`nsmulEqDiv_one_curveCharTwoOne`, `nsmulEqDivω_one`), so
  that index is not a counterexample to it and no other index is examined.
* **Any claim about `curveCharTwoOne` beyond the statements listed above**, and no second witness
  curve.  ⚠️ It is reused from `DoublingOmega`, where it was introduced for the `n = 2` halving's
  falsification; nothing about its reduction type, `j`-invariant or group order is asserted or
  used.
* **Anything about `omegaY` at a general index.**  `OmegaIntegral`'s `nsmul_eq_some_ωNum` and
  `nsmul_eq_some_ωNum_of_ΨSq_ne_zero` are the general-index `y`-coordinate statements and both
  still bind `(2 : F) ≠ 0`, for the `x`-half's reason rather than the halving's.  Neither is
  restated.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.3 and Exercise 3.7.
-/

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-! ### The halved datum in characteristic `2` -/

/-- ⚠️ **In characteristic `2` the ladder's predicted `y`-coordinate is identically `0`** — at every
index, at every point, on every curve.  `divY` divides by `2` and Lean's division convention sends
`_ / 0` to `0`.

⚠️ **This is the precise sense in which `divY`'s `(2 : F) ≠ 0` is not removable**: it is not that
the halved datum is a weaker prediction where `2 = 0`, it is that it carries no information at all.
`divYω` below is what replaces it, and `not_nsmulEqDiv_two_curveCharTwoOne` turns this into a
refutation at a named point. -/
theorem divY_eq_zero_of_two_eq_zero (h2 : (2 : F) = 0) (n : ℤ) : W.divY x y n = 0 := by
  rw [divY, h2, div_zero]

/-! ### `divYω`, the `2`-free predicted `y`-coordinate -/

variable (W) in
/-- **The predicted `y`-coordinate at `n`, with no `2` in it**: `ωNumₙ(x, y)/ψₙ(x, y)³`.

⚠️ Read this as *"the division-polynomial `y`-coordinate at `n`"*, not as `y(n • P)`; that reading
is the ladder's content and holds only under the ladder hypothesis.  ⚠️ **It is honest over every
field**, `ωNumₙ` being a polynomial over every commutative ring, which is exactly what
`WeierstrassCurve.Affine.divY` is not. -/
noncomputable def divYω (x y : F) (n : ℤ) : F :=
  (W.ωNum n).evalEval x y / (W.ψ n).evalEval x y ^ 3

/-- ⚠️ **`divYω x y 1 = y`, with no `(2 : F) ≠ 0`** — the `h2`-free counterpart of `divY_one`.

`ω₁ = Y` (`OmegaIntegral`'s `ωNum_one`, the one index at which `ωNum` is pinned to a named
polynomial over every commutative ring) and `ψ₁ = 1`, so the quotient is `y/1³`.  ⚠️ **`divY_one`
needs `h2` for one reason only — to undo the halving in `divY` — and nothing else about it is
characteristic-dependent**, which is why this version has no hypothesis on `(x, y)` either. -/
@[simp]
theorem divYω_one : W.divYω x y 1 = y := by
  rw [divYω, ωNum_one, ψ_one_evalEval]
  simp

/-- **The bridge: the two predicted `y`-coordinates agree.**  ⚠️ **No new content, and that is the
point of stating it** — it is `NsmulYCoord`'s `divY_eq_omegaY` composed with `OmegaIntegral`'s
`omegaY_eq`, so nothing already proved with `divY` has to be re-proved with `divYω`; it is
re-stated.

⚠️ **The hypotheses are `divY_eq_omegaY`'s and they are necessary, not decorative.**  `h2` pays for
the left-hand side, `divY` being the halved datum; `hψ₂` is where `ψ_two_mul_evalEval` cancels a
factor of `ψ₂` at the point.  `divYω_two_ne_divY_two_curveCharTwoOne` exhibits a point at which the
conclusion fails. -/
theorem divY_eq_divYω (h : W.Equation x y) (h2 : (2 : F) ≠ 0)
    (hψ₂ : (W.ψ 2).evalEval x y ≠ 0) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.divY x y n = W.divYω x y n := by
  rw [divY_eq_omegaY h h2 hψ₂ hψ, omegaY_eq h2, divYω]

/-! ### The ladder predicate, and both base cases with no `(2 : F) ≠ 0` -/

variable [DecidableEq F]

/-- **`divYω x y 2` is the group-law double's `y`-coordinate.**  ⚠️ **This is
`EllipticCurves.Torsion.DoublingOmega`'s `addY_self_eq_div_ωNum` in this file's vocabulary and is
not a second proof of it** — that theorem is the whole mathematical content of the `n = 2` rung
below, and the only thing added here is the name `divYω`. -/
theorem divYω_two_eq_addY_self (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.divYω x y 2 = W.addY x x y (W.slope x x y y) :=
  (addY_self_eq_div_ωNum h hy).symm

/-- **`n • (x, y)` is the affine point `(divX, divYω)`.**  The `ω`-flavoured companion of
`NsmulEqDiv`, packaged as a predicate for the same reason: so that the two-step induction can carry
it without the cast bookkeeping leaking into a dependent `∃`.

⚠️ **Without `(2 : F) ≠ 0` it is not a restatement of `NsmulEqDiv`** — the module docstring's
second sense of that word.  The two agree wherever the halved datum is meaningful
(`nsmulEqDiv_iff_nsmulEqDivω`), and this one **holds** at a characteristic-`2` point where that one
is **false** — see `nsmulEqDivω_two_curveCharTwoOne` against
`not_nsmulEqDiv_two_curveCharTwoOne`.

⚠️ **That pair does NOT make this predicate *stronger* than `NsmulEqDiv`; it refutes exactly that
reading** (`not_forall_nsmulEqDivω_imp_nsmulEqDiv_curveCharTwoOne`).  The two predicates pin the
same `x` and differ only in the `y` they name, so wherever the two data differ at most one of them
can hold (`NsmulEqDiv.divY_eq_divYω`) and neither implication survives there. -/
def NsmulEqDivω {x y : F} (hns : W.Nonsingular x y) (n : ℤ) : Prop :=
  ∃ h' : W.Nonsingular (W.divX x n) (W.divYω x y n),
    (n • Point.some x y hns : W.Point) = .some _ _ h'

/-- ⚠️ **The base case `n = 1`, with no `(2 : F) ≠ 0`.**  `1 • P = P`, and `divX_one` and
`divYω_one` make the predictions agree with it.  ⚠️ The corresponding `nsmulEqDiv_one` binds `h2`,
and `divYω_one` is the only difference. -/
theorem nsmulEqDivω_one (hns : W.Nonsingular x y) : NsmulEqDivω hns 1 := by
  have hX := divX_one (W := W) (x := x)
  have hY := divYω_one (W := W) (x := x) (y := y)
  have hns' : W.Nonsingular (W.divX x 1) (W.divYω x y 1) := by rw [hX, hY]; exact hns
  exact ⟨hns', by rw [one_zsmul, Point.some.injEq]; exact ⟨hX.symm, hY.symm⟩⟩

/-- ⚠️ **The base case `n = 2`, with no `(2 : F) ≠ 0`** — where the doubling formula enters, and the
only place it does.  The step cannot reach `n = 2` from `n = 1`: it would need the rung `0 • P = O`,
which is not affine.

⚠️ **The whole difference from `nsmul_two_eq_div` is which doubling theorem is cited.**  That proof
rewrites with `addY_self_eq_div`, whose right-hand side divides by `2ψ₂³`, and then has to match a
`preΨ₄` numerator against `T₂ = ψ₄/ψ₂⁴` through `ψ_four` and `ΨSq₂ = ψ₂²`.  Here
`divYω_two_eq_addY_self` **is** the `y`-coordinate on the nose, so the `y`-half is one rewrite and
there is no numerator to match — ⚠️ **`ψ_four_evalEval` is not used at all.**  The `x`-half is
unchanged and shares `addX_self_eq_div` with the halved rung; `ht` is what makes `y ≠ negY x y`, and
in characteristic `2` that is a condition on `a₁x + a₃` alone. -/
theorem nsmulEqDivω_two (hns : W.Nonsingular x y) (ht : (W.ψ 2).evalEval x y ≠ 0) :
    NsmulEqDivω hns 2 := by
  have hEq : W.Equation x y := hns.left
  have hyne : y ≠ W.negY x y := by
    intro hc
    exact ht (by rw [ψ_two_evalEval]; rw [negY] at hc; linear_combination hc)
  have hX : W.addX x x (W.slope x x y y) = W.divX x 2 := by
    rw [addX_self_eq_div hEq hyne, divX, ΨSq_two]
  have hY : W.addY x x y (W.slope x x y y) = W.divYω x y 2 :=
    (divYω_two_eq_addY_self hEq hyne).symm
  have hns' : W.Nonsingular (W.divX x 2) (W.divYω x y 2) := by
    rw [← hX, ← hY]; exact nonsingular_add hns hns fun hc => hyne hc.2
  refine ⟨hns', ?_⟩
  rw [two_zsmul, Point.add_self_of_Y_ne hyne, Point.some.injEq]
  exact ⟨hX, hY⟩

/-- **The two ladder predicates agree wherever the halved datum is meaningful.**  ⚠️ **This is what
makes the `ω`-flavoured ladder a restatement of the landed one rather than a fork of it — under
these hypotheses and only under them**: with `divY_eq_divYω`'s hypotheses in hand, anything proved
about `NsmulEqDivω` transfers to `NsmulEqDiv` and back, so no rung of
`EllipticCurves.Torsion.NsmulLadder` is orphaned.  ⚠️ Drop `h2` and the transfer goes with it —
`NsmulEqDiv.divY_eq_divYω` is what remains, and it points the other way.

⚠️ **It is an `Iff` and not a one-way implication only because `divY_eq_divYω` is an equation**; the
hypotheses are needed in both directions and `not_nsmulEqDiv_two_curveCharTwoOne` shows that
dropping `h2` breaks the left-hand side, not the right. -/
theorem nsmulEqDiv_iff_nsmulEqDivω (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (hψ₂ : (W.ψ 2).evalEval x y ≠ 0) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    NsmulEqDiv hns n ↔ NsmulEqDivω hns n := by
  rw [NsmulEqDiv, NsmulEqDivω, divY_eq_divYω hns.left h2 hψ₂ hψ]

/-- **Both predicates name the single point `n • P`, so both holding forces the two predicted
`y`-coordinates to agree.**  ⚠️ **This is the mechanism behind *the two predicates are not
ordered***: they pin the same `x`-coordinate `divX x n` and differ only in the `y`, and `n • P` has
one `y`, so at any point and index where `divY x y n ≠ divYω x y n` **at most one of them can
hold** and neither implication survives there.  `divYω_two_ne_divY_two_curveCharTwoOne` exhibits
such a point, and `not_forall_nsmulEqDivω_imp_nsmulEqDiv_curveCharTwoOne` turns it into a
refutation.

⚠️ **No hypothesis on `2`, on the curve or on `ψ`** — it is the injectivity of `Point.some` and
nothing else.  Contrast `nsmulEqDiv_iff_nsmulEqDivω`, which needs all three to make the two data
agree in the first place: that theorem says *when* the predicates coincide, this one says what
their coinciding costs. -/
theorem NsmulEqDiv.divY_eq_divYω {hns : W.Nonsingular x y} {n : ℤ} (h : NsmulEqDiv hns n)
    (hω : NsmulEqDivω hns n) : W.divY x y n = W.divYω x y n := by
  obtain ⟨h', hp⟩ := h
  obtain ⟨hω', hpω⟩ := hω
  exact ((Point.some.injEq ..).mp (hp.symm.trans hpω)).2

section Nonvacuity

/-! ### ⚠️ Non-vacuity: `NsmulEqDivω` holds at a point where `NsmulEqDiv` is FALSE

One curve and one point, both reused from `EllipticCurves.Torsion.DoublingOmega` rather than built
again: `curveCharTwoOne`, the curve `y² + xy = x³ + 1` over `ZMod 2`, at its point `(1, 0)`.  The
curve exists there because a characteristic-`2` witness needs a point not fixed by negation, which
in characteristic `2` asks for `a₁x + a₃ ≠ 0`. -/

/-- `divY 1 0 2 = 0` on `curveCharTwoOne`, by `divY_eq_zero_of_two_eq_zero` at `2 = 0` in
`ZMod 2`.  ⚠️ The value is `0` for the *definitional* reason and not because the point is special —
every index gives `0` here. -/
theorem divY_two_curveCharTwoOne : curveCharTwoOne.divY 1 0 2 = 0 :=
  divY_eq_zero_of_two_eq_zero (by decide) 2

/-- ⚠️ **`divYω 1 0 2 = 1` on `curveCharTwoOne`**, from `ω₂(1, 0) = 1` and `ψ₂(1, 0) = 1`.  ⚠️ **The
value being nonzero is the whole point**: it is what makes the comparison below a falsification
rather than a coincidence of two zeros. -/
theorem divYω_two_curveCharTwoOne : curveCharTwoOne.divYω 1 0 2 = 1 := by
  rw [divYω, evalEval_ωNum_two_curveCharTwoOne, evalEval_ψ_two_curveCharTwoOne, one_pow, div_one]

/-- ⚠️ **The two predicted `y`-coordinates DIFFER at `(1, 0)` on `curveCharTwoOne`** — `1` against
`0`.  So `divY_eq_divYω`'s hypotheses are necessary and not decorative, and `h2` is the one that
fails here. -/
theorem divYω_two_ne_divY_two_curveCharTwoOne :
    curveCharTwoOne.divYω 1 0 2 ≠ curveCharTwoOne.divY 1 0 2 := by
  rw [divYω_two_curveCharTwoOne, divY_two_curveCharTwoOne]
  decide

/-- ⚠️ **`NsmulEqDivω` HOLDS at `(1, 0)` on `curveCharTwoOne`** — a characteristic-`2` curve, where
every rung of the halved ladder's THEOREMS is unavailable, each of them binding `(2 : F) ≠ 0`.
Immediate from `nsmulEqDivω_two`, `ψ₂(1, 0)` being `1`.

⚠️ **Read *unavailable* of those theorems and never of the predicate `NsmulEqDiv`**, which is a
statement about a point and can perfectly well be true here: `nsmulEqDiv_one_curveCharTwoOne` is
this very curve and point at `n = 1`. -/
theorem nsmulEqDivω_two_curveCharTwoOne : NsmulEqDivω nonsingular_curveCharTwoOne 2 :=
  nsmulEqDivω_two nonsingular_curveCharTwoOne
    (by rw [evalEval_ψ_two_curveCharTwoOne]; decide)

/-- ⚠️⚠️ **AND `NsmulEqDiv` IS FALSE THERE.**  `y(2 • (1, 0)) = 1` by
`DoublingOmega`'s `addY_self_curveCharTwoOne`, while `divY 1 0 2 = 0`, so the halved predicate
asserts an equality of points whose `y`-coordinates are `1` and `0`.

⚠️ **This is stronger than the `h2`-free statements on their own: it is not that `NsmulEqDiv`'s
`(2 : F) ≠ 0` is an artefact one could drop, it is that dropping it makes the predicate FALSE at a
named point of a named curve.**  ⚠️ **What it does NOT say is that `NsmulEqDivω` is *stronger* than
`NsmulEqDiv`** — together with `nsmulEqDivω_two_curveCharTwoOne` it REFUTES that reading, since
*"A is stronger than B"* asserts `A → B`; see
`not_forall_nsmulEqDivω_imp_nsmulEqDiv_curveCharTwoOne`.

⚠️ **`NsmulEqDiv` is never instantiated here** — the proof reads the group-law double directly
through `Point.add_self_of_Y_ne` and contradicts the predicate's own `∃`, rather than applying a
theorem to a curve its hypotheses exclude. -/
theorem not_nsmulEqDiv_two_curveCharTwoOne :
    ¬ NsmulEqDiv nonsingular_curveCharTwoOne 2 := by
  rintro ⟨h', hpt⟩
  rw [two_zsmul, Point.add_self_of_Y_ne y_ne_negY_curveCharTwoOne, Point.some.injEq] at hpt
  rw [addY_self_curveCharTwoOne, divY_two_curveCharTwoOne] at hpt
  exact absurd hpt.2 (by decide)

/-- ⚠️ **`NsmulEqDiv` itself HOLDS at `n = 1` on `curveCharTwoOne` at `(1, 0)`.**  `divX 1 1 = 1`
and `divY 1 0 1 = 0` — the latter by `divY_eq_zero_of_two_eq_zero`, and `y = 0` here, so the halved
prediction is right at this index for the one reason available in characteristic `2`: the true
`y`-coordinate is itself `0`.

⚠️ **This is why *"every rung of the halved ladder is unavailable"* is a claim about the THEOREMS
and never about the predicate**, and it is also the datum that keeps this file's corrected
vocabulary honest in the other direction: at `n = 1` **both** predicates hold (`nsmulEqDivω_one`),
so nothing here refutes `NsmulEqDiv → NsmulEqDivω`, and nothing here asserts it either. -/
theorem nsmulEqDiv_one_curveCharTwoOne : NsmulEqDiv nonsingular_curveCharTwoOne 1 := by
  have hX : curveCharTwoOne.divX 1 1 = 1 := divX_one
  have hY : curveCharTwoOne.divY 1 0 1 = 0 := divY_eq_zero_of_two_eq_zero (by decide) 1
  have hns' : curveCharTwoOne.Nonsingular (curveCharTwoOne.divX 1 1)
      (curveCharTwoOne.divY 1 0 1) := by
    rw [hX, hY]; exact nonsingular_curveCharTwoOne
  exact ⟨hns', by rw [one_zsmul, Point.some.injEq]; exact ⟨hX.symm, hY.symm⟩⟩

/-- ⚠️⚠️ **There is no implication `NsmulEqDivω → NsmulEqDiv`, and the counterexample is this
file's own witness pair**: at a FIXED curve and point, over ALL indices, `n = 2` on
`curveCharTwoOne` at `(1, 0)` refutes it — `nsmulEqDivω_two_curveCharTwoOne` against
`not_nsmulEqDiv_two_curveCharTwoOne`.

⚠️ **So *"`NsmulEqDivω` is strictly stronger than `NsmulEqDiv`"* is precisely the sentence this
datum rules out**, *"A is stronger than B"* asserting `A → B`.  The two predicates are not ordered:
they pin the same `x` and differ only in the `y`, so wherever the two data differ at most one of
them holds (`NsmulEqDiv.divY_eq_divYω`).

⚠️ **The relation that IS an ordering lives at the THEOREM level**: `nsmulEqDivω_two` binds `hns`
and `ht` where `NsmulLadder`'s `nsmulEqDiv_two` binds `h2` as well — strictly fewer hypotheses —
and under `h2` it returns that theorem's own conclusion in one line,
`(nsmulEqDiv_iff_nsmulEqDivω h2 hns ht ht).mpr (nsmulEqDivω_two hns ht)`.  ⚠️ That line is
deliberately **not** a declaration of this file: stating it would re-prove a landed theorem, which
is the one thing the module docstring promises not to do. -/
theorem not_forall_nsmulEqDivω_imp_nsmulEqDiv_curveCharTwoOne :
    ¬ ∀ n : ℤ, NsmulEqDivω nonsingular_curveCharTwoOne n →
      NsmulEqDiv nonsingular_curveCharTwoOne n :=
  fun h => not_nsmulEqDiv_two_curveCharTwoOne (h 2 nsmulEqDivω_two_curveCharTwoOne)

end Nonvacuity

end WeierstrassCurve.Affine
