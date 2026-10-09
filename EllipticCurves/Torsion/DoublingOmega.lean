/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import EllipticCurves.Torsion.OmegaIntegral

/-!
# The `y`-coordinate of `2 • P` with no `(2 : F) ≠ 0`

`EllipticCurves.Torsion.DoublingCoords`' `addY_self_eq_div` computes the `y`-coordinate of the
group-law double of an affine point,

```
y(2 • (x, y)) = (preΨ₄(x) - ψ₂(x, y)·(a₁Φ₂(x) + a₃Ψ₂Sq(x))) / (2 ψ₂(x, y)³),
```

and it binds `(2 : F) ≠ 0`.  ⚠️ **That hypothesis is not a fact about doubling; it is the `2` in
the statement's own denominator.**  `EllipticCurves.Torsion.OmegaIntegral` removed the same `2`
from the numerator at every index — `ωNumₙ` is an honest polynomial over every commutative ring,
with `2·ωNumₙ = ωBracketₙ` — so the halved form at `n = 2` has a companion that does not divide by
`2` at all, and this file is it:

```
y(2 • (x, y)) = ω₂(x, y) / ψ₂(x, y)³
```

for a point `(x, y)` of `W` with `W.Equation x y` and `y ≠ negY x y`, over **any** field,
characteristic `2` included.

## What it costs, and where the halving actually goes

`ωNum` is an `Exists.choose` over the universal curve, so it has no handle but `two_mul_ωNum` and
`map_ωNum`, and `ωNum_one` was the only index at which the tree pinned it to a named polynomial.
So a `2`-free statement about `ω₂` needs `ω₂` itself first, and that is `ωNum_two` below.

What `ωNum_two` rests on is `preΨ₄_eq_two_mul_sub`, an identity of `R[X]` over every commutative
ring:

```
preΨ₄ = 2·((3X² + 2a₂X + a₄)·Ψ₃ - 2(X³ + a₂X² + a₄X + a₆)·Ψ₂Sq)
          - (a₁X + a₃)·(a₁Φ₂ + a₃Ψ₂Sq).
```

⚠️ **This is where the halving is discharged, and it is discharged by exhibiting the half rather
than by dividing.**  `ωBracket₂` is `preΨ₄ - ψ₂·(a₁Φ₂ + a₃Ψ₂Sq)` and `ψ₂` is `2Y + (a₁X + a₃)`, so
subtracting `(a₁X + a₃)·(a₁Φ₂ + a₃Ψ₂Sq)` from both sides of the display above leaves `ωBracket₂` as
`2` times a polynomial written down in full — that is `ωBracket_two`, and `ωNum_two` is what
`two_mul_ωNum` then forces.  ⚠️ **So `OmegaIntegral`'s descent through
`MvPolynomial (Fin 5) (ZMod 2)` is not re-run here and is not re-proved here**: it is what
`two_mul_ωNum` already supplies, and the only cancellation this file performs is the single
`mul_left_cancel₀` over `MvPolynomial (Fin 5) ℤ`, a characteristic-`0` domain — the same step, at
the same ring, as `ωNum_one`'s.

⚠️ **The point-level proof divides by nothing either, and that is what makes it survive `2 = 0`.**
`addY_self_eq_div_ωNum` clears the `addX` and `slope` denominators into hypotheses —
`addX·Ψ₂Sq(x) = Φ₂(x)` and `slope·ψ₂(x, y) = 3x² + 2a₂x + a₄ - a₁y` — before any `ring` runs, and
then supplies `ψ₂(x, y)² = Ψ₂Sq(x)`, `Φ₂ = X·Ψ₂Sq - Ψ₃` and the Weierstrass equation.  The
Weierstrass equation enters with coefficient `-2·Ψ₂Sq(x)`.  ⚠️ **A `2` in a `linear_combination`
coefficient is not a `2` in the statement** — it multiplies a hypothesis whose value is `0`, so it
is invisible to the characteristic, and the hypothesis is the only place the curve is used.

## Main results

* `WeierstrassCurve.preΨ₄_eq_two_mul_sub` — `preΨ₄` written as `2` times an exhibited polynomial
  minus `(a₁X + a₃)·(a₁Φ₂ + a₃Ψ₂Sq)`, over an arbitrary `CommRing` and with no hypotheses;
* `WeierstrassCurve.ωBracket_two` — `ωBracket₂ = 2·ω₂` with `ω₂` exhibited, over an arbitrary
  `CommRing` and with no hypotheses.  It is `preΨ₄_eq_two_mul_sub` transported through
  `ωBracket`'s definition and nothing more;
* **`WeierstrassCurve.ωNum_two`** — `ω₂` in closed form, over an arbitrary `CommRing` and with no
  hypotheses.  ⚠️ This is the second index at which `ωNum` is pinned to a named polynomial, the
  first being `ωNum_one`'s `ω₁ = Y`;
* **`WeierstrassCurve.Affine.addY_self_eq_div_ωNum`** — `y(2 • P) = ω₂(x, y)/ψ₂(x, y)³` over an
  arbitrary field, under `W.Equation x y` and `y ≠ W.negY x y` and ⚠️ **no `(2 : F) ≠ 0`**;

The `Nonvacuity` section below is one curve and one point, and every declaration in it is named
here.  ⚠️ **Each takes no hypotheses at all** — they are closed statements about
`WeierstrassCurve.Affine.curveCharTwoOne`, the curve `y² + xy = x³ + 1` over `ZMod 2`, at its point
`(1, 0)`:

* `curveCharTwoOne` — the curve, as `⟨1, 0, 0, 0, 1⟩`;
* `equation_curveCharTwoOne`, `nonsingular_curveCharTwoOne`, `y_ne_negY_curveCharTwoOne` — `(1, 0)`
  is a point of it, is nonsingular, and is not fixed by negation, so it is a point at which both
  doubling statements apply;
* `slope_curveCharTwoOne`, `addY_self_curveCharTwoOne` — the tangent slope and
  `y(2 • (1, 0))` are both `1`;
* `evalEval_ψ_two_curveCharTwoOne`, `evalEval_ωNum_two_curveCharTwoOne` — `ψ₂(1, 0) = 1` and
  ⚠️ **`ω₂(1, 0) = 1`, read off the group law through `addY_self_eq_div_ωNum`**.  `ωNum` is an
  `Exists.choose`, so a value of it at a characteristic-`2` point is not otherwise available;
* ⚠️ **`addY_self_eq_div_ne_curveCharTwoOne` — the statement that decides whether this file is
  worth anything.  `addY_self_eq_div`'s own right-hand side is *not* `y(2 • (1, 0))` here.**
  Its denominator `2ψ₂(1, 0)³` is `0`, so that right-hand side is `0` by Lean's division
  convention, while `y(2 • (1, 0))` is `1`.  **The halved form is therefore not merely unavailable
  at this point: its conclusion is false there, which is what its `(2 : F) ≠ 0` exists to prevent.**

## What is *not* here

* **Any other index.**  `ωNum_two` is `n = 2` and nothing below generalises it.  The general-index
  `y`-coordinate statements are `OmegaIntegral`'s `nsmul_eq_some_ωNum` and
  `nsmul_eq_some_ωNum_of_ΨSq_ne_zero`, and ⚠️ **both still bind `(2 : F) ≠ 0`, for a reason that is
  not the halving**: that file's own module block names it as the `x`-coordinate/group-law half,
  `nsmulEqDiv_of_forall_ψ_ne_zero`.  Nothing here touches that half.
* **`HasXCoordFormula` at a general index**, which is `#2250`'s target and is not approached here.
  This file is that issue's `n = 2` rung and is deliberately only that.
* **Any change to `addY_self_eq_div`, `divY`, `divT` or `NsmulEqDiv`.**  Everything here is
  additive: the `2`-free form sits beside the halved one, and `addY_self_eq_div_ωNum` is not stated
  as a rewrite of anything landed.
* **A `(2 : F) ≠ 0` sweep.**  No consumer of `addY_self_eq_div` is edited.
* **Any claim about `curveCharTwoOne` beyond the statements listed above.**  It is defined
  here because `addY_self_eq_div_ne_curveCharTwoOne` needs a witness, and nothing about its
  reduction type, its `j`-invariant or its group order is asserted or used.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.3 and Exercise 3.7.
-/

open Polynomial

open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R}

/-- **`preΨ₄` with its even part exhibited.**  Over an arbitrary `CommRing`,

```
preΨ₄ = 2·((3X² + 2a₂X + a₄)·Ψ₃ - 2(X³ + a₂X² + a₄X + a₆)·Ψ₂Sq) - (a₁X + a₃)·(a₁Φ₂ + a₃Ψ₂Sq).
```

⚠️ **The content is that the bracket is `preΨ₄ + (a₁X + a₃)·(a₁Φ₂ + a₃Ψ₂Sq)` halved, written out
rather than divided** — which is why this holds over rings in which `2` is not invertible and in
which it is `0`.  It is the univariate half of `two_mul_ωNum` at `n = 2`, and `ωBracket_two` is the
bivariate statement it gives.

⚠️ The `b`-invariants are unfolded here (`b₂`, `b₄`, `b₆`, `b₈`) because `preΨ₄`, `Ψ₂Sq`, `Ψ₃` and
`Φ₂` are all stated in them and the identity is not a `b`-invariant identity: `2a₂`, `a₄` and
`a₆` appear on the right and no `b` is a multiple of any of them. -/
lemma preΨ₄_eq_two_mul_sub :
    W.preΨ₄ =
      2 * ((3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄) * W.Ψ₃ -
            2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) * W.Ψ₂Sq) -
        W.linForm * (C W.a₁ * W.Φ 2 + C W.a₃ * W.Ψ₂Sq) := by
  rw [preΨ₄, Ψ₂Sq, Ψ₃, Φ_two, linForm, b₂, b₄, b₆, b₈]
  C_simp
  ring

/-- **`ωBracket₂ = 2·ω₂`, with `ω₂` exhibited**, over an arbitrary `CommRing`.

`ωBracket₂` is `preΨ₄ - ψ₂·(a₁Φ₂ + a₃Ψ₂Sq)` by definition (`preΩ_two` supplies `preΩ₂ = preΨ₄`),
and `ψ₂ = 2Y + (a₁X + a₃)`, so this is `preΨ₄_eq_two_mul_sub` with the `2Y` term folded in.

⚠️ **It says nothing `two_mul_ωNum` does not already say about divisibility** — that theorem gives
`2 ∣ ωBracketₙ` at every index.  What is new is the **quotient**, named rather than existentially
quantified, and that is what `ωNum_two` needs. -/
lemma ωBracket_two :
    W.ωBracket 2 =
      2 * (C ((3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄) * W.Ψ₃ -
              2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) * W.Ψ₂Sq) -
            (Y + C W.linForm) * C (C W.a₁ * W.Φ 2 + C W.a₃ * W.Ψ₂Sq)) := by
  rw [ωBracket, if_pos (by decide : Even (2 : ℤ)), preΩ_two, ψ_two, ΨSq_two,
    preΨ₄_eq_two_mul_sub (W := W), ψ₂, Affine.polynomialY, linForm]
  C_simp
  ring

/-- ⚠️ **`ω₂` in closed form**, over an arbitrary `CommRing` and with no hypotheses:

```
ω₂ = ((3X² + 2a₂X + a₄)·Ψ₃ - 2(X³ + a₂X² + a₄X + a₆)·Ψ₂Sq) - (Y + (a₁X + a₃))·(a₁Φ₂ + a₃Ψ₂Sq).
```

⚠️ **This is the second index at which `ωNum` is pinned to a named polynomial**, the first being
`ωNum_one`'s `ω₁ = Y`, and it is pinned the same way: `ωNum` is an `Exists.choose`, so the value is
read off `two_mul_ωNum` over `MvPolynomial (Fin 5) ℤ` — a characteristic-`0` domain, where the `2`
cancels — and carried down to `W` by `map_ωNum`.

The correction term is written as `a₁Φ₂ + a₃Ψ₂Sq` and not in any smaller form on purpose: that is
the shape `ωBracket`'s own definition uses, so `ωBracket_two` above is visibly the same statement
with a factor of `2`.  `Φ_two_eq` turns it into `(a₁X + a₃)·Ψ₂Sq - a₁Ψ₃` for a reader who wants
`Φ₂` gone. -/
theorem ωNum_two :
    W.ωNum 2 =
      C ((3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄) * W.Ψ₃ -
          2 * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) * W.Ψ₂Sq) -
        (Y + C W.linForm) * C (C W.a₁ * W.Φ 2 + C W.a₃ * W.Ψ₂Sq) := by
  have huniv : univ.ωNum 2 =
      C ((3 * X ^ 2 + C (2 * univ.a₂) * X + C univ.a₄) * univ.Ψ₃ -
          2 * (X ^ 3 + C univ.a₂ * X ^ 2 + C univ.a₄ * X + C univ.a₆) * univ.Ψ₂Sq) -
        (Y + C univ.linForm) * C (C univ.a₁ * univ.Φ 2 + C univ.a₃ * univ.Ψ₂Sq) := by
    refine mul_left_cancel₀ (a := (2 : (MvPolynomial (Fin 5) ℤ)[X][Y])) (by norm_num) ?_
    rw [two_mul_ωNum, ωBracket_two]
  have h := map_ωNum (W := univ) W.specialize 2
  rw [univ_map_specialize, huniv] at h
  have ha₁ : W.specialize univ.a₁ = W.a₁ := by
    simpa using congrArg WeierstrassCurve.a₁ (univ_map_specialize (W := W))
  have ha₂ : W.specialize univ.a₂ = W.a₂ := by
    simpa using congrArg WeierstrassCurve.a₂ (univ_map_specialize (W := W))
  have ha₃ : W.specialize univ.a₃ = W.a₃ := by
    simpa using congrArg WeierstrassCurve.a₃ (univ_map_specialize (W := W))
  have ha₄ : W.specialize univ.a₄ = W.a₄ := by
    simpa using congrArg WeierstrassCurve.a₄ (univ_map_specialize (W := W))
  have ha₆ : W.specialize univ.a₆ = W.a₆ := by
    simpa using congrArg WeierstrassCurve.a₆ (univ_map_specialize (W := W))
  have hΨ₃ : univ.Ψ₃.map W.specialize = W.Ψ₃ := by rw [← map_Ψ₃, univ_map_specialize]
  have hΨ₂Sq : univ.Ψ₂Sq.map W.specialize = W.Ψ₂Sq := by rw [← map_Ψ₂Sq, univ_map_specialize]
  have hΦ : (univ.Φ 2).map W.specialize = W.Φ 2 := by rw [← map_Φ, univ_map_specialize]
  have hlin : univ.linForm.map W.specialize = W.linForm := by
    rw [← map_linForm, univ_map_specialize]
  rw [h]
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_ofNat, Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, ha₁, ha₂, ha₃, ha₄,
    ha₆, hΨ₃, hΨ₂Sq, hΦ, hlin, map_mul, map_ofNat]

end WeierstrassCurve

namespace WeierstrassCurve.Affine

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {x y : F}

/-- ⚠️ **The `y`-coordinate of `2 • P`, over an arbitrary field and with no `(2 : F) ≠ 0`.**  For a
point `(x, y)` of `W` not fixed by negation,

```
y(2 • (x, y)) = ω₂(x, y) / ψ₂(x, y)³.
```

This is `EllipticCurves.Torsion.DoublingCoords`' `addY_self_eq_div` with the presentational `2`
removed: that theorem's right-hand side is `ωBracket₂(x, y)/(2 ψ₂³)`, and its `(2 : F) ≠ 0` pays
for that denominator and for nothing else.  ⚠️ **The hypotheses here are exactly `W.Equation x y`
and `y ≠ W.negY x y`**, the second of which is what makes `ψ₂(x, y) ≠ 0`, so the quotient is
honest.

⚠️ **`addY_self_eq_div` is not weakened, superseded or restated by this**; it is a different
right-hand side and it is the one a `2`-invertible computation wants, since `preΨ₄` is a named
polynomial where `ω₂` is an `Exists.choose` pinned by `ωNum_two`.  What this adds is the
characteristic-`2` case, where `addY_self_eq_div`'s conclusion is not merely unavailable but false
— see `addY_self_eq_div_ne_curveCharTwoOne`. -/
theorem addY_self_eq_div_ωNum (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.addY x x y (W.slope x x y y) = (W.ωNum 2).evalEval x y / (W.ψ 2).evalEval x y ^ 3 := by
  have hψ : (W.ψ 2).evalEval x y = 2 * y + W.a₁ * x + W.a₃ := ψ_two_evalEval ..
  have hn : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by simp only [negY]; ring
  have hden0 : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by rw [← hn]; exact sub_ne_zero.mpr hy
  have hs : (2 * y + W.a₁ * x + W.a₃) ^ 2 = W.Ψ₂Sq.eval x := by
    have hsq := ψ_sq_evalEval (W := W) h 2
    rwa [ΨSq_two, ψ_two_evalEval] at hsq
  have hQ0 : W.Ψ₂Sq.eval x ≠ 0 := by rw [← hs]; exact pow_ne_zero _ hden0
  have hA : W.addX x x (W.slope x x y y) * W.Ψ₂Sq.eval x = (W.Φ 2).eval x := by
    rw [addX_self_eq_div h hy, div_mul_cancel₀ _ hQ0]
  have hL : W.slope x x y y * (2 * y + W.a₁ * x + W.a₃) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [slope_of_Y_ne rfl hy, hn, div_mul_cancel₀ _ hden0]
  have hΨ₃ : W.Ψ₃.eval x = x * W.Ψ₂Sq.eval x - (W.Φ 2).eval x := by
    have hh := congrArg (Polynomial.eval x) (Φ_two_eq (W := W))
    simp only [eval_sub, eval_mul, eval_X] at hh
    linear_combination hh
  have hlin : W.linForm.eval x = W.a₁ * x + W.a₃ := by simp [linForm]
  have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y
      - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := (equation_iff' x y).mp h
  rw [ωNum_two, hψ, eq_div_iff (pow_ne_zero 3 hden0), addY, negAddY]
  simp only [negY, evalEval_sub, evalEval_add, evalEval_mul, evalEval_C, evalEval_X, eval_sub,
    eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
  rw [hΨ₃, hlin]
  linear_combination
    (-(3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) - W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hA
      + (-(W.addX x x (W.slope x x y y) - x) * (2 * y + W.a₁ * x + W.a₃) ^ 2) * hL
      + (-((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
              * (W.addX x x (W.slope x x y y) - x)
            + W.a₁ * W.addX x x (W.slope x x y y) * (2 * y + W.a₁ * x + W.a₃)
            + (y + W.a₃) * (2 * y + W.a₁ * x + W.a₃))) * hs
      + (-2 * W.Ψ₂Sq.eval x) * heq

section Nonvacuity

/-- **`y² + xy = x³ + 1` over `ZMod 2`**, as `⟨a₁, a₂, a₃, a₄, a₆⟩ = ⟨1, 0, 0, 0, 1⟩`.

⚠️ It exists for one reason: `addY_self_eq_div_ne_curveCharTwoOne` needs a characteristic-`2` curve
carrying a point that is not fixed by negation, and in characteristic `2` that asks for
`a₁x + a₃ ≠ 0`, so `a₁ = 0` will not do.  Nothing about its reduction type, its `j`-invariant or
its group order is asserted or used.

⚠️ **The tuple is `EllipticCurves.Fixture.y2AddXYEqX3AddC`'s at `c = 1`, and
`curveCharTwoOne_eq` below proves it rather than saying it.**  That family is the shared
`a₁ ≠ 0` fixture and is polymorphic in its base; this definition is kept because the name has code
occurrences in this file and in two others, and retiring it is a separate job (`#2345` stage 2).
⚠️ **No count is given here on purpose**: the population grows, and the pin below is itself an
occurrence, so a numeral in this sentence is one behind the tree in the hunk that writes it. -/
def curveCharTwoOne : Affine (ZMod 2) := ⟨1, 0, 0, 0, 1⟩

/-- **`curveCharTwoOne` IS the shared ordinary fixture at `c = 1`**, not a second spelling of it:
`curveCharTwoOne = EllipticCurves.Fixture.y2AddXYEqX3AddC (ZMod 2) 1`.

⚠️ **The tree must not carry two names for one object with no stated relation**, which is why this
is a proved equation and not a docstring sentence.  It holds by `rfl`: both sides reduce to the
same anonymous constructor application. -/
theorem curveCharTwoOne_eq :
    curveCharTwoOne = EllipticCurves.Fixture.y2AddXYEqX3AddC (ZMod 2) 1 := rfl

/-- `(1, 0)` satisfies `curveCharTwoOne`'s Weierstrass equation: over `ZMod 2`,
`0 + 1·1·0 + 0·0 = 0` and `1 + 0 + 0 + 1 = 0`. -/
theorem equation_curveCharTwoOne : curveCharTwoOne.Equation 1 0 := by
  rw [equation_iff']
  simp only [curveCharTwoOne]
  decide

/-- `(1, 0)` is not fixed by negation on `curveCharTwoOne`: `negY 1 0 = -0 - 1·1 - 0 = 1`.

⚠️ This is what makes `ψ₂(1, 0) ≠ 0`, and in characteristic `2` it is a condition on `a₁x + a₃`
alone, the `2y` of `ψ₂` having died. -/
theorem y_ne_negY_curveCharTwoOne : (0 : ZMod 2) ≠ curveCharTwoOne.negY 1 0 := by
  simp only [negY, curveCharTwoOne]
  decide

/-- `(1, 0)` is a nonsingular point of `curveCharTwoOne`, by the `∂/∂Y` branch of
`nonsingular_iff'` — which is `2y + a₁x + a₃ ≠ 0`, the same `1 ≠ 0` as
`y_ne_negY_curveCharTwoOne`.

⚠️ Recorded so that `(1, 0)` is a point of `curveCharTwoOne.Point` and `addY` at it really is the
group-law double's `y`-coordinate (`Point.add_self_of_Y_ne`); nothing below consumes it. -/
theorem nonsingular_curveCharTwoOne : curveCharTwoOne.Nonsingular 1 0 := by
  refine (nonsingular_iff' 1 0).mpr ⟨equation_curveCharTwoOne, Or.inr ?_⟩
  simp only [curveCharTwoOne]
  decide

/-- The tangent slope of `curveCharTwoOne` at `(1, 0)` is `1`: the numerator
`3·1² + 2·0·1 + 0 - 1·0` is `3 = 1` and the denominator `0 - negY 1 0` is `1`, both in `ZMod 2`. -/
theorem slope_curveCharTwoOne : curveCharTwoOne.slope 1 1 0 0 = 1 := by
  have hd : (0 : ZMod 2) - curveCharTwoOne.negY 1 0 = 1 := by
    simp only [negY, curveCharTwoOne]; decide
  rw [slope_of_Y_ne rfl y_ne_negY_curveCharTwoOne, hd, div_one]
  simp only [curveCharTwoOne]
  decide

/-- ⚠️ **`y(2 • (1, 0)) = 1` on `curveCharTwoOne`.**  With the slope `1`, `addX` is
`1 + 1 - 0 - 1 - 1 = 0` and `negAddY` is `1·(0 - 1) + 0 = 1`, so `addY` is `-1 - 0 - 0 = 1`.

⚠️ **The value being nonzero is the whole point**: it is what makes
`addY_self_eq_div_ne_curveCharTwoOne` a falsification rather than a coincidence of two zeros. -/
theorem addY_self_curveCharTwoOne :
    curveCharTwoOne.addY 1 1 0 (curveCharTwoOne.slope 1 1 0 0) = 1 := by
  rw [slope_curveCharTwoOne, addY, negAddY, addX]
  simp only [negY, curveCharTwoOne]
  decide

/-- `ψ₂(1, 0) = 1` on `curveCharTwoOne`: `2·0 + 1·1 + 0 = 1` in `ZMod 2`. -/
theorem evalEval_ψ_two_curveCharTwoOne : (curveCharTwoOne.ψ 2).evalEval 1 0 = 1 := by
  rw [ψ_two_evalEval]
  simp only [curveCharTwoOne]
  decide

/-- ⚠️ **`ω₂(1, 0) = 1` on `curveCharTwoOne`**, obtained by reading `addY_self_eq_div_ωNum`
backwards at a point where `ψ₂³ = 1`.

⚠️ **This is a value of `ωNum` at a characteristic-`2` point, and it is not otherwise available**:
`ωNum` is an `Exists.choose` over the universal curve whose only handles are `two_mul_ωNum`,
`map_ωNum`, `ωNum_one` and `ωNum_two`, and `two_mul_ωNum` says nothing at all here because
`2 = 0`. -/
theorem evalEval_ωNum_two_curveCharTwoOne : (curveCharTwoOne.ωNum 2).evalEval 1 0 = 1 := by
  have h := addY_self_eq_div_ωNum equation_curveCharTwoOne y_ne_negY_curveCharTwoOne
  rw [addY_self_curveCharTwoOne, evalEval_ψ_two_curveCharTwoOne, one_pow, div_one] at h
  exact h.symm

/-- ⚠️⚠️ **`addY_self_eq_div`'s right-hand side is NOT `y(2 • (1, 0))` on `curveCharTwoOne`.**

That theorem's denominator is `2 ψ₂(x, y)³`, which is `0` here because `2 = 0` in `ZMod 2`, so its
right-hand side is `0` by Lean's division convention — while `y(2 • (1, 0))` is `1`
(`addY_self_curveCharTwoOne`).

⚠️ **So `addY_self_eq_div`'s `(2 : F) ≠ 0` is not removable and is not a presentational artefact of
its own statement: drop it and the theorem is false, at this curve and at this point.**  What is
presentational is the `2` in the *numerator convention* — `ωBracket₂` against `ω₂` — and that is
what `addY_self_eq_div_ωNum` trades it for.  ⚠️ **This is a statement about the halved form's
right-hand side spelled out, not an application of `addY_self_eq_div` to a curve it excludes**;
the theorem is never instantiated here. -/
theorem addY_self_eq_div_ne_curveCharTwoOne :
    curveCharTwoOne.addY 1 1 0 (curveCharTwoOne.slope 1 1 0 0) ≠
      (curveCharTwoOne.preΨ₄.eval 1 -
          (curveCharTwoOne.ψ 2).evalEval 1 0 *
            (curveCharTwoOne.a₁ * (curveCharTwoOne.Φ 2).eval 1 +
              curveCharTwoOne.a₃ * curveCharTwoOne.Ψ₂Sq.eval 1)) /
        (2 * (curveCharTwoOne.ψ 2).evalEval 1 0 ^ 3) := by
  have hz : (2 : ZMod 2) * (curveCharTwoOne.ψ 2).evalEval 1 0 ^ 3 = 0 := by
    rw [evalEval_ψ_two_curveCharTwoOne]; decide
  rw [hz, div_zero, addY_self_curveCharTwoOne]
  decide

end Nonvacuity

end WeierstrassCurve.Affine
