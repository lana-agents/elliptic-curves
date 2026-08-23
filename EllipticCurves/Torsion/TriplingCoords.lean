/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.DoublingCoords
import EllipticCurves.Torsion.OmegaThree
import EllipticCurves.Torsion.TriplingSurjective

/-!
# The tripling formula at a closed point: both coordinates of `3 • P`

`EllipticCurves.Torsion.OmegaThree` proves that the classical division-polynomial tripling
coordinates `(Φ₃(x)/Ψ₃(x)², ω₃(x, y)/ψ₃(x, y)³)` satisfy the Weierstrass equation, and says
explicitly that identifying them with the group-law triple `3 • P` is "a separate, harder statement
not proved here".  This file is that identification, at an affine point `(x, y)` of `W` that is not
fixed by negation and whose `x` is not a root of `Ψ₃`:

```
3 • (x, y) = (Φ₃(x) / ΨSq₃(x), ω₃(x, y) / (2 ψ₃(x, y)³)).
```

## What was already here, and what was not

The `x`-coordinate is merged, with its denominator cleared:
`EllipticCurves.Torsion.TriplingSurjective`'s `addX_add_self_mul_ΨSq_three_eval` proves
`x(3P)·ΨSq₃(x) = Φ₃(x)`, and `addX_add_self_eq_div` below is only its division form — wanted for
the reason `DoublingCoords` gives for `addX_self_eq_div`, namely that it matches
`mulByThreeEndo_genX` on the nose, which is the shape a function-field computation consumes.

The `y`-coordinate existed nowhere at a closed point.  It existed at the **generic point**, as
`addY_gen_eq_mulByThree` (`EllipticCurves.FunctionField.GenericTripling`), stated over the
base-changed curve `W ⁄ F(W)` at `(genX, genY)`, and `TriplingSurjective` records that that
statement cannot be specialised to an `F`-point, there being no ring map `F(W) → F`.

**That is true of the statement and says nothing about the proof.**  Reading
`addY_gen_eq_mulByThree` line by line, the only facts it uses about `(genX, genY)` are

* the Weierstrass equation at the point (`equation_gen`, here `h`);
* `ψ₂ ≠ 0` at the point (`psiTwo_gen_ne`, here `hy` through `two_mul_add_ne_zero_of_Y_ne`);
* `Ψ₃ ≠ 0` at the point (`psiThree_gen_ne`, here `hT`);
* `2 ≠ 0` in the ambient field.

All four hold at any affine point of any Weierstrass curve over any field of characteristic `≠ 2`
that is not `2`-torsion and not `3`-torsion.  So, exactly as `DoublingCoords` found for `n = 2`, the
generic statement is an *instance* of the statement here rather than a generalisation of it, and the
passage is a transcription rather than an evaluation argument.  This is the second time on this
front; the moral is the one `DoublingCoords` recorded, and it is worth repeating because the
prohibition sounds like a mathematical obstruction and is only a syntactic one:

> Before pricing "specialise the generic identity" as a research problem, read the generic proof and
> ask which of its inputs actually mention the generic point.

One structural adjustment is genuinely needed and is recorded here so the next transcription does
not rediscover it.  The generic proof manipulates `mulByTwoEndo h2 (genX W)`, an **opaque** term; at
a closed point the doubled coordinates are the literal `W.addX x x (W.slope x x y y)`, and
`simp only [addX]` then unfolds the *inner* doubling as well as the outer secant sum, which breaks
the final rewrite.  `addY_add_eq_div_aux` below restores the opacity by carrying the doubled
coordinates as variables `X₂`, `Y₂` constrained by the two duplication formulas, and the public
statement is its instance.

## Main results

* `WeierstrassCurve.Affine.addX_add_self_eq_div` — the `x`-coordinate of `3 • P`, in division form.
* **`WeierstrassCurve.Affine.addY_add_self_eq_div`** — the `y`-coordinate of `3 • P`.  This is the
  identity that had no closed-point form.
* `WeierstrassCurve.Affine.nonsingular_tripling` — the tripling coordinates are a nonsingular point,
  from `OmegaThree`'s `tripling_equation`.
* **`WeierstrassCurve.Affine.add_add_self_eq_some`**, `WeierstrassCurve.Affine.nsmul_three_eq_some`
  — the **tripling correspondence** `P + P + P = (Φ₃/ΨSq₃, ω₃/(2 ψ₃³))` and its `(3 : ℕ) • P` form.
  This is the `n = 3` mirror of `GenericTripling`'s `genericPoint_add_add_self`, at a closed point.
* A committed non-vacuity certificate: `3 • (2, 3) = (-1, 0)` on `y² = x³ + 1` over `ℚ`.

## Scope

⚠️ **`(3 : F) ≠ 0` is not needed anywhere below, and is deliberately absent.**  Only `(2 : F) ≠ 0`
is, and only through the tangent slope of the doubling step.  This matches `TriplingSurjective`'s
finding for the `x`-half; the `3`-torsion condition enters as `Ψ₃(x) ≠ 0`, which is a hypothesis on
the point and not on the characteristic.

⚠️ **This is pure point arithmetic.**  No places, no divisors, no function field: like
`DoublingCoords`, this file is imported *by* the function-field layer and not the other way round.

⚠️ **This does not discharge `hprin` at `n = 3`, and does not come close.**  What it supplies is the
first rung of the `n = 3` mirror of `#774` — the `[2]`-fibre description that `#791` consumed.  The
rest of that mirror does not exist: there is no `comapProjPointThree`, no `pullbackDivisorThree` and
no `ramificationIdxThree` in this tree, and the `n = 3` analogue of `#763`'s ramification-index
arithmetic — the step that made `#774` cheap once the coordinates were available — has to be built
before a fibre description follows.  The count it will have to be matched against is `9`
(`card_torsion_three`, `EllipticCurves.Torsion.ThreeTorsionStructure`, merged, and not Ward-gated);
the degree input is `EllipticCurves.FunctionField.MulByThreeDegree`, not anything here.

⚠️ **No claim about the general `ωₙ` (`#404`).**  `ω₃` at a closed point is a much smaller statement
and `OmegaThree` already had its on-curve half; nothing below approaches a general `n`.

⚠️ **`GenericTripling`'s two theorems are instances of the ones below** (take the base-changed curve
over `F(W)` and the point `(genX, genY)`), and collapsing the duplication would be a worthwhile
follow-up.  It is deliberately left out: it edits a merged file for no mathematical gain, exactly as
`DoublingCoords` decided for `n = 2`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Exercise 3.7 (the tripling
  formula), III.2.3.
-/

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {x y : F}

/-! ### The two coordinates of `3 • P` -/

/-- **The `x`-coordinate of `3 • P`, in division form.**  For an affine point `(x, y)` of `W` not
fixed by negation and with `Ψ₃(x) ≠ 0` — equivalently `2P ≠ ±P`, so that `3P = 2P + P` takes the
secant branch — over a field of characteristic `≠ 2`,

```
x(3 • (x, y)) = Φ₃(x) / ΨSq₃(x).
```

The merged `addX_add_self_mul_ΨSq_three_eval` is the same fact with the denominator cleared; the
division form is what the function-field pullback consumes, since `mulByThreeEndo_genX` is stated as
a quotient. -/
theorem addX_add_self_eq_div (h2 : (2 : F) ≠ 0) (h : W.Equation x y) (hy : y ≠ W.negY x y)
    (hT : W.Ψ₃.eval x ≠ 0) :
    W.addX (W.addX x x (W.slope x x y y)) x
        (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y)
      = (W.Φ 3).eval x / (W.ΨSq 3).eval x := by
  rw [eq_div_iff (by rw [ΨSq_three_eval]; exact pow_ne_zero 2 hT)]
  exact addX_add_self_mul_ΨSq_three_eval h2 h hy hT

set_option maxHeartbeats 2000000 in
-- The tripling `y`-identity clears the doubling denominators into a large rational-function
-- identity whose `ring` normalisation needs a raised heartbeat limit, as its generic-point mirror
-- `addY_gen_eq_mulByThree` does.
/-- The `y`-coordinate of `3 • P`, with the doubled coordinates carried as opaque variables `X₂`,
`Y₂` constrained by the two duplication formulas.

The opacity is the point: in the instance below, `X₂` and `Y₂` are literal `addX`/`addY` terms, and
`simp only [addX]` inside this proof would unfold the *inner* doubling as well as the outer secant
sum.  The generic-point mirror does not meet this because `mulByTwoEndo h2 (genX W)` is opaque
there. -/
private theorem addY_add_eq_div_aux (h2 : (2 : F) ≠ 0) (h : W.Equation x y)
    (hy : y ≠ W.negY x y) (hT : W.Ψ₃.eval x ≠ 0) {X₂ Y₂ : F}
    (hX₂ : X₂ = (W.Φ 2).eval x / W.Ψ₂Sq.eval x)
    (hY₂ : Y₂ = (W.preΨ₄.eval x -
        (W.ψ 2).evalEval x y * (W.a₁ * (W.Φ 2).eval x + W.a₃ * W.Ψ₂Sq.eval x)) /
      (2 * (W.ψ 2).evalEval x y ^ 3)) (hne : X₂ ≠ x)
    (hX : W.addX X₂ x (W.slope X₂ x Y₂ y) = (W.Φ 3).eval x / (W.ΨSq 3).eval x) :
    W.addY X₂ x Y₂ (W.slope X₂ x Y₂ y)
      = ((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
          W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
          W.a₃ * (W.ψ 3).evalEval x y ^ 3) / (2 * (W.ψ 3).evalEval x y ^ 3) := by
  set p := W.Ψ₂Sq.eval x with hpdef
  set T := W.Ψ₃.eval x with hTdef
  set Q := W.preΨ₄.eval x with hQdef
  set s := 2 * y + W.a₁ * x + W.a₃ with hsdef
  have hsne : s ≠ 0 := two_mul_add_ne_zero_of_Y_ne hy
  have hs : s ^ 2 = p := (Ψ₂Sq_eval_eq_sq h).symm
  have hpne : p ≠ 0 := by rw [← hs]; exact pow_ne_zero 2 hsne
  set Φ2 := (W.Φ 2).eval x with hΦ2def
  have hΦ2 : Φ2 = x * p - T := by rw [hΦ2def, hpdef, hTdef, Φ_two_eval]
  set Φ3v := (W.Φ 3).eval x with hΦ3def
  have hΦ3 : Φ3v = x * T ^ 2 - Q * p := by
    rw [hΦ3def, Φ_three_eval, ← hTdef, ← hQdef, ← hpdef]
  set Kv := (W.preΨ 5).eval x - Q ^ 2 with hKdef
  have hK : Kv = Q * p ^ 2 - T ^ 3 - Q ^ 2 := by
    rw [hKdef, preΨ_five]
    simp only [eval_sub, eval_mul, eval_pow]
    rw [← hpdef, ← hTdef, ← hQdef]
  -- The secant slope through `2P` and `P`, in the doubling data.
  have hslope : W.slope X₂ x Y₂ y = -(W.a₁) / 2 + (p ^ 2 - Q) * s / (2 * p * T) := by
    have hXsub : X₂ - x = -T / p := by
      rw [hX₂, hΦ2]; field_simp; ring
    have hYsub : Y₂ - y = (Q - p ^ 2 + W.a₁ * T * s) / (2 * p * s) := by
      rw [hY₂, ψ_two_evalEval, ← hsdef, hΦ2,
        show y = (s - W.a₁ * x - W.a₃) / 2 from by rw [eq_div_iff h2, hsdef]; ring]
      field_simp
      linear_combination (p * x * W.a₁ * s - T * W.a₁ * s - p * s ^ 2 + p * W.a₃ * s - Q) * hs
    rw [slope_of_X_ne hne, hYsub, hXsub]
    field_simp
    linear_combination (-(p ^ 2 - Q)) * hs
  -- The `y`-coordinate of `2P`, split into its constant and `ψ₂`-linear parts.
  have hY2 : Y₂ = -(W.a₁ * Φ2 + W.a₃ * p) / (2 * p) + Q / (2 * p ^ 2) * s := by
    rw [hY₂, ψ_two_evalEval, ← hsdef]
    field_simp
    linear_combination (p * s * Φ2 * W.a₁ + p ^ 2 * s * W.a₃ - Q * s ^ 2 - p * Q) * hs
  rw [addY, negAddY, hX, negY, ΨSq_three]
  simp only [eval_pow]
  rw [hslope, hX₂, ← hTdef, hY2, ψ_evalEval h 3, Ψ_three, evalEval_C, ← hTdef, hΦ2, hΦ3, hK]
  field_simp
  ring

/-- **The `y`-coordinate of `3 • P`.**  For an affine point `(x, y)` of `W` not fixed by negation
and with `Ψ₃(x) ≠ 0`, over a field of characteristic `≠ 2`,

```
y(3 • (x, y)) = ω₃(x, y) / (2 ψ₃(x, y)³),
```

where `ω₃(x, y) = (2y + a₁x + a₃)·(preΨ₅(x) − preΨ₄(x)²) − a₁·Φ₃(x)·ψ₃(x, y) − a₃·ψ₃(x, y)³` is the
`3`-division `y`-coordinate value whose on-curve property is `OmegaThree`'s `tripling_equation`.

This is the identity `OmegaThree` records as unbuilt.  The proof is `addY_gen_eq_mulByThree`'s,
transcribed: see the module docstring for why that is not a coincidence. -/
theorem addY_add_self_eq_div (h2 : (2 : F) ≠ 0) (h : W.Equation x y) (hy : y ≠ W.negY x y)
    (hT : W.Ψ₃.eval x ≠ 0) :
    W.addY (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y))
        (W.slope (W.addX x x (W.slope x x y y)) x (W.addY x x y (W.slope x x y y)) y)
      = ((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
          W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
          W.a₃ * (W.ψ 3).evalEval x y ^ 3) / (2 * (W.ψ 3).evalEval x y ^ 3) :=
  addY_add_eq_div_aux h2 h hy hT (addX_self_eq_div h hy) (addY_self_eq_div h h2 hy)
    (fun hc => hT ((addX_self_eq_iff h hy).mp hc)) (addX_add_self_eq_div h2 h hy hT)

/-! ### The tripling correspondence -/

omit [DecidableEq F] in
/-- `ψ₃(x, y) = Ψ₃(x)` at a point of `W`, so the two non-`3`-torsion conditions agree. -/
theorem psiThree_evalEval_ne_zero (h : W.Equation x y) (hT : W.Ψ₃.eval x ≠ 0) :
    (W.ψ 3).evalEval x y ≠ 0 := by
  rwa [ψ_evalEval h 3, Ψ_three, evalEval_C]

variable [W.IsElliptic]

omit [DecidableEq F] in
/-- **The tripling coordinates form a nonsingular point.**  They lie on the curve by
`OmegaThree`'s `tripling_equation`, and on an elliptic curve every equation point is
nonsingular. -/
theorem nonsingular_tripling (h2 : (2 : F) ≠ 0) (h : W.Equation x y) (hT : W.Ψ₃.eval x ≠ 0) :
    W.Nonsingular ((W.Φ 3).eval x / (W.ΨSq 3).eval x)
      (((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
          W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
          W.a₃ * (W.ψ 3).evalEval x y ^ 3) / (2 * (W.ψ 3).evalEval x y ^ 3)) :=
  equation_iff_nonsingular.mp (tripling_equation h h2 (psiThree_evalEval_ne_zero h hT))

/-- **The tripling correspondence at a closed point.**  For an affine point `P = (x, y)` of `W` not
fixed by negation and with `Ψ₃(x) ≠ 0`, over a field of characteristic `≠ 2`,

```
P + P + P = (Φ₃(x) / ΨSq₃(x), ω₃(x, y) / (2 ψ₃(x, y)³)).
```

The double `P + P` is `(addX x x ℓ, addY x x y ℓ)` for the tangent slope `ℓ` (`add_self_of_Y_ne`),
and `x(2P) ≠ x(P)` because `Ψ₃(x) ≠ 0` (`addX_self_eq_iff`), so the further sum `(2P) + P` takes the
secant branch `add_of_X_ne`, whose coordinates are the two identities above.

This is the statement `OmegaThree` calls "a separate, harder statement not proved here", and the
`n = 3` mirror of `GenericTripling`'s `genericPoint_add_add_self`. -/
theorem add_add_self_eq_some (h2 : (2 : F) ≠ 0) {h : W.Nonsingular x y}
    (hy : y ≠ W.negY x y) (hT : W.Ψ₃.eval x ≠ 0) :
    Point.some x y h + Point.some x y h + Point.some x y h
      = Point.some ((W.Φ 3).eval x / (W.ΨSq 3).eval x)
          (((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
              W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
              W.a₃ * (W.ψ 3).evalEval x y ^ 3) / (2 * (W.ψ 3).evalEval x y ^ 3))
          (nonsingular_tripling h2 h.left hT) := by
  rw [Point.add_self_of_Y_ne hy,
    Point.add_of_X_ne (fun hc => hT ((addX_self_eq_iff h.left hy).mp hc)), Point.some.injEq]
  exact ⟨addX_add_self_eq_div h2 h.left hy hT, addY_add_self_eq_div h2 h.left hy hT⟩

/-- **The tripling correspondence**, as a statement about `(3 : ℕ) • P`. -/
theorem nsmul_three_eq_some (h2 : (2 : F) ≠ 0) {h : W.Nonsingular x y}
    (hy : y ≠ W.negY x y) (hT : W.Ψ₃.eval x ≠ 0) :
    (3 : ℕ) • Point.some x y h
      = Point.some ((W.Φ 3).eval x / (W.ΨSq 3).eval x)
          (((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
              W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
              W.a₃ * (W.ψ 3).evalEval x y ^ 3) / (2 * (W.ψ 3).evalEval x y ^ 3))
          (nonsingular_tripling h2 h.left hT) := by
  rw [three'_nsmul]; exact add_add_self_eq_some h2 hy hT

/-! ### Non-vacuity

The statements above quantify over an affine point of a Weierstrass curve that is neither `2`- nor
`3`-torsion.  `y² = x³ + 1` over `ℚ` at `P = (2, 3)` supplies one: `negY 2 3 = −3 ≠ 3` and
`Ψ₃(2) = 72 ≠ 0`.  `TriplingSurjective`'s own non-vacuity section certifies exactly those two
hypotheses on this same curve and point; the certificate below goes one step further and computes
the conclusion, **`3 • (2, 3) = (−1, 0)`**, so what is exhibited is the tripling formula doing
arithmetic rather than merely a curve on which it could be stated.

The hand check: the tangent at `(2, 3)` has slope `3x²/(2y) = 2`, so `2P = (0, 1)`; the secant
through `(0, 1)` and `(2, 3)` has slope `1`, so `3P = (−1, 0)`.  Through the division polynomials
the same answer arrives as `Φ₃(2)/ΨSq₃(2) = −5184/5184 = −1` and, since
`preΨ₅(2) = preΨ₄(2)² = 186624` makes `ω₃(2, 3)` vanish, `y(3P) = 0`.
-/

section Nonvacuity

/-- The curve `y² = x³ + 1` over `ℚ`, of discriminant `-432`. -/
private def exampleCurve : Affine ℚ := ⟨0, 0, 0, 0, 1⟩

private instance : exampleCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `P = (2, 3)` lies on `y² = x³ + 1` and is nonsingular. -/
private lemma exampleNonsingular : exampleCurve.Nonsingular 2 3 :=
  equation_iff_nonsingular.mp (by norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

/-- `P` is not `2`-torsion. -/
private lemma exampleNegY : (3 : ℚ) ≠ exampleCurve.negY 2 3 := by
  norm_num [exampleCurve, WeierstrassCurve.Affine.negY]

/-- `P` is not `3`-torsion: `Ψ₃(2) = 3·2⁴ + 3·b₆·2 = 48 + 24 = 72`. -/
private lemma examplePsiThree : exampleCurve.Ψ₃.eval 2 = 72 := by
  norm_num [exampleCurve, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma examplePsiTwoSq : exampleCurve.Ψ₂Sq.eval 2 = 36 := by
  norm_num [exampleCurve, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]

private lemma examplePrePsiFour : exampleCurve.preΨ₄.eval 2 = 432 := by
  rw [preΨ₄_eval, examplePsiThree, examplePsiTwoSq]
  norm_num [exampleCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

/-- `3 • P = (-1, 0)` lies on `y² = x³ + 1` and is nonsingular. -/
private lemma exampleNonsingularThree : exampleCurve.Nonsingular (-1) 0 :=
  equation_iff_nonsingular.mp (by norm_num [exampleCurve, WeierstrassCurve.Affine.equation_iff])

/-- **The tripling correspondence on a curve that exists**, with both points named:
`3 • (2, 3) = (-1, 0)` on `y² = x³ + 1` over `ℚ`. -/
example : (3 : ℕ) • Point.some (2 : ℚ) 3 exampleNonsingular
    = Point.some (-1) 0 exampleNonsingularThree := by
  rw [nsmul_three_eq_some (by norm_num) exampleNegY (by rw [examplePsiThree]; norm_num),
    Point.some.injEq]
  have hψ : (exampleCurve.ψ 3).evalEval 2 3 = 72 := by
    rw [ψ_evalEval (equation_iff_nonsingular.mpr exampleNonsingular) 3, Ψ_three, evalEval_C,
      examplePsiThree]
  refine ⟨?_, ?_⟩
  · rw [Φ_three_eval, ΨSq_three_eval, examplePsiThree, examplePrePsiFour, examplePsiTwoSq]
    norm_num
  · rw [hψ, preΨ_five]
    simp only [eval_sub, eval_mul, eval_pow]
    rw [examplePrePsiFour, examplePsiTwoSq, examplePsiThree]
    norm_num [exampleCurve]

end Nonvacuity

end WeierstrassCurve.Affine
