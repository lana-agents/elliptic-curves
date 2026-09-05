/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.DoublingSurjective
import EllipticCurves.Torsion.OmegaTwo

/-!
# The duplication formula at a closed point: both coordinates of `2 • P`

`EllipticCurves.Torsion.OmegaTwo` proves that the classical division-polynomial doubling
coordinates `(Φ₂(x)/Ψ₂Sq(x), ω₂(x, y)/ψ₂(x, y)³)` satisfy the Weierstrass equation, and says
explicitly that identifying them with the group-law double `2 • P` is "a separate, harder statement
not proved here".  This file is that identification, at an arbitrary affine point:

```
W.addX x x (W.slope x x y y)   = Φ₂(x) / Ψ₂Sq(x)
W.addY x x y (W.slope x x y y) = (preΨ₄(x) - ψ₂·(a₁Φ₂(x) + a₃Ψ₂Sq(x))) / (2 ψ₂³)
```

for a point `(x, y)` of `W` that is not `2`-torsion (`y ≠ negY x y`), over a field of characteristic
`≠ 2`.  Since `Point.add_self_of_Y_ne` computes `P + P` by exactly those `addX`/`addY`, this says
that `2 • P` **is** the division-polynomial doubling point.

## Where this was, and why it moves here

The `y`-coordinate identity already existed in this tree — but only at the **generic point**, as
`addY_gen_eq_mulByTwo` (`EllipticCurves.FunctionField.GenericDoubling`, `#433`), stated over the
base-changed curve `W ⁄ F(W)` at `(genX, genY)`.  `#774` priced the specialisation of that identity
to a closed point as the open question on the affine half of the `[2]`-fibre description, and
flagged that `addY_gen_eq_mulByTwo`'s proof is a `linear_combination` under
`set_option maxRecDepth 8000`, so that specialising it might not be cheap.

**It is cheap, and the reason is worth recording: that proof was never generic.**  Reading it line
by line, the only facts it uses about `(genX, genY)` are

* the Weierstrass equation at the point (`equation_gen`, here `h`);
* `ψ₂ ≠ 0` at the point (`psiTwo_gen_ne`, here `hy` through `two_mul_add_ne_zero_of_Y_ne`);
* `2 ≠ 0` in the ambient field.

All three are available at any non-`2`-torsion affine point of any Weierstrass curve over any field
of characteristic `≠ 2`.  So the generic statement is an *instance* of the statement here, not a
generalisation of it, and the specialisation is a transcription rather than an evaluation argument.
The moral: before pricing "specialise the generic identity" as a research problem, read the generic
proof and ask which of its inputs actually mention the generic point.

## Main results

* `WeierstrassCurve.Affine.addX_self_eq_div` — the `x`-coordinate of `2 • P`, in division form.
  The merged `addX_self_mul_Ψ₂Sq_eval` is its denominator-cleared form; this one is what a
  function-field computation wants, because it matches `mulByTwoEndo_genX` on the nose;
* **`WeierstrassCurve.Affine.addY_self_eq_div`** — the `y`-coordinate of `2 • P`.  This is the
  statement `#774` records as unbuilt.

## What is *not* here

* Any general `ωₙ` duplication formula, and nothing here approaches it.  ⚠️ **This bullet used to
  attribute that formula to `#404`, and that was wrong in a way later files quoted.**  What
  `addY_self_eq_div` states is `y(2 • P) = ω₂/(2 ψ₂³)` for the **group-law** double, and the
  general-`n` form of *that* is `WeierstrassCurve.Affine.HasXCoordFormula`'s `y`-half — issue
  `#1500`, and it is **closed**: `nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
  (`EllipticCurves.Torsion.NsmulYPeriodic`, PR #579) proves `n • (x, y) = (Φₙ/ΨSqₙ, ωₙ/(2ψₙ³))` at
  every index over a field with `(2 : F) ≠ 0`, under `ΨSqₙ(x) ≠ 0` — the non-vanishing that
  `hasXCoordFormula_of_two_ne_zero`'s `HasXCoordFormula W n` asks of a consumer, that theorem taking
  the same `(2 : F) ≠ 0` and binding no `ΨSq` condition itself.  ⚠️ That module is
  **import-incomparable** with this one, so it is cited and not consumed, and nothing below changes.
  `#404`'s own deliverable was the weaker on-curve identity, that `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` satisfies
  `W.Equation` at all, and it is **closed**: `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` of
  `EllipticCurves.Torsion.OmegaCrux`, at every index over a field with `(2 : F) ≠ 0` and under
  `ψₙ(x, y) ≠ 0`, PR #557.  ⚠️ That module and this one are **import-incomparable** — neither is in
  the other's closure — so the name is not resolvable here and nothing below uses it.  The
  two-reading account is in `EllipticCurves.FunctionField.MulByNPullback`.  ⚠️ The `n = 3` case is
  `EllipticCurves.Torsion.TriplingCoords`, the mirror of this file, likewise not here.
* Any statement about places, divisors or the function field; this file is pure point arithmetic and
  is imported by the function-field layer, not the other way round.
* A re-derivation of `addX_gen_eq_mulByTwo` / `addY_gen_eq_mulByTwo` from the results here.  They
  *are* instances (take the base-changed curve over `F(W)` and the point `(genX, genY)`), and
  collapsing the duplication would be a worthwhile follow-up, but it edits a merged file for no
  mathematical gain and is deliberately left out.

## ⚠️ `GenericDoubling` was cited as `#630`; it is `#433`

Corrected in place rather than retired — the number was wrong when it was typed.  That module's
creation commit subject is *"feat(FunctionField): the doubling correspondence
`𝒫 + 𝒫 = ([2]∗genX, [2]∗genY)` for the generic point (#433, #419) (#163)"*, so the issue is
**`#433`**, and `addY_gen_eq_mulByTwo` is introduced by that same commit.  `#630` is the Dedekind
divisor-transport infrastructure issue, whose module is `FunctionField/DivisorTransport` — real work
on this tree, unrelated to the doubling correspondence.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.3 (the duplication
  formula), Exercise 3.7.
-/

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {x y : F}

/-- **The `x`-coordinate of `2 • P`, in division form.**  For a point `(x, y)` of `W` not fixed by
negation, `x(2 • (x, y)) = Φ₂(x) / Ψ₂Sq(x)`.

The merged `addX_self_mul_Ψ₂Sq_eval` is the same fact with the denominator cleared; the division
form is what the function-field pullback consumes, since `mulByTwoEndo_genX` is stated as a
quotient. -/
theorem addX_self_eq_div (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) = (W.Φ 2).eval x / W.Ψ₂Sq.eval x := by
  rw [slope_of_Y_ne rfl hy]
  set s := 2 * y + W.a₁ * x + W.a₃ with hsdef
  have hden : y - W.negY x y = s := by rw [hsdef]; simp only [negY]; ring
  have hden0 : s ≠ 0 := by rw [← hden]; exact sub_ne_zero.mpr hy
  have hs : s ^ 2 = W.Ψ₂Sq.eval x := by
    have hsq := ψ_sq_evalEval (W := W) h 2
    rw [ΨSq_two, ψ_two_evalEval] at hsq
    rw [hsdef]; exact hsq
  have hΦv : (W.Φ 2).eval x =
      x ^ 4 - (2 * W.a₄ + W.a₁ * W.a₃) * x ^ 2 - 2 * (W.a₃ ^ 2 + 4 * W.a₆) * x
        - (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄
            + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2) := by
    rw [Φ_two, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y
      - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
    (equation_iff' x y).mp h
  rw [hden, ← hs]
  simp only [addX]
  field_simp [hden0]
  linear_combination
    (W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
        - (W.a₂ + 2 * x) * (s + 2 * y + W.a₁ * x + W.a₃)) * hsdef
      + (-W.a₁ ^ 2 - 4 * W.a₂ - 8 * x) * heq - hΦv

set_option maxRecDepth 8000 in
/-- **The `y`-coordinate of `2 • P`.**  For a point `(x, y)` of `W` not fixed by negation, over a
field of characteristic `≠ 2`,

```
y(2 • (x, y)) = (preΨ₄(x) - ψ₂(x, y)·(a₁ Φ₂(x) + a₃ Ψ₂Sq(x))) / (2 ψ₂(x, y)³),
```

the `y`-coordinate `ω₂/ψ₂³` of the division-polynomial doubling point whose on-curve property is
`OmegaTwo`'s `doubling_equation`.

`#774` records this as the one piece of the affine `[2]`-fibre description that had no closed-point
form.  The proof is `addY_gen_eq_mulByTwo`'s, transcribed: see the module docstring for why that is
not a coincidence. -/
theorem addY_self_eq_div (h : W.Equation x y) (h2 : (2 : F) ≠ 0) (hy : y ≠ W.negY x y) :
    W.addY x x y (W.slope x x y y)
      = (W.preΨ₄.eval x -
          (W.ψ 2).evalEval x y * (W.a₁ * (W.Φ 2).eval x + W.a₃ * W.Ψ₂Sq.eval x)) /
        (2 * (W.ψ 2).evalEval x y ^ 3) := by
  rw [addY, negAddY, addX_self_eq_div h hy, slope_of_Y_ne rfl hy]
  simp only [negY]
  rw [ψ_two_evalEval]
  set s := 2 * y + W.a₁ * x + W.a₃ with hsdef
  have hden : y - (-y - W.a₁ * x - W.a₃) = s := by rw [hsdef]; ring
  have hden0 : s ≠ 0 := by
    have hn : y - W.negY x y = s := by rw [hsdef]; simp only [negY]; ring
    rw [← hn]; exact sub_ne_zero.mpr hy
  have hs : s ^ 2 = W.Ψ₂Sq.eval x := by
    have hsq := ψ_sq_evalEval (W := W) h 2
    rw [ΨSq_two, ψ_two_evalEval] at hsq
    rw [hsdef]; exact hsq
  have hΦv : (W.Φ 2).eval x =
      x ^ 4 - (2 * W.a₄ + W.a₁ * W.a₃) * x ^ 2 - 2 * (W.a₃ ^ 2 + 4 * W.a₆) * x
        - (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄
            + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2) := by
    rw [Φ_two, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y
      - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
    (equation_iff' x y).mp h
  rw [hden, ← hs, hΦv]
  simp only [preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
  field_simp [hden0, h2]
  linear_combination (8 * x ^ 3 - 4 * x ^ 2 * W.a₁ ^ 2 - 12 * x * W.a₁ * W.a₃
        - 8 * x * W.a₄ - 16 * W.a₆ - 8 * W.a₃ ^ 2 - 16 * x * W.a₁ * y - 16 * W.a₃ * y
        - 16 * y ^ 2) * heq
    + (5 * x ^ 4 * W.a₁ + 4 * x ^ 2 * W.a₁ * W.a₄ + 8 * x * W.a₁ * W.a₆
        + W.a₁ ^ 3 * W.a₆ + 4 * W.a₁ * W.a₂ * W.a₆ + W.a₁ * W.a₂ * W.a₃ ^ 2
        - W.a₁ ^ 2 * W.a₃ * W.a₄ - W.a₁ * W.a₄ ^ 2 + 6 * x ^ 3 * s + 6 * x ^ 3 * W.a₃
        + 4 * x ^ 2 * W.a₂ * s + 4 * x ^ 3 * W.a₁ * W.a₂ + 4 * x ^ 2 * W.a₂ * W.a₃
        + 2 * x * W.a₄ * s + 2 * x * W.a₃ * W.a₄ - W.a₃ * s ^ 2 - x * W.a₁ * W.a₃ * s
        - W.a₃ ^ 2 * s - W.a₃ ^ 3 + 12 * x ^ 3 * y + 8 * x ^ 2 * W.a₂ * y + 4 * x * W.a₄ * y
        - 4 * x * W.a₁ * s * y - 4 * x ^ 2 * W.a₁ ^ 2 * y - 10 * x * W.a₁ * W.a₃ * y
        - 4 * W.a₃ * s * y - 6 * W.a₃ ^ 2 * y - 2 * s ^ 2 * y - 12 * x * W.a₁ * y ^ 2
        - 12 * W.a₃ * y ^ 2 - 4 * s * y ^ 2 - 8 * y ^ 3) * hsdef

end WeierstrassCurve.Affine
