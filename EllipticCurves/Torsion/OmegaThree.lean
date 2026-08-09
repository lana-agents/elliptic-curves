/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.DivisionPolynomialEval

/-!
# The `3`-division `y`-coordinate and the tripling map is on the curve

Mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` develops the
`x`-coordinate division polynomials (`ψ₂, Ψ₂Sq, Ψ₃, preΨ₄, ΨSq, Ψ, Φ, ψ, φ`) but explicitly leaves
the *`y`-coordinate* division polynomials `ωₙ` as a `TODO`. Consequently there is, on the current
pin, no statement that the multiplication-by-`n` point `[n]P = (Φₙ/ΨSqₙ, ωₙ/ψₙ³)` actually lies on
the curve — the *on-curve identity* that the function-field pullback `[n]∗ : F(W) → F(W)` consumes.

The sibling file `EllipticCurves/Torsion/OmegaTwo.lean` supplies the crux for the **duplication
map** `n = 2`. This file supplies the analogue for the **tripling map** `n = 3` (Silverman AEC,
Exercise 3.7).

The key structural fact used is that a point `(X, Y)` lies on `W` iff
`(2Y + a₁X + a₃)² = 4X³ + b₂X² + 2b₄X + b₆` (valid over a field of characteristic `≠ 2`), and that
for the tripled point the "`ψ₂`-value" `2Y + a₁X + a₃` equals `(2y + a₁x + a₃)·(preΨ₅ − preΨ₄²)/ψ₃³`
(`tripling_ψ₂` below, established by `hlin`). Squaring and feeding in the `b`-relation
`(2y + a₁x + a₃)² = Ψ₂Sq(x)` at a point of `W` (`ψ_sq_evalEval`), the whole verification collapses
to a single univariate identity in `x` — the analogue of `preΨ₄_sq` — closed by `ring` after
substituting the `bᵢ`-relation `4b₈ = b₂b₆ − b₄²`.

Concretely: over a field of characteristic `≠ 2`, for a point `(x, y)` on `W` with `ψ₃(x, y) ≠ 0`
(i.e. `P` is not `3`-torsion), the point `(Φ₃(x)/Ψ₃(x)², ω₃(x,y)/ψ₃(x,y)³)` lies on `W`, where
`ω₃(x,y) = ((2y + a₁x + a₃)·(preΨ₅(x) − preΨ₄(x)²) − a₁·Φ₃(x)·ψ₃(x,y) − a₃·ψ₃(x,y)³) / 2`
is the value of the `3`-division `y`-coordinate polynomial.

Note that this is a purely *algebraic* on-curve identity for the classical division-polynomial
tripling coordinates; identifying `(Φ₃/Ψ₃², ω₃/ψ₃³)` with the group-law triple `3 • P` (which then
makes the on-curve property automatic) is a separate, harder statement not proved here.

## Main statements

* `WeierstrassCurve.preΨ_five`: the closed form `preΨ₅ = preΨ₄·Ψ₂Sq² − Ψ₃³`.
* `WeierstrassCurve.Affine.tripling_equation`: the division-polynomial tripling point lies on the
  curve.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The closed form of the auxiliary `5`-division polynomial `preΨ₅ = preΨ₄·Ψ₂Sq² − Ψ₃³`, obtained
from the odd recurrence for `preΨ'`. -/
lemma preΨ_five : W.preΨ 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  have H := W.preΨ'_odd 0
  norm_num [preΨ'_four, preΨ'_two, preΨ'_one, preΨ'_three] at H
  rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, preΨ_ofNat]; exact H

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
-- The on-curve verification clears the `ψ₃`-denominators and normalises a degree-`27` univariate
-- division-polynomial identity in `x`, which needs a raised heartbeat and recursion-depth limit.
/-- **The tripling point lies on the curve.** For a point `(x, y)` on `W` over a field of
characteristic `≠ 2`, with `ψ₃(x, y) ≠ 0` (i.e. `(x, y)` is not `3`-torsion), the point
`[3](x, y) = (Φ₃(x)/Ψ₃(x)², ω₃(x,y)/ψ₃(x,y)³)` satisfies the Weierstrass equation, where the
`3`-division `y`-coordinate value is
`ω₃(x,y) = ((2y + a₁x + a₃)·(preΨ₅(x) − preΨ₄(x)²) − a₁·Φ₃(x)·ψ₃(x,y) − a₃·ψ₃(x,y)³) / 2`.

This is the crux on-curve identity consumed by the multiplication-by-`3` function-field pullback. -/
theorem tripling_equation (h : W.Equation x y) (h2 : (2 : F) ≠ 0)
    (hψ : (W.ψ 3).evalEval x y ≠ 0) :
    W.Equation ((W.Φ 3).eval x / (W.ΨSq 3).eval x)
      (((2 * y + W.a₁ * x + W.a₃) * ((W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2) -
          W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y -
          W.a₃ * (W.ψ 3).evalEval x y ^ 3) /
        (2 * (W.ψ 3).evalEval x y ^ 3)) := by
  rw [equation_iff]
  set s := (W.ψ 3).evalEval x y with hs_def
  set Φv := (W.Φ 3).eval x with hΦ_def
  set Kv := (W.preΨ 5).eval x - W.preΨ₄.eval x ^ 2 with hK_def
  have hsne : s ≠ 0 := hψ
  -- `s = Ψ₃(x)`, so `s² = ΨSq₃(x)`.
  have hsΨ : s = W.Ψ₃.eval x := by rw [hs_def, ψ_evalEval h 3, Ψ_three, evalEval_C]
  rw [show (W.ΨSq 3).eval x = s ^ 2 from (ψ_sq_evalEval h 3).symm]
  set X' := Φv / s ^ 2 with hX'
  set Y' := ((2 * y + W.a₁ * x + W.a₃) * Kv - W.a₁ * Φv * s - W.a₃ * s ^ 3) / (2 * s ^ 3) with hY'
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  -- The `b`-relation at the point `(x, y)`.
  have hb : (2 * y + W.a₁ * x + W.a₃) ^ 2 = W.Ψ₂Sq.eval x := by
    have H := ψ_sq_evalEval h 2
    rwa [ψ_two_evalEval, ΨSq_two] at H
  -- The univariate tripling identity, evaluated at `x` and expressed via `s`.
  have hstar : W.Ψ₂Sq.eval x * Kv ^ 2 =
      4 * Φv ^ 3 + W.b₂ * Φv ^ 2 * s ^ 2 + 2 * W.b₄ * Φv * s ^ 4 + W.b₆ * s ^ 6 := by
    have hb8 : W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4 := by
      rw [eq_div_iff h4]; linear_combination W.b_relation
    rw [hK_def, hΦ_def, hsΨ]
    simp only [preΨ_five, Φ_three, Ψ₃, preΨ₄, Ψ₂Sq, eval_mul, eval_add, eval_sub, eval_pow,
      eval_ofNat, eval_C, eval_X]
    rw [hb8]; field_simp; ring
  -- The `ψ₂`-value of the tripled point.
  have hlin : 2 * Y' + W.a₁ * X' + W.a₃ = (2 * y + W.a₁ * x + W.a₃) * Kv / s ^ 3 := by
    rw [hY', hX']
    field_simp
    ring
  -- The on-curve `b`-relation for the tripled point.
  have hmain : (2 * Y' + W.a₁ * X' + W.a₃) ^ 2 =
      4 * X' ^ 3 + W.b₂ * X' ^ 2 + 2 * W.b₄ * X' + W.b₆ := by
    rw [hlin, div_pow, mul_pow, hb, hstar, hX']
    field_simp
  -- Deduce the Weierstrass equation from the `b`-relation (characteristic `≠ 2`).
  rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hmain
  refine mul_left_cancel₀ h4 ?_
  linear_combination hmain

end Affine

end WeierstrassCurve
