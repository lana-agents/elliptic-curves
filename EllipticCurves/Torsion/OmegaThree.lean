/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.OmegaOnCurve

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

Both are instances of one general-`n` statement: `EllipticCurves.Torsion.OmegaOnCurve` writes the
`ψ₃`-denominator clearing and the passage from `(2Y + a₁X + a₃)² = 4X³ + b₂X² + 2b₄X + b₆` to the
Weierstrass equation once, at a general index, taking as its only index-dependent input the single
univariate identity `WeierstrassCurve.HasPreΩSqAt` — the analogue of `preΨ₄_sq`, closed by `ring`
after substituting the `bᵢ`-relation `4b₈ = b₂b₆ − b₄²`. At `n = 3` that input is
`WeierstrassCurve.Affine.hasPreΩSqAt_three`, and the theorem below is
`WeierstrassCurve.Affine.equation_of_hasPreΩSqAt` applied to it with the `n = 3` names unfolded.

Concretely: over a field of characteristic `≠ 2`, for a point `(x, y)` on `W` with `ψ₃(x, y) ≠ 0`
(i.e. `P` is not `3`-torsion), the point `(Φ₃(x)/Ψ₃(x)², ω₃(x,y)/ψ₃(x,y)³)` lies on `W`, where
`ω₃(x,y) = ((2y + a₁x + a₃)·(preΨ₅(x) − preΨ₄(x)²) − a₁·Φ₃(x)·ψ₃(x,y) − a₃·ψ₃(x,y)³) / 2`
is the value of the `3`-division `y`-coordinate polynomial.

Note that this is a purely *algebraic* on-curve identity for the classical division-polynomial
tripling coordinates; identifying `(Φ₃/Ψ₃², ω₃/ψ₃³)` with the group-law triple `3 • P` (which then
makes the on-curve property automatic) is a separate statement, not proved here but proved in
`EllipticCurves.Torsion.TriplingCoords`, which consumes `tripling_equation` below for the
nonsingularity of the tripled point.

## Main statements

* `WeierstrassCurve.Affine.tripling_equation`: the division-polynomial tripling point lies on the
  curve.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7, III.6.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

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
  have H := equation_of_hasPreΩSqAt (hasPreΩSqAt_three h2 x) h h2 hψ
  rw [if_neg (by decide : ¬Even (3 : ℤ)), preΩ_three, eval_sub, eval_pow] at H
  have hs : (W.ψ 3).evalEval x y ^ 2 = (W.ΨSq 3).eval x := ψ_sq_evalEval h 3
  have hrw : (W.ψ 3).evalEval x y * (W.a₁ * (W.Φ 3).eval x + W.a₃ * (W.ΨSq 3).eval x) =
      W.a₁ * (W.Φ 3).eval x * (W.ψ 3).evalEval x y + W.a₃ * (W.ψ 3).evalEval x y ^ 3 := by
    rw [← hs]; ring
  rwa [hrw, ← sub_sub] at H

end Affine

end WeierstrassCurve
