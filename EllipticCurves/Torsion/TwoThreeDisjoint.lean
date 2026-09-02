/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.DivisionPolynomial.Coprime
import EllipticCurves.Fixtures
import EllipticCurves.Torsion.DivisionPolynomialEval

/-!
# `E[2] ∩ E[3] = 0`, at a point

`EllipticCurves.DivisionPolynomial.Coprime` proves `IsCoprime W.Ψ₃ W.Ψ₂Sq` on an elliptic curve,
by a Bézout combination landing on `C (Δ²)`.  That is a statement about two polynomials in `R[X]`.
This file spends it at a *point*: on an elliptic curve, a nonzero affine point cannot have both
`ψ₂` and `ψ₃` vanish on it.

```
W.Equation x y   →   ψ₂(x, y) = 0   →   ψ₃(x, y) ≠ 0
```

## Why this is not the point-theoretic statement it looks like

⚠️ The obvious route — *"`ψ₂(P) = 0` says `2 • P = 0`, `ψ₃(P) = 0` says `3 • P = 0`, and
`gcd(2, 3) = 1` forces `P = 0`"* — is **circular here**, and the reason is worth recording.  The
`3`-torsion characterisation this tree owns, `WeierstrassCurve.Affine.mem_torsion_three_some_iff`
(`EllipticCurves.Torsion.ThreeTorsion`), carries the hypothesis `y ≠ W.negY x y`, which is exactly
`ψ₂(x, y) ≠ 0` — the thing that fails at the points in question.  So the group-theoretic reading is
unavailable precisely where it would be used, and the proof below goes through the polynomials
instead: a common root of `Ψ₂Sq` and `Ψ₃` is a common factor `X − C x`, which coprimality forbids.

## The hypotheses, and which of them are real

* `[W.IsElliptic]` is **load-bearing and not removable on this route**: the Bézout certificate lands
  on `C (Δ²)`, which is a unit exactly when `Δ` is.  ⚠️ The statement is genuinely false on a
  singular curve — a node or cusp is a common root of `Ψ₂Sq` and `Ψ₃`.
* `(2 : R) ≠ 0` is **not** needed, and is not assumed.  `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆` has leading
  coefficient `4`, so characteristic `2` degenerates it — but the coprimality is proved over an
  arbitrary commutative ring and characteristic `2` is not an exception to it.
* Only `W.Equation x y` is needed of the point, not `W.Nonsingular x y`: `ψ_sq_evalEval` asks for
  the equation alone.

## Main statements

* `WeierstrassCurve.eval_Ψ₃_ne_zero_of_eval_Ψ₂Sq_eq_zero` : the univariate form — at a root of
  `Ψ₂Sq`, `Ψ₃` does not vanish.
* `WeierstrassCurve.eval_ΨSq_three_ne_zero_of_eval_ΨSq_two_eq_zero` : the same in the `ΨSq`
  register, which is the one `ψ_sq_evalEval` lands in.
* `WeierstrassCurve.Affine.ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero` : the point form.
* `WeierstrassCurve.Affine.ψ_three_ne_zero_two_torsion_y2EqX3AddOne` : the non-vacuity certificate
  — a curve carrying an actual `2`-torsion point, at which `ψ₃` is computed and is nonzero.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [Nontrivial R] {W : WeierstrassCurve R} [W.IsElliptic]

/-- **At a root of `Ψ₂Sq`, the polynomial `Ψ₃` does not vanish.**  The pointwise reading of
`WeierstrassCurve.isCoprime_Ψ₃_Ψ₂Sq`: a common root would be a common factor `X − C x`, and
coprimality makes every common factor a unit. -/
theorem eval_Ψ₃_ne_zero_of_eval_Ψ₂Sq_eq_zero {x : R} (h : W.Ψ₂Sq.eval x = 0) :
    W.Ψ₃.eval x ≠ 0 := fun h₃ =>
  not_isUnit_X_sub_C x <|
    W.isCoprime_Ψ₃_Ψ₂Sq.isUnit_of_dvd' (dvd_iff_isRoot.mpr h₃) (dvd_iff_isRoot.mpr h)

/-- **The `ΨSq` form**, which is what a point-level consumer wants: `ΨSq 2 = Ψ₂Sq` and
`ΨSq 3 = Ψ₃²`, and `ψ_sq_evalEval` lands on `ΨSq` rather than on `Ψ`.

⚠️ This is *not* a corollary of `eval_Ψ₃_ne_zero_of_eval_Ψ₂Sq_eq_zero` over a general commutative
ring: `Ψ₃(x)² = 0` does not give `Ψ₃(x) = 0` without `NoZeroDivisors`.  It is instead the same
argument run on `IsCoprime (W.Ψ₃ ^ 2) W.Ψ₂Sq`, which coprimality supplies directly through
`IsCoprime.pow_left`. -/
theorem eval_ΨSq_three_ne_zero_of_eval_ΨSq_two_eq_zero {x : R} (h : (W.ΨSq 2).eval x = 0) :
    (W.ΨSq 3).eval x ≠ 0 := by
  rw [ΨSq_two] at h
  rw [ΨSq_three]
  exact fun h₃ =>
    not_isUnit_X_sub_C x <|
      (W.isCoprime_Ψ₃_Ψ₂Sq.pow_left (m := 2)).isUnit_of_dvd'
        (dvd_iff_isRoot.mpr h₃) (dvd_iff_isRoot.mpr h)

namespace Affine

variable {W : Affine R} [W.IsElliptic] {x y : R}

/-- **A point of an elliptic curve is not simultaneously `2`-torsion and `3`-torsion**, read off the
division polynomials: if `ψ₂(x, y) = 0` then `ψ₃(x, y) ≠ 0`.

⚠️ This is the quasi-periodicity constant `c = ψ_{d+1}·ψ_{d−1}` of the order dictionary at `d = 2`,
where it degenerates to `c = ψ₃·ψ₁ = ψ₃`.  The `d ≥ 3` argument obtains `c ≠ 0` from
`c·ψ_{d−2}² = −ψ₂²·ψ_{d−1}⁴`, which is vacuous at `d = 2` because `ψ_{d−2} = ψ₀ = 0`; this lemma is
what replaces it. -/
theorem ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero (h : W.Equation x y)
    (h₂ : (W.ψ 2).evalEval x y = 0) : (W.ψ 3).evalEval x y ≠ 0 := by
  intro h₃
  refine eval_ΨSq_three_ne_zero_of_eval_ΨSq_two_eq_zero (W := W) (x := x) ?_ ?_
  · rw [← ψ_sq_evalEval h, h₂]
    ring
  · rw [← ψ_sq_evalEval h, h₃]
    ring

/-! ## Non-vacuity: a curve with a `2`-torsion point at which `ψ₃` is computed -/

section Nonvacuity

open EllipticCurves.Fixture

/-- **The certificate.**  `(−1, 0)` lies on `y² = x³ + 1` over `ℚ` and is `2`-torsion —
`ψ₂(−1, 0) = 2y = 0` — so the hypothesis of
`WeierstrassCurve.Affine.ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero` is met by an actual
point rather than vacuously.  There `ψ₃ = Ψ₃(−1) = 3 − 12 = −9 ≠ 0`.

⚠️ Both conjuncts matter.  Without the first the statement would be compatible with there being no
`2`-torsion point at all; without the second the value of `ψ₃` would be asserted rather than
computed. -/
theorem ψ_three_ne_zero_two_torsion_y2EqX3AddOne :
    ((y2EqX3AddOne ℚ).ψ 2).evalEval (-1) 0 = 0 ∧
      ((y2EqX3AddOne ℚ).ψ 3).evalEval (-1) 0 = -9 := by
  constructor
  · rw [ψ_two_evalEval]; norm_num [y2EqX3AddOne]
  · rw [ψ_three, evalEval_C]
    norm_num [y2EqX3AddOne, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The main theorem, applied at that point.  ⚠️ This is what makes the certificate a statement
about `ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero` rather than about two numbers: the
`2`-torsion hypothesis is discharged by an actual point of an actual elliptic curve, and the
`[IsElliptic]` instance is found rather than assumed. -/
example : ((y2EqX3AddOne ℚ).ψ 3).evalEval (-1) 0 ≠ 0 :=
  ψ_three_evalEval_ne_zero_of_ψ_two_evalEval_eq_zero
    (by norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff])
    ψ_three_ne_zero_two_torsion_y2EqX3AddOne.1

end Nonvacuity

end Affine

end WeierstrassCurve
