/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.XDifference

/-!
# The collinearity identity for the division polynomials

`EllipticCurves.Torsion.XDifference` reads the `r = 1` slice of Ward's relation as the
`x`-difference identity.  This file reads **one instance of the full elliptic-net relation** — the
`s ≠ 0` layer, available since `WeierstrassCurve.Affine.ψ_isEllipticNet` of
`EllipticCurves.Torsion.WardHalving` — as the companion identity for the `y`-coordinate.

`IsEllipticNet.rel W p (p + q) (p - q) q = 0`, with the indices normalised and oddness applied, is

```
W_{2q}·W_{2p+q}·W_p·W_{p+q} = W_q·(W_{2p}·W_{p+2q}·W_{p+q} + W_{2p+2q}·W_p·W_{p-q}),
```

and putting `u = p`, `v = q`, `w = -p - q` makes it **cyclic in three indices summing to zero**:

```
W_{2u}·W_{v-w}·W_v·W_w + W_{2v}·W_{w-u}·W_w·W_u + W_{2w}·W_{u-v}·W_u·W_v = 0,   u + v + w = 0.
```

## What the cyclic form says

Write `Xₙ := Φₙ/ΨSqₙ` for the division-polynomial `x`-coordinate and `Sₙ := ψ_{2n}/ΨSqₙ²` for the
division-polynomial **completed** `y`-coordinate — `S` is the `2Y + a₁X + a₃` of the completed
square `(2Y + a₁X + a₃)² = 4X³ + b₂X² + 2b₄X + b₆`, not `Y` itself.  Multiplying the cyclic identity
by `ψ_u·ψ_v·ψ_w/(ΨSq_u²·ΨSq_v²·ΨSq_w²)` and folding in the `x`-difference identity turns it into

```
S_u·(X_v - X_w) + S_v·(X_w - X_u) + S_w·(X_u - X_v) = 0,
```

which is `WeierstrassCurve.Affine.collinear_div` below.  That is the vanishing of the `3 × 3`
determinant with rows `(1, Xₙ, Sₙ)`, i.e. **the three points `(X_u, S_u)`, `(X_v, S_v)`,
`(X_w, S_w)` are collinear whenever `u + v + w = 0`** — one half of the Weierstrass group law, here
a corollary of Ward's theorem alone, with no curve equation among the hypotheses of the abstract
form.

⚠️ **`Xₙ` and `Sₙ` are the division-polynomial coordinates, not `x(n • P)` and `y(n • P)`.**  The
identification is `WeierstrassCurve.Affine.HasXCoordFormula` — issue `#251` — and holds in this
tree only at `n = 2` and `n = 3`.  As in `EllipticCurves.Torsion.XDifference`, everything below is
a statement about polynomials and their values, never about `n • P`.

⚠️ This file's only import is `EllipticCurves.Torsion.XDifference`, and its closure is the 7
modules that one drags in.  `EllipticCurves.Torsion.NsmulSurjective` (where `HasXCoordFormula`
lives), `EllipticCurves.Torsion.OmegaOnCurve` (where `HasΨSqDoubling` does) and
`EllipticCurves.Torsion.NormEDSHomogeneous` are each **import-incomparable** with this file —
measured over all 387 project modules, none of the three is in this file's closure and this file is
in none of theirs — so those three names are cited here and used nowhere below.  The only module
whose closure contains this file and any of them is the root aggregator `EllipticCurves`, which is
also this file's only direct importer.

## ⚠️ What this does and does not give `#404`'s crux

The Weierstrass group law has two halves.  Collinearity is one; the other is the Vieta relation

```
X_u + X_v + X_w = (λ² - b₂)/4,      λ := (S_u - S_v)/(X_u - X_v),
```

which says the three collinear points are the *three* intersections of that line with the curve.
`#404`'s crux `WeierstrassCurve.HasΨSqDoubling` — `ΨSq₂ₙ = ΨSqₙ·(4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² +
b₆ΨSqₙ³)`, equivalently `Sₙ² = 4Xₙ³ + b₂Xₙ² + 2b₄Xₙ + b₆` at a point *of the curve* where
`ΨSqₙ ≠ 0` (the curve equation is what turns `ψ_{2n}²` into `ΨSq_{2n}`) — is the on-curve
statement, and it is the Vieta half that is missing **here**.

⚠️ **It is no longer missing, and this file is what supplied the other half.**
`EllipticCurves.Torsion.NetVieta` proves that the Vieta defect `4(X_u+X_v+X_w) + b₂ - λ²` is the
*same for every triple* — one further instance of the same `s ≠ 0` relation, at
`(p, q, r, s) = (n-1, n-2, n, 1)` — so three base cases pin it to `0`, and
`EllipticCurves.Torsion.OmegaCrux` cashes that out as `WeierstrassCurve.hasΨSqDoubling`.
`cyclic_two_mul_eq_zero` below is the collinear half that proof consumes.

⚠️ **That split is measured, not proved here, and nothing below is conditional on it.**  The
measurement: in the free model `W = normEDS b c d` over `𝔽_p`, `p = 2⁶¹ - 1`, with `x, b₂, b₄, b, c,
d` random and `b₆ := b² - 4x³ - b₂x² - 2b₄x` (which forces the crux at `n = 1` and nothing else),
the collinearity identity holds at all 18 index pairs tried across three parameter seeds while the
Vieta relation fails at every one of the same 18, and both hold at all of them once `c` and `d` are
replaced by `Ψ₃(x)` and `preΨ₄(x)`.  So the free model separates the two halves, and only the
collinear half is a Ward consequence.

## Main statements

* `IsEllipticNet.mul_two_mul_eq_of_rel` : the identity for an abstract odd sequence, from a
  **single** instance of the elliptic-net relator.  No curve, no `IsEllipticNet` hypothesis.
* `IsEllipticNet.cyclic_two_mul_eq_zero` : its cyclic form at three indices summing to zero.
* `WeierstrassCurve.normEDS_cyclic_two_mul_eq_zero` : the cyclic form for `normEDS b c d`,
  unconditionally, over an arbitrary `CommRing`.
* `WeierstrassCurve.normEDS_cyclic_two_mul_witness` : a witness that the identity is not an
  identity between three zeros — at `(b, c, d) = (1, 2, 3)` over `ℤ` and `(u, v, w) = (3, 1, -4)`
  the three summands are `-420`, `-402` and `822`.
* `WeierstrassCurve.Affine.ψ_cyclic_two_mul_eq_zero`,
  `WeierstrassCurve.Affine.ψ_cyclic_two_mul_evalEval_eq_zero` : the same for the division
  polynomials `W.ψ` in `R[X][Y]`, and for their values at an affine point.
* `WeierstrassCurve.Affine.collinear_div` : the collinearity determinant in quotient form over a
  field.

## References

* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).
* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.2 and Exercise 3.7.
-/

open Polynomial Polynomial.Bivariate

namespace IsEllipticNet

variable {R : Type*} [CommRing R]

/-- **The `y`-companion of the `x`-difference identity, for an abstract odd sequence.**  A single
instance of the elliptic-net relator — at `(p, q, r, s) = (p, p + q, p - q, q)`, so genuinely from
the `s ≠ 0` layer — together with oddness gives

```
W_{2q}·W_{2p+q}·W_p·W_{p+q} = W_q·(W_{2p}·W_{p+2q}·W_{p+q} + W_{2p+2q}·W_p·W_{p-q}).
```

⚠️ The hypothesis is the relator at that **one** quadruple, not `IsEllipticNet W`: nothing here is
an induction, and no other index is touched. -/
theorem mul_two_mul_eq_of_rel {W : ℤ → R} (odd : Function.Odd W) {p q : ℤ}
    (h : rel W p (p + q) (p - q) q = 0) :
    W (2 * q) * W (2 * p + q) * W p * W (p + q)
      = W q * (W (2 * p) * W (p + 2 * q) * W (p + q)
        + W (2 * p + 2 * q) * W p * W (p - q)) := by
  simp only [rel] at h
  rw [show p + (p + q) + q = 2 * p + 2 * q from by ring, show p - (p + q) = -q from by ring,
    show p - q + q = p from by ring, show p + (p - q) + q = 2 * p from by ring,
    show p - (p - q) = q from by ring, show p + q + q = p + 2 * q from by ring,
    show p + q + (p - q) + q = 2 * p + q from by ring,
    show p + q - (p - q) = 2 * q from by ring, odd q] at h
  linear_combination h

/-- **The collinearity identity of an elliptic net.**  At any three indices summing to zero,

```
W_{2u}·W_{v-w}·W_v·W_w + W_{2v}·W_{w-u}·W_w·W_u + W_{2w}·W_{u-v}·W_u·W_v = 0.
```

Cyclic in `(u, v, w)` by construction, and — see the module docstring — the vanishing of the
collinearity determinant of the three points `(Φₙ/ΨSqₙ, ψ_{2n}/ΨSqₙ²)`. -/
theorem cyclic_two_mul_eq_zero {W : ℤ → R} (odd : Function.Odd W) (h : IsEllipticNet W)
    {u v w : ℤ} (huvw : u + v + w = 0) :
    W (2 * u) * W (v - w) * W v * W w + W (2 * v) * W (w - u) * W w * W u
      + W (2 * w) * W (u - v) * W u * W v = 0 := by
  have hw : w = -u - v := by omega
  subst hw
  have key := mul_two_mul_eq_of_rel odd (h u (u + v) (u - v) v)
  rw [show v - (-u - v) = u + 2 * v from by ring, show -u - v - u = -(2 * u + v) from by ring,
    show 2 * (-u - v) = -(2 * u + 2 * v) from by ring, show -u - v = -(u + v) from by ring,
    odd (2 * u + v), odd (2 * u + 2 * v), odd (u + v)]
  linear_combination key

end IsEllipticNet

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- **The collinearity identity for `normEDS b c d`**, unconditionally, over an arbitrary
commutative ring: `normEDS b c d` is an elliptic net by `WeierstrassCurve.normEDS_isEllipticNet`
and odd by Mathlib's `normEDS_neg`. -/
theorem normEDS_cyclic_two_mul_eq_zero (b c d : R) {u v w : ℤ} (huvw : u + v + w = 0) :
    normEDS b c d (2 * u) * normEDS b c d (v - w) * normEDS b c d v * normEDS b c d w
      + normEDS b c d (2 * v) * normEDS b c d (w - u) * normEDS b c d w * normEDS b c d u
      + normEDS b c d (2 * w) * normEDS b c d (u - v) * normEDS b c d u * normEDS b c d v = 0 :=
  IsEllipticNet.cyclic_two_mul_eq_zero (fun n => normEDS_neg b c d n)
    (normEDS_isEllipticNet b c d) huvw

/-! ### A witness that the three summands are not separately zero -/

/-- `normEDS 1 2 3 5 = -5` over `ℤ`, from `normEDS_odd` at `m = 2`. -/
private lemma normEDS_one_two_three_five : normEDS (1 : ℤ) 2 3 5 = -5 := by
  have h := normEDS_odd (1 : ℤ) 2 3 2
  norm_num [normEDS_one, normEDS_two, normEDS_three, normEDS_four] at h
  exact h

/-- `normEDS 1 2 3 6 = -28` over `ℤ`, from `normEDS_even` at `m = 3`. -/
private lemma normEDS_one_two_three_six : normEDS (1 : ℤ) 2 3 6 = -28 := by
  have h := normEDS_even (1 : ℤ) 2 3 3
  norm_num [normEDS_one, normEDS_two, normEDS_three, normEDS_four,
    normEDS_one_two_three_five] at h
  exact h

/-- `normEDS 1 2 3 7 = -67` over `ℤ`, from `normEDS_odd` at `m = 3`. -/
private lemma normEDS_one_two_three_seven : normEDS (1 : ℤ) 2 3 7 = -67 := by
  have h := normEDS_odd (1 : ℤ) 2 3 3
  norm_num [normEDS_two, normEDS_three, normEDS_four, normEDS_one_two_three_five] at h
  exact h

/-- `normEDS 1 2 3 8 = -411` over `ℤ`, from `normEDS_even` at `m = 4`. -/
private lemma normEDS_one_two_three_eight : normEDS (1 : ℤ) 2 3 8 = -411 := by
  have h := normEDS_even (1 : ℤ) 2 3 4
  norm_num [normEDS_two, normEDS_three, normEDS_four, normEDS_one_two_three_five,
    normEDS_one_two_three_six] at h
  exact h

/-- **The collinearity identity is not an identity between three zeros.**  At `(b, c, d) = (1, 2,
3)` over `ℤ` and `(u, v, w) = (3, 1, -4)` the three summands of
`WeierstrassCurve.normEDS_cyclic_two_mul_eq_zero` are `-420`, `-402` and `822`; they are each
nonzero and they cancel.

⚠️ Stated because the sibling `IsEllipticNet.rel_normEDS_homogeneous` of
`EllipticCurves.Torsion.NormEDSHomogeneous` is, on this tree, an identity between two zeros, and
the difference is not visible from the statement of either.  That module is import-incomparable
with this one; see the module docstring. -/
theorem normEDS_cyclic_two_mul_witness :
    normEDS (1 : ℤ) 2 3 (2 * 3) * normEDS 1 2 3 (1 - -4) * normEDS 1 2 3 1 * normEDS 1 2 3 (-4)
        = -420 ∧
      normEDS (1 : ℤ) 2 3 (2 * 1) * normEDS 1 2 3 (-4 - 3) * normEDS 1 2 3 (-4) * normEDS 1 2 3 3
        = -402 ∧
      normEDS (1 : ℤ) 2 3 (2 * -4) * normEDS 1 2 3 (3 - 1) * normEDS 1 2 3 3 * normEDS 1 2 3 1
        = 822 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [show (2 : ℤ) * 3 = 6 by norm_num, show (1 : ℤ) - -4 = 5 by norm_num,
      show (-4 : ℤ) - 3 = -7 by norm_num, show (2 : ℤ) * -4 = -8 by norm_num,
      show (3 : ℤ) - 1 = 2 by norm_num, show (-4 : ℤ) = -(4 : ℤ) by norm_num,
      show (-7 : ℤ) = -(7 : ℤ) by norm_num, show (-8 : ℤ) = -(8 : ℤ) by norm_num, normEDS_neg,
      normEDS_one, normEDS_two, normEDS_three, normEDS_four, normEDS_one_two_three_five,
      normEDS_one_two_three_six, normEDS_one_two_three_seven, normEDS_one_two_three_eight]

namespace Affine

variable (W : Affine R)

/-- **The collinearity identity for the division polynomials**, in `R[X][Y]`. -/
theorem ψ_cyclic_two_mul_eq_zero {u v w : ℤ} (huvw : u + v + w = 0) :
    W.ψ (2 * u) * W.ψ (v - w) * W.ψ v * W.ψ w + W.ψ (2 * v) * W.ψ (w - u) * W.ψ w * W.ψ u
      + W.ψ (2 * w) * W.ψ (u - v) * W.ψ u * W.ψ v = 0 :=
  IsEllipticNet.cyclic_two_mul_eq_zero (fun n => W.ψ_neg n) W.ψ_isEllipticNet huvw

variable {W} {x y : R}

/-- **The collinearity identity among the point-values `ψₙ(x, y)`.**  ⚠️ No hypothesis on `(x, y)`:
the identity is an identity in `R[X][Y]` and evaluation is a ring homomorphism, so unlike
`WeierstrassCurve.Affine.ψ_add_mul_ψ_sub_evalEval` it does not need `W.Equation x y`.  The curve
equation enters only in `WeierstrassCurve.Affine.collinear_div`, which trades `ψₙ²` for `ΨSqₙ`. -/
theorem ψ_cyclic_two_mul_evalEval_eq_zero {u v w : ℤ} (huvw : u + v + w = 0) :
    (W.ψ (2 * u)).evalEval x y * (W.ψ (v - w)).evalEval x y * (W.ψ v).evalEval x y
        * (W.ψ w).evalEval x y
      + (W.ψ (2 * v)).evalEval x y * (W.ψ (w - u)).evalEval x y * (W.ψ w).evalEval x y
        * (W.ψ u).evalEval x y
      + (W.ψ (2 * w)).evalEval x y * (W.ψ (u - v)).evalEval x y * (W.ψ u).evalEval x y
        * (W.ψ v).evalEval x y = 0 :=
  IsEllipticNet.cyclic_two_mul_eq_zero (W := fun n => (W.ψ n).evalEval x y)
    (fun n => by simp only [ψ_neg, evalEval_neg]) W.ψ_isEllipticNet_evalEval huvw

section Field

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **The three division-polynomial points at indices summing to zero are collinear.**  Over a
field, at a point `(x, y)` of `W` where none of `ΨSq_u`, `ΨSq_v`, `ΨSq_w` vanishes,

```
S_u·(X_v - X_w) + S_v·(X_w - X_u) + S_w·(X_u - X_v) = 0,
```

with `Xₙ = Φₙ(x)/ΨSqₙ(x)` and `Sₙ = ψ_{2n}(x, y)/ΨSqₙ(x)²`.  This is the vanishing of the `3 × 3`
determinant with rows `(1, Xₙ, Sₙ)`.

⚠️ It is a statement about the division polynomials, **not** about `u • P`, `v • P`, `w • P`; see
the module docstring.  ⚠️ It is also only the *collinear* half of the group law — the Vieta half,
which is `#404`'s crux, is not proved here and nothing here is conditional on it.  It is proved in
`EllipticCurves.Torsion.OmegaCrux`, from this lemma. -/
theorem collinear_div (h : W.Equation x y) {u v w : ℤ} (huvw : u + v + w = 0)
    (hu : (W.ΨSq u).eval x ≠ 0) (hv : (W.ΨSq v).eval x ≠ 0) (hw : (W.ΨSq w).eval x ≠ 0) :
    (W.ψ (2 * u)).evalEval x y / (W.ΨSq u).eval x ^ 2
        * ((W.Φ v).eval x / (W.ΨSq v).eval x - (W.Φ w).eval x / (W.ΨSq w).eval x)
      + (W.ψ (2 * v)).evalEval x y / (W.ΨSq v).eval x ^ 2
        * ((W.Φ w).eval x / (W.ΨSq w).eval x - (W.Φ u).eval x / (W.ΨSq u).eval x)
      + (W.ψ (2 * w)).evalEval x y / (W.ΨSq w).eval x ^ 2
        * ((W.Φ u).eval x / (W.ΨSq u).eval x - (W.Φ v).eval x / (W.ΨSq v).eval x) = 0 := by
  have e1 : (W.Φ v).eval x / (W.ΨSq v).eval x - (W.Φ w).eval x / (W.ΨSq w).eval x
      = (W.ψ u).evalEval x y * (W.ψ (v - w)).evalEval x y
          / ((W.ΨSq v).eval x * (W.ΨSq w).eval x) := by
    rw [Φ_div_ΨSq_sub_Φ_div_ΨSq h hw hv, show w + v = -u from by omega,
      show w - v = -(v - w) from by ring, ψ_neg, ψ_neg, evalEval_neg, evalEval_neg]
    ring
  have e2 : (W.Φ w).eval x / (W.ΨSq w).eval x - (W.Φ u).eval x / (W.ΨSq u).eval x
      = (W.ψ v).evalEval x y * (W.ψ (w - u)).evalEval x y
          / ((W.ΨSq w).eval x * (W.ΨSq u).eval x) := by
    rw [Φ_div_ΨSq_sub_Φ_div_ΨSq h hu hw, show u + w = -v from by omega,
      show u - w = -(w - u) from by ring, ψ_neg, ψ_neg, evalEval_neg, evalEval_neg]
    ring
  have e3 : (W.Φ u).eval x / (W.ΨSq u).eval x - (W.Φ v).eval x / (W.ΨSq v).eval x
      = (W.ψ w).evalEval x y * (W.ψ (u - v)).evalEval x y
          / ((W.ΨSq u).eval x * (W.ΨSq v).eval x) := by
    rw [Φ_div_ΨSq_sub_Φ_div_ΨSq h hv hu, show v + u = -w from by omega,
      show v - u = -(u - v) from by ring, ψ_neg, ψ_neg, evalEval_neg, evalEval_neg]
    ring
  have key := ψ_cyclic_two_mul_evalEval_eq_zero (W := W) (x := x) (y := y) huvw
  have hu' : (W.ψ u).evalEval x y ≠ 0 := fun hc => hu (by rw [← ψ_sq_evalEval h u, hc]; ring)
  have hv' : (W.ψ v).evalEval x y ≠ 0 := fun hc => hv (by rw [← ψ_sq_evalEval h v, hc]; ring)
  have hw' : (W.ψ w).evalEval x y ≠ 0 := fun hc => hw (by rw [← ψ_sq_evalEval h w, hc]; ring)
  rw [e1, e2, e3, ← ψ_sq_evalEval h u, ← ψ_sq_evalEval h v, ← ψ_sq_evalEval h w]
  set a := (W.ψ u).evalEval x y
  set b := (W.ψ v).evalEval x y
  set c := (W.ψ w).evalEval x y
  set A := (W.ψ (2 * u)).evalEval x y
  set B := (W.ψ (2 * v)).evalEval x y
  set C := (W.ψ (2 * w)).evalEval x y
  set P := (W.ψ (v - w)).evalEval x y
  set Q := (W.ψ (w - u)).evalEval x y
  set S := (W.ψ (u - v)).evalEval x y
  field_simp
  linear_combination key

end Field

end Affine

end WeierstrassCurve
