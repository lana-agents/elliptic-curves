/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.EllipticNetRel

/-!
# Ward's theorem, the `r = 1` slice: the elliptic addition formula for `normEDS`

For the canonical normalised elliptic divisibility sequence `W = normEDS b c d` over a `CommRing R`,
we prove the `r = 1` slice of the elliptic-net relation

```
IsEllipticNet.rel W p q 1 0 = 0    for all p q : ℤ,
```

which, using `W 1 = 1`, is exactly the **elliptic addition formula** of Ward (1948),

```
W (p + q) * W (p - q) = W (p + 1) * W (p - 1) * W q ^ 2 - W (q + 1) * W (q - 1) * W p ^ 2 .
```

The base cases (`p - q ∈ {1, 2}`) are the two-term recurrences packaged in
`EllipticCurves/Torsion/EllipticNetRel.lean` as `normEDS_rel_odd` and `normEDS_rel_even`. This file
records the symmetry reductions of the relator, the trivial `q ∈ {0, 1}` slices, and — the main
result — the full `∀ p q` statement (Ward's theorem for `r = 1`), together with its specialisation
to the division polynomials `W.ψ` and their point-values.

## Main statements

* `normEDS_rel_one` : `IsEllipticNet.rel (normEDS b c d) p q 1 0 = 0` for all `p q : ℤ`.
* `WeierstrassCurve.Affine.ψ_rel_one`,  `ψ_rel_one_evalEval` : the specialisations to `W.ψ`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.4 (Exercise 3.7).
* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace IsEllipticNet

variable {R : Type*} [CommRing R] (W : ℤ → R)

/-! ### Symmetries of the `r = 1`, `s = 0` relator -/

/-- The relator `rel W p q 1 0` is even in its first argument. -/
lemma rel_one_neg_left (odd : W.Odd) (p q : ℤ) : rel W (-p) q 1 0 = rel W p q 1 0 := by
  simp only [rel, add_zero]
  rw [show -p + q = -(p - q) by ring, show -p - q = -(p + q) by ring,
    show -p + 1 = -(p - 1) by ring, show -p - 1 = -(p + 1) by ring,
    odd (p - q), odd (p + q), odd (p - 1), odd (p + 1), odd p]
  ring

/-- The relator `rel W p q 1 0` is even in its second argument. -/
lemma rel_one_neg_right (odd : W.Odd) (p q : ℤ) : rel W p (-q) 1 0 = rel W p q 1 0 := by
  simp only [rel, add_zero]
  rw [show p + -q = p - q by ring, show p - -q = p + q by ring, show -q + 1 = -(q - 1) by ring,
    show -q - 1 = -(q + 1) by ring, odd (q - 1), odd (q + 1), odd q]
  ring

/-- The relator `rel W p q 1 0` is antisymmetric under swapping its two arguments. -/
lemma rel_one_swap (odd : W.Odd) (p q : ℤ) : rel W q p 1 0 = -rel W p q 1 0 := by
  simp only [rel, add_zero]
  rw [show q + p = p + q by ring, show q - p = -(p - q) by ring, odd (p - q)]
  ring

end IsEllipticNet

/-! ### Ward's theorem for `normEDS`, the `r = 1` slice -/

namespace WeierstrassCurve

section NormEDS

variable {R : Type*} [CommRing R] (b c d : R)

/-- Oddness of the canonical normalised EDS as a `Function.Odd` fact. -/
lemma normEDS_odd_fun : (normEDS b c d).Odd := fun n => normEDS_neg b c d n

/-- The `q = 0` slice of Ward's `r = 1` relation vanishes: `rel (normEDS b c d) p 0 1 0 = 0`. -/
lemma normEDS_rel_one_zero (p : ℤ) : IsEllipticNet.rel (normEDS b c d) p 0 1 0 = 0 := by
  have h : normEDS b c d (-1) = -1 := by rw [normEDS_neg, normEDS_one]
  simp only [IsEllipticNet.rel, add_zero, sub_zero, zero_add, zero_sub, normEDS_zero, normEDS_one,
    h]
  ring

/-- The `q = 1` slice of Ward's `r = 1` relation vanishes: `rel (normEDS b c d) p 1 1 0 = 0`. -/
lemma normEDS_rel_one_one (p : ℤ) : IsEllipticNet.rel (normEDS b c d) p 1 1 0 = 0 := by
  simp only [IsEllipticNet.rel, add_zero]
  rw [show (1 : ℤ) - 1 = 0 by ring, normEDS_zero]
  ring

/-- **Ward's theorem, the `r = 1` slice** (the elliptic addition formula): for the canonical
normalised elliptic divisibility sequence `W = normEDS b c d`, the elliptic-net relator
`rel W p q 1 0` vanishes for all `p q : ℤ`. Equivalently (using `W 1 = 1`),
`W (p + q) * W (p - q) = W (p + 1) * W (p - 1) * W q ^ 2 - W (q + 1) * W (q - 1) * W p ^ 2`. -/
theorem normEDS_rel_one (p q : ℤ) : IsEllipticNet.rel (normEDS b c d) p q 1 0 = 0 := by
  sorry

end NormEDS

end WeierstrassCurve

/-! ### Specialisation to the division polynomials `W.ψ` -/

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (W : Affine R)

/-- Ward's `r = 1` relation for the division polynomials `W.ψ`, as an identity in `R[X][Y]`:
`rel W.ψ p q 1 0 = 0`. -/
theorem ψ_rel_one (p q : ℤ) : IsEllipticNet.rel W.ψ p q 1 0 = 0 :=
  WeierstrassCurve.normEDS_rel_one W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) p q

variable {x y : R}

/-- Ward's `r = 1` relation among the point-values of the division polynomials at an affine point
`(x, y)` of `W`: `rel (fun n ↦ (W.ψ n).evalEval x y) p q 1 0 = 0`. -/
theorem ψ_rel_one_evalEval (p q : ℤ) :
    IsEllipticNet.rel (fun n ↦ (W.ψ n).evalEval x y) p q 1 0 = 0 := by
  have h := IsEllipticNet.map_rel W.ψ (evalEvalRingHom x y) p q 1 0
  rw [ψ_rel_one, map_zero] at h
  exact h.symm

end WeierstrassCurve.Affine
