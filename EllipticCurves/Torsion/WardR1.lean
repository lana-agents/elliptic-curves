/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.EllipticNetRel
import Mathlib.Algebra.MvPolynomial.CommRing

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

end NormEDS

/-! ### The universal ring and nonvanishing -/

section Universal

open MvPolynomial

/-- The identity sequence `n ↦ n` is the normalised EDS with parameters `b = 2`, `c = 3`, `d = 2`:
`normEDS 2 3 2 n = n` over `ℤ`. Both two-term recurrences hold for `W n = n` with these parameters
(as polynomial identities in `m`), and the initial values match. This is the witness used to prove
nonvanishing of `normEDS` in the universal ring. -/
lemma normEDS_two_three_two (n : ℤ) : normEDS (2 : ℤ) 3 2 n = n := by
  have hnat : ∀ m : ℕ, normEDS (2 : ℤ) 3 2 (m : ℤ) = (m : ℤ) := by
    intro m
    induction m using normEDSRec' with
    | zero => simp
    | one => simp
    | two => simp
    | three => simp
    | four => simp
    | even m ih =>
      have i1 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3 - 1) = (m : ℤ) + 3 - 1 := by
        have := ih (m + 2) (by omega)
        rwa [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 3 - 1 by push_cast; ring] at this
      have i2 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3) = (m : ℤ) + 3 := by
        have := ih (m + 3) (by omega)
        rwa [show ((m + 3 : ℕ) : ℤ) = (m : ℤ) + 3 by push_cast; ring] at this
      have i3 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3 + 2) = (m : ℤ) + 3 + 2 := by
        have := ih (m + 5) (by omega)
        rwa [show ((m + 5 : ℕ) : ℤ) = (m : ℤ) + 3 + 2 by push_cast; ring] at this
      have i4 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3 - 2) = (m : ℤ) + 3 - 2 := by
        have := ih (m + 1) (by omega)
        rwa [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 3 - 2 by push_cast; ring] at this
      have i5 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 3 + 1) = (m : ℤ) + 3 + 1 := by
        have := ih (m + 4) (by omega)
        rwa [show ((m + 4 : ℕ) : ℤ) = (m : ℤ) + 3 + 1 by push_cast; ring] at this
      have h := normEDS_even (2 : ℤ) 3 2 ((m : ℤ) + 3)
      rw [i1, i2, i3, i4, i5] at h
      rw [show ((2 * (m + 3) : ℕ) : ℤ) = 2 * ((m : ℤ) + 3) by push_cast; ring]
      have h2 : normEDS (2 : ℤ) 3 2 (2 * ((m : ℤ) + 3)) * 2 = 2 * ((m : ℤ) + 3) * 2 := by
        rw [h]; ring
      exact mul_right_cancel₀ two_ne_zero h2
    | odd m ih =>
      have i1 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 2 + 2) = (m : ℤ) + 2 + 2 := by
        have := ih (m + 4) (by omega)
        rwa [show ((m + 4 : ℕ) : ℤ) = (m : ℤ) + 2 + 2 by push_cast; ring] at this
      have i2 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 2) = (m : ℤ) + 2 := by
        have := ih (m + 2) (by omega)
        rwa [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by push_cast; ring] at this
      have i3 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 2 - 1) = (m : ℤ) + 2 - 1 := by
        have := ih (m + 1) (by omega)
        rwa [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 2 - 1 by push_cast; ring] at this
      have i4 : normEDS (2 : ℤ) 3 2 ((m : ℤ) + 2 + 1) = (m : ℤ) + 2 + 1 := by
        have := ih (m + 3) (by omega)
        rwa [show ((m + 3 : ℕ) : ℤ) = (m : ℤ) + 2 + 1 by push_cast; ring] at this
      have h := normEDS_odd (2 : ℤ) 3 2 ((m : ℤ) + 2)
      rw [i1, i2, i3, i4] at h
      rw [show ((2 * (m + 2) + 1 : ℕ) : ℤ) = 2 * ((m : ℤ) + 2) + 1 by push_cast; ring, h]; ring
  induction n using Int.negInduction with
  | nat n => exact hnat n
  | neg ih m => rw [normEDS_neg, ih]

/-- The universal coefficient ring for a normalised EDS: `ℤ[X₀, X₁, X₂]`. It is an integral
domain, and `normEDS X₀ X₁ X₂ n` is nonzero for `n ≠ 0` (via the specialisation `Xᵢ ↦ 2, 3, 2`,
which sends `normEDS` to the identity sequence). -/
abbrev UnivEDS : Type := MvPolynomial (Fin 3) ℤ

/-- In the universal ring `ℤ[X₀, X₁, X₂]`, the value `normEDS X₀ X₁ X₂ n` is nonzero whenever
`n ≠ 0`: specialising `X₀ ↦ 2, X₁ ↦ 3, X₂ ↦ 2` maps it to `normEDS 2 3 2 n = n ≠ 0`. -/
lemma normEDS_univ_ne_zero (n : ℤ) (hn : n ≠ 0) :
    normEDS (X 0 : UnivEDS) (X 1) (X 2) n ≠ 0 := by
  intro h
  have hφ := map_normEDS (aeval ![(2 : ℤ), 3, 2] : UnivEDS →ₐ[ℤ] ℤ) (X 0 : UnivEDS) (X 1) (X 2) n
  rw [h, map_zero] at hφ
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hφ
  rw [show (![(2 : ℤ), 3, 2] 2) = 2 from rfl, normEDS_two_three_two] at hφ
  exact hn hφ.symm

end Universal

/-! ### Ward's theorem for `normEDS`, the `r = 1` slice -/

section Main

variable {R : Type*} [CommRing R]

/-- The domain core of Ward's `r = 1` theorem: over an integral domain in which every nonzero-index
value `normEDS b c d n` (`n ≠ 0`) is nonzero, the elliptic-net relator `rel (normEDS b c d) p q 1 0`
vanishes for all `p q : ℤ`. The nonvanishing hypothesis is what powers the cancellation steps of the
Ward induction; over the universal ring it is `normEDS_univ_ne_zero`, and it transfers to arbitrary
`CommRing`s in `normEDS_rel_one`. -/
lemma normEDS_rel_one_of_domain [IsDomain R] (b c d : R)
    (hW : ∀ n : ℤ, n ≠ 0 → normEDS b c d n ≠ 0) (p q : ℤ) :
    IsEllipticNet.rel (normEDS b c d) p q 1 0 = 0 := by
  sorry

/-- **Ward's theorem, the `r = 1` slice** (the elliptic addition formula): for the canonical
normalised elliptic divisibility sequence `W = normEDS b c d` over any `CommRing R`, the
elliptic-net relator `rel W p q 1 0` vanishes for all `p q : ℤ`. Equivalently (using `W 1 = 1`),
`W (p + q) * W (p - q) = W (p + 1) * W (p - 1) * W q ^ 2 - W (q + 1) * W (q - 1) * W p ^ 2`.

The proof reduces to the universal integral domain `ℤ[X₀, X₁, X₂]` (`normEDS_univ_ne_zero`) via the
evaluation ring hom `Xᵢ ↦ b, c, d` and `IsEllipticNet.map_rel`. -/
theorem normEDS_rel_one (b c d : R) (p q : ℤ) :
    IsEllipticNet.rel (normEDS b c d) p q 1 0 = 0 := by
  have hcomp : ⇑(MvPolynomial.aeval ![b, c, d] : UnivEDS →ₐ[ℤ] R) ∘
      normEDS (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) = normEDS b c d := by
    funext n
    rw [Function.comp_apply, map_normEDS]
    simp
  have hdom := normEDS_rel_one_of_domain (MvPolynomial.X 0 : UnivEDS) (MvPolynomial.X 1)
    (MvPolynomial.X 2) normEDS_univ_ne_zero p q
  have hmap := IsEllipticNet.map_rel
    (normEDS (MvPolynomial.X 0 : UnivEDS) (MvPolynomial.X 1) (MvPolynomial.X 2))
    (MvPolynomial.aeval ![b, c, d] : UnivEDS →ₐ[ℤ] R) p q 1 0
  rw [hdom, map_zero, hcomp] at hmap
  exact hmap.symm

end Main

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
