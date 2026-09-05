/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.Data.Int.Interval
import EllipticCurves.Torsion.NetVieta
import EllipticCurves.Torsion.OmegaCharZero
import EllipticCurves.Torsion.ThreeTorsionStructure

/-!
# `#404`'s crux, at every index

`EllipticCurves.Torsion.NetVieta` proves the crux for an abstract elliptic net over a field, from
the three base cases `τ₁ = τ₂ = τ₃ = 0` and one instance of Ward's `s ≠ 0` relation.  This file
instantiates it at the division polynomials and descends to the polynomial identity, giving

```
ΨSq₂ₙ = ΨSqₙ · (4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³)      in R[X]
```

— `WeierstrassCurve.HasΨSqDoubling n` — and hence `WeierstrassCurve.HasPreΩSq n`, for **every**
index and **every** Weierstrass curve over **every** commutative ring.

## The route

`WeierstrassCurve.Affine.ψ_isEllipticNet_evalEval` makes `k ↦ ψₖ(x, y)` an elliptic net for any
`(x, y)`, and `ψ_sq_evalEval` identifies `ψₖ(x, y)² = ΨSqₖ(x)` at a point *of the curve*.  Under
those two the abstract coordinates are the division-polynomial ones,

```
netX = Φₙ/ΨSqₙ,      netS = ψ₂ₙ/ΨSqₙ²,      netDefect · ΨSqₙ⁴ = ΨSq₂ₙ - ΨSqₙ·(…),
```

so the abstract crux is the evaluated one.  Its three base cases are the shipped
`WeierstrassCurve.hasPreΩSq_one`, `hasPreΩSq_two` and `hasPreΩSq_three`.

⚠️ **Nondegeneracy is what the descent has to pay for.**  The abstract theorem needs `ψₖ(x, y) ≠ 0`
for `k` up to roughly the index, which fails at torsion points; so the evaluated identity is
available only away from the zero set of `∏ₖ ΨSqₖ`.  That is enough: over a characteristic-`0`
field that product is a *nonzero* polynomial (`WeierstrassCurve.ΨSq_ne_zero`), and a polynomial
vanishing wherever a fixed nonzero polynomial does not is zero
(`WeierstrassCurve.eq_zero_of_eval_ne_zero`, below).  ⚠️ This is why
`WeierstrassCurve.hasPreΩSq_of_forall_hasPreΩSqAt`, which quantifies over **every** point, is not
the lemma used here.

The base is taken algebraically closed only to produce a `y` with `W.Equation x y` above a given
`x`; `hasPreΩSq_of_forall_hasΨSqDoubling_algClosed` already asks for exactly that base.

## Main statements

* `WeierstrassCurve.Affine.netDefect_mul_ΨSq_pow` : the abstract defect times `ΨSqₙ⁴` is the crux.
* `WeierstrassCurve.eq_zero_of_eval_ne_zero` : the descent step — over an infinite field, a
  polynomial vanishing off the zero set of a fixed nonzero `g` is zero.
* `WeierstrassCurve.hasΨSqDoubling` : the crux in `R[X]`, at every index, every commutative ring.
* `WeierstrassCurve.hasPreΩSq` : `#404`'s crux, at every index, every commutative ring.
* `WeierstrassCurve.Affine.equation_div_of_ψ_ne_zero` : `#404`'s on-curve identity, with its one
  index-dependent hypothesis discharged — `(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` is a point of `W`.

## References

* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).
* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **The abstract `x`-coordinate of the point net is `Φₙ/ΨSqₙ`.** -/
lemma netX_evalEval (h : W.Equation x y) {n : ℤ} (hn : (W.ΨSq n).eval x ≠ 0) :
    IsEllipticNet.netX (fun m => (W.ψ m).evalEval x y) x n
      = (W.Φ n).eval x / (W.ΨSq n).eval x := by
  have hprod := ψ_add_mul_ψ_sub_evalEval h n 1
  rw [Φ_one, ΨSq_one, eval_X, eval_one, mul_one] at hprod
  rw [IsEllipticNet.netX, hprod, ψ_sq_evalEval h]
  field_simp
  ring

/-- **The abstract defect, cleared of denominators, is the crux at `n` evaluated at `x`.** -/
lemma netDefect_mul_ΨSq_pow (h : W.Equation x y) {n : ℤ} (hn : (W.ΨSq n).eval x ≠ 0) :
    IsEllipticNet.netDefect (fun m => (W.ψ m).evalEval x y) x W.b₂ W.b₄ W.b₆ n
        * (W.ΨSq n).eval x ^ 4
      = (W.ΨSq (2 * n)).eval x - (W.ΨSq n).eval x * (4 * (W.Φ n).eval x ^ 3
        + W.b₂ * (W.Φ n).eval x ^ 2 * (W.ΨSq n).eval x
        + 2 * W.b₄ * (W.Φ n).eval x * (W.ΨSq n).eval x ^ 2
        + W.b₆ * (W.ΨSq n).eval x ^ 3) := by
  have h4 : (W.ψ n).evalEval x y ^ 4 = (W.ΨSq n).eval x ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ψ_sq_evalEval h]
  rw [IsEllipticNet.netDefect, IsEllipticNet.netS, netX_evalEval h hn, h4, div_pow,
    ψ_sq_evalEval h]
  field_simp

/-- **The abstract defect vanishes at an index where the crux holds.** -/
lemma netDefect_eq_zero_of_hasΨSqDoubling (h : W.Equation x y) {n : ℤ}
    (hn : (W.ΨSq n).eval x ≠ 0) (hd : W.HasΨSqDoubling n) :
    IsEllipticNet.netDefect (fun m => (W.ψ m).evalEval x y) x W.b₂ W.b₄ W.b₆ n = 0 := by
  have hev := congrArg (Polynomial.eval x) hd
  simp only [eval_mul, eval_add, eval_pow, eval_ofNat, eval_C] at hev
  have key := netDefect_mul_ΨSq_pow h hn
  rw [hev] at key
  have hz : IsEllipticNet.netDefect (fun m => (W.ψ m).evalEval x y) x W.b₂ W.b₄ W.b₆ n
      * (W.ΨSq n).eval x ^ 4 = 0 := by rw [key]; ring
  exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ hn)

/-- **The crux at a nondegenerate point of the curve.**  `IsEllipticNet.netDefect_eq_zero`
instantiated at the point net, with the three base cases supplied by the shipped
`WeierstrassCurve.hasPreΩSq_one`, `hasPreΩSq_two` and `hasPreΩSq_three`. -/
theorem hasΨSqDoublingAt (h : W.Equation x y) {N n : ℤ} (hN : 5 ≤ N) (hn : 1 ≤ n)
    (hnN : n + 2 ≤ N) (hne : ∀ k : ℤ, 1 ≤ k → k ≤ N → (W.ΨSq k).eval x ≠ 0) :
    (W.ΨSq (2 * n)).eval x = (W.ΨSq n).eval x * (4 * (W.Φ n).eval x ^ 3
      + W.b₂ * (W.Φ n).eval x ^ 2 * (W.ΨSq n).eval x
      + 2 * W.b₄ * (W.Φ n).eval x * (W.ΨSq n).eval x ^ 2
      + W.b₆ * (W.ΨSq n).eval x ^ 3) := by
  have hnz : (W.ΨSq n).eval x ≠ 0 := hne n hn (by omega)
  have hτ := IsEllipticNet.netDefect_eq_zero (a := fun m => (W.ψ m).evalEval x y)
    W.ψ_isEllipticNet_evalEval (fun m => by simp only [ψ_neg, evalEval_neg]) ψ_one_evalEval
    (netDefect_eq_zero_of_hasΨSqDoubling h (hne 1 le_rfl (by omega))
      ((W.hasPreΩSq_one).hasΨSqDoubling W))
    (netDefect_eq_zero_of_hasΨSqDoubling h (hne 2 (by norm_num) (by omega))
      ((W.hasPreΩSq_two).hasΨSqDoubling W))
    (netDefect_eq_zero_of_hasΨSqDoubling h (hne 3 (by norm_num) (by omega))
      ((W.hasPreΩSq_three).hasΨSqDoubling W))
    hN (fun k hk1 hkN hc => hne k hk1 hkN (by rw [← ψ_sq_evalEval h k, hc]; ring)) hn hnN
  have key := netDefect_mul_ΨSq_pow h hnz
  rw [hτ, zero_mul] at key
  linear_combination -key

end WeierstrassCurve.Affine

namespace WeierstrassCurve

/-- **A polynomial vanishing wherever a fixed nonzero polynomial does not is zero**, over an
infinite field.  ⚠️ This, not `WeierstrassCurve.hasPreΩSq_of_forall_hasPreΩSqAt`, is the descent
this file needs: the evaluated crux is available only away from the torsion locus. -/
lemma eq_zero_of_eval_ne_zero {F : Type*} [Field F] [Infinite F] {P g : F[X]} (hg : g ≠ 0)
    (h : ∀ x : F, g.eval x ≠ 0 → P.eval x = 0) : P = 0 := by
  have hPg : P * g = 0 := by
    refine Polynomial.funext fun x => ?_
    rw [eval_mul, eval_zero]
    by_cases hx : g.eval x = 0
    · rw [hx, mul_zero]
    · rw [h x hx, zero_mul]
  exact (mul_eq_zero.mp hPg).resolve_right hg

/-- **The crux in `F[X]`, over an algebraically closed field of characteristic `0`.**  The
evaluated identity holds off the zero set of `∏_{k ≤ n+5} ΨSqₖ`, which is a nonzero polynomial. -/
theorem hasΨSqDoubling_of_algClosed {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (W : WeierstrassCurve F) {n : ℤ} (hn : 1 ≤ n) : W.HasΨSqDoubling n := by
  have hg : (∏ k ∈ Finset.Icc (1 : ℤ) (n + 5), W.ΨSq k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k hk =>
      W.ΨSq_ne_zero (Int.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hk).1; omega))
  rw [HasΨSqDoubling, ← sub_eq_zero]
  refine eq_zero_of_eval_ne_zero hg fun x hx => ?_
  obtain ⟨y, hy⟩ := Affine.exists_equation (W := W) (by norm_num) x
  have hne : ∀ k : ℤ, 1 ≤ k → k ≤ n + 5 → (W.ΨSq k).eval x ≠ 0 := by
    intro k h1 h2 hc
    exact hx (by
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨h1, h2⟩) hc)
  have key := Affine.hasΨSqDoublingAt hy (N := n + 5) (by omega) hn (by omega) hne
  simp only [eval_sub, eval_mul, eval_add, eval_pow, eval_ofNat, eval_C]
  linear_combination key

variable {R : Type*} [CommRing R]

/-- **`#404`'s crux at a positive index**, for every Weierstrass curve over every commutative
ring. -/
theorem hasPreΩSq_of_one_le {n : ℤ} (hn : 1 ≤ n) (W : WeierstrassCurve R) : W.HasPreΩSq n :=
  hasPreΩSq_of_forall_hasΨSqDoubling_algClosed (by omega)
    (fun _ _ _ _ V => hasΨSqDoubling_of_algClosed V hn) W

/-- **⚠️ `#404`'s CRUX, at every index, for every Weierstrass curve over every commutative ring.**

```
preΩₙ² · (if Even n then 1 else Ψ₂Sq) = 4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³.
```

The identity is even in `n`, so the positive case covers everything except `n = 0`, which is
`WeierstrassCurve.hasPreΩSq_zero`. -/
theorem hasPreΩSq (W : WeierstrassCurve R) (n : ℤ) : W.HasPreΩSq n := by
  rcases lt_trichotomy n 0 with h | h | h
  · simpa using (hasPreΩSq_of_one_le (n := -n) (by omega) W).neg
  · rw [h]; exact W.hasPreΩSq_zero
  · exact hasPreΩSq_of_one_le (by omega) W

/-- **⚠️ `#404`'s ON-CURVE IDENTITY, UNCONDITIONALLY.**  For a point `(x, y)` of `W` over a field
of characteristic `≠ 2` with `ψₙ(x, y) ≠ 0`, the division-polynomial coordinates at `n`

```
(Φₙ(x)/ΨSqₙ(x),  ωₙ(x, y)/ψₙ(x, y)³)
```

satisfy the Weierstrass equation.  This is `WeierstrassCurve.Affine.equation_of_hasPreΩSq` with its
one index-dependent hypothesis discharged by `WeierstrassCurve.hasPreΩSq`.

⚠️ It is a statement about the division polynomials, **not** about `n • P`: identifying
`(Φₙ/ΨSqₙ, ωₙ/ψₙ³)` with the group-law multiple is `WeierstrassCurve.Affine.HasXCoordFormula`,
issue `#251`, and is untouched by this file.

⚠️ **Both halves of that identification have since been supplied, elsewhere and not here.**  The
`x`-half holds at every index over any field with `(2 : F) ≠ 0`
(`WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero`, `EllipticCurves.Torsion.NsmulOrder`).
The `y`-half — that the second coordinate above **is** `y(n • P)` — is
`WeierstrassCurve.Affine.nsmul_eq_some_omegaY_of_ΨSq_ne_zero`
(`EllipticCurves.Torsion.NsmulYPeriodic`, issue `#1500`), and ⚠️ it holds at **every** index under
`ΨSqₙ(x) ≠ 0` — at a point of `W` that is this theorem's `ψₙ(x, y) ≠ 0`, by
`ψ_sq_evalEval` (`EllipticCurves.Torsion.DivisionPolynomialEval`) — with the same `(2 : F) ≠ 0` as
here, and `W.Nonsingular x y` where this theorem asks only `W.Equation x y`.  ⚠️ The ladder-only
`WeierstrassCurve.Affine.nsmul_eq_some_omegaY` (`EllipticCurves.Torsion.NsmulYCoord`) is its weaker
predecessor and is **not** the sharp statement.

⚠️ **The three sit differently against this file, and the difference is measured.**
`EllipticCurves.Torsion.NsmulYCoord` and `EllipticCurves.Torsion.NsmulYPeriodic` are genuinely
**downstream**: both import this module, and the `ω`-form they name is this theorem's second
coordinate verbatim.  `EllipticCurves.Torsion.NsmulOrder` is **import-incomparable** with this file
— it reaches this module in neither direction, so the `x`-half was supplied on a different stack
rather than below this one, and citing it here is a cross-reference and not a dependency.  None of
the three is imported here and no name of theirs is consumed. -/
theorem Affine.equation_div_of_ψ_ne_zero {F : Type*} [Field F] {W : Affine F} {x y : F}
    (h : W.Equation x y) (h2 : (2 : F) ≠ 0) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.Equation ((W.Φ n).eval x / (W.ΨSq n).eval x)
      (((if Even n then 1 else 2 * y + W.a₁ * x + W.a₃) * (W.preΩ n).eval x -
          (W.ψ n).evalEval x y * (W.a₁ * (W.Φ n).eval x + W.a₃ * (W.ΨSq n).eval x)) /
        (2 * (W.ψ n).evalEval x y ^ 3)) :=
  Affine.equation_of_hasPreΩSq (W.hasPreΩSq n) h h2 hψ

/-- **The crux in Mathlib's vocabulary, at every index and every commutative ring**:
`ΨSq₂ₙ = ΨSqₙ · (4Φₙ³ + b₂Φₙ²ΨSqₙ + 2b₄ΦₙΨSqₙ² + b₆ΨSqₙ³)`. -/
theorem hasΨSqDoubling (W : WeierstrassCurve R) (n : ℤ) : W.HasΨSqDoubling n :=
  (W.hasPreΩSq n).hasΨSqDoubling W

end WeierstrassCurve
