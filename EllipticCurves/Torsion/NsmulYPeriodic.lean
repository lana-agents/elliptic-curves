/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulOrder
import EllipticCurves.Torsion.NsmulYCoord

/-!
# `y(n • P) = ωₙ/(2ψₙ³)` at **every** index: the `d`-periodicity of the `y`-prediction

Issue `#1500`, narrowed by PR #577 to exactly one statement — *the `y`-prediction is `d`-periodic
off the multiples of `d`* — and this file discharges it and the coordinate formula it gates.

`EllipticCurves.Torsion.NsmulYCoord` identifies the ladder's `y`-coordinate `divY` with the
`ω`-quotient `omegaY` and lands `n • (x, y) = (Φₙ/ΨSqₙ, ωₙ/(2ψₙ³))` **wherever the ladder
`ψ₁, …, ψₙ` has no zero**.  `EllipticCurves.Torsion.NsmulOrder` lifts the `x`-half off that ladder
to every index, through the `d`-periodicity of `divX` at a point of order `d`
(`divX_add_mul_of_not_dvd`).  ⚠️ **The `y`-half had no such transport**, and PR #577 measured that
the engine the `x`-half runs on does not supply one.  This file supplies a different one.

## The obstruction PR #577 recorded, and why it is real

Write `rₙ = ψ_{n+d}/ψₙ` at a point of order `d`, and `c = ψ_{d+1}·ψ_{d−1}`.  The `x`-half consumes
`ψ_mul_ψ_sub_of_ψ_eq_zero`, `ψ_{n+d}·ψ_{n−d} = −c·ψₙ²`, which says exactly `rₙ = −c·r_{n−d}` — a
recursion **along the progression `n + dℤ` and nothing else**.  Periodicity of the `y`-prediction
`Tₙ = ψ₂ₙ/ψₙ⁴` unwinds to `−c·r₂ₙ² = rₙ⁴`, a relation between `r` at `n` and at `2n`, which that
recursion cannot reach.  ⚠️ That measurement stands: the route below does **not** imitate
`divX_add_mul_of_not_dvd`, and an attempt that does will stall exactly there.

## The route: one Ward instance nobody had used

The relator `IsEllipticNet.rel ψ p q r 0 = 0` at `(p, q, r) = (m + d, k, m)` has its **third** term
`ψ_{2m+d}·ψ_{−d}·ψ_k²`, and `ψ_{−d} = −ψ_d = 0`.  What is left is

```
ψ_{(m+k)+d} · ψ_{(m−k)+d} · ψₘ²  =  ψ_{m+k} · ψ_{m−k} · ψ_{m+d}²
```

— `ψ_shift_symm_of_ψ_eq_zero`, i.e. `r_{m+k}·r_{m−k} = rₘ²` for **every** `k`, not only for `k`
along one residue class.  ⚠️ This is the relation the shift engine does not give, and it is the
whole difference.  A second instance,
at `(p, q, r) = (d, n, 1)`, gives `ψ_{d+n}·ψ_{d−n} = c·ψₙ²`, i.e. `rₙ·r_{−n} = −c`
(`ψ_add_mul_ψ_sub_of_ψ_eq_zero`).  With those two, for any `p`,

```
−c·r₂ₙ²  =  (r_p·r_{−p})·(r_{2n+p}·r_{2n−p})  =  (r_{2n−p}·r_p)·(r_{2n+p}·r_{−p})  =  rₙ²·rₙ²
```

— three applications of the first instance (centres `n`, `n`, `2n`) and one of the second.  That is
`divT_add_of_ψ_eq_zero`, and it is pure algebra: no induction, no group law, no characteristic
hypothesis.

## ⚠️ The choice of `p`, and why `d = 3` is genuinely different

`p` must avoid the multiples of `d` at `p`, `2n + p` and `2n − p` — three forbidden residues — so
`p ∈ {1, 2}` always works **once `d ≥ 4`** (`not_dvd_shift`: if both fail then `d ∣ 1` or `d ∣ 3`).
At `d = 3` the forbidden residues are all of them, and the failure is not an artefact of this
proof:

⚠️ **At `d = 3` the periodicity is not a consequence of the elliptic-net relations at all**, and
that is machine-checked here as `exists_isEllipticNet_not_divT_periodic`: for the normalised EDS
`W₁ = 1`, `W₂ = 2`, `W₃ = 0`, `W₄ = 5` over `ℚ` the recurrences force `W₅ = 40` and `W₈ = −8000`,
so `T₁ = 2` while `T₄ = −8000/5⁴ = −64/5`.  Every Ward relation holds and periodicity fails.  What
rules this out on a curve is a **curve-specific** identity,

```
preΨ₄ + Ψ₂Sq² = (6X² + b₂X + b₄)·Ψ₃                        (`preΨ₄_add_Ψ₂Sq_sq`, any `CommRing`)
```

whose only input beyond `ring` is `4b₈ = b₂b₆ − b₄²`.  At a point with `Ψ₃(x) = 0` it reads
`ψ₄ = −ψ₂⁵` (`ψ_four_evalEval_of_ψ_three_evalEval_eq_zero`) — and `−ψ₂⁵ = −32` at `(0, 1)` on
`y² = x³ + 1`, which is the value `EllipticCurves.Torsion.NsmulOrder` computes there from `preΨ₄`
by a different route.  From it, `ψ_{n+3} = −ψ₂^{2n+3}·ψₙ` by a step-of-`3` induction, and the
`d = 3` periodicity follows.

## Main definitions and statements

All **13** public declarations of this file are listed; the other 7 are `private` (two packaging
shims for `e = 0`, the shift-existence lemma `not_dvd_shift`, the `n = 1` extension of the ladder
statement, and three facts about the fixture point `(0, 1)`).

* `WeierstrassCurve.Affine.ψ_shift_symm_of_ψ_eq_zero`, `ψ_add_mul_ψ_sub_of_ψ_eq_zero` : the two
  Ward instances above.
* `WeierstrassCurve.Affine.divT_add_of_ψ_eq_zero` : **the algebraic core**, `T_{n+d} = Tₙ` from an
  explicit shift `p`, over any field and with no minimality packaging.
* `WeierstrassCurve.preΨ₄_add_Ψ₂Sq_sq` : the `d = 3` polynomial identity, over any `CommRing`.
* `WeierstrassCurve.Affine.ψ_four_evalEval_of_ψ_three_evalEval_eq_zero` : `ψ₄ = −ψ₂⁵` at a point
  of order `3`.
* `WeierstrassCurve.Affine.ψ_add_three_evalEval_of_ψ_three_eq_zero` : `ψ_{n+3} = −ψ₂^{2n+3}·ψₙ`.
* `WeierstrassCurve.Affine.divT_add_three_of_ψ_three_eq_zero` : the `d = 3` case.
* `WeierstrassCurve.Affine.divT_add_of_not_dvd`, `divT_add_mul_of_not_dvd` : one period and every
  period, in the packaging `EllipticCurves.Torsion.NsmulOrder` uses.
* `WeierstrassCurve.Affine.divY_add_mul_of_not_dvd` : **the statement `#1500` was narrowed to.**
* `WeierstrassCurve.Affine.nsmul_eq_some_omegaY_of_ΨSq_ne_zero` : **the headline** —
  `n • (x, y) = (Φₙ(x)/ΨSqₙ(x), ωₙ/(2ψₙ³))` at every index, under `ΨSqₙ(x) ≠ 0`, which is exactly
  the hypothesis `hasXCoordFormula_of_two_ne_zero` asks of the `x`-half.
* `WeierstrassCurve.Affine.nsmul_four_omegaY_y2EqX3AddOne` : the non-vacuity certificate — the
  `y`-half at an index the ladder cannot reach, landing in the `d = 3` branch.
* `WeierstrassCurve.Affine.exists_isEllipticNet_not_divT_periodic` : ⚠️ the certificate that the
  `d = 3` branch **cannot** be replaced by Ward.

## ⚠️ What this does *not* do

* **It does not remove `(2 : F) ≠ 0`.**  The `y`-coordinate is read off `ψ₂(n • P)` by halving; the
  headline inherits the hypothesis from `divY` exactly as the `x`-half does.
* **It does not touch the `2`-torsion sign question in `EllipticCurves.Torsion.OmegaCrux`.**  At a
  `2`-torsion point the headline is proved by a *different* branch — `n` is forced odd, `n • P = P`
  and the odd parity factor of `ωₙ` **is** `ψ₂(x, y) = 0`, so `ωₙ/(2ψₙ³) = −(a₁x + a₃)/2 = y`.
  ⚠️ `divY_eq_omegaY` is unusable there (it spends `ψ₂ ≠ 0`) and is not used.
* **It says nothing about the function field.**  The `#251` bullets under `FunctionField/` that
  mean the `y`-half are untouched; relettering them is a separate subtractive sweep.

## Import position, measured rather than guessed

`EllipticCurves.Torsion.NsmulYCoord` has a transitive closure of 32 modules in this library.  This
file adds exactly **one**, `EllipticCurves.Torsion.NsmulOrder` (33 in total): every module
`NsmulOrder` needs was already in `NsmulYCoord`'s closure.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7.
* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. **70** (1948).
-/

open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **Ward's relation at `(p, q, r, s) = (m + d, k, m, 0)` with `ψ_d(x, y) = 0`.**  The third term
of the relator is `ψ_{2m+d}·ψ_{−d}·ψ_k²`, and `ψ_{−d} = −ψ_d = 0` kills it.

⚠️ Read as `r_{m+k}·r_{m−k} = rₘ²` for `rₙ = ψ_{n+d}/ψₙ`, this is the relation that
`WeierstrassCurve.Affine.ψ_mul_ψ_sub_of_ψ_eq_zero` — the engine the `x`-half of the coordinate
formula runs on — does **not** supply: that one only recurses along `n + dℤ`.  The whole of this
file's route is the extra freedom in `k`. -/
theorem ψ_shift_symm_of_ψ_eq_zero {d : ℤ} (hd : (W.ψ d).evalEval x y = 0) (m k : ℤ) :
    (W.ψ (m + k + d)).evalEval x y * (W.ψ (m - k + d)).evalEval x y *
        (W.ψ m).evalEval x y ^ 2
      = (W.ψ (m + k)).evalEval x y * (W.ψ (m - k)).evalEval x y *
        (W.ψ (m + d)).evalEval x y ^ 2 := by
  have H := W.ψ_isEllipticSequence_evalEval (x := x) (y := y) (m + d) k m
  simp only [IsEllipticNet.rel, add_zero] at H
  rw [show m + d - m = d by ring, hd, show m + d + k = m + k + d by ring,
    show m + d - k = m - k + d by ring, show k + m = m + k by ring,
    show k - m = -(m - k) by ring, ψ_neg, evalEval_neg] at H
  linear_combination H

/-- **Ward's relation at `(p, q, r, s) = (d, n, 1, 0)` with `ψ_d(x, y) = 0`**, i.e.
`rₙ·r_{−n} = −c` with `c = ψ_{d+1}ψ_{d−1}`.

⚠️ It is *not* `WeierstrassCurve.Affine.ψ_mul_ψ_sub_of_ψ_eq_zero`, which is the same relator with
`p` and `q` exchanged and gives `ψ_{n+d}·ψ_{n−d} = −c·ψₙ²`.  Both are needed below. -/
theorem ψ_add_mul_ψ_sub_of_ψ_eq_zero {d : ℤ} (hd : (W.ψ d).evalEval x y = 0) (n : ℤ) :
    (W.ψ (d + n)).evalEval x y * (W.ψ (d - n)).evalEval x y =
      (W.ψ (d + 1)).evalEval x y * (W.ψ (d - 1)).evalEval x y * (W.ψ n).evalEval x y ^ 2 := by
  have H := W.ψ_rel_one_evalEval (x := x) (y := y) d n
  simp only [IsEllipticNet.rel, add_zero, ψ_one_evalEval] at H
  rw [hd] at H
  linear_combination H

/-- **The algebraic core: the predicted `ψ₂`-value `Tₙ = ψ₂ₙ/ψₙ⁴` is unchanged by `n ↦ n + d`.**

The proof is four instances of the two Ward relations above and nothing else:

```
−c·r₂ₙ² = (r_p·r_{−p})·(r_{2n+p}·r_{2n−p}) = (r_{2n−p}·r_p)·(r_{2n+p}·r_{−p}) = rₙ²·rₙ² = rₙ⁴,
```

the three regroupings being `ψ_shift_symm_of_ψ_eq_zero` at centres `n`, `n` and `2n`, and the last
step `ψ_mul_ψ_sub_of_ψ_eq_zero` at `2n + d` converting `ψ_{2n+2d}/ψ_{2n}` into `−c·r₂ₙ²`.

⚠️ `p` is a **parameter**, not a choice made here: the caller must supply an index at which `ψ`
does not vanish at `p`, `2n + p` and `2n − p`.  `WeierstrassCurve.Affine.divT_add_of_not_dvd` makes
that choice, and ⚠️ it is exactly the choice that is impossible at `d = 3`.

⚠️ No characteristic hypothesis, no induction and no group law: this is an identity between
division-polynomial values. -/
theorem divT_add_of_ψ_eq_zero {d : ℤ} (hd : (W.ψ d).evalEval x y = 0) {n p : ℤ}
    (hn : (W.ψ n).evalEval x y ≠ 0) (hnd : (W.ψ (n + d)).evalEval x y ≠ 0)
    (h2n : (W.ψ (2 * n)).evalEval x y ≠ 0) (hp : (W.ψ p).evalEval x y ≠ 0)
    (hpa : (W.ψ (2 * n + p)).evalEval x y ≠ 0)
    (hpb : (W.ψ (2 * n - p)).evalEval x y ≠ 0) :
    W.divT x y (n + d) = W.divT x y n := by
  have La := ψ_shift_symm_of_ψ_eq_zero hd n (n - p)
  rw [show n + (n - p) = 2 * n - p by ring, show n - (n - p) = p by ring,
    show p + d = d + p by ring] at La
  have Lb := ψ_shift_symm_of_ψ_eq_zero hd n (n + p)
  rw [show n + (n + p) = 2 * n + p by ring, show n - (n + p) = -p by ring,
    show -p + d = d - p by ring, ψ_neg, evalEval_neg] at Lb
  have Lc := ψ_shift_symm_of_ψ_eq_zero hd (2 * n) p
  have Cp := ψ_add_mul_ψ_sub_of_ψ_eq_zero hd p
  have A := ψ_mul_ψ_sub_of_ψ_eq_zero hd (2 * n + d)
  rw [show 2 * n + d + d = 2 * n + 2 * d by ring, show 2 * n + d - d = 2 * n by ring] at A
  have I : (W.ψ (d + 1)).evalEval x y * (W.ψ (d - 1)).evalEval x y *
        ((W.ψ (2 * n - p + d)).evalEval x y * (W.ψ (2 * n + p + d)).evalEval x y) *
          (W.ψ n).evalEval x y ^ 4
      = -((W.ψ (2 * n - p)).evalEval x y * (W.ψ (2 * n + p)).evalEval x y *
          (W.ψ (n + d)).evalEval x y ^ 4) := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hp) ?_
    linear_combination ((W.ψ (2 * n + p + d)).evalEval x y * (W.ψ (d - p)).evalEval x y *
        (W.ψ n).evalEval x y ^ 2) * La +
      ((W.ψ (2 * n - p)).evalEval x y * (W.ψ p).evalEval x y *
        (W.ψ (n + d)).evalEval x y ^ 2) * Lb -
      ((W.ψ (2 * n - p + d)).evalEval x y * (W.ψ (2 * n + p + d)).evalEval x y *
        (W.ψ n).evalEval x y ^ 4) * Cp
  have II : (W.ψ (d + 1)).evalEval x y * (W.ψ (d - 1)).evalEval x y *
        (W.ψ (2 * n + d)).evalEval x y ^ 2 * (W.ψ n).evalEval x y ^ 4
      = -((W.ψ (n + d)).evalEval x y ^ 4 * (W.ψ (2 * n)).evalEval x y ^ 2) := by
    refine mul_left_cancel₀ (mul_ne_zero hpa hpb) ?_
    linear_combination (W.ψ (2 * n)).evalEval x y ^ 2 * I -
      ((W.ψ (d + 1)).evalEval x y * (W.ψ (d - 1)).evalEval x y *
        (W.ψ n).evalEval x y ^ 4) * Lc
  have III : (W.ψ (2 * n + 2 * d)).evalEval x y * (W.ψ n).evalEval x y ^ 4
      = (W.ψ (2 * n)).evalEval x y * (W.ψ (n + d)).evalEval x y ^ 4 := by
    refine mul_left_cancel₀ h2n ?_
    linear_combination (W.ψ n).evalEval x y ^ 4 * A - II
  rw [divT, divT, div_eq_div_iff (pow_ne_zero 4 hnd) (pow_ne_zero 4 hn),
    show 2 * (n + d) = 2 * n + 2 * d by ring]
  exact III

end WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- **`preΨ₄ + Ψ₂Sq² = (6X² + b₂X + b₄)·Ψ₃` in `R[X]`**, over an arbitrary commutative ring.

Its only input beyond `ring` is `WeierstrassCurve.b_relation`, `4b₈ = b₂b₆ − b₄²`.

⚠️ This is the file's one piece of genuinely **curve-specific** input, and it is not decoration:
at `d = 3` the periodicity below is *false* for an abstract elliptic net with the same initial
values, so no amount of Ward can replace it.  See the module docstring for the counterexample. -/
theorem preΨ₄_add_Ψ₂Sq_sq (W : WeierstrassCurve R) :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 = (6 * X ^ 2 + C W.b₂ * X + C W.b₄) * W.Ψ₃ := by
  have hb : (C W.b₂ * C W.b₆ - C W.b₄ ^ 2 : R[X]) = 4 * C W.b₈ := by
    rw [← C_pow, ← C_mul, ← C_sub, ← W.b_relation, map_mul, map_ofNat]
  simp only [preΨ₄, Ψ₂Sq, Ψ₃, map_mul, map_sub, map_pow, map_ofNat]
  linear_combination (-(X ^ 2) : R[X]) * hb

end WeierstrassCurve

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- **At a point of `W` where `ψ₃` vanishes, `ψ₄ = −ψ₂⁵`.**  Evaluate `preΨ₄_add_Ψ₂Sq_sq` at `x`
and use `Ψ₂Sq(x) = ψ₂(x, y)²`.

⚠️ No hypothesis that `ψ₂` is nonzero, and none on the characteristic.  At `(0, 1)` on
`y² = x³ + 1` it gives `ψ₄ = −2⁵ = −32`, which is the value
`EllipticCurves.Torsion.NsmulOrder` computes there from `preΨ₄` directly — see
`nsmul_four_omegaY_y2EqX3AddOne`. -/
theorem ψ_four_evalEval_of_ψ_three_evalEval_eq_zero (h : W.Equation x y)
    (h3 : (W.ψ 3).evalEval x y = 0) :
    (W.ψ 4).evalEval x y = -(W.ψ 2).evalEval x y ^ 5 := by
  have hΨ3 : W.Ψ₃.eval x = 0 := by rwa [ψ_three, evalEval_C] at h3
  have hsq : W.Ψ₂Sq.eval x = (W.ψ 2).evalEval x y ^ 2 := by
    rw [Ψ₂Sq_eval_eq_sq h, ψ_two_evalEval]
  have hpoly := congrArg (Polynomial.eval x) W.preΨ₄_add_Ψ₂Sq_sq
  simp only [eval_add, eval_mul, eval_pow, hΨ3, mul_zero, hsq] at hpoly
  rw [ψ_four, evalEval_mul, evalEval_C, ← ψ_two]
  linear_combination (W.ψ 2).evalEval x y * hpoly


/-- The `e = 0` instance of the least-vanishing-index packaging: `ψ₃(x, y) = 0` at a point which
is not `2`-torsion makes `3` the least index at which `ψ` vanishes. -/
private lemma minimal_of_ψ_three_eq_zero (ht : (W.ψ 2).evalEval x y ≠ 0) :
    ∀ k : ℤ, 1 ≤ k → k < ((0 : ℕ) : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0 := by
  intro k hk1 hk2
  rw [Nat.cast_zero, zero_add] at hk2
  interval_cases k
  · rw [ψ_one_evalEval]; exact one_ne_zero
  · exact ht

/-- `ψ₃(x, y) = 0` in the `e + 3` shape at `e = 0`. -/
private lemma ψ_three_eq_zero_cast (h3 : (W.ψ 3).evalEval x y = 0) :
    (W.ψ (((0 : ℕ) : ℤ) + 3)).evalEval x y = 0 := by simpa using h3

/-- **Quasi-periodicity of `ψ` at a point of order `3`**: `ψ_{n+3} = −ψ₂^{2n+3}·ψₙ`.

⚠️ The induction is in steps of **three**, not one: the two-step relation
`ψ_shift_symm_of_ψ_eq_zero` at `k = 1` needs `ψₙ ≠ 0`, which fails at every multiple of `3`, so
consecutive indices cannot be chained.  What does chain is
`WeierstrassCurve.Affine.ψ_mul_ψ_sub_of_ψ_eq_zero` at `n + 3`, and the base cases are `ψ₃ = 0`,
`ψ₄ = −ψ₂⁵` and `ψ₅ = ψ₄ψ₂³`. -/
theorem ψ_add_three_evalEval_of_ψ_three_eq_zero (h2 : (2 : F) ≠ 0)
    (hns : W.Nonsingular x y) (ht : (W.ψ 2).evalEval x y ≠ 0)
    (h3 : (W.ψ 3).evalEval x y = 0) (n : ℕ) :
    (W.ψ ((n : ℤ) + 3)).evalEval x y
      = -(W.ψ 2).evalEval x y ^ (2 * n + 3) * (W.ψ (n : ℤ)).evalEval x y := by
  classical
  have h4 : (W.ψ 4).evalEval x y = -(W.ψ 2).evalEval x y ^ 5 :=
    ψ_four_evalEval_of_ψ_three_evalEval_eq_zero hns.left h3
  have hd0 := ψ_three_eq_zero_cast h3
  have hmin0 := minimal_of_ψ_three_eq_zero ht
  have hzero := ψ_evalEval_eq_zero_of_dvd h2 hns ht hd0 hmin0
  have hnz := ψ_evalEval_ne_zero_of_not_dvd h2 hns ht hd0 hmin0
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · interval_cases n
    · simpa using h3
    · rw [show ((1 : ℕ) : ℤ) + 3 = 4 by norm_num, h4, Nat.cast_one, ψ_one_evalEval]
      norm_num
    · have H := ψ_mul_ψ_sub_of_ψ_eq_zero h3 2
      rw [show (2 : ℤ) - 3 = -1 by norm_num, ψ_neg, evalEval_neg, ψ_one_evalEval,
        show (3 : ℤ) + 1 = 4 by norm_num, show (3 : ℤ) - 1 = 2 by norm_num, h4] at H
      rw [show ((2 : ℕ) : ℤ) + 3 = 2 + 3 by norm_num, Nat.cast_ofNat]
      linear_combination -H
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have ihm := ih m (by omega)
    have H := ψ_mul_ψ_sub_of_ψ_eq_zero h3 ((m : ℤ) + 3)
    rw [show (m : ℤ) + 3 - 3 = (m : ℤ) by ring, show (3 : ℤ) + 1 = 4 by norm_num,
      show (3 : ℤ) - 1 = 2 by norm_num, h4] at H
    rw [show (((m + 3 : ℕ) : ℤ) + 3) = (m : ℤ) + 3 + 3 by push_cast; ring,
      show ((m + 3 : ℕ) : ℤ) = (m : ℤ) + 3 by push_cast; ring,
      show 2 * (m + 3) + 3 = 2 * m + 3 + 6 by ring]
    by_cases hm : (3 : ℕ) ∣ m
    · have hm0 : (W.ψ (m : ℤ)).evalEval x y = 0 := hzero m hm
      have hm3 : (W.ψ ((m : ℤ) + 3)).evalEval x y = 0 := by rw [ihm, hm0, mul_zero]
      have hm6 : (W.ψ ((m : ℤ) + 3 + 3)).evalEval x y = 0 := by
        have := hzero (m + 3 + 3) (by omega)
        rwa [show (((m + 3 + 3 : ℕ)) : ℤ) = (m : ℤ) + 3 + 3 by push_cast; ring] at this
      rw [hm3, hm6, mul_zero]
    · have hmne : (W.ψ (m : ℤ)).evalEval x y ≠ 0 := hnz m hm
      refine mul_right_cancel₀ hmne ?_
      linear_combination H + ((W.ψ 2).evalEval x y ^ 6 * (W.ψ ((m : ℤ) + 3)).evalEval x y) * ihm


/-- **The `d = 3` case of the `y`-periodicity**, which the general route cannot reach.

⚠️ Not a specialisation of `WeierstrassCurve.Affine.divT_add_of_ψ_eq_zero`: at `d = 3` every shift
`p` is forbidden, and the statement is not a consequence of the elliptic-net relations at all.  It
runs instead on the explicit quasi-periodicity above, so `ψ_{2n+6}` and `ψ_{n+3}⁴` acquire the
**same** factor `ψ₂^{8n+12}` and it cancels. -/
theorem divT_add_three_of_ψ_three_eq_zero (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) (h3 : (W.ψ 3).evalEval x y = 0)
    {n : ℕ} (hn : ¬ (3 ∣ n)) :
    W.divT x y ((n : ℤ) + 3) = W.divT x y (n : ℤ) := by
  classical
  have hnz := ψ_evalEval_ne_zero_of_not_dvd h2 hns ht (ψ_three_eq_zero_cast h3)
    (minimal_of_ψ_three_eq_zero ht)
  have hA := ψ_add_three_evalEval_of_ψ_three_eq_zero h2 hns ht h3 n
  have hB := ψ_add_three_evalEval_of_ψ_three_eq_zero h2 hns ht h3 (2 * n)
  have hC := ψ_add_three_evalEval_of_ψ_three_eq_zero h2 hns ht h3 (2 * n + 3)
  rw [show (((2 * n : ℕ) : ℤ)) = 2 * (n : ℤ) by push_cast; ring] at hB
  rw [show (((2 * n + 3 : ℕ) : ℤ)) = 2 * (n : ℤ) + 3 by push_cast; ring,
    show 2 * (2 * n + 3) + 3 = 4 * n + 9 by ring] at hC
  rw [show 2 * (2 * n) + 3 = 4 * n + 3 by ring] at hB
  have hψn : (W.ψ (n : ℤ)).evalEval x y ≠ 0 := hnz n hn
  have hψn3 : (W.ψ ((n : ℤ) + 3)).evalEval x y ≠ 0 := by
    rw [hA]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ ht)) hψn
  rw [divT, divT, div_eq_div_iff (pow_ne_zero 4 hψn3) (pow_ne_zero 4 hψn),
    show 2 * ((n : ℤ) + 3) = 2 * (n : ℤ) + 3 + 3 by ring, hC, hB, hA]
  ring


/-- For `d ≥ 4` and `m` with `d ∤ 2m`, one of the two shifts `p = 1`, `p = 2` avoids the
multiples of `d` on both sides of `2m`.  ⚠️ This is exactly what fails at `d = 3`. -/
private lemma not_dvd_shift {d m : ℕ} (hd : 4 ≤ d) (h2m : ¬ d ∣ 2 * m) :
    (¬ d ∣ 2 * m + 1 ∧ ¬ d ∣ 2 * m - 1) ∨ (¬ d ∣ 2 * m + 2 ∧ ¬ d ∣ 2 * m - 2) := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (by simp) h2m
    · exact h
  by_cases h1 : d ∣ 2 * m + 1
  · refine Or.inr ⟨fun h => ?_, fun h => ?_⟩
    · have hone : d ∣ 1 := by
        have := Nat.dvd_sub h h1
        rwa [show 2 * m + 2 - (2 * m + 1) = 1 by omega] at this
      have := Nat.eq_one_of_dvd_one hone
      omega
    · have hthree : d ∣ 3 := by
        have := Nat.dvd_sub h1 h
        rwa [show 2 * m + 1 - (2 * m - 2) = 3 by omega] at this
      have := Nat.le_of_dvd (by norm_num) hthree
      omega
  · by_cases h1' : d ∣ 2 * m - 1
    · refine Or.inr ⟨fun h => ?_, fun h => ?_⟩
      · have hthree : d ∣ 3 := by
          have := Nat.dvd_sub h h1'
          rwa [show 2 * m + 2 - (2 * m - 1) = 3 by omega] at this
        have := Nat.le_of_dvd (by norm_num) hthree
        omega
      · have hone : d ∣ 1 := by
          have := Nat.dvd_sub h1' h
          rwa [show 2 * m - 1 - (2 * m - 2) = 1 by omega] at this
        have := Nat.eq_one_of_dvd_one hone
        omega
    · exact Or.inl ⟨h1, h1'⟩

/-- **One period of the predicted `ψ₂`-value `Tₙ = ψ₂ₙ/ψₙ⁴`**, off the multiples of the order —
the `y`-counterpart of `WeierstrassCurve.Affine.divX_add_of_not_dvd`, in the same packaging.

Three branches: at a multiple of `d` in `2m` both sides are `0/ψ⁴ = 0`; at `d = 3` the special
route above; otherwise `p ∈ {1, 2}`, one of which works by `not_dvd_shift`. -/
theorem divT_add_of_not_dvd (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0)
    (m : ℕ) (hm : ¬ ((e + 3) ∣ m)) :
    W.divT x y ((m : ℤ) + ((e : ℤ) + 3)) = W.divT x y (m : ℤ) := by
  classical
  have hnz := ψ_evalEval_ne_zero_of_not_dvd h2 hns ht hd hmin
  have hz := ψ_evalEval_eq_zero_of_dvd h2 hns ht hd hmin
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (dvd_zero _) hm
    · exact h
  have hcast : ((e + 3 : ℕ) : ℤ) = (e : ℤ) + 3 := by push_cast; ring
  by_cases h2m : (e + 3) ∣ 2 * m
  · have hA : (W.ψ (2 * (m : ℤ))).evalEval x y = 0 := by
      have := hz (2 * m) h2m
      rwa [show (((2 * m : ℕ)) : ℤ) = 2 * (m : ℤ) by push_cast; ring] at this
    have hB : (W.ψ (2 * ((m : ℤ) + ((e : ℤ) + 3)))).evalEval x y = 0 := by
      have := hz (2 * m + 2 * (e + 3)) (Nat.dvd_add h2m ⟨2, by ring⟩)
      rwa [show (((2 * m + 2 * (e + 3) : ℕ)) : ℤ) = 2 * ((m : ℤ) + ((e : ℤ) + 3)) by
        push_cast; ring] at this
    rw [divT, divT, hA, hB, zero_div, zero_div]
  · rcases Nat.lt_or_ge e 1 with he | he
    · obtain rfl : e = 0 := by omega
      have h3 : (W.ψ 3).evalEval x y = 0 := by simpa using hd
      have hm3 : ¬ (3 ∣ m) := by simpa using hm
      have := divT_add_three_of_ψ_three_eq_zero h2 hns ht h3 hm3
      rwa [show ((0 : ℕ) : ℤ) + 3 = 3 by norm_num]
    · have hd4 : 4 ≤ e + 3 := by omega
      have hn : (W.ψ (m : ℤ)).evalEval x y ≠ 0 := hnz m hm
      have hnd : (W.ψ ((m : ℤ) + ((e : ℤ) + 3))).evalEval x y ≠ 0 := by
        have := hnz (m + (e + 3)) (fun hdv =>
          hm ((Nat.dvd_add_iff_left (dvd_refl (e + 3))).mpr hdv))
        rwa [show (((m + (e + 3) : ℕ)) : ℤ) = (m : ℤ) + ((e : ℤ) + 3) by push_cast; ring] at this
      have h2n : (W.ψ (2 * (m : ℤ))).evalEval x y ≠ 0 := by
        have := hnz (2 * m) h2m
        rwa [show (((2 * m : ℕ)) : ℤ) = 2 * (m : ℤ) by push_cast; ring] at this
      rcases not_dvd_shift hd4 h2m with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · refine divT_add_of_ψ_eq_zero hd hn hnd h2n (p := 1) ?_ ?_ ?_
        · rw [ψ_one_evalEval]; exact one_ne_zero
        · have := hnz (2 * m + 1) ha
          rwa [show (((2 * m + 1 : ℕ)) : ℤ) = 2 * (m : ℤ) + 1 by push_cast; ring] at this
        · have := hnz (2 * m - 1) hb
          rwa [show (((2 * m - 1 : ℕ)) : ℤ) = 2 * (m : ℤ) - 1 by omega] at this
      · refine divT_add_of_ψ_eq_zero hd hn hnd h2n (p := 2) ht ?_ ?_
        · have := hnz (2 * m + 2) ha
          rwa [show (((2 * m + 2 : ℕ)) : ℤ) = 2 * (m : ℤ) + 2 by push_cast; ring] at this
        · have := hnz (2 * m - 2) hb
          rwa [show (((2 * m - 2 : ℕ)) : ℤ) = 2 * (m : ℤ) - 2 by omega] at this


/-- **The predicted `ψ₂`-value is periodic with period `d` off the multiples of `d`**, at every
multiple of the period.  ⚠️ The `q = 0` case is `rfl`-level and the step is one application of
`divT_add_of_not_dvd`; there is no new mathematics here. -/
theorem divT_add_mul_of_not_dvd (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0)
    (j : ℕ) (hj : ¬ ((e + 3) ∣ j)) :
    ∀ q : ℕ, W.divT x y ((j : ℤ) + q * ((e : ℤ) + 3)) = W.divT x y (j : ℤ) := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have hnj : ¬ ((e + 3) ∣ (j + q * (e + 3))) := fun hdv =>
      hj ((Nat.dvd_add_iff_left (dvd_mul_left (e + 3) q)).mpr hdv)
    have hstep := divT_add_of_not_dvd h2 hns ht hd hmin (j + q * (e + 3)) hnj
    rw [show (((j + q * (e + 3) : ℕ)) : ℤ) = (j : ℤ) + q * ((e : ℤ) + 3) by push_cast; ring]
      at hstep
    rw [show (j : ℤ) + ((q : ℕ) + 1 : ℕ) * ((e : ℤ) + 3)
        = (j : ℤ) + q * ((e : ℤ) + 3) + ((e : ℤ) + 3) by push_cast; ring, hstep, ih]

/-- **The predicted `y`-coordinate is periodic with period `d` off the multiples of `d`** — the
statement `#1500` was narrowed to after PR #577, and the last thing between the ladder régime and
the coordinate formula at every index.

`divY = (divT − a₁·divX − a₃)/2`, so this is `divT_add_mul_of_not_dvd` together with the merged
`WeierstrassCurve.Affine.divX_add_mul_of_not_dvd` and nothing else. -/
theorem divY_add_mul_of_not_dvd (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0)
    (j : ℕ) (hj : ¬ ((e + 3) ∣ j)) :
    ∀ q : ℕ, W.divY x y ((j : ℤ) + q * ((e : ℤ) + 3)) = W.divY x y (j : ℤ) := by
  intro q
  rw [divY, divY, divT_add_mul_of_not_dvd h2 hns ht hd hmin j hj q,
    divX_add_mul_of_not_dvd h2 hns ht hd hmin j hj q]


section Formula

variable [DecidableEq F]

/-- The ladder régime at **every** index `n ≥ 1`, including `n = 1`, which
`WeierstrassCurve.Affine.nsmul_eq_some_omegaY` excludes. -/
private lemma nsmul_eq_some_omegaY_of_ladder (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    ∃ h' : W.Nonsingular ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x) (W.omegaY x y (n : ℤ)),
      (n • Point.some x y hns : W.Point) = .some _ _ h' := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · obtain rfl : n = 1 := by omega
    have hB : W.omegaY x y ((1 : ℕ) : ℤ) = y := by
      rw [Nat.cast_one, ← divY_eq_omegaY hns.left h2 ht (by rw [ψ_one_evalEval]; exact one_ne_zero),
        divY_one h2]
    have hA : (W.Φ ((1 : ℕ) : ℤ)).eval x / (W.ΨSq ((1 : ℕ) : ℤ)).eval x = x := by
      rw [Nat.cast_one, Φ_one, ΨSq_one, eval_X, eval_one, div_one]
    exact ⟨by rw [hA, hB]; exact hns, by rw [one_nsmul, Point.some.injEq]; exact ⟨hA.symm, hB.symm⟩⟩
  · exact nsmul_eq_some_omegaY h2 hns hge hψ

/-- **`n • (x, y) = (Φₙ(x)/ΨSqₙ(x), ωₙ/(2ψₙ³))` at EVERY index**, over any field of characteristic
`≠ 2`, with the same hypothesis `ΨSqₙ(x) ≠ 0` that
`WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero` asks of the `x`-half. -/
theorem nsmul_eq_some_omegaY_of_ΨSq_ne_zero (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) {n : ℕ}
    (hΨ : (W.ΨSq (n : ℤ)).eval x ≠ 0) :
    ∃ h' : W.Nonsingular ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x) (W.omegaY x y (n : ℤ)),
      (n • Point.some x y hns : W.Point) = .some _ _ h' := by
  classical
  have hψn : (W.ψ (n : ℤ)).evalEval x y ≠ 0 := fun h =>
    hΨ (by rw [← ψ_sq_evalEval hns.left, h]; ring)
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (by simp) hψn
    · exact h
  by_cases ht : (W.ψ 2).evalEval x y = 0
  · -- `(x, y)` is a `2`-torsion point: `n` is odd, `n • (x, y) = (x, y)`, and `ωₙ/(2ψₙ³) = y`
    -- because the odd parity factor of `ωₙ` **is** `ψ₂(x, y) = 0`.
    have hy : 2 * y + W.a₁ * x + W.a₃ = 0 := by rwa [ψ_two_evalEval] at ht
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
      · refine absurd ?_ hψn
        rw [show ((n : ℤ)) = 2 * (m : ℤ) by rw [hm]; push_cast; ring]
        exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht m
      · exact hodd
    have htwo : ((2 : ℕ) • Point.some x y hns : W.Point) = 0 :=
      nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero h2 hns (by omega)
        (by rw [Nat.cast_ofNat]; exact ht)
        (fun k hk1 hk2 => by rw [show k = 1 by omega, ψ_one_evalEval]; exact one_ne_zero)
    have hnP : ((2 * m + 1 : ℕ) • Point.some x y hns : W.Point) = Point.some x y hns := by
      rw [add_nsmul, mul_comm, ← smul_smul, htwo, smul_zero, one_nsmul, zero_add]
    have hup : (W.ψ (((2 * m + 1 : ℕ) : ℤ) + 1)).evalEval x y = 0 := by
      rw [show (((2 * m + 1 : ℕ) : ℤ) + 1) = 2 * ((m : ℤ) + 1) by push_cast; ring]
      exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht _
    have hdown : (W.ψ (((2 * m + 1 : ℕ) : ℤ) - 1)).evalEval x y = 0 := by
      rw [show (((2 * m + 1 : ℕ) : ℤ) - 1) = 2 * (m : ℤ) by push_cast; ring]
      exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht _
    have hsq : (W.ΨSq ((2 * m + 1 : ℕ) : ℤ)).eval x
        = (W.ψ ((2 * m + 1 : ℕ) : ℤ)).evalEval x y ^ 2 := (ψ_sq_evalEval hns.left _).symm
    have hΦ : (W.Φ ((2 * m + 1 : ℕ) : ℤ)).eval x
        = x * (W.ψ ((2 * m + 1 : ℕ) : ℤ)).evalEval x y ^ 2 := by
      rw [Φ_eval_eq_of_equation hns.left, hup, hdown]
      ring
    have hA : (W.Φ ((2 * m + 1 : ℕ) : ℤ)).eval x / (W.ΨSq ((2 * m + 1 : ℕ) : ℤ)).eval x = x := by
      rw [hΦ, hsq]
      field_simp
    have hodd : ¬ Even (((2 * m + 1 : ℕ) : ℤ)) := by
      rw [Int.even_iff]
      push_cast
      omega
    have hB : W.omegaY x y ((2 * m + 1 : ℕ) : ℤ) = y := by
      rw [omegaY, if_neg hodd, hy, hΦ, hsq, zero_mul, zero_sub]
      field_simp
      linear_combination -hy
    exact ⟨by rw [hA, hB]; exact hns,
      by rw [hnP, Point.some.injEq]; exact ⟨hA.symm, hB.symm⟩⟩
  · by_cases hall : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0
    · exact nsmul_eq_some_omegaY_of_ladder h2 hns ht hn1 hall
    · push Not at hall
      obtain ⟨k₀, hk₀1, -, hk₀⟩ := hall
      obtain ⟨e, hd0, hmin'⟩ := exists_minimal_ψ_evalEval_eq_zero ht
        ⟨k₀.toNat, by omega, by rwa [Int.toNat_of_nonneg (by omega)]⟩
      have hcastd : (((e + 3 : ℕ)) : ℤ) = (e : ℤ) + 3 := by push_cast; ring
      have hdvd := ψ_evalEval_eq_zero_of_dvd h2 hns ht hd0 hmin'
      have hnotdvd : ¬ ((e + 3) ∣ n) := fun h => hψn (hdvd n h)
      have hzero : ((e + 3 : ℕ) • Point.some x y hns : W.Point) = 0 :=
        nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero h2 hns (by omega)
          (by rw [hcastd]; exact hd0) (fun k hk1 hk2 => hmin' k hk1 (by rwa [hcastd] at hk2))
      obtain ⟨j, q, hn, hj0, hjlt⟩ :
          ∃ j q : ℕ, n = j + q * (e + 3) ∧ j ≠ 0 ∧ j < e + 3 :=
        ⟨n % (e + 3), n / (e + 3), (Nat.mod_add_div' n (e + 3)).symm,
          fun h => hnotdvd (Nat.dvd_of_mod_eq_zero h), Nat.mod_lt _ (by omega)⟩
      have hnotdvdj : ¬ ((e + 3) ∣ j) := fun h => by
        have := Nat.le_of_dvd (by omega) h; omega
      have hjne : ∀ k : ℤ, 1 ≤ k → k ≤ (j : ℤ) → (W.ψ k).evalEval x y ≠ 0 :=
        fun k hk1 hk2 => hmin' k hk1 (by omega)
      obtain ⟨h', hjP⟩ := nsmul_eq_some_omegaY_of_ladder h2 hns ht (by omega) hjne
      have hqz : ∀ r : ℕ, ((r * (e + 3) : ℕ) • Point.some x y hns : W.Point) = 0 := by
        intro r
        induction r with
        | zero => simp
        | succ r ihr =>
          rw [show (r + 1) * (e + 3) = r * (e + 3) + (e + 3) by ring, add_nsmul, ihr, hzero,
            add_zero]
      have hnP : ((n : ℕ) • Point.some x y hns : W.Point) = j • Point.some x y hns := by
        conv_lhs => rw [hn]
        rw [add_nsmul, hqz q, add_zero]
      have hcastn : (j : ℤ) + (q : ℤ) * ((e : ℤ) + 3) = (n : ℤ) := by rw [hn]; push_cast; ring
      have hψj : (W.ψ (j : ℤ)).evalEval x y ≠ 0 := hjne j (by omega) le_rfl
      have hA : (W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x
          = (W.Φ (j : ℤ)).eval x / (W.ΨSq (j : ℤ)).eval x := by
        have hper := divX_add_mul_of_not_dvd h2 hns ht hd0 hmin' j hnotdvdj q
        rw [hcastn] at hper
        simpa only [divX] using hper
      have hB : W.omegaY x y (n : ℤ) = W.omegaY x y (j : ℤ) := by
        have hper := divY_add_mul_of_not_dvd h2 hns ht hd0 hmin' j hnotdvdj q
        rw [hcastn] at hper
        rw [← divY_eq_omegaY hns.left h2 ht hψn, ← divY_eq_omegaY hns.left h2 ht hψj, hper]
      exact ⟨by rw [hA, hB]; exact h',
        by rw [hnP, hjP, Point.some.injEq]; exact ⟨hA.symm, hB.symm⟩⟩

end Formula


/-! ## ⚠️ Non-vacuity: the `y`-half at an index the ladder cannot reach

`EllipticCurves.Torsion.NsmulOrder` certifies the `x`-half at `n = 4` on the point `Q = (0, 1)` of
`y² = x³ + 1`, whose order is `3`, so the ladder `ψ₁, …, ψ₄` passes through the zero `ψ₃(Q) = 0`
and `nsmul_eq_some_omegaY` is inapplicable.  ⚠️ This is the `y`-half of that certificate, and it
lands in the `d = 3` branch — the one that is not a consequence of Ward.
-/

section Nonvacuity

open EllipticCurves.Fixture

/-- `Q = (0, 1)` lies on `y² = x³ + 1` and is nonsingular. -/
private lemma nonsingularZeroOne : (y2EqX3AddOne ℚ).Nonsingular 0 1 :=
  equation_iff_nonsingular.mp (by norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff])

/-- `ψ₂(0, 1) = 2`, so `Q` is not `2`-torsion. -/
private lemma ψTwoZeroOne : ((y2EqX3AddOne ℚ).ψ 2).evalEval 0 1 = 2 := by
  rw [ψ_two_evalEval]; norm_num [y2EqX3AddOne]

/-- `ψ₃(0, 1) = Ψ₃(0) = b₈ = 0`. -/
private lemma ψThreeZeroOne : ((y2EqX3AddOne ℚ).ψ 3).evalEval 0 1 = 0 := by
  rw [ψ_three, evalEval_C]
  norm_num [y2EqX3AddOne, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **The `y`-half of `WeierstrassCurve.Affine.nsmul_four_y2EqX3AddOne`.**  At `Q = (0, 1)` on
`y² = x³ + 1` the rung `ψ₃(Q) = 0` breaks the ladder at `n = 4`, so
`WeierstrassCurve.Affine.nsmul_eq_some_omegaY` does not apply; `ΨSq₄(0) = ψ₄(Q)² = 1024 ≠ 0`, so
`nsmul_eq_some_omegaY_of_ΨSq_ne_zero` does, and it computes `y(4 • Q) = ω₄/(2ψ₄³) = 1`.

⚠️ That value is forced — `Q` has order `3`, so `4 • Q = Q = (0, 1)` — and that is exactly the
point: the theorem says the `ω`-quotient **is** the `y`-coordinate of the multiple, at an index no
ladder statement reaches.  ⚠️ `ψ₄(Q) = −32` is obtained here from
`ψ_four_evalEval_of_ψ_three_evalEval_eq_zero` as `−ψ₂(Q)⁵ = −2⁵`;
`EllipticCurves.Torsion.NsmulOrder` obtains the same value from `preΨ₄(0) = −16` by a different
route, so the `d = 3` identity of this file is cross-checked against a merged computation. -/
theorem nsmul_four_omegaY_y2EqX3AddOne :
    ((y2EqX3AddOne ℚ).ψ 3).evalEval 0 1 = 0 ∧
      ((y2EqX3AddOne ℚ).ψ 4).evalEval 0 1 = -32 ∧
        (y2EqX3AddOne ℚ).omegaY 0 1 ((4 : ℕ) : ℤ) = 1 := by
  have hψ4 : ((y2EqX3AddOne ℚ).ψ 4).evalEval 0 1 = -32 := by
    rw [ψ_four_evalEval_of_ψ_three_evalEval_eq_zero nonsingularZeroOne.left ψThreeZeroOne,
      ψTwoZeroOne]
    norm_num
  refine ⟨ψThreeZeroOne, hψ4, ?_⟩
  have hΨ : ((y2EqX3AddOne ℚ).ΨSq ((4 : ℕ) : ℤ)).eval 0 ≠ 0 := by
    rw [← ψ_sq_evalEval nonsingularZeroOne.left, show (((4 : ℕ)) : ℤ) = 4 by norm_num, hψ4]
    norm_num
  obtain ⟨h', heq⟩ := nsmul_eq_some_omegaY_of_ΨSq_ne_zero (W := y2EqX3AddOne ℚ) (by norm_num)
    nonsingularZeroOne hΨ
  have h3 : ((3 : ℕ) • (Point.some 0 1 nonsingularZeroOne : (y2EqX3AddOne ℚ).Point)) = 0 :=
    nsmul_three_y2EqX3AddOne_eq_zero
  have h4 : ((4 : ℕ) • (Point.some 0 1 nonsingularZeroOne : (y2EqX3AddOne ℚ).Point))
      = Point.some 0 1 nonsingularZeroOne := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, add_nsmul, h3, zero_add, one_nsmul]
  rw [h4, Point.some.injEq] at heq
  exact heq.2.symm

/-- ⚠️ **At `d = 3` the periodicity is not a consequence of the elliptic-net relations**, so the
curve-specific input of `preΨ₄_add_Ψ₂Sq_sq` is not an artefact of the route taken here.

The witness is the normalised EDS over `ℚ` with `b = 2`, `c = 0`, `d = 5/2`, i.e. `W₁ = 1`,
`W₂ = 2`, `W₃ = 0`, `W₄ = 5`.  Ward's relations hold — it is `normEDS`, so
`WeierstrassCurve.normEDS_isEllipticNet` applies — and `W₃ = 0` puts it in exactly the situation of
this file at `d = 3`.  The recurrences then force `W₅ = 40`, `W₆ = 0` and `W₈ = −8000`, so

```
T₄ = W₈/W₄⁴ = −8000/625 = −64/5  ≠  2 = W₂/W₁⁴ = T₁ .
```

⚠️ On a curve this cannot happen: `ψ₄ = −ψ₂⁵` at a point of order `3` forces `W₄ = −32` here, and
`W₈` then comes out as `2·W₄⁴ = 2097152`.  The statement is phrased as `W₈·W₁⁴ ≠ W₂·W₄⁴` rather than
with division so that it is exactly the cross-multiplied form of `T₄ ≠ T₁`. -/
theorem exists_isEllipticNet_not_divT_periodic :
    ∃ W : ℤ → ℚ, IsEllipticNet W ∧ W 1 = 1 ∧ W 3 = 0 ∧ W 8 * W 1 ^ 4 ≠ W 2 * W 4 ^ 4 := by
  refine ⟨normEDS 2 0 (5 / 2), WeierstrassCurve.normEDS_isEllipticNet 2 0 (5 / 2), normEDS_one ..,
    normEDS_three .., ?_⟩
  have h1 : normEDS (2 : ℚ) 0 (5 / 2) 1 = 1 := normEDS_one ..
  have h2 : normEDS (2 : ℚ) 0 (5 / 2) 2 = 2 := normEDS_two ..
  have h3 : normEDS (2 : ℚ) 0 (5 / 2) 3 = 0 := normEDS_three ..
  have h4 : normEDS (2 : ℚ) 0 (5 / 2) 4 = 5 := by rw [normEDS_four]; norm_num
  have h5 := normEDS_odd (b := (2 : ℚ)) (c := 0) (d := 5 / 2) 2
  have h6 := normEDS_even (b := (2 : ℚ)) (c := 0) (d := 5 / 2) 3
  have h8 := normEDS_even (b := (2 : ℚ)) (c := 0) (d := 5 / 2) 4
  norm_num [h1, h2, h3, h4] at h5 h6 h8
  have h8' : normEDS (2 : ℚ) 0 (5 / 2) 8 = -8000 := by rw [h5] at h8; linarith
  rw [h8', h1, h2, h4]
  norm_num

end Nonvacuity

end WeierstrassCurve.Affine
