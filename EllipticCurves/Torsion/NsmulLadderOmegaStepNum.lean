/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulLadderOmegaStep
import EllipticCurves.Torsion.OmegaOnCurveCharFree

/-!
# The characteristic-`2` ladder step is **one polynomial divisibility**: `W.polynomial ∣ stepNumₙ`

`EllipticCurves.Torsion.NsmulLadderOmegaStep` reduced the `ω`-flavoured ladder step to a single
hypothesis `hY` — the group law's `y`-coordinate at `(n • P) + P` — and measured that everything
else in the step is free of `(2 : F) ≠ 0`.  It also proved `hY` **doubled**
(`two_mul_addY_divYω_eq`), so the whole residue of `h2` in the step is one cancellation of `2` in
`F`.  `#2340`'s round 3 then ruled that that row's route (a) is impossible at the *definition*
`WeierstrassCurve.Affine.divY`, and named what a route (b) owes.

⚠️⚠️ **That ruling is PR #931's `EllipticCurves.Torsion.OddCharTwoLadderObstruction`, which is
approved but had NOT landed at this file's base — it is cited here as a pull request and not as a
module of the tree, and nothing below imports it or depends on it.**

**This file pays the first rung of that route: it moves the residue out of the field and into the
polynomial ring, where the `2` is cancellable.**  The cleared numerator of `hY` is a single
polynomial `WeierstrassCurve.stepNum n ∈ R[X][Y]`, defined over every commutative ring with no
division anywhere, and

* `W.polynomial ∣ W.stepNumₙ` ⇒ the ladder step holds **with no hypothesis on `2` at all**
  (`nsmulEqDivω_step_of_dvd`), and so does the whole two-step induction
  (`nsmulEqDivω_of_forall_ψ_ne_zero_of_dvd`) and `n • P = (Φₙ/ΨSqₙ, ωNumₙ/ψₙ³)`
  (`nsmul_eq_some_divX_divYω_of_dvd`);
* the converse direction is priced exactly: `2·stepNumₙ(x, y) = 0` at every point of every curve
  over every field under the step's own hypotheses (`two_mul_evalEval_stepNum_eq_zero`), and
  `stepNumₙ(x, y) = 0` outright as soon as `(2 : F) ≠ 0`
  (`evalEval_stepNum_eq_zero_of_two_ne_zero`).

⚠️⚠️ **So the open problem is no longer a group-law statement about a characteristic and a point.
It is `W.polynomial ∣ W.stepNum n` over an arbitrary commutative ring, and nothing else.**  That is
worth the move because a divisibility in `R[X][Y]` is exactly the shape this tree already knows how
to prove by cancelling a unit-less integer **once**, over the universal curve: `map_stepNum` is
supplied here for that purpose, and `EllipticCurves.Torsion.OmegaOnCurveCharFree`'s
`polynomial_dvd_divPairNum` is the worked precedent — it cancels a `4` over
`MvPolynomial (Fin 5) ℤ` and carries the result down along `WeierstrassCurve.specialize`.

## What the numerator is, and why it is the right unit

Writing `pₘ = ψₘ(x, y)`, `wₘ = ωNumₘ(x, y)`, `Fₘ = Φₘ(x)`, the step's `y`-half is

```
addY (Φₙ/ΨSqₙ) x (ωNumₙ/ψₙ³) (slope …) − ωNum_{n+1}/ψ_{n+1}³
  = stepNumₙ(x, y) / (pₙ³·p_{n+1}³·p_{n−1})
```

(`addY_divYω_sub_eq`), with

```
stepNumₙ = (ωNumₙ − Y·ψₙ³)·(Φ_{n+1}·ψₙ² − Φₙ·ψ_{n+1}²)
             − ωNumₙ·ψ_{n+1}³·ψ_{n−1} − a₁·Φ_{n+1}·ψₙ³·ψ_{n+1}·ψ_{n−1}
             − a₃·ψₙ³·ψ_{n+1}³·ψ_{n−1} − ωNum_{n+1}·ψₙ³·ψ_{n−1}.
```

⚠️ **The three denominators are exactly the three nonvanishing hypotheses the step already
carries** — `ψₙ`, `ψ_{n+1}` and `ψ_{n−1}` — so clearing them costs no new hypothesis, and the
`slope`'s own denominator `x − Φₙ/ΨSqₙ` is `ψ_{n+1}ψ_{n−1}/ψₙ²` by `sub_Φ_div_ΨSq` rather than a
fourth datum.

⚠️ **`ψₙ²` and not `ΨSqₙ` in the `x`-coordinate terms**, unlike
`EllipticCurves.Torsion.OmegaOnCurveCharFree`'s `divPairNum`: the two agree at a point of the curve
(`ψ_sq_evalEval`) and differ as polynomials by a multiple of `4·W.polynomial`
(`four_mul_polynomial_dvd_ψ_sq_sub_C_ΨSq`), so either spelling states the same divisibility; this
one is chosen because it is the shape the point-level identity above clears to.

## ⚠️ Why the doubled identity cannot be cancelled where it stands

`two_mul_evalEval_stepNum_eq_zero` is `2·stepNumₙ(x, y) = 0`, not `2·stepNumₙ = 2·(W.polynomial·G)`
in `R[X][Y]`, and the difference is the whole point.  A field identity multiplied by `2` carries no
information in characteristic `2` — both sides are `0` — and no field is `2`-torsion-free, so the
cancellation cannot happen in `F`.  ⚠️ **In `MvPolynomial (Fin 5) ℤ` it can**, and that is the only
reason to restate the step as a divisibility: `R[X][Y]` over the universal curve is an integral
domain of characteristic `0`, `stepNum` and `W.polynomial` both commute with base change
(`map_stepNum`, `WeierstrassCurve.Affine.map_polynomial`), and a divisibility proved once there maps
to every ring.

## What is **not** here

* ⚠️⚠️ **`W.polynomial ∣ W.stepNum n` is NOT proved**, at any index past `n = 1`, and no statement
  below asserts it.  Every theorem that uses it takes it as a hypothesis, and
  `stepNum_one` is the one index at which it is discharged here — `stepNumₙ` is identically `0` at
  `n = 1`, because `ψ₀ = 0` kills four of its five terms and `ωNum₁ = Y` kills the fifth.
* ⚠️ **Nothing here weakens, restates or deprecates a landed statement.**  `nsmulEqDivω_step` keeps
  its `(2 : F) ≠ 0` and its proof; this file sits beside it.  The `215`-file `h2` population
  `#2340` measures is untouched.
* ⚠️ **No claim about `n • P = 0 ↔ ψₙ(P) = 0`.**  The dictionary of
  `EllipticCurves.Torsion.NsmulOrder` consumes the ladder and is not re-proved here; what is
  delivered is the ladder's step and the induction over it, conditionally.
* ⚠️ **Nothing about the Tate module.**  `#2340` items 4 and 5 consume item 3, which consumes the
  divisibility above.
* ⚠️ **`(ℓ : F) ≠ 0` is nowhere mentioned and is sharp**; `ℓ = 2` in characteristic `2` is
  `ℓ = char F`, where the conclusion of `#2340`'s headline is false rather than unproved.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], Exercise 3.7.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **The cleared numerator of the ladder step's `y`-half at index `n`**:

```
stepNumₙ = (ωNumₙ − Y·ψₙ³)·(Φ_{n+1}·ψₙ² − Φₙ·ψ_{n+1}²)
             − ωNumₙ·ψ_{n+1}³·ψ_{n−1} − a₁·Φ_{n+1}·ψₙ³·ψ_{n+1}·ψ_{n−1}
             − a₃·ψₙ³·ψ_{n+1}³·ψ_{n−1} − ωNum_{n+1}·ψₙ³·ψ_{n−1}   ∈ R[X][Y].
```

This is `addY (Φₙ/ΨSqₙ) x (ωNumₙ/ψₙ³) (slope …) = ωNum_{n+1}/ψ_{n+1}³` multiplied through by
`ψₙ³·ψ_{n+1}³·ψ_{n−1}`, with no division anywhere, so that it makes sense over a ring in which the
`ψ` are not invertible and in which `2 = 0`.  ⚠️ `ωNumₙ` is
`EllipticCurves.Torsion.OmegaIntegral`'s `2`-free `y`-numerator (`2·ωNumₙ = ωBracketₙ`), which is
why no `2` appears in the definition. -/
noncomputable def stepNum (n : ℤ) : R[X][Y] :=
  (W.ωNum n - Y * W.ψ n ^ 3) * (C (W.Φ (n + 1)) * W.ψ n ^ 2 - C (W.Φ n) * W.ψ (n + 1) ^ 2)
    - W.ωNum n * W.ψ (n + 1) ^ 3 * W.ψ (n - 1)
    - C (C W.a₁) * C (W.Φ (n + 1)) * W.ψ n ^ 3 * W.ψ (n + 1) * W.ψ (n - 1)
    - C (C W.a₃) * W.ψ n ^ 3 * W.ψ (n + 1) ^ 3 * W.ψ (n - 1)
    - W.ωNum (n + 1) * W.ψ n ^ 3 * W.ψ (n - 1)

/-- **`stepNum` commutes with base change.**

⚠️ **This is the lemma that makes the open divisibility provable over the universal curve alone**:
with it and `WeierstrassCurve.Affine.map_polynomial`, a proof of `W.polynomial ∣ W.stepNum n` over
`MvPolynomial (Fin 5) ℤ` — where `2` may be cancelled — descends to every commutative ring along
`WeierstrassCurve.specialize`, which is exactly how
`EllipticCurves.Torsion.OmegaOnCurveCharFree`'s `polynomial_dvd_divPairNum` cancels its `4`.  Of the
base-change family it uses, `map_ψ` and `map_Φ` are Mathlib's and `map_ωNum` is this project's, in
`EllipticCurves.Torsion.OmegaIntegral`. -/
lemma map_stepNum {S : Type*} [CommRing S] (f : R →+* S) (n : ℤ) :
    (W.map f).stepNum n = (W.stepNum n).map (mapRingHom f) := by
  simp only [stepNum, map_ωNum, map_ψ, map_Φ, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    coe_mapRingHom, Polynomial.map_X]

/-- **`stepNum 1 = 0` over every commutative ring**, so the divisibility hypothesis of every
theorem below is discharged at `n = 1` and the family is not vacuous.

⚠️ It is `0` for a reason that carries no information about the step: `ψ₀ = 0` annihilates the four
terms carrying `ψ_{n−1}`, and the surviving first factor is `ωNum₁ − Y·ψ₁³ = Y − Y = 0` by
`EllipticCurves.Torsion.OmegaIntegral`'s `ωNum_one` and Mathlib's `ψ_one`.  ⚠️ **The rung this
discharges is the one the ladder's base case already owns** (`nsmulEqDivω_one`), so nothing new
follows from it; it is here as a non-vacuity check on the hypothesis' shape. -/
lemma stepNum_one : W.stepNum 1 = 0 := by
  rw [stepNum, show (1 : ℤ) - 1 = 0 by ring, ψ_zero, ωNum_one, ψ_one]
  ring

namespace Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- `stepNumₙ` evaluated at a point, in the `ψ`/`ωNum`/`Φ` values the step's hypotheses name. -/
lemma evalEval_stepNum (n : ℤ) : (W.stepNum n).evalEval x y =
    ((W.ωNum n).evalEval x y - y * (W.ψ n).evalEval x y ^ 3) *
        ((W.Φ (n + 1)).eval x * (W.ψ n).evalEval x y ^ 2
          - (W.Φ n).eval x * (W.ψ (n + 1)).evalEval x y ^ 2)
      - (W.ωNum n).evalEval x y * (W.ψ (n + 1)).evalEval x y ^ 3 * (W.ψ (n - 1)).evalEval x y
      - W.a₁ * (W.Φ (n + 1)).eval x * (W.ψ n).evalEval x y ^ 3
          * (W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y
      - W.a₃ * (W.ψ n).evalEval x y ^ 3 * (W.ψ (n + 1)).evalEval x y ^ 3
          * (W.ψ (n - 1)).evalEval x y
      - (W.ωNum (n + 1)).evalEval x y * (W.ψ n).evalEval x y ^ 3
          * (W.ψ (n - 1)).evalEval x y := by
  simp only [stepNum, evalEval_sub, evalEval_mul, evalEval_pow, evalEval_C, eval_C, evalEval_X]

/-- **A divisibility by `W.polynomial` is a vanishing at every point of the curve.**  ⚠️ No
hypothesis on `2`: `W.Equation x y` *is* `W.polynomial.evalEval x y = 0`. -/
lemma evalEval_stepNum_eq_zero_of_dvd (h : W.Equation x y) {n : ℤ}
    (hdvd : W.polynomial ∣ W.stepNum n) : (W.stepNum n).evalEval x y = 0 := by
  obtain ⟨G, hG⟩ := hdvd
  rw [hG, evalEval_mul, show W.polynomial.evalEval x y = 0 from h, zero_mul]

variable [DecidableEq F]

/-- **The step's `y`-gap is `stepNumₙ` over the three `ψ` the step already assumes nonzero.**

⚠️ **This is the whole bridge between the field and the polynomial ring, and it binds no hypothesis
on `2`.**  The left-hand side is the difference the ladder step has to kill; the right-hand side has
the shape a divisibility can reach.  ⚠️ `hX` is the step's `x`-half, which
`EllipticCurves.Torsion.NsmulLadderOmegaStep`'s `nsmul_stepω_of_addY_eq` already proves `h2`-free;
it is a hypothesis here so that this lemma is about the `y`-coordinate alone, exactly as
`two_mul_addY_divYω_eq` is. -/
theorem addY_divYω_sub_eq (h : W.Equation x y) {n : ℤ}
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0)
    (hX : W.addX (W.divX x n) x (W.slope (W.divX x n) x (W.divYω x y n) y)
      = W.divX x (n + 1)) :
    W.addY (W.divX x n) x (W.divYω x y n)
          (W.slope (W.divX x n) x (W.divYω x y n) y)
        - W.divYω x y (n + 1)
      = (W.stepNum n).evalEval x y
        / ((W.ψ n).evalEval x y ^ 3 * (W.ψ (n + 1)).evalEval x y ^ 3
          * (W.ψ (n - 1)).evalEval x y) := by
  rw [evalEval_stepNum]
  have hsq0 : (W.ΨSq n).eval x = (W.ψ n).evalEval x y ^ 2 := (ψ_sq_evalEval h n).symm
  have hsq1 : (W.ΨSq (n + 1)).eval x = (W.ψ (n + 1)).evalEval x y ^ 2 :=
    (ψ_sq_evalEval h (n + 1)).symm
  have hgap0 := sub_Φ_div_ΨSq h h0
  have hsub0 : x - W.divX x n ≠ 0 := by
    rw [divX, hgap0]
    exact div_ne_zero (mul_ne_zero hp hm) (pow_ne_zero 2 h0)
  have hxne : W.divX x n ≠ x := fun hc => hsub0 (sub_eq_zero_of_eq hc.symm)
  have hXn : W.divX x n = (W.Φ n).eval x / (W.ψ n).evalEval x y ^ 2 := by rw [divX, hsq0]
  have hXn1 : W.divX x (n + 1) = (W.Φ (n + 1)).eval x / (W.ψ (n + 1)).evalEval x y ^ 2 := by
    rw [divX, hsq1]
  have hgapv : W.divX x n - x
      = -((W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y
          / (W.ψ n).evalEval x y ^ 2) := by
    rw [divX]; linear_combination -hgap0
  have hL : W.slope (W.divX x n) x (W.divYω x y n) y
      = -(((W.ωNum n).evalEval x y - y * (W.ψ n).evalEval x y ^ 3)
          / ((W.ψ n).evalEval x y * (W.ψ (n + 1)).evalEval x y
            * (W.ψ (n - 1)).evalEval x y)) := by
    rw [slope_of_X_ne hxne, divYω, hgapv]
    field_simp
  rw [addY, negAddY, hX, hL, negY, hXn1, hXn, divYω, divYω]
  field_simp
  ring

/-- ⚠️⚠️ **The step's `y`-half, with `(2 : F) ≠ 0` DELETED, from the vanishing of one polynomial.**
This is `#2250`'s route step 3 and the `hY` that
`EllipticCurves.Torsion.NsmulLadderOmegaStep`'s `## What is *not* here` prices, discharged from a
hypothesis that mentions neither the characteristic nor the point. -/
theorem addY_divYω_eq_of_evalEval_stepNum (h : W.Equation x y) {n : ℤ}
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0)
    (hX : W.addX (W.divX x n) x (W.slope (W.divX x n) x (W.divYω x y n) y)
      = W.divX x (n + 1))
    (hs : (W.stepNum n).evalEval x y = 0) :
    W.addY (W.divX x n) x (W.divYω x y n)
        (W.slope (W.divX x n) x (W.divYω x y n) y)
      = W.divYω x y (n + 1) := by
  rw [← sub_eq_zero, addY_divYω_sub_eq h hm h0 hp hX, hs, zero_div]

/-- **`2·stepNumₙ(x, y) = 0` at every point of every curve over every field**, under the step's own
hypotheses and with no hypothesis on `2`.

⚠️⚠️ **This is the pricing, moved from a proof to a polynomial.**  It is
`EllipticCurves.Torsion.NsmulLadderOmegaStep`'s `two_mul_addY_divYω_eq` read through
`addY_divYω_sub_eq`, and it says that the only thing standing between this tree and a
characteristic-free ladder step is a cancellation of `2`.  ⚠️ **In characteristic `2` it carries no
information** — both sides are `0` — which is exactly why the cancellation has to be performed
somewhere other than `F`; see the module docstring. -/
theorem two_mul_evalEval_stepNum_eq_zero (h : W.Equation x y) {n : ℤ}
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) (ht : (W.ψ 2).evalEval x y ≠ 0)
    (hX : W.addX (W.divX x n) x (W.slope (W.divX x n) x (W.divYω x y n) y)
      = W.divX x (n + 1)) :
    2 * (W.stepNum n).evalEval x y = 0 := by
  have hD : (W.ψ n).evalEval x y ^ 3 * (W.ψ (n + 1)).evalEval x y ^ 3
      * (W.ψ (n - 1)).evalEval x y ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h0) (pow_ne_zero 3 hp)) hm
  have key := two_mul_addY_divYω_eq h hm h0 hp ht hX
  have hsub := addY_divYω_sub_eq h hm h0 hp hX
  have h2 : (2 : F) * ((W.stepNum n).evalEval x y
      / ((W.ψ n).evalEval x y ^ 3 * (W.ψ (n + 1)).evalEval x y ^ 3
        * (W.ψ (n - 1)).evalEval x y)) = 0 := by
    rw [← hsub]; linear_combination key
  field_simp at h2
  linear_combination h2

/-- **`stepNumₙ(x, y) = 0` outright as soon as `(2 : F) ≠ 0`**, under the step's hypotheses.

⚠️ **This is the calibration that says the divisibility hypothesis below asks for nothing new in
characteristic `≠ 2`**: there the vanishing is already a theorem, so a proof of
`W.polynomial ∣ W.stepNum n` can add content only at `2 = 0`.  ⚠️ **It is a POINTWISE vanishing and
not the divisibility**: it is quantified over one point of one curve over one field, and no argument
here passes from such a family to a divisibility in `R[X][Y]`. -/
theorem evalEval_stepNum_eq_zero_of_two_ne_zero (h2 : (2 : F) ≠ 0) (h : W.Equation x y) {n : ℤ}
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) (ht : (W.ψ 2).evalEval x y ≠ 0)
    (hX : W.addX (W.divX x n) x (W.slope (W.divX x n) x (W.divYω x y n) y)
      = W.divX x (n + 1)) :
    (W.stepNum n).evalEval x y = 0 :=
  (mul_eq_zero.mp (two_mul_evalEval_stepNum_eq_zero h hm h0 hp ht hX)).resolve_left h2

/-- **The step's `x`-half, extracted from `nsmul_stepω_of_addY_eq`'s proof and with no hypothesis on
`2`.**

⚠️ It is stated separately because the `y`-half above consumes it: `addY_divYω_sub_eq` needs the
`x`-coordinate of `(n • P) + P` to be `divX x (n + 1)` before it can name the `y`-gap, and inside
`nsmul_stepω_of_addY_eq` that fact is derived after `hY` is already in hand.  ⚠️ **No content is
added here** — the proof is that file's, and the two point-level rungs are what make it a statement
about `n • P` rather than about the formulas. -/
theorem addX_divYω_eq (hns : W.Nonsingular x y) {n : ℤ}
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) (ht : (W.ψ 2).evalEval x y ≠ 0)
    (hm' : W.Nonsingular (W.divX x (n - 1)) (W.divYω x y (n - 1)))
    (h0' : W.Nonsingular (W.divX x n) (W.divYω x y n))
    (IHm : ((n - 1) • Point.some x y hns : W.Point) = .some _ _ hm')
    (IH0 : ((n : ℤ) • Point.some x y hns : W.Point) = .some _ _ h0') :
    W.addX (W.divX x n) x (W.slope (W.divX x n) x (W.divYω x y n) y)
      = W.divX x (n + 1) := by
  have hEq : W.Equation x y := hns.left
  have hgap0 := sub_Φ_div_ΨSq hEq h0
  have hsub0 : x - W.divX x n ≠ 0 := by
    rw [divX, hgap0]
    exact div_ne_zero (mul_ne_zero hp hm) (pow_ne_zero 2 h0)
  have hxne : W.divX x n ≠ x := fun hc => hsub0 (sub_eq_zero_of_eq hc.symm)
  have hminus : ((n - 1 : ℤ) • Point.some x y hns : W.Point)
      = (n : ℤ) • Point.some x y hns + -(Point.some x y hns) := by
    rw [sub_smul, one_zsmul, sub_eq_add_neg]
  rw [IH0, Point.neg_some, Point.add_of_X_ne hxne, IHm, Point.some.injEq] at hminus
  have hT : W.divYω x y n - W.negY (W.divX x n) (W.divYω x y n) = W.divT x y n :=
    divYω_sub_negY_divX hEq ht h0
  have hψ₂ : y - W.negY x y = (W.ψ 2).evalEval x y := by
    rw [negY, ψ_two_evalEval]; ring
  rw [addX_eq_addX_negY_sub _ _ hxne, ← hminus.1, hT, hψ₂, divX_add_one hEq hm h0 hp]

/-- ⚠️⚠️ **THE LADDER STEP WITH NO `(2 : F) ≠ 0`, FROM ONE POLYNOMIAL DIVISIBILITY.**

`EllipticCurves.Torsion.NsmulLadderOmegaStep`'s `nsmulEqDivω_step` binds `(2 : F) ≠ 0`; this is the
same step with that hypothesis replaced by `W.polynomial ∣ W.stepNum n`, a statement about the
curve's coefficient ring and not about its characteristic.  ⚠️ **The three `ψ ≠ 0` hypotheses and
`ψ₂ ≠ 0` are unchanged and are not weakened** — in characteristic `2` the last of them reads
`a₁x + a₃ ≠ 0`, which is where smoothness is spent. -/
theorem nsmulEqDivω_step_of_dvd (hns : W.Nonsingular x y) {n : ℤ}
    (hdvd : W.polynomial ∣ W.stepNum n)
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) (ht : (W.ψ 2).evalEval x y ≠ 0)
    (Gm : NsmulEqDivω hns (n - 1)) (G0 : NsmulEqDivω hns n) : NsmulEqDivω hns (n + 1) := by
  obtain ⟨hm', IHm⟩ := Gm
  obtain ⟨h0', IH0⟩ := G0
  have hX := addX_divYω_eq hns hm h0 hp ht hm' h0' IHm IH0
  exact nsmul_stepω_of_addY_eq hns hm h0 hp ht hm' h0' IHm IH0
    (addY_divYω_eq_of_evalEval_stepNum hns.left hm h0 hp hX
      (evalEval_stepNum_eq_zero_of_dvd hns.left hdvd))

/-- **The two-step induction, with no hypothesis on `2`.**  ⚠️ Both components are needed in the
statement — the step consumes two consecutive rungs — and the shape is
`EllipticCurves.Torsion.NsmulLadder`'s `nsmulEqDiv_pair` with `h2` replaced by the divisibility and
`ψ₂ ≠ 0` promoted out of the ladder hypothesis, because the `n = 2` base case needs it on its
own. -/
private theorem nsmulEqDivω_pair_of_dvd (hns : W.Nonsingular x y)
    (hdvd : ∀ k : ℤ, W.polynomial ∣ W.stepNum k) (ht : (W.ψ 2).evalEval x y ≠ 0) :
    ∀ m : ℕ, (∀ k : ℤ, 1 ≤ k → k ≤ (m : ℤ) + 2 → (W.ψ k).evalEval x y ≠ 0) →
      NsmulEqDivω hns ((m : ℤ) + 1) ∧ NsmulEqDivω hns ((m : ℤ) + 2) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨by simpa using nsmulEqDivω_one hns, by simpa using nsmulEqDivω_two hns ht⟩
  | succ k IH =>
    intro hψ
    obtain ⟨G1, G2⟩ := IH fun j hj hj2 => hψ j hj (by push_cast at hj2 ⊢; omega)
    have hcast : ((k : ℕ) : ℤ) + 1 + 1 = ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    refine ⟨by rw [← hcast]; exact G2, ?_⟩
    have hne : ∀ j : ℤ, 1 ≤ j → j ≤ (k : ℤ) + 3 → (W.ψ j).evalEval x y ≠ 0 := by
      intro j hj hj2; exact hψ j hj (by push_cast; omega)
    have hstep := nsmulEqDivω_step_of_dvd (n := (k : ℤ) + 2) hns (hdvd _)
      (by rw [show (k : ℤ) + 2 - 1 = (k : ℤ) + 1 by ring]
          exact hne _ (by omega) (by omega))
      (hne _ (by omega) (by omega))
      (by rw [show (k : ℤ) + 2 + 1 = (k : ℤ) + 3 by ring]
          exact hne _ (by omega) (by omega))
      ht
      (by rw [show (k : ℤ) + 2 - 1 = (k : ℤ) + 1 by ring]; exact G1) G2
    rw [show ((k + 1 : ℕ) : ℤ) + 2 = (k : ℤ) + 2 + 1 by push_cast; ring]
    exact hstep

/-- ⚠️⚠️ **THE LADDER ALONG A NONVANISHING `ψ`, WITH NO `(2 : F) ≠ 0`.**  The `h2`-free counterpart
of `EllipticCurves.Torsion.NsmulLadder`'s `nsmulEqDiv_of_forall_ψ_ne_zero`, conditional on the one
divisibility.

⚠️ The hypothesis needed is `ψ_k ≠ 0` up to `k = n` and no further, as there: the induction is
arranged so that the rung reaching `n` is the second component of the pair.  ⚠️ **`ψ₂ ≠ 0` is not a
separate hypothesis here** — it is the `k = 2` instance of the ladder hypothesis, which `n ≥ 2`
supplies. -/
theorem nsmulEqDivω_of_forall_ψ_ne_zero_of_dvd (hns : W.Nonsingular x y)
    (hdvd : ∀ k : ℤ, W.polynomial ∣ W.stepNum k) {n : ℕ} (hn : 1 ≤ n)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    NsmulEqDivω hns (n : ℤ) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · obtain rfl : n = 1 := by omega
    simpa using nsmulEqDivω_one hns
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have ht : (W.ψ 2).evalEval x y ≠ 0 := hψ 2 (by norm_num) (by push_cast; omega)
    have H := (nsmulEqDivω_pair_of_dvd hns hdvd ht m
      fun k hk hk2 => hψ k hk (by push_cast at hk2 ⊢; omega)).2
    rwa [show ((m : ℕ) : ℤ) + 2 = ((m + 2 : ℕ) : ℤ) by push_cast; ring] at H

/-- ⚠️⚠️ **`n • P = (Φₙ(x)/ΨSqₙ(x), ωNumₙ(x, y)/ψₙ(x, y)³)` WITH NO HYPOTHESIS ON `2`**, at every
index `n ≥ 1` whose ladder has no zero — conditional on the divisibility.

⚠️ **This is `#2340`'s route (b) in one statement.**  `EllipticCurves.Torsion.NsmulLadder`'s
`nsmul_eq_some_Φ_div_ΨSq` gives only the `x`-coordinate and binds `h2`; this names both coordinates
and binds none, the `y`-coordinate being
`EllipticCurves.Torsion.OmegaIntegral`'s unhalved `ωNumₙ` rather than `divY`.  ⚠️ **In
characteristic `2` the landed form is not merely unproved but false**, which PR #931's
`not_nsmul_one_eq_div_of_two_eq_zero` proves at `n = 1` (⚠️ a pull request and not yet a module of
this tree), so this is a different statement and not a weakening of one. -/
theorem nsmul_eq_some_divX_divYω_of_dvd (hns : W.Nonsingular x y)
    (hdvd : ∀ k : ℤ, W.polynomial ∣ W.stepNum k) {n : ℕ} (hn : 1 ≤ n)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    ∃ h' : W.Nonsingular ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x)
        ((W.ωNum (n : ℤ)).evalEval x y / (W.ψ (n : ℤ)).evalEval x y ^ 3),
      (n • Point.some x y hns : W.Point) = .some _ _ h' := by
  obtain ⟨h', heq⟩ := nsmulEqDivω_of_forall_ψ_ne_zero_of_dvd hns hdvd hn hψ
  exact ⟨h', by rw [← natCast_zsmul]; exact heq⟩

/-- **`n • P = 0` forces one of `ψ₁(P), …, ψₙ(P)` to vanish, with no hypothesis on `2`** —
conditional on the divisibility.

⚠️ **This is the half of the division-polynomial dictionary that the ladder gives, and it is the
half `#2340`'s odd-index count consumes through
`EllipticCurves.Torsion.NsmulOrder`.**  The converse (`ψₙ(P) = 0 → n • P = 0`) is not proved here
and is not this file's; neither is the sharpening that the vanishing index may be taken to be `n`
itself. -/
theorem exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero_of_dvd (hns : W.Nonsingular x y)
    (hdvd : ∀ k : ℤ, W.polynomial ∣ W.stepNum k) {n : ℕ} (hn : 1 ≤ n)
    (hzero : (n • Point.some x y hns : W.Point) = 0) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ (n : ℤ) ∧ (W.ψ k).evalEval x y = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h', heq⟩ := nsmul_eq_some_divX_divYω_of_dvd hns hdvd hn
    fun k hk hk2 => hcon k hk hk2
  rw [heq] at hzero
  exact Point.some_ne_zero h' hzero

/-! ### ⚠️ What the reduction buys in characteristic `2`, exhibited and not asserted -/

section CharTwo

open EllipticCurves.Fixture

/-- ⚠️⚠️ **The rung at `n = 3` over `ZMod 2`, which no `h2`-bound statement of this tree can
produce** — conditional on the divisibility, which is what makes the conditional worth stating.

`curveCharTwoOne = ⟨1, 0, 0, 0, 1⟩` over `ZMod 2` at `(1, 0)`, where `2 = 0`, `ψ₂(1, 0) = 1 ≠ 0`
(`EllipticCurves.Torsion.DoublingOmega`'s `evalEval_ψ_two_curveCharTwoOne`) and `ψ₃(1, 0) ≠ 0`
(`EllipticCurves.Torsion.OmegaOnCurveCharFree`'s
`ψ_three_evalEval_ne_zero_curveCharTwoOne`).  ⚠️ **`NsmulEqDiv` is FALSE at this point** —
`EllipticCurves.Torsion.NsmulLadderOmega`'s `not_nsmulEqDiv_two_curveCharTwoOne` — so the
`ω`-flavoured predicate is doing the work and not the halved one. -/
example (hdvd : ∀ k : ℤ, curveCharTwoOne.polynomial ∣ curveCharTwoOne.stepNum k) :
    NsmulEqDivω nonsingular_curveCharTwoOne 3 := by
  refine nsmulEqDivω_of_forall_ψ_ne_zero_of_dvd nonsingular_curveCharTwoOne hdvd
    (n := 3) (by norm_num) ?_
  intro k hk hk2
  interval_cases k
  · rw [ψ_one_evalEval]; exact one_ne_zero
  · rw [evalEval_ψ_two_curveCharTwoOne]; exact one_ne_zero
  · exact ψ_three_evalEval_ne_zero_curveCharTwoOne

end CharTwo

end Affine

end WeierstrassCurve
