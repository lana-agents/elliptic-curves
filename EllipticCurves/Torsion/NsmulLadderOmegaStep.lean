/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulLadderOmega

/-!
# The `ω`-flavoured ladder step: the `x`-half with no `(2 : F) ≠ 0`, and the `y`-half priced

`EllipticCurves.Torsion.NsmulLadderOmega` landed `divYω`, the predicted `y`-coordinate
`ωNumₙ(x, y)/ψₙ(x, y)³` with no `2` in it, the predicate `NsmulEqDivω`, and both base cases
`n = 1` and `n = 2` with no `(2 : F) ≠ 0`.  Its `## What is *not* here` named the ladder STEP as
the next rung and called it the expensive one.

**This file runs that step as far as it goes without `(2 : F) ≠ 0`, and prices exactly what is
left.**  The answer is sharper than *"the step needs `h2`"*:

* the **`x`-coordinate half is `h2`-free outright** — it is inside `nsmul_stepω_of_addY_eq`, which
  binds no hypothesis on `2` at all;
* the **`y`-coordinate half holds after multiplying by `2`**, also `h2`-free
  (`two_mul_addY_divYω_eq`);
* so the whole residue of `h2` in the `ω` ladder step is **one division by `2` in `F`**, and
  nothing else.

## Where `NsmulLadder`'s `h2` actually goes, measured rather than predicted

`EllipticCurves.Torsion.NsmulLadder`'s `nsmul_step` binds `(2 : F) ≠ 0` and **never mentions it in
its proof text** — `grep` for the token over that proof returns its own binder and nothing else —
so it is spent implicitly, by `field_simp`.  ⚠️ **That it is spent at the two sites below and
nowhere else in the step is MEASURED and not asserted**: `nsmul_stepω_of_addY_eq` is that proof
with both sites supplied, and it binds no hypothesis on `2` at all.

1. `hT`, which says `divYₙ − negY(divXₙ, divYₙ) = divTₙ`.  `divY` is *defined* as
   `(divTₙ − a₁divXₙ − a₃)/2`, so that equation is `2·(z/2) = z` and needs `2 ≠ 0`.
   ⚠️ **`divYω_sub_negY_divX` below is the same statement for `divYω` and binds no `h2`**: the
   `ω`-numerator is not halved, and the identity that replaces the cancellation is
   `two_mul_evalEval_ωNum_mul`, itself `two_mul_ωNum` and `ψ_two_mul_evalEval` combined.
2. `hY`, the group law's `y`-coordinate.  ⚠️ **Once `divY` is replaced by `divYω`**, doubling that
   goal turns it into `divT_add_one`, which is `h2`-free — `two_mul_addY_divYω_eq` below is exactly
   that doubled form — so the goal holds up to a factor of `2` over any field, and `h2` is spent
   only on cancelling it.  ⚠️ **On `divY` itself the doubling is not free**, because
   `2·divYₙ = divTₙ − a₁divXₙ − a₃` is site 1's own cancellation over again.

⚠️⚠️ **Site 1 is NOT the `x`-coordinate's and site 2 IS the `y`-coordinate's, which sharpens
the prediction `EllipticCurves.Torsion.OmegaIntegral`'s `nsmul_eq_some_ωNum` records.**  That
docstring says the residual `h2` of `nsmul_eq_some_omegaY` is *"the `x`-coordinate / group-law
half, which no amount of work on `ωₙ` can reach"*.  ⚠️ It is that theorem's docstring and not
`omegaY_eq`'s, which makes the opposite-facing point — that `h2` there pays for the halved
left-hand side and *"does not pay for `ωNum`"* — and asserts nothing about an `x`-coordinate
half.  The load-bearing claim is true and is not disturbed here: `nsmul_eq_some_ωNum` still binds
`h2`.  What is measured here is **where**: work on `ωₙ` reaches the `x`-coordinate half entirely,
and the residue is the group law's **`y`**-coordinate, reduced to a single cancellation of `2`.

## ⚠️ Why the last step is a genuine characteristic-`2` statement and not bookkeeping

`two_mul_addY_divYω_eq` **carries no information where `2 = 0`**: both sides are `0` there.  That
is not a defect of the lemma, it is the pricing — it says the remaining gap is exactly the content
`divT` loses in characteristic `2`.  And `divT` does lose it: `two_mul_divYω_add` reads
`a₁divXₙ + a₃ = divTₙ` when `2 = 0`, an identity with **no `y` in it at all**, so `divTₙ` cannot
distinguish `n • P` from `−n • P` there.  ⚠️ **The sign therefore has to come from `ωNum` itself**,
which is why the remaining half is a new polynomial identity rather than a rearrangement of the
landed ones.

## Main results

⚠️ Every public declaration of this file is listed: **7 public, 0 private, 7 listed.**

* `WeierstrassCurve.Affine.two_mul_evalEval_ωNum_mul` :
  `2ωₙ(x, y)·ψₙ + a₁Φₙ(x)·ψₙ² + a₃·ψₙ⁴ = ψ₂ₙ(x, y)` at a point of `W` at which `ψ₂` does not
  vanish, over **any** field — binds `W.Equation x y` and `ψ₂(x, y) ≠ 0` and **no `h2`**.
* `WeierstrassCurve.Affine.two_mul_divYω_add` : `2·divYωₙ + a₁divXₙ + a₃ = divTₙ`, no `h2`.
* `WeierstrassCurve.Affine.divYω_sub_negY_divX` : `divYωₙ − negY(divXₙ, divYωₙ) = divTₙ`, no `h2` —
  the `ω` counterpart of `nsmul_step`'s `hT`.
* `WeierstrassCurve.Affine.two_mul_addY_divYω_eq` : the ladder step's `y`-half **after multiplying
  by `2`**, no `h2`.
* `WeierstrassCurve.Affine.nsmul_stepω_of_addY_eq` : **the ladder step on `divYω` with `h2`
  DROPPED**, conditional on the undoubled `y`-half, which it takes as the hypothesis `hY`.  The
  `x`-half is proved inside it.
* `WeierstrassCurve.Affine.nsmulEqDivω_step` : the ladder step on `NsmulEqDivω`, **unconditional**,
  under `h2` — route step 3 of `#2250` as far as `h2` makes it free.
* `WeierstrassCurve.Affine.divX_two_eq_divT_two_curveCharTwoOne` : a characteristic-`2`
  non-vacuity certificate for `two_mul_divYω_add`, obtained with no computation.

## ⚠️ What is *not* here

**The undoubled `y`-half.**  `nsmul_stepω_of_addY_eq`'s hypothesis `hY` is `#2250`'s route step 3
in its entirety, and this file does not discharge it.  ⚠️ **What a round that wants it must build
is a polynomial identity over an arbitrary commutative ring**, in `ωNumₙ`, `ωNumₙ₊₁`, `Φₙ`,
`Φₙ₊₁`, `ψₙ₋₁`, `ψₙ`, `ψₙ₊₁` and `ψ₂`, descended from a characteristic-`0` domain where the
factor of `2` cancels — the pattern `EllipticCurves.Torsion.OmegaChordSum` already runs for
`WeierstrassCurve.HasOmegaChord`, whose own `2` is cancelled over `univQ` and carried back to every
ring by `hasOmegaChord_of_univQ`.  ⚠️ **It cannot be got from `divT_add_one`**: that route is the
doubled one, and `two_mul_addY_divYω_eq` is it.

**Route step 4 and the `h2`-free general-`n` `HasXCoordFormula`.**  Untouched; `#2250` names it and
it is downstream of the step above.

**A ruling on one landed sentence, measured and deliberately NOT edited.**
`NsmulLadderOmega`'s own `## What is *not* here` says of `nsmul_eq_some_ωNum` and
`nsmul_eq_some_ωNum_of_ΨSq_ne_zero` that both *"still bind `(2 : F) ≠ 0`, for the `x`-half's
reason rather than the halving's"*.  ⚠️ **Both do still bind it — that half is untouched here.**
But the two sites the section above measures are `nsmul_step`'s, and the chain
`nsmulEqDiv_of_forall_ψ_ne_zero` spends its own `h2` through has as its leaves `divY_one`,
`addY_self_eq_div`'s `/(2·ψ₂³)` and `nsmul_step`'s `hT` and `hY` — of which only `hY` is the group
law's and every other is a halving; so *"rather than the halving's"* is a disjunction this file
measures to be a conjunction.
⚠️ **It is left standing rather than re-worded because it is a claim about two theorems of another
module and the sharpening belongs in one place**, which is the section above.

**Nothing landed is re-proved and nothing landed is edited** beyond one paragraph of
`NsmulLadderOmega`'s own `## What is *not* here`, which named the step as absent and would
otherwise now be stale.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Exercise 3.7
-/

open Polynomial WeierstrassCurve

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-! ### The `ω`/`divT` bridge with no `(2 : F) ≠ 0` -/

/-- **`2ωₙ(x, y)·ψₙ + a₁Φₙ(x)·ψₙ² + a₃·ψₙ⁴ = ψ₂ₙ(x, y)`**, at a point of `W` at which `ψ₂` does not
vanish, over **any** field.

⚠️ **No `(2 : F) ≠ 0`**, and the `2` on the left is not cancelled anywhere: the proof is
`two_mul_ωNum` (`2ωₙ = ωBracketₙ`, an identity in `R[X][Y]` over every commutative ring) evaluated
at the point, plus `ψ_two_mul_evalEval` for `ψ₂ₙ`, and the `a₁Φₙ`/`a₃ΨSqₙ` terms of `ωBracket` are
exactly what the two added terms cancel.

⚠️ **`hψ₂` is `ψ_two_mul_evalEval`'s and is not decoration** — it is where that lemma cancels a
common factor of `ψ₂` at the point; `h` is where `ΨSqₙ(x) = ψₙ(x, y)²` is read off the curve. -/
theorem two_mul_evalEval_ωNum_mul (h : W.Equation x y)
    (hψ₂ : (W.ψ 2).evalEval x y ≠ 0) (n : ℤ) :
    2 * (W.ωNum n).evalEval x y * (W.ψ n).evalEval x y
        + W.a₁ * (W.Φ n).eval x * (W.ψ n).evalEval x y ^ 2
        + W.a₃ * (W.ψ n).evalEval x y ^ 4
      = (W.ψ (2 * n)).evalEval x y := by
  have hsq : (W.ΨSq n).eval x = (W.ψ n).evalEval x y ^ 2 := (ψ_sq_evalEval h n).symm
  have hbr := congrArg (Polynomial.evalEval x y) (two_mul_ωNum (W := W) n)
  rw [evalEval_ωBracket] at hbr
  have h2c : Polynomial.evalEval x y (2 : Polynomial (Polynomial F)) = 2 := by
    rw [← map_ofNat (C : Polynomial F →+* Polynomial (Polynomial F)) 2, evalEval_C, eval_ofNat]
  rw [evalEval_mul, h2c, hsq, ← ψ_two_evalEval (W := W) (x := x) (y := y)] at hbr
  rw [ψ_two_mul_evalEval h hψ₂ n]
  linear_combination (W.ψ n).evalEval x y * hbr

/-- **`2·divYωₙ + a₁·divXₙ + a₃ = divTₙ`**, over any field and with no `(2 : F) ≠ 0`.

This is `two_mul_evalEval_ωNum_mul` with the denominators put back: `divYω = ωNum/ψ³`,
`divX = Φ/ΨSq` and `divT = ψ₂ₙ/ψₙ⁴`, with `ΨSqₙ = ψₙ²` on the curve.

⚠️ **In characteristic `2` it reads `a₁divXₙ + a₃ = divTₙ`, an identity with no `y` in it**, which
is the module docstring's point: `divT` is the halved datum's companion and carries no sign
information where `2 = 0`. -/
theorem two_mul_divYω_add (h : W.Equation x y) (hψ₂ : (W.ψ 2).evalEval x y ≠ 0)
    {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    2 * W.divYω x y n + W.a₁ * W.divX x n + W.a₃ = W.divT x y n := by
  have hsq : (W.ΨSq n).eval x = (W.ψ n).evalEval x y ^ 2 := (ψ_sq_evalEval h n).symm
  have key := two_mul_evalEval_ωNum_mul h hψ₂ n
  rw [divYω, divX, divT, hsq]
  field_simp
  linear_combination key

/-- **`divYωₙ − negY(divXₙ, divYωₙ) = divTₙ`**, with no `(2 : F) ≠ 0`.

⚠️ **This is the `ω` counterpart of `NsmulLadder`'s `nsmul_step` step `hT`, and it is the site at
which that proof spends its `h2`** — there the left-hand side is `2·(divTₙ − a₁divXₙ − a₃)/2` and
the cancellation needs `2 ≠ 0`; here the numerator is never halved.  `negY a b = −b − a₁a − a₃`,
so the left-hand side is `2·divYωₙ + a₁divXₙ + a₃` and this is `two_mul_divYω_add` restated in the
shape the group law consumes. -/
theorem divYω_sub_negY_divX (h : W.Equation x y) (hψ₂ : (W.ψ 2).evalEval x y ≠ 0)
    {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    W.divYω x y n - W.negY (W.divX x n) (W.divYω x y n) = W.divT x y n := by
  rw [negY]
  linear_combination two_mul_divYω_add h hψ₂ hψ

/-! ### The ladder step: the `x`-half free, the `y`-half priced -/

variable [DecidableEq F]

/-- **The ladder step's `y`-half, after multiplying by `2`**, with no `(2 : F) ≠ 0`.

Doubling the goal turns every `divYω` into a `divT` through `two_mul_divYω_add` and every `y` into
`ψ₂(x, y)` through `ψ_two_evalEval`, and what is left is `divT_add_one` — which binds no `h2`.  The
`a₁` terms cancel identically, which is why no hypothesis on `a₁` appears.

⚠️⚠️ **It carries no information where `2 = 0`**: both sides are `0` there.  That is the pricing
and not a defect — see the module docstring.  ⚠️ `hX` is the `x`-half, which
`nsmul_stepω_of_addY_eq` proves `h2`-free; it is a hypothesis here so that this lemma is about the
`y`-coordinate alone. -/
theorem two_mul_addY_divYω_eq (h : W.Equation x y)
    {n : ℤ} (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) (ht : (W.ψ 2).evalEval x y ≠ 0)
    (hX : W.addX (W.divX x n) x (W.slope (W.divX x n) x (W.divYω x y n) y)
      = W.divX x (n + 1)) :
    2 * W.addY (W.divX x n) x (W.divYω x y n)
        (W.slope (W.divX x n) x (W.divYω x y n) y)
      = 2 * W.divYω x y (n + 1) := by
  have hgap0 := sub_Φ_div_ΨSq h h0
  have hsub0 : x - W.divX x n ≠ 0 := by
    rw [divX, hgap0]
    exact div_ne_zero (mul_ne_zero hp hm) (pow_ne_zero 2 h0)
  have hxne : W.divX x n ≠ x := fun hc => hsub0 (sub_eq_zero_of_eq hc.symm)
  have hT0 := two_mul_divYω_add h ht h0
  have hT1 := two_mul_divYω_add h ht hp
  have hstep := divT_add_one h h0 hp ht
  have hψ₂' : 2 * y + W.a₁ * x + W.a₃ = (W.ψ 2).evalEval x y := ψ_two_evalEval.symm
  rw [addY, negAddY, hX, slope_of_X_ne hxne, negY]
  have hd : W.divX x n - x ≠ 0 := fun hc => hsub0 (by linear_combination -hc)
  field_simp
  linear_combination (-hstep) + (W.divX x (n + 1) - W.divX x n) * hψ₂'
    - (W.divX x n - x) * hT1 - (W.divX x (n + 1) - x) * hT0

/-- **The ladder step on `divYω` with `(2 : F) ≠ 0` DROPPED**, conditional on the `y`-half.

Every ingredient of `NsmulLadder`'s `nsmul_step` survives the substitution of `divYω` for `divY`
with no hypothesis on `2`: the two point-level rewrites are the group law, `divX_add_one` is
`h2`-free already, and the one site that was not — `hT` — is `divYω_sub_negY_divX`.

⚠️ **`hY` is `#2250`'s route step 3 and this file does not discharge it.**  It is stated exactly as
`nsmul_step` proves its own `hY`, so a later round that supplies it closes the step by plugging in
one lemma and changing nothing here.  `two_mul_addY_divYω_eq` is `hY` doubled, so what `hY` adds
over this file is precisely one cancellation of `2` in `F`. -/
theorem nsmul_stepω_of_addY_eq (hns : W.Nonsingular x y) {n : ℤ}
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) (ht : (W.ψ 2).evalEval x y ≠ 0)
    (hm' : W.Nonsingular (W.divX x (n - 1)) (W.divYω x y (n - 1)))
    (h0' : W.Nonsingular (W.divX x n) (W.divYω x y n))
    (IHm : ((n - 1) • Point.some x y hns : W.Point) = .some _ _ hm')
    (IH0 : ((n : ℤ) • Point.some x y hns : W.Point) = .some _ _ h0')
    (hY : W.addY (W.divX x n) x (W.divYω x y n)
      (W.slope (W.divX x n) x (W.divYω x y n) y) = W.divYω x y (n + 1)) :
    NsmulEqDivω hns (n + 1) := by
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
  have hplus : ((n + 1 : ℤ) • Point.some x y hns : W.Point)
      = (n : ℤ) • Point.some x y hns + Point.some x y hns := by
    rw [add_smul, one_zsmul]
  rw [IH0, Point.add_of_X_ne hxne] at hplus
  have hT : W.divYω x y n - W.negY (W.divX x n) (W.divYω x y n) = W.divT x y n :=
    divYω_sub_negY_divX hEq ht h0
  have hψ₂ : y - W.negY x y = (W.ψ 2).evalEval x y := by
    rw [negY, ψ_two_evalEval]; ring
  have hX : W.addX (W.divX x n) x (W.slope (W.divX x n) x (W.divYω x y n) y)
      = W.divX x (n + 1) := by
    rw [addX_eq_addX_negY_sub _ _ hxne, ← hminus.1, hT, hψ₂, divX_add_one hEq hm h0 hp]
  have hns' : W.Nonsingular (W.divX x (n + 1)) (W.divYω x y (n + 1)) := by
    rw [← hX, ← hY]
    exact nonsingular_add h0' hns fun hc => hxne hc.1
  exact ⟨hns', by rw [hplus, Point.some.injEq]; exact ⟨hX, hY⟩⟩

/-- **The ladder step on `NsmulEqDivω`, unconditional, under `(2 : F) ≠ 0`** — `#2250`'s route
step 3 as far as `h2` makes it free.

⚠️ **It is `NsmulLadder`'s `nsmulEqDiv_step` transported across `nsmulEqDivω_one`'s companion
`nsmulEqDiv_iff_nsmulEqDivω`, and that is the whole proof**: under `h2` and the three `ψ ≠ 0`
hypotheses the two predicates are interchangeable at each of `n − 1`, `n` and `n + 1`, so nothing
is re-proved.  ⚠️ **What it does NOT do is drop `h2`** — that is `nsmul_stepω_of_addY_eq` plus the
one lemma that file's `## What is *not* here` prices. -/
theorem nsmulEqDivω_step (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) {n : ℤ}
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) (ht : (W.ψ 2).evalEval x y ≠ 0)
    (Gm : NsmulEqDivω hns (n - 1)) (G0 : NsmulEqDivω hns n) : NsmulEqDivω hns (n + 1) :=
  (nsmulEqDiv_iff_nsmulEqDivω h2 hns ht hp).mp
    (nsmulEqDiv_step h2 hns hm h0 hp ht
      ((nsmulEqDiv_iff_nsmulEqDivω h2 hns ht hm).mpr Gm)
      ((nsmulEqDiv_iff_nsmulEqDivω h2 hns ht h0).mpr G0))

/-! ### ⚠️ Non-vacuity in characteristic `2`, with no computation -/

/-- ⚠️⚠️ **`divX 1 2 = divT 1 0 2` on `curveCharTwoOne`** — a nontrivial identity in
characteristic `2`, read straight off `two_mul_divYω_add` with **no evaluation of any division
polynomial**.

`curveCharTwoOne = ⟨1, 0, 0, 0, 1⟩` over `ZMod 2`, so `a₁ = 1`, `a₃ = 0` and `2 = 0`, and
`2·divYω₂ + a₁divX₂ + a₃ = divT₂` collapses to `divX₂ = divT₂`.  ⚠️ **No `h2`-bound lemma of this
development can produce it**, which is what makes it a non-vacuity certificate for the `h2`-free
form rather than a restatement: `NsmulLadder`'s own `hT` is `divY₂ − negY(divX₂, divY₂) = divT₂`,
and at this point `divY 1 0 2 = 0` by `divY_eq_zero_of_two_eq_zero`, so that equation reads
`a₁divX₂ + a₃ = divT₂` only *after* the halving has been undone — which is exactly what fails
here. -/
theorem divX_two_eq_divT_two_curveCharTwoOne :
    curveCharTwoOne.divX 1 2 = curveCharTwoOne.divT 1 0 2 := by
  have hψ₂ : (curveCharTwoOne.ψ 2).evalEval 1 0 ≠ 0 := by
    rw [evalEval_ψ_two_curveCharTwoOne]; decide
  have key := two_mul_divYω_add (W := curveCharTwoOne) equation_curveCharTwoOne hψ₂ hψ₂
  have h2 : (2 : ZMod 2) = 0 := by decide
  have ha₁ : curveCharTwoOne.a₁ = 1 := rfl
  have ha₃ : curveCharTwoOne.a₃ = 0 := rfl
  rw [h2, ha₁, ha₃] at key
  linear_combination key

end WeierstrassCurve.Affine
