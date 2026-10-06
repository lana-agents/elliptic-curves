/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulLadderOmegaStepDvd

/-!
# `n • P = 0 ↔ ψₙ(P) = 0` with `(2 : F) ≠ 0` DELETED

`EllipticCurves.Torsion.NsmulOrder` proves the order dictionary — `n • P = 0 ↔ ψₙ(P) = 0` at a
point which is not `2`-torsion — over a field with `(2 : F) ≠ 0`.  Every one of the eleven
declarations of that file which binds `h2 : (2 : F) ≠ 0` spends it in exactly one way: it hands it
to one of **three** theorems of `EllipticCurves.Torsion.NsmulLadder`, namely
`nsmulEqDiv_of_forall_ψ_ne_zero`, `nsmul_eq_some_Φ_div_ΨSq` and
`exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero`.

`EllipticCurves.Torsion.NsmulLadderOmegaStepDvd` has since proved all three with no hypothesis on
`2` — `nsmulEqDivω_of_forall_ψ_ne_zero'`, `nsmul_eq_some_divX_divYω` and
`exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero'`, the `ω`-flavoured ladder.  **This file is that
substitution carried out, so the dictionary holds over every field and in particular in
characteristic `2`.**

## ⚠️⚠️ Why this is a new module and not an edit to `NsmulOrder.lean`

**`EllipticCurves.Torsion.NsmulOrder` is seven import edges BELOW the `ω` tower**, so it cannot
see route (b) at all:

```
NsmulLadderOmegaStepDvd → NsmulLadderOmegaStepNum → NsmulLadderOmegaStep → NsmulLadderOmega
  → DoublingOmega → OmegaIntegral → NsmulYPeriodic → NsmulOrder
```

Each of those seven is a single `import` line in the file on its left.  Adding
`import EllipticCurves.Torsion.NsmulLadderOmegaStepDvd` to `NsmulOrder.lean` is therefore an
**import cycle** and not a module-count cost, and the same holds for the `stepNumω` route of
`#2250`, which lives in the same tower.  ⚠️ **So the eleven landed signatures of `NsmulOrder.lean`
cannot move — not as a matter of style, but because their proofs cannot reach an `h2`-free
ladder.**  Nothing in that file is edited, weakened, restated or deprecated by this one.

⚠️ **The primed names are `EllipticCurves.Torsion.NsmulLadderOmegaStepDvd`'s own convention**,
installed there for this same reason: the unprimed name is landed and no landed signature moves.

## What is reached from below rather than re-proved

The four declarations of `EllipticCurves.Torsion.NsmulOrder` that bind no `h2` are already
characteristic-free and are **used** here, not duplicated: `ψ_mul_ψ_sub_of_ψ_eq_zero` and
`ψ_shift_step_of_ψ_eq_zero` (the two Ward instances at a vanishing index),
`ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero` (every even index vanishes at a `2`-torsion point)
and `exists_minimal_ψ_evalEval_eq_zero` (the least vanishing index is at least `3`).  So is
`EllipticCurves.Torsion.NsmulLadder`'s `sub_Φ_div_ΨSq`, and `divX`, `divT` and `Point.X_eq_iff`.

## The two substitutions, and only one of them reads a `y`

`NsmulEqDiv` and `NsmulEqDivω` pin the **same** `x`-coordinate `divX x n` and differ only in the
`y` they name (`divY` against `divYω`), so the substitution is free wherever the rung's `y` is
never read.

* `nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero'` **never reads it**: its `3 ≤ d` branch uses the
  two rungs only through `Point.X_eq_iff`, `Point.some_ne_zero`, `succ_nsmul` and
  `add_right_cancel`.
* ⚠️ `ψ_add_four_evalEval_ne_zero_of_minimal'` **does** read it — it is the one step that descends
  to the point group — and the replacement is
  `EllipticCurves.Torsion.NsmulLadderOmegaStep`'s `divYω_sub_negY_divX`, which is exactly where
  `NsmulLadder`'s own proof spends its `h2`: there the datum is `(divT − a₁divX − a₃)/2` and the
  cancellation needs `2 ≠ 0`; here the numerator is never halved.  With `divXₙ = x` and
  `divYωₙ = negY x y` the identity reads `negY x y − negY x (negY x y) = divTₙ`, whose left-hand
  side is `−(2y + a₁x + a₃) = −ψ₂(x, y)` by `negY` alone.

## Main statements

* `WeierstrassCurve.Affine.nsmul_eq_zero_iff_ψ_evalEval_eq_zero'` : **`n • P = 0 ↔ ψₙ(P) = 0`,
  with no hypothesis on `2`**, at every point which is not `2`-torsion and at every index.  This is
  `#2340` item 3.
* `WeierstrassCurve.Affine.ψ_evalEval_eq_zero_of_nsmul_eq_zero'` : `n • P = 0 → ψₙ(P) = 0` at
  **every** point, `2`-torsion included, with no hypothesis on `2`.
* `WeierstrassCurve.Affine.exists_order_of_exists_ψ_evalEval_eq_zero'` : the full dictionary at a
  point of finite order that is not `2`-torsion — both the annihilator of the point and the
  vanishing set of `ψ` are the multiples of the order.
* `WeierstrassCurve.Affine.nsmul_three_eq_zero_of_ψ_three_evalEval_eq_zero'` : the `d = 3` instance
  spelled out, because `e = 0` is the one index at which the `ω`-ladder's `ψ₂` and the minimality
  hypothesis could have failed to meet — the order-`3` criterion, with no hypothesis on `2`.
* `WeierstrassCurve.Affine.nsmul_four_curveCharTwoOne_eq_zero` and
  `WeierstrassCurve.Affine.nsmul_eq_zero_iff_four_dvd_curveCharTwoOne` : the characteristic-`2`
  payoff, exhibited and not asserted — on `y² + xy = x³ + 1` over `ZMod 2` the point `(1, 0)` has
  order exactly `4`, and the order is read off `ψ₄(1, 0) = 0`.

## ⚠️ What this file does NOT do

* ⚠️ **`HasXCoordFormula W n` is NOT generalised here**, so
  `EllipticCurves.Torsion.NsmulOrder`'s `hasXCoordFormula_of_two_ne_zero` and
  `nsmul_surjective_of_root` keep their `h2` and their names.  Both are reachable by the same
  substitution — the route is `divX_add_of_not_dvd` and `divX_add_mul_of_not_dvd`, whose `h2`
  comes only from `ψ_evalEval_ne_zero_of_not_dvd` — and neither is `#2340` item 3.  ⚠️ The reason
  this is a separate job and not an omission is the **name**: `hasXCoordFormula_of_two_ne_zero` is
  cited by name at **140** places in the tracked `.lean` files, **128** of them within three lines
  of characteristic-`2` prose, so the generalisation needs a round that owns both the rename and
  that prose.  A keyed reading at `071f044b`; re-measure it rather than carry it.
* ⚠️ **No statement about the `2`-torsion case.**  `nsmul_eq_zero_iff_ψ_evalEval_eq_zero'` keeps
  `NsmulOrder`'s `ht : ψ₂(x, y) ≠ 0`, which is sharp for this route: at a `2`-torsion point the
  forward implication at odd `n` reduces to `Ψ₃(x) ≠ 0` at a root of `Ψ₂Sq`, which this tree has
  only under `[W.IsElliptic]`.  See `EllipticCurves.Torsion.NsmulOrder`'s module docstring.
* ⚠️ **Nothing below `NsmulOrder` is moved.**  The `h2` uses of
  `EllipticCurves.Torsion.TwoTorsionOrder`, `EllipticCurves.Torsion.NsmulYPeriodic`,
  `EllipticCurves.Torsion.ChordSum`, `EllipticCurves.Torsion.XSupport` and
  `EllipticCurves.FunctionField.MulByNXCoordFormula` are untouched, and no call site anywhere
  changes: this file only adds names.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7.
* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. **70** (1948).
-/

open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-! ## The minimal vanishing index is the order of the point, with no hypothesis on `2` -/

section Order

variable [DecidableEq F]

/-- **If `d ≥ 1` is the least index at which `ψ` vanishes at `(x, y)`, then `d • (x, y) = 0`** —
`EllipticCurves.Torsion.NsmulOrder`'s `nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero` with
`(2 : F) ≠ 0` deleted and nothing in its place.

⚠️ **The `y`-coordinate of the two rungs is never read**, which is why the substitution of
`nsmulEqDivω_of_forall_ψ_ne_zero'` for `nsmulEqDiv_of_forall_ψ_ne_zero` costs nothing: the `3 ≤ d`
branch consumes them through `Point.X_eq_iff` — an `x`-comparison — `Point.some_ne_zero`,
`succ_nsmul` and `add_right_cancel`, and through nothing else.

⚠️ **And no new hypothesis is needed**: the `ω`-ladder wants `ψₖ ≠ 0` for `1 ≤ k ≤ n`, the `k = 2`
one included, and `hmin` already supplies exactly that below `d`.  At `d = 3` (`e = 0`) this is
`ψ₂ ≠ 0` out of `2 < 3 = d`, which is the one index where the two could have failed to line up. -/
theorem nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero' (hns : W.Nonsingular x y) {d : ℕ}
    (hd1 : 1 ≤ d) (hd : (W.ψ (d : ℤ)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (d : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    (d • Point.some x y hns : W.Point) = 0 := by
  have hcases : d = 1 ∨ d = 2 ∨ 3 ≤ d := by omega
  rcases hcases with rfl | rfl | hge
  · rw [Nat.cast_one, ψ_one_evalEval] at hd
    exact absurd hd one_ne_zero
  · rw [Nat.cast_ofNat, ψ_two_evalEval] at hd
    have hy : W.negY x y = y := by rw [negY]; linear_combination -hd
    have hneg : -(Point.some x y hns : W.Point) = Point.some x y hns := by
      rw [Point.neg_some, Point.some.injEq]
      exact ⟨rfl, hy⟩
    rw [two_nsmul]
    nth_rewrite 2 [← hneg]
    exact add_neg_cancel _
  · obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 3 := ⟨d - 3, by omega⟩
    have hcast : (((e + 3 : ℕ) : ℤ)) = (e : ℤ) + 3 := by push_cast; ring
    rw [hcast] at hd
    have hne : ∀ k : ℤ, 1 ≤ k → k ≤ (e : ℤ) + 2 → (W.ψ k).evalEval x y ≠ 0 :=
      fun k hk1 hk2 => hmin k hk1 (by rw [hcast]; omega)
    obtain ⟨hA, HA⟩ := nsmulEqDivω_of_forall_ψ_ne_zero' (n := e + 2) hns (by omega)
      (fun k hk1 hk2 => hne k hk1 (by push_cast at hk2; omega))
    obtain ⟨hB, HB⟩ := nsmulEqDivω_of_forall_ψ_ne_zero' (n := e + 1) hns (by omega)
      (fun k hk1 hk2 => hne k hk1 (by push_cast at hk2; omega))
    rw [natCast_zsmul] at HA HB
    have hX : W.divX x (((e + 2 : ℕ) : ℤ)) = x := by
      have hsub := sub_Φ_div_ΨSq (W := W) (x := x) (y := y) hns.left
        (n := ((e + 2 : ℕ) : ℤ)) (hne _ (by push_cast; omega) (by push_cast; omega))
      have hz : (W.ψ (((e + 2 : ℕ) : ℤ) + 1)).evalEval x y = 0 := by
        rw [show (((e + 2 : ℕ) : ℤ) + 1) = (e : ℤ) + 3 by push_cast; ring]; exact hd
      rw [hz, zero_mul, zero_div] at hsub
      exact (eq_of_sub_eq_zero hsub).symm
    rcases (Point.X_eq_iff (h₁ := hA) (h₂ := hns)).mp hX with h | h
    · exfalso
      have h1 : ((e + 1 : ℕ) • (Point.some x y hns : W.Point)) + Point.some x y hns =
          0 + Point.some x y hns := by
        rw [zero_add, ← succ_nsmul, show e + 1 + 1 = e + 2 from rfl, HA, h]
      exact Point.some_ne_zero hB (HB.symm.trans (add_right_cancel h1))
    · rw [show e + 3 = (e + 2) + 1 from rfl, succ_nsmul, HA, h, neg_add_cancel]

/-- ⚠️ **THE `d = 3` INSTANCE SPELLED OUT, BECAUSE `e = 0` IS THE ONE INDEX WHERE THE LADDER'S
`ψ₂` AND THE MINIMALITY HYPOTHESIS COULD HAVE FAILED TO MEET**: the `ω`-ladder at `n = e + 2 = 2`
wants `ψ₂(x, y) ≠ 0`, and `hmin` supplies it only out of `2 < 3 = d`.  Machine-checked here rather
than argued in the docstring above.

Read as mathematics it is the order-`3` criterion with no hypothesis on `2`: at a point which is
not `2`-torsion, `ψ₃(P) = 0` forces `3 • P = 0`. -/
theorem nsmul_three_eq_zero_of_ψ_three_evalEval_eq_zero' (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) (h3 : (W.ψ 3).evalEval x y = 0) :
    ((3 : ℕ) • Point.some x y hns : W.Point) = 0 :=
  nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero' hns (by omega)
    (by rw [show (((3 : ℕ)) : ℤ) = 3 by norm_num]; exact h3)
    (fun k hk1 hk2 => by
      rw [show ((3 : ℕ) : ℤ) = 3 by norm_num] at hk2
      rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
      · rw [ψ_one_evalEval]; exact one_ne_zero
      · exact ht)

end Order

/-! ## The constant of quasi-periodicity is a unit, with no hypothesis on `2` -/

section Dictionary

/-- **`ψ_{d+1}(x, y) ≠ 0` at the least vanishing index `d = e + 3 ≥ 3`**, with `(2 : F) ≠ 0`
deleted — `EllipticCurves.Torsion.NsmulOrder`'s `ψ_add_four_evalEval_ne_zero_of_minimal`.

⚠️ **This is the one step of the argument that reads the rung's `y`-coordinate**, and so the one
place the `ω` substitution is not free.  It reads `ψ_{2d−2} = −ψ₂·ψ_{d−1}⁴` off the ladder at
`d − 1`, where `(d−1) • (x, y) = −(x, y)`; the halved form gets there through `divY`, whose
denominator is `2`, and the `ω` form through
`EllipticCurves.Torsion.NsmulLadderOmegaStep`'s `divYω_sub_negY_divX`, whose numerator is never
halved.  With `divXₙ = x` and `divYωₙ = negY x y` that identity reads
`negY x y − negY x (negY x y) = divTₙ`, and `negY` alone turns the left-hand side into
`−(2y + a₁x + a₃) = −ψ₂(x, y)`. -/
theorem ψ_add_four_evalEval_ne_zero_of_minimal' (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0) :
    (W.ψ ((e : ℤ) + 4)).evalEval x y ≠ 0 := by
  classical
  have hc2 : ((e + 2 : ℕ) : ℤ) = (e : ℤ) + 2 := by push_cast; ring
  have hzero : ((e + 3 : ℕ) • Point.some x y hns : W.Point) = 0 :=
    nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero' hns (by omega)
      (by rw [show (((e + 3 : ℕ)) : ℤ) = (e : ℤ) + 3 by push_cast; ring]; exact hd)
      (fun k hk1 hk2 => hmin k hk1 (by push_cast at hk2; omega))
  have hprev : ((e + 2 : ℕ) • Point.some x y hns : W.Point) = -Point.some x y hns :=
    eq_neg_of_add_eq_zero_left (by rw [← succ_nsmul]; exact hzero)
  obtain ⟨hA, HA⟩ := nsmulEqDivω_of_forall_ψ_ne_zero' (n := e + 2) hns (by omega)
    (fun k hk1 hk2 => hmin k hk1 (by push_cast at hk2; omega))
  rw [natCast_zsmul, hprev, Point.neg_some, Point.some.injEq] at HA
  obtain ⟨hXeq, hYeq⟩ := HA
  rw [hc2] at hXeq hYeq
  have hψn : (W.ψ ((e : ℤ) + 2)).evalEval x y ≠ 0 := hmin _ (by omega) (by omega)
  have hT : W.divT x y ((e : ℤ) + 2) = -((W.ψ 2).evalEval x y) := by
    have hbr := divYω_sub_negY_divX (W := W) (x := x) (y := y) hns.left ht
      (n := (e : ℤ) + 2) hψn
    rw [← hXeq, ← hYeq] at hbr
    simp only [negY] at hbr
    rw [ψ_two_evalEval]
    linear_combination -hbr
  have h2e4 : (W.ψ (2 * (e : ℤ) + 4)).evalEval x y
      = -((W.ψ 2).evalEval x y) * (W.ψ ((e : ℤ) + 2)).evalEval x y ^ 4 := by
    rw [divT, show (2 : ℤ) * ((e : ℤ) + 2) = 2 * (e : ℤ) + 4 by ring,
      div_eq_iff (pow_ne_zero 4 hψn)] at hT
    exact hT
  have hstar := ψ_mul_ψ_sub_of_ψ_eq_zero hd ((e : ℤ) + 1)
  rw [show ((e : ℤ) + 1) + ((e : ℤ) + 3) = 2 * (e : ℤ) + 4 by ring,
    show ((e : ℤ) + 1) - ((e : ℤ) + 3) = -(2 : ℤ) by ring,
    show ((e : ℤ) + 3) + 1 = (e : ℤ) + 4 by ring,
    show ((e : ℤ) + 3) - 1 = (e : ℤ) + 2 by ring, ψ_neg, evalEval_neg, h2e4] at hstar
  intro hcon
  rw [hcon] at hstar
  have : ((W.ψ 2).evalEval x y) ^ 2 * (W.ψ ((e : ℤ) + 2)).evalEval x y ^ 4 = 0 := by
    linear_combination hstar
  rcases mul_eq_zero.mp this with h | h
  · exact ht (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
  · exact hψn (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h)

/-! ## The vanishing set of `ψ` at a point is exactly the multiples of the order -/

/-- **Away from the multiples of the least vanishing index, `ψ` does not vanish**, with
`(2 : F) ≠ 0` deleted.  The step is `ψ_mul_ψ_sub_of_ψ_eq_zero`, which binds no `h2` and is
imported from `EllipticCurves.Torsion.NsmulOrder` rather than restated. -/
theorem ψ_evalEval_ne_zero_of_not_dvd' (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0) :
    ∀ m : ℕ, ¬ ((e + 3) ∣ m) → (W.ψ (m : ℤ)).evalEval x y ≠ 0 := by
  have hc1 : (W.ψ ((e : ℤ) + 4)).evalEval x y ≠ 0 :=
    ψ_add_four_evalEval_ne_zero_of_minimal' hns ht hd hmin
  have hc2 : (W.ψ ((e : ℤ) + 2)).evalEval x y ≠ 0 := hmin _ (by omega) (by omega)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.lt_or_ge m (e + 3) with hlt | hge
    · have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero _)
      exact hmin (m : ℤ) (by omega) (by omega)
    · have hne : m ≠ e + 3 := fun h => hm (h ▸ dvd_refl _)
      have hIH := ih (m - (e + 3)) (by omega) (fun hdv => hm (by
        have := Nat.dvd_add hdv (dvd_refl (e + 3))
        rwa [Nat.sub_add_cancel hge] at this))
      have hstar := ψ_mul_ψ_sub_of_ψ_eq_zero hd (((m - (e + 3) : ℕ)) : ℤ)
      rw [show (((m - (e + 3) : ℕ)) : ℤ) + ((e : ℤ) + 3) = (m : ℤ) by omega,
        show ((e : ℤ) + 3) + 1 = (e : ℤ) + 4 by ring,
        show ((e : ℤ) + 3) - 1 = (e : ℤ) + 2 by ring] at hstar
      intro hzero
      rw [hzero, zero_mul] at hstar
      exact mul_ne_zero (mul_ne_zero hc1 hc2) (pow_ne_zero 2 hIH) (by linear_combination hstar)

/-- **At every multiple of the least vanishing index, `ψ` vanishes**, with `(2 : F) ≠ 0` deleted.
The step is `ψ_shift_step_of_ψ_eq_zero`, which binds no `h2` either. -/
theorem ψ_evalEval_eq_zero_of_dvd' (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0) :
    ∀ m : ℕ, ((e + 3) ∣ m) → (W.ψ (m : ℤ)).evalEval x y = 0 := by
  have hnd := ψ_evalEval_ne_zero_of_not_dvd' hns ht hd hmin
  rintro m ⟨k, rfl⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [show (e + 3) * (0 + 1) = e + 3 by ring, show (((e + 3 : ℕ)) : ℤ) = (e : ℤ) + 3 by
        push_cast; ring]
      exact hd
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hstep := ψ_shift_step_of_ψ_eq_zero hd ((((e + 3) * (j + 1) : ℕ)) : ℤ)
      rw [ih] at hstep
      have hp1 : (W.ψ ((((e + 3) * (j + 1) : ℕ)) + 1 : ℤ)).evalEval x y ≠ 0 := by
        have hnd1 := hnd ((e + 3) * (j + 1) + 1) (fun hdv => by
          have h1 : (e + 3) ∣ 1 := (Nat.dvd_add_right ⟨j + 1, rfl⟩).mp hdv
          have := Nat.le_of_dvd one_pos h1
          omega)
        rwa [show ((((e + 3) * (j + 1) + 1 : ℕ)) : ℤ) = (((e + 3) * (j + 1) : ℕ) : ℤ) + 1 by
          push_cast; ring] at hnd1
      have hm1 : (W.ψ ((((e + 3) * (j + 1) : ℕ)) - 1 : ℤ)).evalEval x y ≠ 0 := by
        have hnd1 := hnd ((e + 3) * j + (e + 2)) (fun hdv => by
          have h1 : (e + 3) ∣ (e + 2) := (Nat.dvd_add_right ⟨j, rfl⟩).mp hdv
          have := Nat.le_of_dvd (by omega) h1
          omega)
        rwa [show ((((e + 3) * j + (e + 2) : ℕ)) : ℤ) = (((e + 3) * (j + 1) : ℕ) : ℤ) - 1 by
          push_cast; ring] at hnd1
      have hsq : (W.ψ (((((e + 3) * (j + 1) : ℕ)) : ℤ) + ((e : ℤ) + 3))).evalEval x y ^ 2 = 0 := by
        rw [zero_pow (by norm_num), mul_zero] at hstep
        rcases mul_eq_zero.mp hstep.symm with h | h
        · exact absurd h (mul_ne_zero hp1 hm1)
        · exact h
      rw [show ((((e + 3) * (j + 1 + 1) : ℕ)) : ℤ)
          = ((((e + 3) * (j + 1) : ℕ)) : ℤ) + ((e : ℤ) + 3) by push_cast; ring]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

end Dictionary

/-! ## The order dictionary: `ψₙ(P) = 0 ⟺ n • P = 0`, over every field -/

section Formula

variable [DecidableEq F]

/-- **At a point which is not `2`-torsion and has finite order, both the vanishing set of `ψ` and
the annihilator of the point are exactly the multiples of the order** — with `(2 : F) ≠ 0`
deleted, and so in characteristic `2` as well.

⚠️ The order is produced in the `e + 3` shape, out of the imported
`exists_minimal_ψ_evalEval_eq_zero`, which binds no `h2`: a point that is not `2`-torsion and has
an index at which `ψ` vanishes has order at least `3`.  ⚠️ The one `h2` of `NsmulOrder`'s own proof
that is not covered by the rungs is its `nsmul_eq_some_Φ_div_ΨSq`, and
`EllipticCurves.Torsion.NsmulLadderOmegaStepDvd`'s `nsmul_eq_some_divX_divYω` is **strictly
stronger** there: it names the `y`-coordinate as `ωNumₙ/ψₙ³` rather than leaving it existential. -/
theorem exists_order_of_exists_ψ_evalEval_eq_zero' (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0)
    (hfin : ∃ m : ℕ, 1 ≤ m ∧ (W.ψ (m : ℤ)).evalEval x y = 0) :
    ∃ e : ℕ, ∀ m : ℕ,
      (((m • Point.some x y hns : W.Point) = 0) ↔ (e + 3) ∣ m) ∧
        (((W.ψ (m : ℤ)).evalEval x y = 0) ↔ (e + 3) ∣ m) := by
  obtain ⟨e, hd0, hmin'⟩ := exists_minimal_ψ_evalEval_eq_zero ht hfin
  have hcastd : (((e + 3 : ℕ)) : ℤ) = (e : ℤ) + 3 := by push_cast; ring
  have hnd := ψ_evalEval_ne_zero_of_not_dvd' hns ht hd0 hmin'
  have hdvd := ψ_evalEval_eq_zero_of_dvd' hns ht hd0 hmin'
  have hzero : ((e + 3 : ℕ) • Point.some x y hns : W.Point) = 0 :=
    nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero' hns (by omega)
      (by rw [hcastd]; exact hd0) (fun k hk1 hk2 => hmin' k hk1 (by rwa [hcastd] at hk2))
  have hqz : ∀ r : ℕ, ((r * (e + 3) : ℕ) • Point.some x y hns : W.Point) = 0 := by
    intro r
    induction r with
    | zero => simp
    | succ r ihr =>
      rw [show (r + 1) * (e + 3) = r * (e + 3) + (e + 3) by ring, add_nsmul, ihr, hzero, add_zero]
  refine ⟨e, fun m => ⟨⟨?_, ?_⟩, ⟨fun h => by_contra fun hc => hnd m hc h, hdvd m⟩⟩⟩
  · intro hm0
    by_contra hc
    obtain ⟨j, q, hm, hj0, hjlt⟩ : ∃ j q : ℕ, m = j + q * (e + 3) ∧ j ≠ 0 ∧ j < e + 3 :=
      ⟨m % (e + 3), m / (e + 3), (Nat.mod_add_div' m (e + 3)).symm,
        fun h => hc (Nat.dvd_of_mod_eq_zero h), Nat.mod_lt _ (by omega)⟩
    have hjcast : ((j : ℤ)) < (e : ℤ) + 3 := by exact_mod_cast hjlt
    have hjne : ∀ k : ℤ, 1 ≤ k → k ≤ (j : ℤ) → (W.ψ k).evalEval x y ≠ 0 := by
      intro k hk1 hk2
      exact hmin' k hk1 (by omega)
    obtain ⟨h', hjP⟩ := nsmul_eq_some_divX_divYω hns (by omega) hjne
    rw [hm, add_nsmul, hqz q, add_zero, hjP] at hm0
    exact Point.some_ne_zero h' hm0
  · rintro ⟨r, rfl⟩
    rw [show (e + 3) * r = r * (e + 3) by ring]
    exact hqz r

/-- ⚠️⚠️ **`n • (x, y) = 0 ↔ ψₙ(x, y) = 0` WITH NO HYPOTHESIS ON `2`**, at every point which is not
`2`-torsion and at every index.  **This is `#2340` item 3**, and
`EllipticCurves.Torsion.NsmulOrder`'s `nsmul_eq_zero_iff_ψ_evalEval_eq_zero` with `(2 : F) ≠ 0`
deleted and nothing in its place.

⚠️ `ht : ψ₂(x, y) ≠ 0` is **kept and is not a weakening of the characteristic hypothesis**: in
characteristic `2` it reads `a₁x + a₃ ≠ 0`, the `2y` of `ψ₂` having died, and it is exactly the
statement that `(x, y)` is not `2`-torsion.  See the module docstring for why the `2`-torsion case
is a separate statement and not a relaxation of this one. -/
theorem nsmul_eq_zero_iff_ψ_evalEval_eq_zero' (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) (n : ℕ) :
    ((n • Point.some x y hns : W.Point) = 0) ↔ (W.ψ (n : ℤ)).evalEval x y = 0 := by
  by_cases hfin : ∃ m : ℕ, 1 ≤ m ∧ (W.ψ (m : ℤ)).evalEval x y = 0
  · obtain ⟨e, hdict⟩ := exists_order_of_exists_ψ_evalEval_eq_zero' hns ht hfin
    exact (hdict n).1.trans (hdict n).2.symm
  · push Not at hfin
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · constructor
      · intro hz
        obtain ⟨k, hk1, -, hk0⟩ := exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero' hns hn hz
        exact absurd (show (W.ψ ((k.toNat : ℕ) : ℤ)).evalEval x y = 0 by
          rwa [Int.toNat_of_nonneg (by omega)]) (hfin k.toNat (by omega))
      · exact fun hz => absurd hz (hfin n hn)

/-- **`n • (x, y) = 0 → ψₙ(x, y) = 0` at EVERY point and every index, with no hypothesis on `2`** —
`EllipticCurves.Torsion.NsmulOrder`'s `ψ_evalEval_eq_zero_of_nsmul_eq_zero` with `(2 : F) ≠ 0`
deleted.  The `2`-torsion branch costs nothing: there every even index of `ψ` vanishes
(`ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero`, which binds no `h2`), and an odd `n` with
`n • P = 0` is impossible because `2 • P = 0` makes `n • P = P ≠ 0`. -/
theorem ψ_evalEval_eq_zero_of_nsmul_eq_zero' (hns : W.Nonsingular x y)
    {n : ℕ} (hz : (n • Point.some x y hns : W.Point) = 0) :
    (W.ψ (n : ℤ)).evalEval x y = 0 := by
  by_cases ht : (W.ψ 2).evalEval x y = 0
  · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      rw [show ((m + m : ℕ) : ℤ) = 2 * (m : ℤ) by push_cast; ring]
      exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht m
    · exfalso
      have htwo : ((2 : ℕ) • Point.some x y hns : W.Point) = 0 :=
        nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero' hns (by omega)
          (by rw [Nat.cast_ofNat]; exact ht)
          (fun k hk1 hk2 => by rw [show k = 1 by omega, ψ_one_evalEval]; exact one_ne_zero)
      rw [hm, add_nsmul, mul_comm, ← smul_smul, htwo, smul_zero, one_nsmul, zero_add] at hz
      exact Point.some_ne_zero hns hz
  · exact (nsmul_eq_zero_iff_ψ_evalEval_eq_zero' hns ht n).mp hz

/-! ## ⚠️ The characteristic-`2` payoff, exhibited and not asserted -/

section CharTwo

/-- `preΨ₄(1) = 0` on `curveCharTwoOne = ⟨1, 0, 0, 0, 1⟩` over `ZMod 2`.

With `b₂ = 1`, `b₄ = 0`, `b₆ = 0` and `b₈ = 1` the polynomial
`2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + (b₂b₈ − b₄b₆)X + (b₄b₈ − b₆²)` is `X⁵ + X`, which is `0`
at `X = 1`. -/
theorem preΨ₄_eval_one_curveCharTwoOne : curveCharTwoOne.preΨ₄.eval 1 = 0 := by
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curveCharTwoOne, eval_add, eval_mul, eval_ofNat,
    eval_pow, eval_X, eval_C, one_pow, mul_one, mul_zero, add_zero, zero_mul, sub_zero,
    zero_sub]
  decide

/-- ⚠️ **`ψ₄(1, 0) = 0` on `curveCharTwoOne` over `ZMod 2`** — `ψ₄ = preΨ₄·ψ₂` at a point where
`ψ₂ = 1`.

⚠️ This is the rung the order dictionary reads, and it is a vanishing one: the point `(1, 0)` has
order `4` in a group of order `4`. -/
theorem ψ_four_evalEval_curveCharTwoOne : (curveCharTwoOne.ψ 4).evalEval 1 0 = 0 := by
  rw [ψ_four_evalEval equation_curveCharTwoOne
      (by rw [evalEval_ψ_two_curveCharTwoOne]; exact one_ne_zero),
    evalEval_ψ_two_curveCharTwoOne, preΨ₄_eval_one_curveCharTwoOne, mul_zero]

/-- ⚠️⚠️ **THE DICTIONARY RUN BACKWARDS IN CHARACTERISTIC `2`**: `ψ₄(1, 0) = 0` forces
`4 • (1, 0) = 0` on `curveCharTwoOne` over `ZMod 2`.

**No `h2`-bound theorem of this tree can produce this**, and it is the direction that is new:
`EllipticCurves.Torsion.NsmulLadderOmegaStepDvd`'s
`exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero'` gives `n • P = 0 → some ψₖ(P) = 0` with no hypothesis
on `2` already, while `ψₙ(P) = 0 → n • P = 0` is this file's content. -/
theorem nsmul_four_curveCharTwoOne_eq_zero :
    ((4 : ℕ) • (Point.some 1 0 nonsingular_curveCharTwoOne : curveCharTwoOne.Point)) = 0 :=
  (nsmul_eq_zero_iff_ψ_evalEval_eq_zero' nonsingular_curveCharTwoOne
      (by rw [evalEval_ψ_two_curveCharTwoOne]; exact one_ne_zero) 4).mpr
    (by rw [show (((4 : ℕ)) : ℤ) = 4 by norm_num]; exact ψ_four_evalEval_curveCharTwoOne)

/-- ⚠️⚠️ **THE FULL ORDER OF A CHARACTERISTIC-`2` POINT, READ OFF `ψ` ALONE**: on
`curveCharTwoOne = ⟨1, 0, 0, 0, 1⟩` over `ZMod 2`, `m • (1, 0) = 0 ↔ 4 ∣ m` at every `m`.

The order is pinned by two values of `ψ` and nothing else — `ψ₄(1, 0) = 0` puts the order among the
divisors of `4`, and `ψ₃(1, 0) ≠ 0`
(`EllipticCurves.Torsion.OmegaOnCurveCharFree`'s `ψ_three_evalEval_ne_zero_curveCharTwoOne`)
rules out `1` and `2` through the dictionary's second half.

⚠️ **A reader can audit this without Lean**: `y² + xy = x³ + 1` over `ZMod 2` has exactly
`O`, `(0, 1)`, `(1, 0)`, `(1, 1)`, and `−(x, y) = (x, y + x)` gives `−(1, 0) = (1, 1) ≠ (1, 0)`, so
the group of order `4` is cyclic and `(1, 0)` generates it. -/
theorem nsmul_eq_zero_iff_four_dvd_curveCharTwoOne (m : ℕ) :
    ((m • (Point.some 1 0 nonsingular_curveCharTwoOne : curveCharTwoOne.Point)) = 0) ↔ 4 ∣ m := by
  have ht : (curveCharTwoOne.ψ 2).evalEval 1 0 ≠ 0 := by
    rw [evalEval_ψ_two_curveCharTwoOne]; exact one_ne_zero
  have h4 : (curveCharTwoOne.ψ ((4 : ℕ) : ℤ)).evalEval 1 0 = 0 := by
    rw [show (((4 : ℕ)) : ℤ) = 4 by norm_num]; exact ψ_four_evalEval_curveCharTwoOne
  obtain ⟨e, hdict⟩ := exists_order_of_exists_ψ_evalEval_eq_zero'
    nonsingular_curveCharTwoOne ht ⟨4, by omega, h4⟩
  have hd4 : (e + 3) ∣ 4 := (hdict 4).2.mp h4
  have hn3 : ¬ ((e + 3) ∣ 3) := fun hc => ψ_three_evalEval_ne_zero_curveCharTwoOne
    (by rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num]; exact (hdict 3).2.mpr hc)
  have hle : e + 3 ≤ 4 := Nat.le_of_dvd (by norm_num) hd4
  obtain rfl : e = 1 := by
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · exact absurd (show (0 + 3) ∣ 3 from dvd_refl 3) hn3
    · rfl
  exact hdict m |>.1

end CharTwo

end Formula

end WeierstrassCurve.Affine
