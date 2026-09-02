/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.NsmulLadder
import EllipticCurves.Torsion.NsmulSurjective

/-!
# `ψₙ(P) = 0 ⟺ n • P = 0`, and `x(n • P) = Φₙ/ΨSqₙ` at **every** index

`EllipticCurves.Torsion.NsmulLadder` proves the multiplication-by-`n` coordinate formula along a
ladder that must not pass through a zero:

```
ψ_k(x, y) ≠ 0 for every 1 ≤ k ≤ n   ⟹   n • (x, y) = (Φₙ(x)/ΨSqₙ(x), Yₙ(x, y)).
```

That hypothesis is strictly stronger than the one of
`WeierstrassCurve.Affine.HasXCoordFormula W n`, which asks only for `ΨSqₙ(x) ≠ 0`.  The two part
company at a point of order `d` with `d < n` and `d ∤ n` — take `d = 3`, `n = 4`, where `ψ₃` breaks
the ladder while `ψ₄ ≠ 0` keeps `HasXCoordFormula`'s hypothesis alive.  **This file closes that
gap**, over any field with `(2 : F) ≠ 0` and with no further hypothesis on the curve.

## The route

Everything runs on two instances of Ward's relation `IsEllipticNet.rel ψ p q r 0 = 0` at a point
`(x, y)` where some `ψ_d` vanishes.  Writing `c := ψ_{d+1}(x, y)·ψ_{d−1}(x, y)`:

* `(p, q, r) = (n, d, 1)` gives `ψ_mul_ψ_sub_of_ψ_eq_zero` : `ψ_{n+d}·ψ_{n−d} = −c·ψₙ²`.
  A nonzero rung therefore propagates upwards in steps of `d`, provided `c ≠ 0`.
* `(p, q, r) = (n + d, n, 1)` gives `ψ_shift_step_of_ψ_eq_zero` :
  `ψ_{n+d+1}·ψ_{n+d−1}·ψₙ² = ψ_{n+1}·ψ_{n−1}·ψ_{n+d}²`.  Since `x − Φₙ/ΨSqₙ = ψ_{n+1}ψ_{n−1}/ψₙ²`
  (`sub_Φ_div_ΨSq`), this says exactly that **`Φₙ/ΨSqₙ` is `d`-periodic in `n`**, and — read at a
  multiple of `d` instead — that `ψ` vanishes at every multiple of `d`.

Both instances have `r = 1`, so both are supplied by the `r = 1` slice `ψ_rel_one_evalEval`; both
have `s = 0`, so neither reaches for the `s`-general `ψ_isEllipticNet`.

⚠️ **No saving should be read off that first clause: on the `r` axis there is no hierarchy to
climb.**  `IsEllipticNet.isEllipticSequence_iff_rel_one` (`EllipticCurves.Torsion.WardR1`) makes
the `r = 1` slice and the `r`-general `IsEllipticSequence` the *same* statement for any odd
normalised sequence, and `ψ` is both, by `ψ_neg` and `ψ_one`.  It is not merely available: it is
how this tree builds the `r`-general form, since `normEDS_isEllipticSequence_of_gapCore` is
`isEllipticSequence_of_rel_one` applied to the slice, and the step between them is a `ring` call.
Both `ψ_rel_one` and `ψ_isEllipticSequence` are corollaries of `wardGapCore` and of nothing else.
So calling `ψ_rel_one_evalEval` here rather than `ψ_isEllipticSequence_evalEval` buys no Ward, and
the `r = n` instance `ψ_net_instance` of `EllipticCurves.Torsion.NsmulLadder` costs none.

⚠️ **The `s` axis is the same story, and it is the half easiest to get wrong.**  The general
statement `IsEllipticNet.isEllipticNet_iff_isEllipticSequence` does spend a regularity hypothesis
on the values at nonzero indices — but `normEDS_isEllipticNet_of_gapCore`
(`EllipticCurves.Torsion.EllipticNetSlices`) discharges it once and for all in `UnivEDS` through
`normEDS_univ_ne_zero` and transports the conclusion to every `CommRing`, so `ψ_isEllipticNet` is
a corollary of `wardGapCore` too.  ⚠️ So neither axis is a hierarchy **for `ψ`**; both are for a
general sequence over a general ring, which is what those two files are for.

The gap this file closes is therefore not paid for with a stronger Ward input than the ladder
already carries, and the reason is the strong one: both rest on exactly `wardGapCore`.  Everything
new here is the two `ψ_d = 0` specialisations and what they are pointed at.

Two things have to be supplied before those two identities do any work.

1. **`d` is the order of the point.**  If `d` is the *least* index with `ψ_d(x, y) = 0` then
   `d • (x, y) = 0` (`nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero`).  The ladder reaches `d − 1` and
   `d − 2`; `x((d−1) • P) − x(P) = −ψ_d·ψ_{d−2}/ψ_{d−1}² = 0`, so `(d−1) • P = ±P` by
   `Point.X_eq_iff`, and `(d−1) • P = P` is impossible because the ladder makes `(d−2) • P` affine.
2. **`c ≠ 0`** (`ψ_add_four_evalEval_ne_zero_of_minimal`).  This is the one step that has to descend
   to the point group.  From `(d−1) • P = −P` the ladder's *`y`*-coordinate gives
   `ψ_{2d−2} = −ψ₂·ψ_{d−1}⁴`, and the first relator instance at `n = d − 2` gives
   `ψ_{2d−2}·ψ₂ = c·ψ_{d−2}²`.  Together: `c·ψ_{d−2}² = −ψ₂²·ψ_{d−1}⁴ ≠ 0`.

⚠️ Step 2 needs `ψ₂(x, y) ≠ 0` and `d ≥ 3`, which are the same condition: `ψ₂(x, y) = 0` says
`y = −y − a₁x − a₃`, i.e. `2 • (x, y) = 0`.  The `2`-torsion case is handled separately and much
more cheaply: there **every even index of `ψ` vanishes**, because `ψ` carries an explicit factor
`ψ₂` at even indices (`ψ_two_mul_eq_mul_ψ₂`), so if `ψₙ(x, y) ≠ 0` then `n` is odd, `n • P = P`,
and `Φₙ(x) = x·ΨSqₙ(x) − ψ_{n+1}ψ_{n−1} = x·ΨSqₙ(x)` because *both* neighbours are even.

## What this does **not** use

⚠️ **No elliptic divisibility.**  Mathlib's standing `TODO` `IsDvdSequence (normEDS b c d)` — the
statement that would propagate `ψ_d = 0` along `d ∣ n` — is used nowhere here.  The propagation is
obtained instead from the second relator instance at `n = k·d`, whose two surviving neighbours
`ψ_{kd±1}` are nonzero by the first instance.  ⚠️ This is *not* a proof of `IsDvdSequence`: the
argument is pointwise and consumes `c ≠ 0`, which is a fact about the point, not about the
sequence.

## The one case that is still open

⚠️ `ψₙ(P) = 0 → n • P = 0` is proved at every `P` that is **not** `2`-torsion, and the reverse
implication is proved at every `P`.  At a `2`-torsion point the forward implication is missing for
odd `n`, and it reduces to a single fact: `Ψ₃(x) ≠ 0` at a root `x` of `Ψ₂Sq`, i.e.
`E[2] ∩ E[3] = 0` read off the polynomials.  Given it, the same two relator instances with `d = 2`
close the case (`c = ψ₃ψ₁ = ψ₃`, and the induction is unchanged).

⚠️ **That fact is available, but only under `[W.IsElliptic]`** — it follows from the merged
`WeierstrassCurve.isCoprime_Ψ₃_Ψ₂Sq` (`EllipticCurves.DivisionPolynomial.Coprime`), a Bézout
combination landing on `C (Δ²)`, which is a unit exactly when the curve is elliptic and which
genuinely fails on a singular curve.  Every statement in this file is hypothesis-free in that
respect, so the `2`-torsion case should arrive as a **separate statement carrying that instance**
rather than as a weakening of `nsmul_eq_zero_iff_ψ_evalEval_eq_zero`'s signature.  ⚠️ *"This route
needs `IsElliptic`"* is not *"the case is false without it"*; nothing here measures that.

⚠️ Nothing below depends on any of this — `hasXCoordFormula_of_two_ne_zero` covers `2`-torsion
points already, by the parity argument above.

## Main statements

* `WeierstrassCurve.Affine.hasXCoordFormula_of_two_ne_zero` : **`HasXCoordFormula W n` at every
  index `n`** — `#251`'s scope item 1, with the ladder hypothesis removed.
* `WeierstrassCurve.Affine.nsmul_surjective_of_root` : the payoff — `[n]`-surjectivity on `E(F̄)`
  now needs only `∀ x, ΨSqₙ(x) = 0 → Φₙ(x) ≠ 0`, the weakening of `#1184`.
* `WeierstrassCurve.Affine.nsmul_eq_zero_iff_ψ_evalEval_eq_zero` : `n • P = 0 ↔ ψₙ(P) = 0` away
  from the `2`-torsion — `#251`'s scope item 2.
* `WeierstrassCurve.Affine.ψ_evalEval_eq_zero_of_nsmul_eq_zero` : `n • P = 0 → ψₙ(P) = 0` at every
  point, sharpening `exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero`.
* `WeierstrassCurve.Affine.exists_order_of_exists_ψ_evalEval_eq_zero` : the full dictionary at a
  point of finite order that is not `2`-torsion — both the annihilator of the point and the
  vanishing set of `ψ` are the multiples of the order.
* `WeierstrassCurve.Affine.nsmul_four_y2EqX3AddOne` : the certificate that the ladder is strictly
  extended — an index the ladder cannot reach, at a point where it passes through a zero.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7.
* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. **70** (1948).
-/

open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-! ## Two relator instances at an index where `ψ` vanishes -/

/-- Ward's relation at `(p, q, r, s) = (n, d, 1, 0)` with `ψ_d(x, y) = 0`. -/
theorem ψ_mul_ψ_sub_of_ψ_eq_zero {d : ℤ} (hd : (W.ψ d).evalEval x y = 0) (n : ℤ) :
    (W.ψ (n + d)).evalEval x y * (W.ψ (n - d)).evalEval x y =
      -((W.ψ (d + 1)).evalEval x y * (W.ψ (d - 1)).evalEval x y *
        (W.ψ n).evalEval x y ^ 2) := by
  have H := W.ψ_rel_one_evalEval (x := x) (y := y) n d
  simp only [IsEllipticNet.rel, add_zero, ψ_one_evalEval] at H
  rw [hd] at H
  linear_combination H

/-- Ward's relation at `(p, q, r, s) = (n + d, n, 1, 0)` with `ψ_d(x, y) = 0`. -/
theorem ψ_shift_step_of_ψ_eq_zero {d : ℤ} (hd : (W.ψ d).evalEval x y = 0) (n : ℤ) :
    (W.ψ (n + d + 1)).evalEval x y * (W.ψ (n + d - 1)).evalEval x y *
        (W.ψ n).evalEval x y ^ 2 =
      (W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y *
        (W.ψ (n + d)).evalEval x y ^ 2 := by
  have H := W.ψ_rel_one_evalEval (x := x) (y := y) (n + d) n
  simp only [IsEllipticNet.rel, add_zero, ψ_one_evalEval] at H
  rw [show n + d - n = d by ring, hd] at H
  linear_combination -H

/-- Every even index of `ψ` carries a factor `ψ₂`. -/
theorem ψ_two_mul_eq_mul_ψ₂ (m : ℤ) :
    W.ψ (2 * m) = preNormEDS (W.ψ₂ ^ 4) (C W.Ψ₃) (C W.preΨ₄) (2 * m) * W.ψ₂ := by
  simp only [WeierstrassCurve.ψ, normEDS, if_pos (even_two_mul m)]

/-- At a `2`-torsion point every even index of `ψ` vanishes. -/
theorem ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero (ht : (W.ψ 2).evalEval x y = 0) (m : ℤ) :
    (W.ψ (2 * m)).evalEval x y = 0 := by
  rw [ψ_two_mul_eq_mul_ψ₂, evalEval_mul, ← ψ_two, ht, mul_zero]

/-! ## The minimal vanishing index is the order of the point -/

section Order

variable [DecidableEq F]

/-- **If `d ≥ 1` is the least index at which `ψ` vanishes at `(x, y)`, then `d • (x, y) = 0`.** -/
theorem nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero (h2 : (2 : F) ≠ 0)
    (hns : W.Nonsingular x y) {d : ℕ} (hd1 : 1 ≤ d)
    (hd : (W.ψ (d : ℤ)).evalEval x y = 0)
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
    obtain ⟨hA, HA⟩ := nsmulEqDiv_of_forall_ψ_ne_zero (n := e + 2) h2 hns (by omega)
      (fun k hk1 hk2 => hne k hk1 (by push_cast at hk2; omega))
    obtain ⟨hB, HB⟩ := nsmulEqDiv_of_forall_ψ_ne_zero (n := e + 1) h2 hns (by omega)
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

end Order

/-! ## The constant of quasi-periodicity is a unit -/

section Dictionary

/-- **`ψ_{d+1}(x, y) ≠ 0` at the least vanishing index `d = e + 3 ≥ 3`.**  This is what makes the
quasi-periodicity constant `c = ψ_{d+1}·ψ_{d−1}` invertible, and it is the one step of the argument
that has to descend to the point group: it reads `ψ_{2d−2} = −ψ₂·ψ_{d−1}⁴` off the ladder's
`y`-coordinate at `d − 1`, where `(d−1) • (x, y) = −(x, y)`. -/
theorem ψ_add_four_evalEval_ne_zero_of_minimal (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0) :
    (W.ψ ((e : ℤ) + 4)).evalEval x y ≠ 0 := by
  classical
  have hc2 : ((e + 2 : ℕ) : ℤ) = (e : ℤ) + 2 := by push_cast; ring
  have hzero : ((e + 3 : ℕ) • Point.some x y hns : W.Point) = 0 :=
    nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero h2 hns (by omega)
      (by rw [show (((e + 3 : ℕ)) : ℤ) = (e : ℤ) + 3 by push_cast; ring]; exact hd)
      (fun k hk1 hk2 => hmin k hk1 (by push_cast at hk2; omega))
  have hprev : ((e + 2 : ℕ) • Point.some x y hns : W.Point) = -Point.some x y hns :=
    eq_neg_of_add_eq_zero_left (by rw [← succ_nsmul]; exact hzero)
  obtain ⟨hA, HA⟩ := nsmulEqDiv_of_forall_ψ_ne_zero (n := e + 2) h2 hns (by omega)
    (fun k hk1 hk2 => hmin k hk1 (by push_cast at hk2; omega))
  rw [natCast_zsmul, hprev, Point.neg_some, Point.some.injEq] at HA
  obtain ⟨hXeq, hYeq⟩ := HA
  rw [hc2] at hXeq hYeq
  have hψn : (W.ψ ((e : ℤ) + 2)).evalEval x y ≠ 0 := hmin _ (by omega) (by omega)
  have hT : W.divT x y ((e : ℤ) + 2) = -((W.ψ 2).evalEval x y) := by
    rw [divY, ← hXeq, negY] at hYeq
    rw [ψ_two_evalEval]
    field_simp at hYeq
    linear_combination -hYeq
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

/-- **Away from the multiples of the least vanishing index, `ψ` does not vanish.**  The step is
Ward's relation at `(n, d, 1, 0)`, which reads `ψ_{n+d}·ψ_{n−d} = −c·ψₙ²` with
`c = ψ_{d+1}·ψ_{d−1} ≠ 0`, so a nonzero rung propagates upwards in steps of `d`. -/
theorem ψ_evalEval_ne_zero_of_not_dvd (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0) :
    ∀ m : ℕ, ¬ ((e + 3) ∣ m) → (W.ψ (m : ℤ)).evalEval x y ≠ 0 := by
  have hc1 : (W.ψ ((e : ℤ) + 4)).evalEval x y ≠ 0 :=
    ψ_add_four_evalEval_ne_zero_of_minimal h2 hns ht hd hmin
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

/-- **At every multiple of the least vanishing index, `ψ` vanishes.**  The step is Ward's relation
at `(n + d, n, 1, 0)`, whose left-hand side is killed by the induction hypothesis while the two
neighbours `ψ_{n±1}` are nonzero by `ψ_evalEval_ne_zero_of_not_dvd`. -/
theorem ψ_evalEval_eq_zero_of_dvd (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0) :
    ∀ m : ℕ, ((e + 3) ∣ m) → (W.ψ (m : ℤ)).evalEval x y = 0 := by
  have hnd := ψ_evalEval_ne_zero_of_not_dvd h2 hns ht hd hmin
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

/-! ## `d`-periodicity of the predicted `x`-coordinate -/

/-- **One period of the predicted `x`-coordinate.**  Ward's relation at `(m + d, m, 1, 0)` says
exactly that `ψ_{m+1}ψ_{m−1}/ψₘ²` is unchanged by `m ↦ m + d`, and that quotient is
`x − Φₘ/ΨSqₘ`. -/
theorem divX_add_of_not_dvd (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0)
    (m : ℕ) (hm : ¬ ((e + 3) ∣ m)) :
    W.divX x ((m : ℤ) + ((e : ℤ) + 3)) = W.divX x (m : ℤ) := by
  have hnd := ψ_evalEval_ne_zero_of_not_dvd h2 hns ht hd hmin
  have hA : (W.ψ (m : ℤ)).evalEval x y ≠ 0 := hnd m hm
  have hB : (W.ψ ((m : ℤ) + ((e : ℤ) + 3))).evalEval x y ≠ 0 := by
    have hnd1 := hnd (m + (e + 3)) (fun hdv =>
      hm ((Nat.dvd_add_iff_left (dvd_refl (e + 3))).mpr hdv))
    rwa [show (((m + (e + 3) : ℕ)) : ℤ) = (m : ℤ) + ((e : ℤ) + 3) by push_cast; ring] at hnd1
  have hlow := sub_Φ_div_ΨSq (W := W) (y := y) hns.left (n := (m : ℤ)) hA
  have hhigh := sub_Φ_div_ΨSq (W := W) (y := y) hns.left (n := (m : ℤ) + ((e : ℤ) + 3)) hB
  have hstep := ψ_shift_step_of_ψ_eq_zero hd (m : ℤ)
  have hEq : (W.ψ ((m : ℤ) + ((e : ℤ) + 3) + 1)).evalEval x y *
        (W.ψ ((m : ℤ) + ((e : ℤ) + 3) - 1)).evalEval x y /
        (W.ψ ((m : ℤ) + ((e : ℤ) + 3))).evalEval x y ^ 2 =
      (W.ψ ((m : ℤ) + 1)).evalEval x y * (W.ψ ((m : ℤ) - 1)).evalEval x y /
        (W.ψ (m : ℤ)).evalEval x y ^ 2 := by
    rw [div_eq_div_iff (pow_ne_zero 2 hB) (pow_ne_zero 2 hA)]
    linear_combination hstep
  simp only [divX]
  linear_combination -(hhigh.trans (hEq.trans hlow.symm))

/-- **The predicted `x`-coordinate is periodic with period `d` off the multiples of `d`.** -/
theorem divX_add_mul_of_not_dvd (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) {e : ℕ}
    (hd : (W.ψ ((e : ℤ) + 3)).evalEval x y = 0)
    (hmin : ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0)
    (j : ℕ) (hj : ¬ ((e + 3) ∣ j)) :
    ∀ q : ℕ, W.divX x ((j : ℤ) + q * ((e : ℤ) + 3)) = W.divX x (j : ℤ) := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have hnj : ¬ ((e + 3) ∣ (j + q * (e + 3))) := fun hdv =>
      hj ((Nat.dvd_add_iff_left (dvd_mul_left (e + 3) q)).mpr hdv)
    have := divX_add_of_not_dvd h2 hns ht hd hmin (j + q * (e + 3)) hnj
    rw [show (((j + q * (e + 3) : ℕ)) : ℤ) = (j : ℤ) + q * ((e : ℤ) + 3) by push_cast; ring] at this
    rw [show (j : ℤ) + ((q : ℕ) + 1 : ℕ) * ((e : ℤ) + 3)
        = (j : ℤ) + q * ((e : ℤ) + 3) + ((e : ℤ) + 3) by push_cast; ring, this, ih]

/-! ## The least vanishing index -/

/-- **The least index at which `ψ` vanishes at a non-`2`-torsion point is at least `3`.**  Packaged
in the `e + 3` shape the lemmas above consume. -/
theorem exists_minimal_ψ_evalEval_eq_zero (ht : (W.ψ 2).evalEval x y ≠ 0)
    (hfin : ∃ m : ℕ, 1 ≤ m ∧ (W.ψ (m : ℤ)).evalEval x y = 0) :
    ∃ e : ℕ, (W.ψ ((e : ℤ) + 3)).evalEval x y = 0 ∧
      ∀ k : ℤ, 1 ≤ k → k < (e : ℤ) + 3 → (W.ψ k).evalEval x y ≠ 0 := by
  classical
  obtain ⟨d, ⟨hd1, hd0⟩, hmin⟩ :
      ∃ d : ℕ, (1 ≤ d ∧ (W.ψ (d : ℤ)).evalEval x y = 0) ∧
        ∀ k : ℤ, 1 ≤ k → k < (d : ℤ) → (W.ψ k).evalEval x y ≠ 0 :=
    ⟨Nat.find hfin, Nat.find_spec hfin, fun k hk1 hkd hk0 =>
      Nat.find_min hfin (m := k.toNat) (by omega)
        ⟨by omega, by rwa [Int.toNat_of_nonneg (by omega)]⟩⟩
  have hd3 : 3 ≤ d := by
    rcases (show d = 1 ∨ d = 2 ∨ 3 ≤ d by omega) with h | h | h
    · rw [h, Nat.cast_one, ψ_one_evalEval] at hd0; exact absurd hd0 one_ne_zero
    · rw [h, Nat.cast_ofNat] at hd0; exact absurd hd0 ht
    · exact h
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 3 := ⟨d - 3, by omega⟩
  have hcastd : (((e + 3 : ℕ)) : ℤ) = (e : ℤ) + 3 := by push_cast; ring
  rw [hcastd] at hd0
  exact ⟨e, hd0, fun k hk1 hk2 => hmin k hk1 (by rw [hcastd]; exact hk2)⟩


end Dictionary

/-! ## The coordinate formula at every index -/

section Formula

variable [DecidableEq F]

/-- **`WeierstrassCurve.Affine.HasXCoordFormula W n` at every index `n`**, over any field of
characteristic `≠ 2`.  This is `#251`'s scope item 1 with the ladder hypothesis removed, and it is
the index-dependent input of the `[n]`-surjectivity engine. -/
theorem hasXCoordFormula_of_two_ne_zero (h2 : (2 : F) ≠ 0) (n : ℕ) :
    HasXCoordFormula W n := by
  classical
  intro x y hns hΨ
  have hψn : (W.ψ (n : ℤ)).evalEval x y ≠ 0 := fun h =>
    hΨ (by rw [← ψ_sq_evalEval hns.left, h]; ring)
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (by simp) hψn
    · exact h
  by_cases ht : (W.ψ 2).evalEval x y = 0
  · -- `(x, y)` is a `2`-torsion point: `n` is odd, `n • (x, y) = (x, y)` and `Φₙ/ΨSqₙ = x`.
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
      · refine absurd ?_ hψn
        have hcast : ((n : ℤ)) = 2 * (m : ℤ) := by rw [hm]; push_cast; ring
        rw [hcast]
        exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht m
      · obtain ⟨m, hm⟩ := hodd
        exact ⟨m, hm⟩
    have htwo : ((2 : ℕ) • Point.some x y hns : W.Point) = 0 :=
      nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero h2 hns (by omega)
        (by rw [Nat.cast_ofNat]; exact ht)
        (fun k hk1 hk2 => by
          rw [show k = 1 by omega, ψ_one_evalEval]; exact one_ne_zero)
    have hnP : ((2 * m + 1 : ℕ) • Point.some x y hns : W.Point) = Point.some x y hns := by
      rw [add_nsmul, mul_comm, ← smul_smul, htwo, smul_zero, one_nsmul, zero_add]
    have hup : (W.ψ (((2 * m + 1 : ℕ) : ℤ) + 1)).evalEval x y = 0 := by
      rw [show (((2 * m + 1 : ℕ) : ℤ) + 1) = 2 * ((m : ℤ) + 1) by push_cast; ring]
      exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht _
    have hdown : (W.ψ (((2 * m + 1 : ℕ) : ℤ) - 1)).evalEval x y = 0 := by
      rw [show (((2 * m + 1 : ℕ) : ℤ) - 1) = 2 * (m : ℤ) by push_cast; ring]
      exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht _
    have hXx : (W.Φ ((2 * m + 1 : ℕ) : ℤ)).eval x / (W.ΨSq ((2 * m + 1 : ℕ) : ℤ)).eval x = x := by
      rw [Φ_eval_eq_of_equation hns.left, hup, hdown, ← ψ_sq_evalEval hns.left]
      field_simp
      ring
    rw [hXx]
    exact ⟨y, hns, hnP⟩
  · -- `(x, y)` is not `2`-torsion.
    by_cases hall : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0
    · exact nsmul_eq_some_Φ_div_ΨSq h2 hns hn1 hall
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
      have hjne : ∀ k : ℤ, 1 ≤ k → k ≤ (j : ℤ) → (W.ψ k).evalEval x y ≠ 0 := by
        intro k hk1 hk2
        exact hmin' k hk1 (by omega)
      obtain ⟨y', h', hjP⟩ := nsmul_eq_some_Φ_div_ΨSq h2 hns (by omega) hjne
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
      have hXX : (W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x
          = (W.Φ (j : ℤ)).eval x / (W.ΨSq (j : ℤ)).eval x := by
        have hper := divX_add_mul_of_not_dvd h2 hns ht hd0 hmin' j hnotdvdj q
        rw [show (j : ℤ) + (q : ℤ) * ((e : ℤ) + 3) = (n : ℤ) by rw [hn]; push_cast; ring] at hper
        simpa only [divX] using hper
      rw [hXX]
      exact ⟨y', h', by rw [hnP]; exact hjP⟩

/-! ## The order dictionary: `ψₙ(P) = 0 ⟺ n • P = 0` -/

/-- **At a point which is not `2`-torsion and has finite order, both the vanishing set of `ψ` and
the annihilator of the point are exactly the multiples of the order.**  ⚠️ The order is produced in
the `e + 3` shape: a point that is not `2`-torsion and has an index at which `ψ` vanishes has order
at least `3`. -/
theorem exists_order_of_exists_ψ_evalEval_eq_zero (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0)
    (hfin : ∃ m : ℕ, 1 ≤ m ∧ (W.ψ (m : ℤ)).evalEval x y = 0) :
    ∃ e : ℕ, ∀ m : ℕ,
      (((m • Point.some x y hns : W.Point) = 0) ↔ (e + 3) ∣ m) ∧
        (((W.ψ (m : ℤ)).evalEval x y = 0) ↔ (e + 3) ∣ m) := by
  obtain ⟨e, hd0, hmin'⟩ := exists_minimal_ψ_evalEval_eq_zero ht hfin
  have hcastd : (((e + 3 : ℕ)) : ℤ) = (e : ℤ) + 3 := by push_cast; ring
  have hnd := ψ_evalEval_ne_zero_of_not_dvd h2 hns ht hd0 hmin'
  have hdvd := ψ_evalEval_eq_zero_of_dvd h2 hns ht hd0 hmin'
  have hzero : ((e + 3 : ℕ) • Point.some x y hns : W.Point) = 0 :=
    nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero h2 hns (by omega)
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
    obtain ⟨y', h', hjP⟩ := nsmul_eq_some_Φ_div_ΨSq h2 hns (by omega) hjne
    rw [hm, add_nsmul, hqz q, add_zero, hjP] at hm0
    exact Point.some_ne_zero h' hm0
  · rintro ⟨r, rfl⟩
    rw [show (e + 3) * r = r * (e + 3) by ring]
    exact hqz r

/-- **`n • (x, y) = 0 ↔ ψₙ(x, y) = 0`**, at every point which is not `2`-torsion and at every
index.  This is `#251`'s scope item 2 away from the `2`-torsion. -/
theorem nsmul_eq_zero_iff_ψ_evalEval_eq_zero (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) (n : ℕ) :
    ((n • Point.some x y hns : W.Point) = 0) ↔ (W.ψ (n : ℤ)).evalEval x y = 0 := by
  by_cases hfin : ∃ m : ℕ, 1 ≤ m ∧ (W.ψ (m : ℤ)).evalEval x y = 0
  · obtain ⟨e, hdict⟩ := exists_order_of_exists_ψ_evalEval_eq_zero h2 hns ht hfin
    exact (hdict n).1.trans (hdict n).2.symm
  · push Not at hfin
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · constructor
      · intro hz
        obtain ⟨k, hk1, -, hk0⟩ := exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero h2 hns hn hz
        exact absurd (show (W.ψ ((k.toNat : ℕ) : ℤ)).evalEval x y = 0 by
          rwa [Int.toNat_of_nonneg (by omega)]) (hfin k.toNat (by omega))
      · exact fun hz => absurd hz (hfin n hn)

/-- **`n • (x, y) = 0 → ψₙ(x, y) = 0`**, at every point and every index.  This sharpens
`WeierstrassCurve.Affine.exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero`, which only produced *some*
vanishing rung `k ≤ n`, to the statement that the rung can be taken to be `n` itself. -/
theorem ψ_evalEval_eq_zero_of_nsmul_eq_zero (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    {n : ℕ} (hz : (n • Point.some x y hns : W.Point) = 0) :
    (W.ψ (n : ℤ)).evalEval x y = 0 := by
  by_cases ht : (W.ψ 2).evalEval x y = 0
  · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      rw [show ((m + m : ℕ) : ℤ) = 2 * (m : ℤ) by push_cast; ring]
      exact ψ_evalEval_eq_zero_of_ψ_two_evalEval_eq_zero ht m
    · exfalso
      have htwo : ((2 : ℕ) • Point.some x y hns : W.Point) = 0 :=
        nsmul_eq_zero_of_minimal_ψ_evalEval_eq_zero h2 hns (by omega)
          (by rw [Nat.cast_ofNat]; exact ht)
          (fun k hk1 hk2 => by rw [show k = 1 by omega, ψ_one_evalEval]; exact one_ne_zero)
      rw [hm, add_nsmul, mul_comm, ← smul_smul, htwo, smul_zero, one_nsmul, zero_add] at hz
      exact Point.some_ne_zero hns hz
  · exact (nsmul_eq_zero_iff_ψ_evalEval_eq_zero h2 hns ht n).mp hz

/-! ## The payoff: `[n]`-surjectivity now needs only the root condition -/

/-- **Multiplication by `n` is surjective on `E(F̄)` as soon as `Φₙ` and `ΨSqₙ` have no common
root.**  The coordinate formula, the *other* input of
`WeierstrassCurve.Affine.nsmul_surjective_of_hasXCoordFormula`, is no longer a hypothesis: it holds
at every index.  ⚠️ What is left, `hroot`, is the weakening of `#1184` recorded there; this theorem
does **not** discharge it. -/
theorem nsmul_surjective_of_root [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hroot : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0) :
    Function.Surjective fun P : W.Point => n • P :=
  nsmul_surjective_of_hasXCoordFormula h2 hn hroot (hasXCoordFormula_of_two_ne_zero h2 n)

end Formula

/-! ## Non-vacuity: an index the ladder cannot reach -/

section Nonvacuity

open EllipticCurves.Fixture

/-- `Q = (0, 1)` lies on `y² = x³ + 1` and is nonsingular. -/
private lemma exampleNonsingularZeroOne : (y2EqX3AddOne ℚ).Nonsingular 0 1 :=
  equation_iff_nonsingular.mp (by norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff])

private lemma exampleEquationZeroOne : (y2EqX3AddOne ℚ).Equation 0 1 :=
  exampleNonsingularZeroOne.left

/-- `ψ₂(0, 1) = 2`, so `Q` is not `2`-torsion. -/
private lemma exampleψTwoZeroOne : ((y2EqX3AddOne ℚ).ψ 2).evalEval 0 1 = 2 := by
  rw [ψ_two_evalEval]; norm_num [y2EqX3AddOne]

/-- `ψ₃(0, 1) = Ψ₃(0) = b₈ = 0`. -/
private lemma exampleψThreeZeroOne : ((y2EqX3AddOne ℚ).ψ 3).evalEval 0 1 = 0 := by
  rw [ψ_three, evalEval_C]
  norm_num [y2EqX3AddOne, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `preΨ₄(0) = b₄b₈ − b₆² = −16`. -/
private lemma examplePreΨFourZeroOne : (y2EqX3AddOne ℚ).preΨ₄.eval 0 = -16 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `ψ₄(0, 1) = ψ₂·preΨ₄ = −32 ≠ 0`. -/
private lemma exampleψFourZeroOne : ((y2EqX3AddOne ℚ).ψ 4).evalEval 0 1 = -32 := by
  rw [ψ_four_evalEval exampleEquationZeroOne (by rw [exampleψTwoZeroOne]; norm_num),
    exampleψTwoZeroOne, examplePreΨFourZeroOne]
  norm_num

/-- **The order dictionary, run forwards on a concrete point.**  `ψ₃(0, 1) = 0` and `(0, 1)` is not
`2`-torsion, so `3 • (0, 1) = 0` — a conclusion `EllipticCurves.Torsion.NsmulLadder` explicitly
could not draw from a vanishing `ψ`. -/
theorem nsmul_three_y2EqX3AddOne_eq_zero :
    ((3 : ℕ) • (Point.some 0 1 exampleNonsingularZeroOne : (y2EqX3AddOne ℚ).Point)) = 0 :=
  (nsmul_eq_zero_iff_ψ_evalEval_eq_zero (by norm_num) exampleNonsingularZeroOne
      (by rw [exampleψTwoZeroOne]; norm_num) 3).mpr
    (by rw [show (((3 : ℕ)) : ℤ) = 3 by norm_num]; exact exampleψThreeZeroOne)

/-- **The certificate that this file strictly extends the ladder.**  At `Q = (0, 1)` on
`y² = x³ + 1` the rung `ψ₃(Q) = 0` is a zero, so
`WeierstrassCurve.Affine.nsmul_eq_some_Φ_div_ΨSq` is inapplicable at `n = 4` — its hypothesis asks
for `ψ_k(Q) ≠ 0` at every `k ≤ 4`, and `k = 3` fails.  `ΨSq₄(0) = ψ₄(Q)² = 1024 ≠ 0`, so
`hasXCoordFormula_of_two_ne_zero` *does* apply, and it computes `x(4 • Q) = Φ₄(0)/ΨSq₄(0) = 0`.
That is right: `Q` has order `3` (proved just above), so `4 • Q = Q = (0, 1)`.

⚠️ The vanishing rung is stated as the first conjunct so that the inapplicability of the ladder is
machine-checked here rather than asserted in prose.  ⚠️ The `x`-value the formula computes is
`x(Q)` itself, and it cannot be anything else: every nonzero multiple of a point of order `3` has
the same `x`-coordinate.  The content of the certificate is that `4 • Q` is **affine** and that its
`x`-coordinate is `Φ₄/ΨSq₄`, at an index the ladder does not reach. -/
theorem nsmul_four_y2EqX3AddOne :
    ((y2EqX3AddOne ℚ).ψ 3).evalEval 0 1 = 0 ∧
      ∃ (y' : ℚ) (h' : (y2EqX3AddOne ℚ).Nonsingular 0 y'),
        ((4 : ℕ) • (Point.some 0 1 exampleNonsingularZeroOne : (y2EqX3AddOne ℚ).Point))
          = Point.some 0 y' h' := by
  refine ⟨exampleψThreeZeroOne, ?_⟩
  have hΨ : ((y2EqX3AddOne ℚ).ΨSq ((4 : ℕ) : ℤ)).eval 0 ≠ 0 := by
    rw [← ψ_sq_evalEval exampleEquationZeroOne, show (((4 : ℕ)) : ℤ) = 4 by norm_num,
      exampleψFourZeroOne]
    norm_num
  obtain ⟨y', h', heq⟩ := hasXCoordFormula_of_two_ne_zero (W := y2EqX3AddOne ℚ) (by norm_num) 4
    exampleNonsingularZeroOne hΨ
  have hx : ((y2EqX3AddOne ℚ).Φ ((4 : ℕ) : ℤ)).eval 0
      / ((y2EqX3AddOne ℚ).ΨSq ((4 : ℕ) : ℤ)).eval 0 = 0 := by
    have hΦ := Φ_eval_eq_of_equation exampleEquationZeroOne ((4 : ℕ) : ℤ)
    rw [show ((((4 : ℕ)) : ℤ) - 1) = 3 by norm_num] at hΦ
    rw [hΦ, exampleψThreeZeroOne]
    norm_num
  refine ⟨y', hx ▸ h', ?_⟩
  rw [heq, Point.some.injEq]
  exact ⟨hx, rfl⟩

end Nonvacuity


end WeierstrassCurve.Affine
