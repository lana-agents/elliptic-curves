/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.TwoTorsionOrder

/-!
# `ΨSqₙ` is coprime to its neighbours over a field: the root route, run and descended

`EllipticCurves.DivisionPolynomial.Coprime` reduces the coprimality of `Φₙ` and `ΨSqₙ` to one
statement in which `Φ` does not appear,

```
IsCoprime (W.ΨSq (n + 1) * W.ΨSq (n - 1)) (W.ΨSq n) ,
```

and records it as open, with two routes and where each stops.  **This file runs the first of those
two routes** — the root argument — and lands the statement over a field of characteristic `≠ 2` on
an elliptic curve.

## The argument, and how much of it was already merged

⚠️ The geometric half is **not new here**.  `EllipticCurves.Torsion.TwoTorsionOrder` already
lifts a root `x` of `ΨSqₙ` to a point `(x, y)` of `W` over `F̄`, kills it with `n` through the
order dictionary `nsmul_eq_zero_iff_ψ_evalEval_eq_zero_of_isElliptic`, and concludes that neither
neighbour `ψ_{n±1}` vanishes there — because `n • P = 0` together with `(n ± 1) • P = 0` forces
`P = 0`, and `P` is affine.  That argument was written for `hroot` and its two subgoals *are* the
pointwise statement; it is now named
`WeierstrassCurve.Affine.eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero` in that file, and
`eval_Φ_ne_zero_of_eval_ΨSq_eq_zero` consumes it rather than repeating it.

**What is new here is the descent**, which is the half of the old gate that survived when `#251`'s
dictionary landed.  It is one Mathlib lemma:
`Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed` says that over a field `k`, coprimality of
`p q : k[X]` is *equivalent* to the absence of a common root in any algebraically closed extension.
Taking that extension to be `AlgebraicClosure F` and transporting along
`WeierstrassCurve.map_ΨSq` turns the pointwise statement over `F̄` into `IsCoprime` over `F`.  No
`gcd` computation, no `Polynomial.map` injectivity argument by hand.

## ⚠️ What is proved, and at what price

* **No hypothesis on `n`.**  Neither `n ≠ 0` nor `(n : F) ≠ 0` appears.  The `n = 0` case is
  separate and trivial (`ΨSq 0 = 0`, and the adjacent product is `ΨSq 1 * ΨSq (-1) = 1`), and
  everywhere else the root argument runs.  This is strictly more than the degree tower asks for.
* **A field, characteristic `≠ 2`, and `[W.IsElliptic]`.**  This is the price, and it is real.
  `EllipticCurves.DivisionPolynomial.Coprime` proves everything over an **arbitrary commutative
  ring** with none of the three, and `isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent` — the reduction
  this file feeds — carries no hypothesis at all.  ⚠️ **So this file does not close that file's
  `## What is *not* here` bullet in that file's own generality**, and does not claim to; it closes
  it in the generality every consumer in this development actually works in.
* ⚠️ **The second route is untouched.**  The recurrence/strong-divisibility route recorded in
  `EllipticCurves.DivisionPolynomial.Coprime` — through Mathlib's `IsEllipticDvdSequence` TODO and
  this development's `#254` / `#258` / `#260` — is still the only known route to the
  arbitrary-ring form, and nothing here bears on it.  ⚠️ In particular this file is **not**
  evidence that the Ward front is closer; it is evidence that the Ward front is not needed by the
  consumers that were waiting on this statement.

## Main statements

* `WeierstrassCurve.Affine.isCoprime_ΨSq_adjacent` : **`IsCoprime (ΨSqₙ₊₁ · ΨSqₙ₋₁) (ΨSqₙ)`** at
  every `n : ℤ`.
* `WeierstrassCurve.Affine.isCoprime_ΨSq_succ`, `WeierstrassCurve.Affine.isCoprime_ΨSq_pred` : the
  two-factor form.
* `WeierstrassCurve.Affine.isCoprime_Φ_ΨSq` : **`IsCoprime (Φₙ) (ΨSqₙ)`** at every `n : ℤ`, through
  the merged reduction — the statement `EllipticCurves.DivisionPolynomial.Coprime` proves by hand
  at `n = 2` and `n = 3` only.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7.
-/

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

/-- The workhorse, at a natural-number index: the pointwise statement over `AlgebraicClosure F`,
descended through `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`.

`isCoprime_ΨSq_adjacent` below is this statement at every `n : ℤ`; the two agree at a nonnegative
index, so this one is `private`. -/
private lemma isCoprime_ΨSq_adjacent_natCast [W.IsElliptic] (h2 : (2 : F) ≠ 0) (n : ℕ) :
    IsCoprime (W.ΨSq ((n : ℤ) + 1) * W.ΨSq ((n : ℤ) - 1)) (W.ΨSq (n : ℤ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [show ((0 : ℕ) : ℤ) = 0 from rfl, zero_add, zero_sub,
      WeierstrassCurve.ΨSq_one, WeierstrassCurve.ΨSq_neg, WeierstrassCurve.ΨSq_one, one_mul]
    exact isCoprime_one_left
  refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    (K := AlgebraicClosure F) _ _ _).mpr ?_
  intro a
  by_cases hq : (aeval a) (W.ΨSq (n : ℤ)) = 0
  · left
    have h2' : (2 : AlgebraicClosure F) ≠ 0 := fun h =>
      h2 ((algebraMap F (AlgebraicClosure F)).injective (by rw [map_ofNat, map_zero]; exact h))
    have hq' : ((W.map (algebraMap F (AlgebraicClosure F))).ΨSq (n : ℤ)).eval a = 0 := by
      rw [WeierstrassCurve.map_ΨSq, eval_map, ← aeval_def]; exact hq
    have key := eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero
      (W := W.map (algebraMap F (AlgebraicClosure F))) h2' hn hq'
    rw [map_mul]
    intro hcon
    refine key ?_
    rw [WeierstrassCurve.map_ΨSq, WeierstrassCurve.map_ΨSq, eval_map, eval_map, ← aeval_def,
      ← aeval_def]
    exact hcon
  · right
    exact hq

/-- **`ΨSqₙ₊₁ · ΨSqₙ₋₁` and `ΨSqₙ` are coprime**, at every `n : ℤ`, for an elliptic curve over a
field of characteristic `≠ 2`.

This is the obligation `EllipticCurves.DivisionPolynomial.Coprime`'s reduction leaves behind, and
its root route run: over `AlgebraicClosure F` a common root of the two would be the `x`-coordinate
of a point killed by `n` **and** by one of `n ± 1`, hence of `0`, which is not affine
(`WeierstrassCurve.Affine.eval_ΨSq_adjacent_ne_zero_of_eval_ΨSq_eq_zero`).

⚠️ Negative indices are free rather than a second case: `ΨSq` is even
(`WeierstrassCurve.ΨSq_neg`), so at `n < 0` the two neighbours swap and the product is the same.

⚠️ **`[W.IsElliptic]` and `(2 : F) ≠ 0` are the price of the route**, and they are not decoration:
the point-lifting step needs a smooth curve over a field in which `2` is invertible.  See the
module docstring for what this does and does not settle about the arbitrary-ring statement. -/
theorem isCoprime_ΨSq_adjacent [W.IsElliptic] (h2 : (2 : F) ≠ 0) (n : ℤ) :
    IsCoprime (W.ΨSq (n + 1) * W.ΨSq (n - 1)) (W.ΨSq n) := by
  rcases Int.natAbs_eq n with hn | hn
  · rw [hn]
    exact isCoprime_ΨSq_adjacent_natCast h2 n.natAbs
  · rw [hn, show -(n.natAbs : ℤ) + 1 = -((n.natAbs : ℤ) - 1) by ring,
      show -(n.natAbs : ℤ) - 1 = -((n.natAbs : ℤ) + 1) by ring,
      WeierstrassCurve.ΨSq_neg, WeierstrassCurve.ΨSq_neg, WeierstrassCurve.ΨSq_neg, mul_comm]
    exact isCoprime_ΨSq_adjacent_natCast h2 n.natAbs

/-- **`ΨSqₙ₊₁` and `ΨSqₙ` are coprime** — one factor of `isCoprime_ΨSq_adjacent`. -/
theorem isCoprime_ΨSq_succ [W.IsElliptic] (h2 : (2 : F) ≠ 0) (n : ℤ) :
    IsCoprime (W.ΨSq (n + 1)) (W.ΨSq n) :=
  (isCoprime_ΨSq_adjacent h2 n).of_mul_left_left

/-- **`ΨSqₙ₋₁` and `ΨSqₙ` are coprime** — the other factor of `isCoprime_ΨSq_adjacent`. -/
theorem isCoprime_ΨSq_pred [W.IsElliptic] (h2 : (2 : F) ≠ 0) (n : ℤ) :
    IsCoprime (W.ΨSq (n - 1)) (W.ΨSq n) :=
  (isCoprime_ΨSq_adjacent h2 n).of_mul_left_right

/-- **`Φₙ` and `ΨSqₙ` are coprime**, at every `n : ℤ`, for an elliptic curve over a field of
characteristic `≠ 2`.

This is `isCoprime_ΨSq_adjacent` through the merged, hypothesis-free reduction
`WeierstrassCurve.isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent`
(`EllipticCurves.DivisionPolynomial.Coprime`), which is where the observation that `Φ` is not the
difficulty was made.

⚠️ `EllipticCurves.DivisionPolynomial.Coprime` proves this by hand at `n = 2` and `n = 3` **over an
arbitrary commutative ring**, through explicit `Δ²` Bézout certificates.  Those two instances are
*not* superseded — they carry none of the three hypotheses here — and the two `example`s below
check that this theorem agrees with them where both apply. -/
theorem isCoprime_Φ_ΨSq [W.IsElliptic] (h2 : (2 : F) ≠ 0) (n : ℤ) :
    IsCoprime (W.Φ n) (W.ΨSq n) :=
  WeierstrassCurve.isCoprime_Φ_ΨSq_of_isCoprime_ΨSq_adjacent (isCoprime_ΨSq_adjacent h2 n)

/-! ### Agreement with the two merged hand certificates

⚠️ Neither `example` is a new result — `WeierstrassCurve.isCoprime_Φ_two_Ψ₂Sq` and
`WeierstrassCurve.isCoprime_Φ_three_ΨSq_three` are merged, over an arbitrary commutative ring, and
are **stronger** than what is reproduced here.  They are the check that the general theorem
evaluates to the right statement at the two indices where an independent proof exists. -/

example [W.IsElliptic] (h2 : (2 : F) ≠ 0) : IsCoprime (W.Φ 2) W.Ψ₂Sq := by
  simpa [WeierstrassCurve.ΨSq_two] using isCoprime_Φ_ΨSq h2 2

example [W.IsElliptic] (h2 : (2 : F) ≠ 0) : IsCoprime (W.Φ 3) (W.ΨSq 3) :=
  isCoprime_Φ_ΨSq h2 3

end WeierstrassCurve.Affine
