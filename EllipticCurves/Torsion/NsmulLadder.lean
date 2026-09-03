/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.DoublingCoords
import EllipticCurves.Torsion.OmegaDivisionPolynomial
import EllipticCurves.Torsion.XDifference

/-!
# The division-polynomial ladder: `x(n • P) = Φₙ(x)/ΨSqₙ(x)` at a general index

Issue `#251` asks for the multiplication-by-`n` coordinate formula.  This file proves it, by a
**two-step induction along the point group**, at every index `n` for which the ladder it climbs
does not pass through a zero:

```
ψ_k(x, y) ≠ 0 for every 1 ≤ k ≤ n   ⟹   n • (x, y) = (Φₙ(x)/ΨSqₙ(x), Yₙ(x, y)).
```

⚠️ Read the hypothesis carefully.  It is **not** `ΨSqₙ(x) ≠ 0`, which is what
`WeierstrassCurve.Affine.HasXCoordFormula` assumes, and the difference is not cosmetic — see
*"What this does not prove"* below.

## The route, and why it could not be written before

Every input is merged, and the last of them landed on 2026-09-01–02.

1. **The `x`-half is Ward's `x`-difference identity.**  Mathlib's `addX_eq_addX_negY_sub` says
   `x(P₁ + P₂) = x(P₁ − P₂) − ψ₂(P₁)·ψ₂(P₂)/(x₂ − x₁)²`.  Taking `P₁ = n • P` and `P₂ = P`, the
   left-hand side is what the step must compute, the first right-hand term is the *previous* rung
   `x((n−1) • P)`, and `x(n • P) − x(P) = −ψ_{n+1}ψ_{n−1}/ψₙ²` because `φₙ = X·ψₙ² − ψ_{n+1}ψ_{n−1}`
   is Mathlib's **definition** of `φ`.  The step then collapses to exactly
   `ψ_add_mul_ψ_sub (n+1) (n−1)` of `EllipticCurves.Torsion.XDifference` — Ward's relation with
   `ψ₁ = 1` folded in.  That is `divX_add_one`.

2. **The `y`-half is one instance of the elliptic-net relation.**  Carrying a `y`-coordinate through
   the induction is unavoidable: `ψ₂(n • P)` appears in step 1 and it is not a function of
   `x(n • P)` alone — its **sign** is the difference between `n • P` and `−n • P`.  The quantity
   that makes the recursion close is

   ```
   Tₙ := ψ₂ₙ(x, y)/ψₙ(x, y)⁴,   so that   Tₙ = 2·y(n • P) + a₁·x(n • P) + a₃,
   ```

   and unfolding Mathlib's `addY`/`negAddY` at `slope_of_X_ne` turns the group law into the
   recursion `divT_add_one`.
   Cleared of denominators that recursion is `ψ_ladder_mul_ψ_two`, and — after the substitution
   `ψ₂ₘ·ψ₂ = ψₘ·Ωₘ` (`ψ_mul_Ω`) and an exact cancellation of two middle terms — it is

   ```
   ψ_{n+3}·ψ_{n−1}·ψₙ² − ψ_{n−2}·ψ_{n+2}·ψ_{n+1}² = ψ₂²·ψ_{2n+1},
   ```

   which is literally `IsEllipticNet.rel W.ψ (n+1) 2 n 0 = 0`.  That is `ψ_net_instance`.

   ⚠️ Note **which** form of Ward's theorem this needs.  It has `s = 0`, so it lies inside
   `WeierstrassCurve.Affine.ψ_isEllipticSequence` (`EllipticCurves.Torsion.WardHalving`), and it
   has `r = n`, so it is **not** literally an instance of the `r = 1` slice `ψ_rel_one` that
   `EllipticCurves.Torsion.XDifference` consumes.  It is not obtainable from the `x`-difference
   identity alone, which is why the `y`-half is a separate argument rather than a corollary of the
   `x`-half.

   ⚠️ **That is a statement about shapes, not about cost, and it must not be read as one.**  For
   `ψ` the three named forms are not a hierarchy: `ψ_rel_one`, `ψ_isEllipticSequence` and
   `ψ_isEllipticNet` are each `… _of_gapCore W wardGapCore`, and there is nothing behind any of
   them that is not behind all three.  On the `r` axis the collapse is
   `IsEllipticNet.isEllipticSequence_iff_rel_one` (`EllipticCurves.Torsion.WardR1`), applicable to
   `ψ` through `ψ_neg` and `ψ_one`, with a `ring` call between the two.  On the `s` axis it is
   `normEDS_isEllipticNet_of_gapCore` (`EllipticCurves.Torsion.EllipticNetSlices`), which pays the
   regularity hypothesis once and for all in `UnivEDS`.  ⚠️ Neither collapse is automatic for
   `IsEllipticNet.rel` in general, and on **both** axes this tree now exhibits the gap.  On the
   `r` axis: `signMultiplesOfThree` is odd (`signMultiplesOfThree_odd`) and satisfies the whole
   `r = 1` slice (`signMultiplesOfThree_rel_one`) yet is not an elliptic sequence
   (`not_isEllipticSequence_signMultiplesOfThree`), because `signMultiplesOfThree 1 = 0`.  On the
   `s` axis: `sqZeroSeq` (`EllipticCurves.Torsion.EllipticNetRegularity`) is odd
   (`sqZeroSeq_odd`) and is an elliptic sequence (`isEllipticSequence_sqZeroSeq`) yet is not an
   elliptic net (`not_isEllipticNet_sqZeroSeq`), because its values all square to zero.
   ⚠️ The two witnesses fail *different* hypotheses — `W 1 = 1` on the `r` axis, regularity on the
   `s` axis — so the axes match in having a gap, not in what closes it.
   ⚠️ `EllipticCurves.Torsion.NsmulOrder` states the same split; keep the two in step.  What
   being outside the slice costs *this* file is the `ψ_mul_Ω` route to the instance, recorded
   next; it is not Ward.

⚠️ **The ladder identity is not itself a relator instance**, and it is worth recording why so nobody
looks for one: its three terms force `p + q + r = (6n+5)/2`, which is not an integer.  Only the
`Ω`-reduced form is an instance.  The route therefore has to pass through `ψ_mul_Ω`.

## What this does not prove

⚠️ **This file does not prove `HasXCoordFormula W n` at general `n`.**  That predicate assumes only
`ΨSqₙ(x) ≠ 0`; the ladder assumes `ψ_k(x, y) ≠ 0` for **every** `k ≤ n`.  The two differ at a
torsion point: if `(x, y)` has order `d` with `d < n` and `d ∤ n`, then `ψ_d(x, y)` may vanish while
`ψₙ(x, y)` does not, and the ladder breaks at `k = d` while `HasXCoordFormula`'s hypothesis still
holds.

⚠️ **The gap is closed, one file up.**  `hasXCoordFormula_of_two_ne_zero`
(`EllipticCurves.Torsion.NsmulOrder`) proves the predicate at every `n` over a field of
characteristic `≠ 2`, in three cases.  At a `2`-torsion point `n` is forced odd and
`n • (x, y) = (x, y)`, with `Φₙ(x)/ΨSqₙ(x) = x`.  Otherwise, if the ladder `ψ₁, …, ψₙ` has no zero
it applies `nsmul_eq_some_Φ_div_ΨSq` directly; and if it has one it takes `d` to be the **least**
index at which `ψ` vanishes, replaces `n` by its residue `j = n mod d`, runs
`nsmul_eq_some_Φ_div_ΨSq` at `j` — where by minimality no rung vanishes — and transports the
prediction back along `divX_add_mul_of_not_dvd`, which says the prediction `divX x` is `d`-periodic
at such a point.  So in two of the three cases the ladder of this file is what that argument
consumes, and it is not superseded.  ⚠️ The other route this paragraph names —
running the argument at the generic point and specialising — is **not** the one taken, and the
descent layer it would need is still absent.

⚠️ Nor does this file supply the elliptic **divisibility** half of Mathlib's standing `TODO`
(`IsDvdSequence (normEDS b c d)`), which is what would let `ψ_d = 0` propagate to `ψₙ = 0` along
`d ∣ n`.  It is proved neither in Mathlib nor here.

## Main statements

* `WeierstrassCurve.Affine.ψ_net_instance` : `rel ψ (n+1) 2 n 0 = 0`, unfolded — the elliptic-net
  instance the `y`-half runs on, over an arbitrary `CommRing`.
* `WeierstrassCurve.Affine.ψ_ladder_mul_ψ_two` : the ladder identity, over an arbitrary `CommRing`,
  carrying the spurious `ψ₂` that only a non-zero-divisor hypothesis removes.
* `WeierstrassCurve.Affine.divX`, `divT`, `divY` : the coordinates the division polynomials
  predict.  ⚠️ `divY` is stated through `divT = ψ₂ₙ/ψₙ⁴` because that is what closes the induction;
  its `ω`-form `ωₙ/(2ψₙ³)`, which is what `EllipticCurves.Torsion.OmegaCrux`'s on-curve identity is
  written with, is `WeierstrassCurve.Affine.divY_eq_omegaY`
  (`EllipticCurves.Torsion.NsmulYCoord`, issue `#1500`, **downstream** of this file).
* `WeierstrassCurve.Affine.divX_add_one`, `divT_add_one` : the two halves of the ladder step, as
  identities between those predictions.
* `WeierstrassCurve.Affine.nsmul_step` : the step at the level of points.
* `WeierstrassCurve.Affine.nsmul_eq_some_Φ_div_ΨSq` : **the coordinate formula**, the headline.
* `WeierstrassCurve.Affine.exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero` : its contrapositive —
  `n • P = 0` forces one of `ψ₁(P), …, ψₙ(P)` to vanish.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and Exercise 3.7.
* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. **70** (1948).
-/

open Polynomial Polynomial.Bivariate IsEllipticNet

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (W : Affine R)

/-- **The elliptic-net instance the `y`-half of the ladder runs on.**  Unfolding
`IsEllipticNet.rel W.ψ (n+1) 2 n 0 = 0` and using `ψ₁ = 1` and `ψ_{2−n} = −ψ_{n−2}` gives

```
ψ_{n+3}·ψ_{n−1}·ψₙ² − ψ_{n−2}·ψ_{n+2}·ψ_{n+1}² = ψ₂²·ψ_{2n+1}.
```

⚠️ It has `s = 0` but `r = n`, so it is *not* literally an instance of the `r = 1` slice
`WeierstrassCurve.Affine.ψ_rel_one` that `EllipticCurves.Torsion.XDifference` consumes, and it is
stated here from `ψ_isEllipticSequence`.  ⚠️ **That is not a stronger Ward input.**  For `ψ` the
two are the same statement (`IsEllipticNet.isEllipticSequence_iff_rel_one`, applicable through
`ψ_neg` and `ψ_one`, with a `ring` call between them), and both are corollaries of `wardGapCore`.
⚠️ It is *not* the first consumer of Ward's `ψ`-level corollaries in this tree —
`EllipticCurves.Torsion.OmegaCrux` and `EllipticCurves.Torsion.Collinearity` already consume
`ψ_isEllipticNet`, which is not a stronger input either: `normEDS_isEllipticNet_of_gapCore` is
`wardGapCore` as well.  What is new is the *use* it is put to. -/
theorem ψ_net_instance (n : ℤ) :
    W.ψ (n + 3) * W.ψ (n - 1) * W.ψ n ^ 2 - W.ψ (n - 2) * W.ψ (n + 2) * W.ψ (n + 1) ^ 2
      = W.ψ 2 ^ 2 * W.ψ (2 * n + 1) := by
  have h := W.ψ_isEllipticSequence (n + 1) 2 n
  rw [IsEllipticNet.rel] at h
  rw [show n + 1 + 2 + (0:ℤ) = n + 3 by ring, show n + 1 - 2 = n - 1 by ring,
    show n + (0:ℤ) = n by ring, show n + 1 + n + (0:ℤ) = 2 * n + 1 by ring,
    show n + 1 - n = (1:ℤ) by ring, show (2:ℤ) + 0 = 2 by ring,
    show (2:ℤ) + n + 0 = n + 2 by ring, show (2:ℤ) - n = -(n - 2) by ring,
    show n + 1 + (0:ℤ) = n + 1 by ring, ψ_one, ψ_neg] at h
  linear_combination h

/-- **The ladder identity**, over an arbitrary `CommRing`:

```
ψ_{2n+2}·ψ_{n−1}·ψₙ + ψ_{2n}·ψ_{n+2}·ψ_{n+1} = ψ₂·ψ_{2n+1}·ψₙ·ψ_{n+1},
```

cleared of denominators, and multiplied through by the spurious `ψ₂` that only a non-zero-divisor
hypothesis removes.  It is the recursion satisfied by `Tₙ = ψ₂ₙ/ψₙ⁴`, which is the `ψ₂`-value of
`n • P`; `divT_add_one` is that reading.

The proof multiplies by `ψ₂`, substitutes `ψ₂ₘ·ψ₂ = ψₘ·Ωₘ` (`ψ_mul_Ω`,
`EllipticCurves.Torsion.OmegaDivisionPolynomial`) at `m = n` and `m = n+1`, and finds that
`ψₙ·ψ_{n+1}` factors out with the two `ψ_{n−1}²ψ_{n+2}²` terms cancelling exactly, leaving
`ψ_net_instance`.

⚠️ **The identity is not itself a relator instance.**  Its three terms force
`p + q + r = (6n+5)/2`, which is not an integer, so no `(p, q, r, s)` produces it directly.  Only
the `Ω`-reduced form is an instance — which is why the route has to pass through `ψ_mul_Ω`. -/
theorem ψ_ladder_mul_ψ_two (n : ℤ) :
    (W.ψ (2 * n + 2) * W.ψ (n - 1) * W.ψ n + W.ψ (2 * n) * W.ψ (n + 2) * W.ψ (n + 1)
        - W.ψ 2 * W.ψ (2 * n + 1) * W.ψ n * W.ψ (n + 1)) * W.ψ 2 = 0 := by
  have h1 := W.ψ_mul_Ω (n + 1)
  have h0 := W.ψ_mul_Ω n
  rw [show 2 * (n + 1) = 2 * n + 2 by ring, Ω, show n + 1 + 2 = n + 3 by ring,
    show n + 1 - 1 = n by ring, show n + 1 - 2 = n - 1 by ring,
    show n + 1 + 1 = n + 2 by ring, ← ψ_two] at h1
  rw [Ω, ← ψ_two] at h0
  have hnet := W.ψ_net_instance n
  linear_combination (W.ψ (n - 1) * W.ψ n) * h1 + (W.ψ (n + 2) * W.ψ (n + 1)) * h0
    + (W.ψ n * W.ψ (n + 1)) * hnet

section Field

variable {F : Type*} [Field F] {W : Affine F} {x y : F}

/-- `Φₙ(x) = x·ψₙ(x,y)² − ψ_{n+1}(x,y)·ψ_{n−1}(x,y)` at a point of `W`. -/
theorem Φ_eval_eq_of_equation (h : W.Equation x y) (n : ℤ) :
    (W.Φ n).eval x = x * (W.ψ n).evalEval x y ^ 2
      - (W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y := by
  have H := ψ_add_mul_ψ_sub_evalEval h n 1
  simp only [Φ_one, ΨSq_one, eval_X, eval_one, mul_one] at H
  rw [← ψ_sq_evalEval h] at H
  linear_combination H

/-- The `x`-coordinate gap `x − Φₙ/ΨSqₙ` in division-polynomial form. -/
theorem sub_Φ_div_ΨSq (h : W.Equation x y) {n : ℤ} (hn : (W.ψ n).evalEval x y ≠ 0) :
    x - (W.Φ n).eval x / (W.ΨSq n).eval x
      = (W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y
          / (W.ψ n).evalEval x y ^ 2 := by
  have hsq : (W.ΨSq n).eval x = (W.ψ n).evalEval x y ^ 2 := (ψ_sq_evalEval h n).symm
  rw [hsq, Φ_eval_eq_of_equation h n]
  field_simp
  ring

/-- **The ladder identity at a point**, with the spurious `ψ₂` divided out.  Over a field this
costs one hypothesis, `ψ₂(x, y) ≠ 0` — i.e. `(x, y)` is not `2`-torsion — and the ladder needs that
anyway from `n = 2` on. -/
theorem ψ_ladder_evalEval (ht : (W.ψ 2).evalEval x y ≠ 0) (n : ℤ) :
    (W.ψ (2 * n + 2)).evalEval x y * (W.ψ (n - 1)).evalEval x y * (W.ψ n).evalEval x y
        + (W.ψ (2 * n)).evalEval x y * (W.ψ (n + 2)).evalEval x y
            * (W.ψ (n + 1)).evalEval x y
      = (W.ψ 2).evalEval x y * (W.ψ (2 * n + 1)).evalEval x y * (W.ψ n).evalEval x y
          * (W.ψ (n + 1)).evalEval x y := by
  have H := congrArg (fun g : F[X][Y] => g.evalEval x y) (W.ψ_ladder_mul_ψ_two n)
  simp only [evalEval_mul, evalEval_sub, evalEval_add, evalEval_zero] at H
  linear_combination (mul_eq_zero.mp H).resolve_right ht

/-- **The `x`-coordinate the division polynomials predict for `n • (x, y)`**: `Φₙ(x)/ΨSqₙ(x)`.

⚠️ Read this as *"the division-polynomial `x`-coordinate at `n`"*, not as `x(n • P)`.  That reading
is the content of this file and holds only under the ladder hypothesis. -/
noncomputable def divX (W : Affine F) (x : F) (n : ℤ) : F :=
  (W.Φ n).eval x / (W.ΨSq n).eval x

/-- **The value of `ψ₂ = 2Y + a₁X + a₃` the division polynomials predict at `n • (x, y)`**:
`Tₙ = ψ₂ₙ(x, y)/ψₙ(x, y)⁴`.

This is the quantity that makes the induction close.  ⚠️ Carrying an `x`-coordinate alone does
**not** work: the group law needs `ψ₂(n • P)`, whose *square* is a function of `x(n • P)` but whose
*sign* distinguishes `n • P` from `−n • P`.  `Tₙ` is what pins the sign, and the fact that this
particular ratio is the right thing is `ψ_mul_Ω` plus the even/odd `preΨ` split. -/
noncomputable def divT (W : Affine F) (x y : F) (n : ℤ) : F :=
  (W.ψ (2 * n)).evalEval x y / (W.ψ n).evalEval x y ^ 4

/-- **The `y`-coordinate the division polynomials predict for `n • (x, y)`**, read off `divT`
through `Tₙ = 2y + a₁x + a₃`.  Over a field of characteristic `≠ 2` this determines it. -/
noncomputable def divY (W : Affine F) (x y : F) (n : ℤ) : F :=
  (W.divT x y n - W.a₁ * W.divX x n - W.a₃) / 2

/-- `Φ₁/ΨSq₁ = X/1 = x`.  ⚠️ No hypothesis on `(x, y)`: this is a statement about the polynomials
`Φ₁ = X` and `ΨSq₁ = 1`, not about a point. -/
theorem divX_one : W.divX x 1 = x := by
  simp [divX, Φ_one, ΨSq_one]

/-- `T₁ = ψ₂/ψ₁⁴ = 2y + a₁x + a₃`. -/
theorem divT_one : W.divT x y 1 = 2 * y + W.a₁ * x + W.a₃ := by
  rw [divT, ψ_one_evalEval, show (2 : ℤ) * 1 = 2 by ring, ψ_two_evalEval]
  ring

/-- The predicted `y`-coordinate at `n = 1` is `y` itself.  ⚠️ Like `divX_one` and `divT_one` this
needs no equation on `(x, y)`, only `(2 : F) ≠ 0` to undo the halving in `divY`. -/
theorem divY_one (h2 : (2 : F) ≠ 0) : W.divY x y 1 = y := by
  rw [divY, divT_one, divX_one]
  field_simp
  ring

/-- **The `x`-half of the ladder step.**  In `x(P₁ + P₂) = x(P₁ − P₂) − ψ₂(P₁)ψ₂(P₂)/(x₂ − x₁)²`
at `P₁ = n • P`, `P₂ = P`, every term is a division-polynomial expression, and the identity that
closes it is `ψ_add_mul_ψ_sub_evalEval` at `(p, q) = (n+1, n−1)`:
`ψ_{2n}·ψ₂ = Φ_{n−1}·ΨSq_{n+1} − Φ_{n+1}·ΨSq_{n−1}`.

⚠️ This is a statement about the *predictions* `divX`, `divT`; it says nothing about `n • P`.  The
point-level reading is `nsmul_step`. -/
theorem divX_add_one (h : W.Equation x y) {n : ℤ}
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) :
    W.divX x (n + 1)
      = W.divX x (n - 1)
        - W.divT x y n * (W.ψ 2).evalEval x y / (x - W.divX x n) ^ 2 := by
  have key := ψ_add_mul_ψ_sub_evalEval h (n + 1) (n - 1)
  rw [show n + 1 + (n - 1) = 2 * n by ring, show n + 1 - (n - 1) = (2 : ℤ) by ring] at key
  simp only [← ψ_sq_evalEval h] at key
  rw [divX, divX, divX, divT, sub_Φ_div_ΨSq h h0]
  simp only [← ψ_sq_evalEval h]
  field_simp
  linear_combination key

/-- **The `y`-half of the ladder step**, as a recursion for `Tₙ = ψ₂ₙ/ψₙ⁴`.  It is
`ψ_ladder_evalEval` divided by `ψₙ³ψ_{n+1}³`, with Mathlib's `ψ_odd` used to recognise
`ψ_{n+2}ψₙ³ − ψ_{n−1}ψ_{n+1}³` as `ψ_{2n+1}`.

⚠️ Unlike `divX_add_one` this needs **no** hypothesis at `n − 1`: the denominators it clears are
`ψₙ²` and `ψ_{n+1}²` only.  `ψ_{n−1} ≠ 0` enters the step elsewhere — in `divX_add_one` as the
denominator `ΨSq_{n−1}` of the previous rung, and in `nsmul_step` as what makes `x(n • P) ≠ x(P)`
and hence the group law applicable. -/
theorem divT_add_one (h : W.Equation x y) {n : ℤ}
    (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) (ht : (W.ψ 2).evalEval x y ≠ 0) :
    W.divT x y (n + 1) * (W.divX x n - x)
      = -(W.divT x y n * (W.divX x (n + 1) - x))
        - (W.ψ 2).evalEval x y * (W.divX x n - W.divX x (n + 1)) := by
  have hgap0 := sub_Φ_div_ΨSq h h0
  have hgap1 := sub_Φ_div_ΨSq h hp
  rw [show n + 1 + 1 = n + 2 by ring, show n + 1 - 1 = n by ring] at hgap1
  have hladder := ψ_ladder_evalEval (W := W) (x := x) (y := y) ht n
  have hodd := congrArg (fun g : Polynomial (Polynomial F) => g.evalEval x y) (W.ψ_odd n)
  simp only [evalEval_mul, evalEval_sub, evalEval_pow] at hodd
  have e0 : W.divX x n - x
      = -((W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y
          / (W.ψ n).evalEval x y ^ 2) := by
    rw [divX]; linear_combination -hgap0
  have e1 : W.divX x (n + 1) - x
      = -((W.ψ (n + 2)).evalEval x y * (W.ψ n).evalEval x y
          / (W.ψ (n + 1)).evalEval x y ^ 2) := by
    rw [divX]; linear_combination -hgap1
  have e2 : W.divX x n - W.divX x (n + 1)
      = (W.ψ (n + 2)).evalEval x y * (W.ψ n).evalEval x y / (W.ψ (n + 1)).evalEval x y ^ 2
        - (W.ψ (n + 1)).evalEval x y * (W.ψ (n - 1)).evalEval x y
            / (W.ψ n).evalEval x y ^ 2 := by
    rw [divX, divX]; linear_combination hgap1 - hgap0
  rw [divT, divT, show 2 * (n + 1) = 2 * n + 2 by ring, e0, e1, e2]
  field_simp
  linear_combination (-((W.ψ n).evalEval x y * (W.ψ (n + 1)).evalEval x y
      * (W.ψ 2).evalEval x y)) * hodd - hladder

variable [DecidableEq F]

/-- **The ladder step at the level of points.**  Given that the two previous rungs `(n−1) • P` and
`n • P` are the points the division polynomials predict, and that `ψ_{n−1}`, `ψₙ`, `ψ_{n+1}` and
`ψ₂` do not vanish at `(x, y)`, the next rung `(n+1) • P` is too.

The two ingredients are Mathlib's group law — `addX_eq_addX_negY_sub` for the `x`-coordinate, and
`addY`/`negAddY` unfolded at `slope_of_X_ne` for the `y`-coordinate — and the two halves
`divX_add_one` / `divT_add_one`.  ⚠️ `(n−1) • P` enters as `n • P + (−P)`, which is why the step
needs the rung *before* the previous one and the induction is two-step rather than one. -/
theorem nsmul_step (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) {n : ℤ}
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) (ht : (W.ψ 2).evalEval x y ≠ 0)
    (hm' : W.Nonsingular (W.divX x (n - 1)) (W.divY x y (n - 1)))
    (h0' : W.Nonsingular (W.divX x n) (W.divY x y n))
    (IHm : ((n - 1) • Point.some x y hns : W.Point) = .some _ _ hm')
    (IH0 : ((n : ℤ) • Point.some x y hns : W.Point) = .some _ _ h0') :
    ∃ h' : W.Nonsingular (W.divX x (n + 1)) (W.divY x y (n + 1)),
      ((n + 1 : ℤ) • Point.some x y hns : W.Point) = .some _ _ h' := by
  have hEq : W.Equation x y := hns.left
  have hgap0 := sub_Φ_div_ΨSq hEq h0
  have hsub0 : x - W.divX x n ≠ 0 := by
    rw [divX, hgap0]
    exact div_ne_zero (mul_ne_zero hp hm) (pow_ne_zero 2 h0)
  have hxne : W.divX x n ≠ x := fun hc => hsub0 (sub_eq_zero_of_eq hc.symm)
  -- the `(n-1)` step, giving the `x`-coordinate of `n • P - P`
  have hminus : ((n - 1 : ℤ) • Point.some x y hns : W.Point)
      = (n : ℤ) • Point.some x y hns + -(Point.some x y hns) := by
    rw [sub_smul, one_zsmul, sub_eq_add_neg]
  rw [IH0, Point.neg_some, Point.add_of_X_ne hxne, IHm, Point.some.injEq] at hminus
  -- the `(n+1)` step
  have hplus : ((n + 1 : ℤ) • Point.some x y hns : W.Point)
      = (n : ℤ) • Point.some x y hns + Point.some x y hns := by
    rw [add_smul, one_zsmul]
  rw [IH0, Point.add_of_X_ne hxne] at hplus
  -- the `x`-coordinate
  have hT : W.divY x y n - W.negY (W.divX x n) (W.divY x y n) = W.divT x y n := by
    rw [negY, divY]; field_simp; ring
  have hψ₂ : y - W.negY x y = (W.ψ 2).evalEval x y := by
    rw [negY, ψ_two_evalEval]; ring
  have hψ₂' : 2 * y + W.a₁ * x + W.a₃ = (W.ψ 2).evalEval x y := ψ_two_evalEval.symm
  have hX : W.addX (W.divX x n) x (W.slope (W.divX x n) x (W.divY x y n) y)
      = W.divX x (n + 1) := by
    rw [addX_eq_addX_negY_sub _ _ hxne, ← hminus.1, hT, hψ₂,
      divX_add_one hEq hm h0 hp]
  have hY : W.addY (W.divX x n) x (W.divY x y n)
      (W.slope (W.divX x n) x (W.divY x y n) y) = W.divY x y (n + 1) := by
    have hstep := divT_add_one hEq h0 hp ht
    rw [addY, negAddY, hX, slope_of_X_ne hxne, negY, divY, divY]
    field_simp
    linear_combination (-hstep) + (W.divX x (n + 1) - W.divX x n) * hψ₂'
  have hns' : W.Nonsingular (W.divX x (n + 1)) (W.divY x y (n + 1)) := by
    rw [← hX, ← hY]
    exact nonsingular_add h0' hns fun hc => hxne hc.1
  exact ⟨hns', by rw [hplus, Point.some.injEq]; exact ⟨hX, hY⟩⟩

/-- **The base case `n = 1`**: `1 • P = P`, and `Φ₁/ΨSq₁ = X/1` and `T₁ = ψ₂/ψ₁⁴ = 2y + a₁x + a₃`
make the predictions agree with it. -/
theorem nsmul_one_eq_div (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) :
    ∃ h' : W.Nonsingular (W.divX x 1) (W.divY x y 1),
      ((1 : ℤ) • Point.some x y hns : W.Point) = .some _ _ h' := by
  have hX := divX_one (W := W) (x := x)
  have hY := divY_one (W := W) (x := x) (y := y) h2
  have hns' : W.Nonsingular (W.divX x 1) (W.divY x y 1) := by rw [hX, hY]; exact hns
  exact ⟨hns', by rw [one_zsmul, Point.some.injEq]; exact ⟨hX.symm, hY.symm⟩⟩

/-- **The base case `n = 2`**, which is where the doubling formula enters and the only place it
does.  The step cannot reach `n = 2` from `n = 1`: it would need the rung `0 • P = O`, which is not
affine, and `x(1 • P) = x(P)` makes `addX_eq_addX_negY_sub` inapplicable.  The coordinates come
from `addX_self_eq_div` and `addY_self_eq_div` (`EllipticCurves.Torsion.DoublingCoords`), and
matching `addY_self_eq_div`'s `preΨ₄` numerator with `T₂ = ψ₄/ψ₂⁴` is `ψ_four` plus
`ΨSq₂ = ψ₂²`. -/
theorem nsmul_two_eq_div (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) :
    ∃ h' : W.Nonsingular (W.divX x 2) (W.divY x y 2),
      ((2 : ℤ) • Point.some x y hns : W.Point) = .some _ _ h' := by
  have hEq : W.Equation x y := hns.left
  have hyne : y ≠ W.negY x y := by
    intro hc
    exact ht (by rw [ψ_two_evalEval]; rw [negY] at hc; linear_combination hc)
  have hsq : (W.Ψ₂Sq).eval x = (W.ψ 2).evalEval x y ^ 2 := by
    rw [← ΨSq_two, ← ψ_sq_evalEval hEq]
  have hfour := ψ_four_evalEval hEq ht
  have hX : W.addX x x (W.slope x x y y) = W.divX x 2 := by
    rw [addX_self_eq_div hEq hyne, divX, ΨSq_two]
  have hY : W.addY x x y (W.slope x x y y) = W.divY x y 2 := by
    rw [addY_self_eq_div hEq h2 hyne, divY, divT, divX, ΨSq_two, show (2 : ℤ) * 2 = 4 by norm_num,
      hfour, hsq]
    field_simp
    ring
  have hns' : W.Nonsingular (W.divX x 2) (W.divY x y 2) := by
    rw [← hX, ← hY]; exact nonsingular_add hns hns fun hc => hyne hc.2
  refine ⟨hns', ?_⟩
  rw [two_zsmul, Point.add_self_of_Y_ne hyne, Point.some.injEq]
  exact ⟨hX, hY⟩

/-- **`n • (x, y)` is the affine point the division polynomials predict.**  Packaged as a
predicate so the two-step induction can carry it without the cast bookkeeping leaking into a
dependent `∃`. -/
def NsmulEqDiv {x y : F} (hns : W.Nonsingular x y) (n : ℤ) : Prop :=
  ∃ h' : W.Nonsingular (W.divX x n) (W.divY x y n),
    (n • Point.some x y hns : W.Point) = .some _ _ h'

/-- The base case `n = 1`, as a `NsmulEqDiv`. -/
theorem nsmulEqDiv_one (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) :
    NsmulEqDiv hns 1 := nsmul_one_eq_div h2 hns

/-- The base case `n = 2`, as a `NsmulEqDiv`. -/
theorem nsmulEqDiv_two (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y)
    (ht : (W.ψ 2).evalEval x y ≠ 0) : NsmulEqDiv hns 2 := nsmul_two_eq_div h2 hns ht

/-- The ladder step, as a `NsmulEqDiv`. -/
theorem nsmulEqDiv_step (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) {n : ℤ}
    (hm : (W.ψ (n - 1)).evalEval x y ≠ 0) (h0 : (W.ψ n).evalEval x y ≠ 0)
    (hp : (W.ψ (n + 1)).evalEval x y ≠ 0) (ht : (W.ψ 2).evalEval x y ≠ 0)
    (Gm : NsmulEqDiv hns (n - 1)) (G0 : NsmulEqDiv hns n) : NsmulEqDiv hns (n + 1) := by
  obtain ⟨hm', IHm⟩ := Gm
  obtain ⟨h0', IH0⟩ := G0
  exact nsmul_step h2 hns hm h0 hp ht hm' h0' IHm IH0

/-- The two-step induction: with `(2 : F) ≠ 0`, at a point of `W`, the ladder holds at `m+1` and
`m+2` together, provided it does not pass through a zero up to `m+2`.  ⚠️ Both components are
needed in the statement — the step consumes two consecutive rungs, so a single-rung induction
hypothesis does not carry. -/
private theorem nsmulEqDiv_pair (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) :
    ∀ m : ℕ, (∀ k : ℤ, 1 ≤ k → k ≤ (m : ℤ) + 2 → (W.ψ k).evalEval x y ≠ 0) →
      NsmulEqDiv hns ((m : ℤ) + 1) ∧ NsmulEqDiv hns ((m : ℤ) + 2) := by
  intro m
  induction m with
  | zero =>
    intro hψ
    refine ⟨?_, ?_⟩
    · simpa using nsmulEqDiv_one h2 hns
    · simpa using nsmulEqDiv_two h2 hns (hψ 2 (by norm_num) (by push_cast))
  | succ k IH =>
    intro hψ
    obtain ⟨G1, G2⟩ := IH fun j hj hj2 => hψ j hj (by push_cast at hj2 ⊢; omega)
    have hcast : ((k : ℕ) : ℤ) + 1 + 1 = ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    refine ⟨by rw [← hcast]; exact G2, ?_⟩
    have hne : ∀ j : ℤ, 1 ≤ j → j ≤ (k : ℤ) + 3 → (W.ψ j).evalEval x y ≠ 0 := by
      intro j hj hj2; exact hψ j hj (by push_cast; omega)
    have hstep := nsmulEqDiv_step (n := (k : ℤ) + 2) h2 hns
      (by rw [show (k : ℤ) + 2 - 1 = (k : ℤ) + 1 by ring]
          exact hne _ (by omega) (by omega))
      (hne _ (by omega) (by omega))
      (by rw [show (k : ℤ) + 2 + 1 = (k : ℤ) + 3 by ring]
          exact hne _ (by omega) (by omega))
      (hne 2 (by norm_num) (by omega))
      (by rw [show (k : ℤ) + 2 - 1 = (k : ℤ) + 1 by ring]; exact G1) G2
    rw [show ((k + 1 : ℕ) : ℤ) + 2 = (k : ℤ) + 2 + 1 by push_cast; ring]
    exact hstep

/-- **The multiplication-by-`n` coordinate formula along a nonvanishing ladder**, in packaged form.
⚠️ Note the hypothesis needed is `ψ_k ≠ 0` up to `k = n` and no further: the induction is arranged
so that the rung whose ladder reaches `n` is the *second* component of `nsmulEqDiv_pair`. -/
theorem nsmulEqDiv_of_forall_ψ_ne_zero (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) {n : ℕ}
    (hn : 1 ≤ n) (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    NsmulEqDiv hns (n : ℤ) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · obtain rfl : n = 1 := by omega
    simpa using nsmulEqDiv_one h2 hns
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have H := (nsmulEqDiv_pair h2 hns m
      fun k hk hk2 => hψ k hk (by push_cast at hk2 ⊢; omega)).2
    rwa [show ((m : ℕ) : ℤ) + 2 = ((m + 2 : ℕ) : ℤ) by push_cast; ring] at H

/-- **The `x`-coordinate formula** `x(n • P) = Φₙ(x)/ΨSqₙ(x)`, with `(2 : F) ≠ 0`, at every index
`n ≥ 1` whose ladder `ψ₁(x, y), …, ψₙ(x, y)` has no zero.  This is `#251`'s scope item 1 at a
point.

⚠️ It is **not** `WeierstrassCurve.Affine.HasXCoordFormula W n`, whose hypothesis is the weaker
`ΨSqₙ(x) ≠ 0` and which quantifies over all points of `W`.  See the module docstring for why the
gap is real and what closing it would take. -/
theorem nsmul_eq_some_Φ_div_ΨSq (h2 : (2 : F) ≠ 0) (hns : W.Nonsingular x y) {n : ℕ}
    (hn : 1 ≤ n) (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → (W.ψ k).evalEval x y ≠ 0) :
    ∃ (y' : F) (h' : W.Nonsingular ((W.Φ (n : ℤ)).eval x / (W.ΨSq (n : ℤ)).eval x) y'),
      (n • Point.some x y hns : W.Point) = .some _ y' h' := by
  obtain ⟨h', heq⟩ := nsmulEqDiv_of_forall_ψ_ne_zero h2 hns hn hψ
  exact ⟨W.divY x y (n : ℤ), h', by rw [← natCast_zsmul]; exact heq⟩

/-- **`n • P = 0` forces one of `ψ₁(P), …, ψₙ(P)` to vanish** — the contrapositive of the
coordinate formula, and the half of `#251`'s scope item 2 that the ladder does give.

⚠️ The converse (`ψₙ(P) = 0 → n • P = 0`) is **not** proved here, and neither is the sharpening
that the vanishing index can be taken to be `n` itself; that needs the elliptic **divisibility**
half of Mathlib's `TODO`.  What this says is only that *some* rung of the ladder is a zero. -/
theorem exists_ψ_evalEval_eq_zero_of_nsmul_eq_zero (h2 : (2 : F) ≠ 0)
    (hns : W.Nonsingular x y) {n : ℕ} (hn : 1 ≤ n)
    (hzero : (n • Point.some x y hns : W.Point) = 0) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ (n : ℤ) ∧ (W.ψ k).evalEval x y = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y', h', heq⟩ := nsmul_eq_some_Φ_div_ΨSq h2 hns hn
    fun k hk hk2 => hcon k hk hk2
  rw [heq] at hzero
  exact Point.some_ne_zero h' hzero

end Field

/-! ## Non-vacuity: the ladder at `n = 5` on `y² = x³ + 1` -/

section Nonvacuity

open EllipticCurves.Fixture

/-- `P = (2, 3)` lies on `y² = x³ + 1` and is nonsingular. -/
private lemma exampleNonsingular : (y2EqX3AddOne ℚ).Nonsingular 2 3 :=
  equation_iff_nonsingular.mp (by norm_num [y2EqX3AddOne, WeierstrassCurve.Affine.equation_iff])

private lemma exampleEquation : (y2EqX3AddOne ℚ).Equation 2 3 := exampleNonsingular.left

/-- `ψ₂(2, 3) = 2·3 = 6`. -/
private lemma exampleψTwo : ((y2EqX3AddOne ℚ).ψ 2).evalEval 2 3 = 6 := by
  rw [ψ_two_evalEval]; norm_num [y2EqX3AddOne]

/-- `ψ₃(2, 3) = Ψ₃(2) = 3·2⁴ + 3·b₆·2 = 72`. -/
private lemma exampleψThree : ((y2EqX3AddOne ℚ).ψ 3).evalEval 2 3 = 72 := by
  rw [ψ_three, evalEval_C]
  norm_num [y2EqX3AddOne, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `preΨ₄(2) = 432`. -/
private lemma examplePreΨFour : (y2EqX3AddOne ℚ).preΨ₄.eval 2 = 432 := by
  norm_num [y2EqX3AddOne, WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `ψ₄(2, 3) = ψ₂·preΨ₄ = 6·432 = 2592`. -/
private lemma exampleψFour : ((y2EqX3AddOne ℚ).ψ 4).evalEval 2 3 = 2592 := by
  rw [ψ_four_evalEval exampleEquation (by rw [exampleψTwo]; norm_num), exampleψTwo,
    examplePreΨFour]
  norm_num

/-- `ψ₅(2, 3) = ψ₄ψ₂³ − ψ₁ψ₃³ = 2592·216 − 373248 = 186624`, through Mathlib's `ψ_odd`. -/
private lemma exampleψFive : ((y2EqX3AddOne ℚ).ψ 5).evalEval 2 3 = 186624 := by
  have h := (y2EqX3AddOne ℚ).ψ_odd 2
  rw [show (2 : ℤ) * 2 + 1 = 5 by norm_num, show (2 : ℤ) + 2 = 4 by norm_num,
    show (2 : ℤ) - 1 = 1 by norm_num, show (2 : ℤ) + 1 = 3 by norm_num] at h
  have h' := congrArg (fun g : Polynomial (Polynomial ℚ) => g.evalEval 2 3) h
  simp only [evalEval_sub, evalEval_mul, evalEval_pow] at h'
  rw [h', exampleψFour, exampleψTwo, exampleψThree, ψ_one_evalEval]
  norm_num

/-- `ψ₆(2, 3) = 0`: `P` has order `6`.  Through Mathlib's `ψ_even` at `m = 3`, with the `ψ₂` on the
left cancelled by `ψ₂(2, 3) = 6 ≠ 0`. -/
private lemma exampleψSix : ((y2EqX3AddOne ℚ).ψ 6).evalEval 2 3 = 0 := by
  have h := (y2EqX3AddOne ℚ).ψ_even 3
  rw [show (2 : ℤ) * 3 = 6 by norm_num, show (3 : ℤ) - 1 = 2 by norm_num,
    show (3 : ℤ) + 2 = 5 by norm_num, show (3 : ℤ) - 2 = 1 by norm_num,
    show (3 : ℤ) + 1 = 4 by norm_num, ← ψ_two] at h
  have h' := congrArg (fun g : Polynomial (Polynomial ℚ) => g.evalEval 2 3) h
  simp only [evalEval_sub, evalEval_mul, evalEval_pow] at h'
  rw [exampleψTwo, exampleψThree, exampleψFour, exampleψFive, ψ_one_evalEval] at h'
  linarith

/-- **The certificate.**  On `y² = x³ + 1` over `ℚ` the point `P = (2, 3)` has
`ψ₁ = 1, ψ₂ = 6, ψ₃ = 72, ψ₄ = 2592, ψ₅ = 186624` — all nonzero — so the ladder reaches `n = 5`,
two rungs past the largest index at which this tree previously had a coordinate formula.  The
value it computes is `x(5 • P) = Φ₅(2)/ΨSq₅(2) = 2 = x(P)`, so `5 • P = ±P`.  That is right: `P`
has order `6` on this curve, so `5 • P = -P = (2, -3)`.

⚠️ **This file does not prove the order claim**, and the `ψ₆(2, 3) = 0` computed above does not
prove it either — `ψ_d(P) = 0 → d • P = 0` is exactly the converse the module docstring flags as
unproved.  The order is stated here as the external fact that explains the value, not as a
consequence of anything below.

⚠️ The content is that `5 • P` is **affine with `x`-coordinate `2`**, and in particular nonzero —
so nothing in this file is a statement about an empty hypothesis set, and the `n = 5` instance is
out of reach of `hasXCoordFormula_two` / `hasXCoordFormula_three`. -/
theorem nsmul_five_y2EqX3AddOne :
    ∃ (y' : ℚ) (h' : (y2EqX3AddOne ℚ).Nonsingular 2 y'),
      ((5 : ℕ) • (Point.some 2 3 exampleNonsingular : (y2EqX3AddOne ℚ).Point))
        = Point.some 2 y' h' := by
  have hne : ∀ k : ℤ, 1 ≤ k → k ≤ ((5 : ℕ) : ℤ) →
      ((y2EqX3AddOne ℚ).ψ k).evalEval 2 3 ≠ 0 := by
    intro k hk hk5
    norm_num at hk5
    interval_cases k
    · rw [ψ_one_evalEval]; norm_num
    · rw [exampleψTwo]; norm_num
    · rw [exampleψThree]; norm_num
    · rw [exampleψFour]; norm_num
    · rw [exampleψFive]; norm_num
  obtain ⟨y', h', heq⟩ :=
    nsmul_eq_some_Φ_div_ΨSq (W := y2EqX3AddOne ℚ) (by norm_num) exampleNonsingular
      (n := 5) (by norm_num) hne
  have hx : ((y2EqX3AddOne ℚ).Φ ((5 : ℕ) : ℤ)).eval 2
      / ((y2EqX3AddOne ℚ).ΨSq ((5 : ℕ) : ℤ)).eval 2 = 2 := by
    have hΦ := Φ_eval_eq_of_equation exampleEquation ((5 : ℕ) : ℤ)
    have hΨ := ψ_sq_evalEval exampleEquation ((5 : ℕ) : ℤ)
    rw [show (((5 : ℕ) : ℤ) + 1) = 6 by norm_num,
      show (((5 : ℕ) : ℤ) - 1) = 4 by norm_num] at hΦ
    rw [show ((5 : ℕ) : ℤ) = 5 by norm_num] at hΦ hΨ ⊢
    rw [hΦ, ← hΨ, exampleψSix, exampleψFive]
    norm_num
  refine ⟨y', hx ▸ h', ?_⟩
  rw [heq, Point.some.injEq]
  exact ⟨hx, rfl⟩

end Nonvacuity

end WeierstrassCurve.Affine
