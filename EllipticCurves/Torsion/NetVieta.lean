/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Torsion.Collinearity

/-!
# The Vieta half of the group law for an elliptic net, and the crux by induction

`EllipticCurves.Torsion.Collinearity` reads one instance of Ward's `s ≠ 0` relation as the
statement that the three division-polynomial points at indices summing to zero are **collinear**,
and records that the missing half of the Weierstrass group law is the **Vieta** relation

```
X_u + X_v + X_w = (Λ² - b₂)/4,      Λ := (S_u - S_v)/(X_u - X_v),
```

which is `#404`'s crux.  This file proves the Vieta half by induction, for an abstract elliptic net
over a field, from three base cases.

## The structure

For a nondegenerate net `a : ℤ → F` with `a 1 = 1` write

```
Xₙ := x - a_{n+1}·a_{n-1}/a_n²,     Sₙ := a_{2n}/a_n⁴,
τₙ := Sₙ² - (4Xₙ³ + b₂Xₙ² + 2b₄Xₙ + b₆),
𝒱(u,v,w) := 4(X_u + X_v + X_w) + b₂ - Λ(u,v)².
```

`τₙ = 0` is the crux at `n`, and `𝒱 = 0` is the Vieta relation.  Two facts drive everything:

* **`IsEllipticNet.netDefect_collinear`** (elementary, from collinearity alone): for `u+v+w = 0`,

  ```
  τ_u(X_v - X_w) + τ_v(X_w - X_u) + τ_w(X_u - X_v) = 𝒱(u,v,w)·(X_u-X_v)(X_v-X_w)(X_w-X_u).
  ```

  Three collinear points lie on the line `S = ΛX + M`, so `Σ S_u²(X_v-X_w) = -Λ²·δ`, while
  `Σ X_u³(X_v-X_w) = -δ·ΣX` and `Σ X_u²(X_v-X_w) = -δ`; nothing but `ring` is involved.

* **`IsEllipticNet.netVieta_succ`** (⚠️ the whole certificate): `𝒱` is the **same for every
  triple** — concretely `𝒱(1, n, -1-n) = 𝒱(1, n-1, -n)` — and this is **one instance of Ward's
  `s ≠ 0` relation**, `rel a (n-1) (n-2) n 1 = 0`, together with the odd base relator
  `rel a n (n-1) 1 0 = 0`.  It factors: with `Λₘ := (S₁ - Sₘ)/(X₁ - Xₘ)`,

  ```
  Λₙ - Λₙ₋₁ = -2a_{2n}/(a_n²a_{n+1}a_{n-1}),     Λₙ + Λₙ₋₁ = 2a₂a_n²/(a_{n+1}a_{n-1}),
  ```

  whose product is `4(X_{n+1} - X_{n-1})`.

Given those, the crux is a two-line induction.  `τ₁ = τ₂ = τ₃ = 0` and the triple `(1, 2, -3)`
force `𝒱 = 0`; then `𝒱 = 0` at the triple `(1, n, -1-n)` with `τ₁ = τₙ = 0` gives
`τ_{n+1}·(X₁ - Xₙ) = 0`.  **Three base cases and no fourth**, which is exactly what the free model
of `#1440` measures: `τₙ` is a *fixed* quadratic `A·Xₙ² + B·Xₙ + C` in `Xₙ` — all the points
`(Xₙ, Sₙ)` lie on one cubic — and `𝒱 = -A`.

## ⚠️ What is and is not assumed

The net is **not** assumed to come from a curve.  `hτ₁`, the base case at `n = 1`, is exactly the
Weierstrass equation `a₂² = 4x³ + b₂x² + 2b₄x + b₆` in completed-square form, and it is the only
place a curve enters.  Nondegeneracy `a k ≠ 0` is a genuine hypothesis and not an artefact: at a
torsion point the coordinates `Xₙ` are undefined and the statement is vacuous there.

## Main statements

* `IsEllipticNet.netDefect_collinear` : the interpolation identity above.
* `IsEllipticNet.netVieta_succ` : `𝒱` is independent of the triple, from one Ward relator.
* `IsEllipticNet.netDefect_eq_zero` : the crux at every index in range, from `τ₁`, `τ₂`, `τ₃`.

## References

* M. Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).
* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.2 and Exercise 3.7.
-/

namespace IsEllipticNet

variable {F : Type*} [Field F] {a : ℤ → F} {x b₂ b₄ b₆ : F}

/-- **The division-polynomial `x`-coordinate of an elliptic net**, `Xₙ = x - a_{n+1}a_{n-1}/a_n²`.
For the division polynomials of a Weierstrass curve, evaluated at a point, this is `Φₙ/ΨSqₙ`. -/
def netX (a : ℤ → F) (x : F) (n : ℤ) : F :=
  x - a (n + 1) * a (n - 1) / a n ^ 2

/-- **The completed `y`-coordinate of an elliptic net**, `Sₙ = a_{2n}/a_n⁴`.  For the division
polynomials this is `ψ_{2n}/ΨSqₙ²`, the `2Y + a₁X + a₃` of the completed square. -/
def netS (a : ℤ → F) (n : ℤ) : F :=
  a (2 * n) / a n ^ 4

/-- **The Weierstrass defect at index `n`**, `τₙ = Sₙ² - (4Xₙ³ + b₂Xₙ² + 2b₄Xₙ + b₆)`.  Its
vanishing says the point `(Xₙ, Sₙ)` lies on the completed-square curve, and for the division
polynomials it is `#404`'s crux at `n`. -/
def netDefect (a : ℤ → F) (x b₂ b₄ b₆ : F) (n : ℤ) : F :=
  netS a n ^ 2 - (4 * netX a x n ^ 3 + b₂ * netX a x n ^ 2 + 2 * b₄ * netX a x n + b₆)

/-- **The Vieta defect of a triple**, `𝒱 = 4(X_u + X_v + X_w) + b₂ - Λ²` with
`Λ = (S_u - S_v)/(X_u - X_v)`.  Its vanishing is the second half of the Weierstrass group law: the
three collinear points are the *three* intersections of their line with the curve. -/
def netVieta (a : ℤ → F) (x b₂ : F) (u v w : ℤ) : F :=
  4 * (netX a x u + netX a x v + netX a x w) + b₂
    - ((netS a u - netS a v) / (netX a x u - netX a x v)) ^ 2

/-! ### Evenness and oddness in the index -/

/-- `X` is an even function of the index. -/
lemma netX_neg (hodd : Function.Odd a) (x : F) (n : ℤ) : netX a x (-n) = netX a x n := by
  rw [netX, netX, show -n + 1 = -(n - 1) from by ring, show -n - 1 = -(n + 1) from by ring,
    hodd, hodd, hodd, neg_mul_neg, neg_pow, mul_comm (a (n - 1))]
  norm_num

/-- `S` is an odd function of the index. -/
lemma netS_neg (hodd : Function.Odd a) (n : ℤ) : netS a (-n) = -netS a n := by
  rw [netS, netS, show 2 * -n = -(2 * n) from by ring, hodd, hodd]
  ring

/-- `τ` is an even function of the index. -/
lemma netDefect_neg (hodd : Function.Odd a) (x b₂ b₄ b₆ : F) (n : ℤ) :
    netDefect a x b₂ b₄ b₆ (-n) = netDefect a x b₂ b₄ b₆ n := by
  rw [netDefect, netDefect, netX_neg hodd, netS_neg hodd, neg_pow]
  norm_num

/-! ### The two Ward inputs, in net coordinates -/

/-- **The `x`-difference identity in net coordinates**, `X_p - X_q = -a_{p+q}a_{p-q}/(a_p²a_q²)`.
This is Ward's `r = 1` relator at the single pair `(p, q)`, divided through; see
`EllipticCurves.Torsion.XDifference`. -/
lemma netX_sub_netX (hnet : IsEllipticNet a) (h1 : a 1 = 1) (x : F) {p q : ℤ}
    (hp : a p ≠ 0) (hq : a q ≠ 0) :
    netX a x p - netX a x q = -(a (p + q) * a (p - q)) / (a p ^ 2 * a q ^ 2) := by
  have key := mul_sub_eq_of_rel_one h1 (hnet p q 1 0)
  rw [netX, netX]
  field_simp
  linear_combination key

/-- **The collinearity identity in net coordinates.**  For `u + v + w = 0` the three points
`(Xₙ, Sₙ)` are collinear.  This is `IsEllipticNet.cyclic_two_mul_eq_zero` divided through; see
`EllipticCurves.Torsion.Collinearity`. -/
lemma netS_collinear (hnet : IsEllipticNet a) (hodd : Function.Odd a) (h1 : a 1 = 1) (x : F)
    {u v w : ℤ} (huvw : u + v + w = 0) (hu : a u ≠ 0) (hv : a v ≠ 0) (hw : a w ≠ 0) :
    netS a u * (netX a x v - netX a x w) + netS a v * (netX a x w - netX a x u)
      + netS a w * (netX a x u - netX a x v) = 0 := by
  have e1 : netX a x v - netX a x w = a u * a (v - w) / (a v ^ 2 * a w ^ 2) := by
    rw [netX_sub_netX hnet h1 x hv hw, show v + w = -u from by omega, hodd]
    ring
  have e2 : netX a x w - netX a x u = a v * a (w - u) / (a w ^ 2 * a u ^ 2) := by
    rw [netX_sub_netX hnet h1 x hw hu, show w + u = -v from by omega, hodd]
    ring
  have e3 : netX a x u - netX a x v = a w * a (u - v) / (a u ^ 2 * a v ^ 2) := by
    rw [netX_sub_netX hnet h1 x hu hv, show u + v = -w from by omega, hodd]
    ring
  have key := cyclic_two_mul_eq_zero hodd hnet huvw
  rw [e1, e2, e3, netS, netS, netS]
  field_simp
  linear_combination key

/-- **The interpolation identity for three collinear points.**  With `s = Λx + M` on all three,
the cyclic sum of the Weierstrass defects is the Vieta defect times the Vandermonde product.  Pure
algebra: `Σ x_u³(x_v - x_w) = -δ·Σx`, `Σ x_u²(x_v - x_w) = -δ`, `Σ x_u(x_v - x_w) = 0`. -/
private lemma defect_sum_of_line {G : Type*} [CommRing G] (b₂ b₄ b₆ Λ M xu xv xw su sv sw : G)
    (hu : su = Λ * xu + M) (hv : sv = Λ * xv + M) (hw : sw = Λ * xw + M) :
    (su ^ 2 - (4 * xu ^ 3 + b₂ * xu ^ 2 + 2 * b₄ * xu + b₆)) * (xv - xw)
      + (sv ^ 2 - (4 * xv ^ 3 + b₂ * xv ^ 2 + 2 * b₄ * xv + b₆)) * (xw - xu)
      + (sw ^ 2 - (4 * xw ^ 3 + b₂ * xw ^ 2 + 2 * b₄ * xw + b₆)) * (xu - xv)
      = (4 * (xu + xv + xw) + b₂ - Λ ^ 2) * ((xu - xv) * (xv - xw) * (xw - xu)) := by
  subst hu
  subst hv
  subst hw
  ring

/-- **The interpolation identity, with the line recovered from collinearity.**  Over a field, at
three collinear points with `xu ≠ xv`, the slope is `(su - sv)/(xu - xv)` and the third point lies
on the same line, so `defect_sum_of_line` applies. -/
private lemma defect_sum_of_collinear {G : Type*} [Field G] (b₂ b₄ b₆ : G) {xu xv xw su sv sw : G}
    (hcol : su * (xv - xw) + sv * (xw - xu) + sw * (xu - xv) = 0) (hd : xu - xv ≠ 0) :
    (su ^ 2 - (4 * xu ^ 3 + b₂ * xu ^ 2 + 2 * b₄ * xu + b₆)) * (xv - xw)
      + (sv ^ 2 - (4 * xv ^ 3 + b₂ * xv ^ 2 + 2 * b₄ * xv + b₆)) * (xw - xu)
      + (sw ^ 2 - (4 * xw ^ 3 + b₂ * xw ^ 2 + 2 * b₄ * xw + b₆)) * (xu - xv)
      = (4 * (xu + xv + xw) + b₂ - ((su - sv) / (xu - xv)) ^ 2)
        * ((xu - xv) * (xv - xw) * (xw - xu)) := by
  refine defect_sum_of_line b₂ b₄ b₆ ((su - sv) / (xu - xv)) (su - (su - sv) / (xu - xv) * xu)
    xu xv xw su sv sw (by ring) ?_ ?_
  · field_simp
    ring
  · field_simp
    linear_combination hcol

/-- **The defect identity in net coordinates.**  For `u + v + w = 0`,

```
τ_u(X_v - X_w) + τ_v(X_w - X_u) + τ_w(X_u - X_v) = 𝒱(u,v,w)·(X_u-X_v)(X_v-X_w)(X_w-X_u).
```

⚠️ This is an identity, not a theorem about the crux: it holds whether or not any `τ` vanishes.
What it buys is that **`τ` propagates exactly when `𝒱` vanishes**. -/
lemma netDefect_collinear (hnet : IsEllipticNet a) (hodd : Function.Odd a) (h1 : a 1 = 1)
    {u v w : ℤ} (huvw : u + v + w = 0) (hu : a u ≠ 0) (hv : a v ≠ 0) (hw : a w ≠ 0)
    (hne : netX a x u ≠ netX a x v) :
    netDefect a x b₂ b₄ b₆ u * (netX a x v - netX a x w)
        + netDefect a x b₂ b₄ b₆ v * (netX a x w - netX a x u)
        + netDefect a x b₂ b₄ b₆ w * (netX a x u - netX a x v)
      = netVieta a x b₂ u v w
        * ((netX a x u - netX a x v) * (netX a x v - netX a x w) * (netX a x w - netX a x u)) := by
  simp only [netDefect, netVieta]
  exact defect_sum_of_collinear b₂ b₄ b₆ (netS_collinear hnet hodd h1 x huvw hu hv hw)
    (sub_ne_zero.mpr hne)

/-! ### ⚠️ The transfer: `𝒱` does not depend on the triple -/

/-- **The certificate.**  One instance of Ward's `s ≠ 0` relation, `rel a (n-1) (n-2) n 1 = 0`,
together with the odd base relator `rel a n (n-1) 1 0 = 0`, gives

```
(a_{2n} - a₂a_n⁴)·a_{n-1}a_{n-2} - (a_{2n-2} - a₂a_{n-1}⁴)·a_n a_{n+1} = 2a_{2n}a_{n-1}a_{n-2}.
```

The two brackets are the numerators of the slopes `Λₙ` and `Λₙ₋₁`, so this is the difference of
slopes; the *sum* of slopes is the same identity read the other way, because the sum of the two
sides of the bracket difference is `2(a_{2n} - a₂a_n⁴)a_{n-1}a_{n-2}` by `ring`.

⚠️ **This is the whole of `#1440`.**  No multiplier, no monomial enumeration: the missing step is
a step on the Vieta defect, not on the crux, and at that level it is a single relator instance. -/
private lemma transfer_key (hnet : IsEllipticNet a) (hodd : Function.Odd a) (h1 : a 1 = 1)
    (n : ℤ) :
    (a (2 * n) - a 2 * a n ^ 4) * (a (n - 1) * a (n - 2))
        - (a (2 * n - 2) - a 2 * a (n - 1) ^ 4) * (a n * a (n + 1))
      = 2 * a (2 * n) * a (n - 1) * a (n - 2) := by
  have hm1 : a (-1) = -1 := by rw [hodd 1, h1]
  have hm2 : a (-2) = -a 2 := hodd 2
  have r1 := hnet (n - 1) (n - 2) n 1
  have r2 := hnet n (n - 1) 1 0
  simp only [rel] at r1 r2
  rw [show n - 1 + (n - 2) + 1 = 2 * n - 2 from by ring,
    show n - 1 - (n - 2) = (1 : ℤ) from by ring, show n - 1 + n + 1 = 2 * n from by ring,
    show n - 1 - n = (-1 : ℤ) from by ring, show n - 2 + 1 = n - 1 from by ring,
    show n - 2 + n + 1 = 2 * n - 1 from by ring, show n - 2 - n = (-2 : ℤ) from by ring,
    show n - 1 + 1 = n from by ring, h1, hm1, hm2] at r1
  rw [show n + (n - 1) + 0 = 2 * n - 1 from by ring, show n - (n - 1) = (1 : ℤ) from by ring,
    show (1 : ℤ) + 0 = 1 from by ring, show n + 1 + 0 = n + 1 from by ring,
    show n - 1 + 0 = n - 1 from by ring, show n - 1 + 1 + 0 = n from by ring,
    show n - 1 - 1 = n - 2 from by ring, show n + 0 = n from by ring, h1] at r2
  linear_combination -r1 - a 2 * a n * a (n - 1) * r2

/-- The slope of the line through `(X₁, S₁)` and `(Xₘ, Sₘ)`, in net values. -/
private lemma netSlope_eq (hnet : IsEllipticNet a) (hodd : Function.Odd a) (h1 : a 1 = 1) (x : F)
    {m : ℤ} (hm : a m ≠ 0) (hp : a (m + 1) ≠ 0) (hq : a (m - 1) ≠ 0) :
    (netS a 1 - netS a m) / (netX a x 1 - netX a x m)
      = (a 2 * a m ^ 4 - a (2 * m)) / (a m ^ 2 * (a (m + 1) * a (m - 1))) := by
  have ha1 : a 1 ≠ 0 := by rw [h1]; exact one_ne_zero
  have hx : netX a x 1 - netX a x m = a (m + 1) * a (m - 1) / a m ^ 2 := by
    rw [netX_sub_netX hnet h1 x ha1 hm, show (1 : ℤ) + m = m + 1 from by ring,
      show (1 : ℤ) - m = -(m - 1) from by ring, hodd, h1]
    ring
  have hs : netS a 1 = a 2 := by
    rw [netS, show 2 * (1 : ℤ) = 2 from by ring, h1]
    norm_num
  rw [hx, hs, netS]
  field_simp

/-- `p² - q²` from the difference and the sum. -/
private lemma sq_sub_sq_of {G : Type*} [CommRing G] {p q d s : G} (hd : p - q = d)
    (hs : p + q = s) : p ^ 2 - q ^ 2 = d * s := by
  rw [← hd, ← hs]; ring

/-- **⚠️ THE STEP.**  The Vieta defect at the triple `(1, n, -1-n)` equals the one at
`(1, n-1, -n)`: `𝒱` does not depend on the triple.  Everything comes from
`IsEllipticNet.transfer_key`, one instance of Ward's `s ≠ 0` relation, through the two slope
identities

```
Λₙ - Λₙ₋₁ = -2a_{2n}/(a_n²a_{n+1}a_{n-1}),      Λₙ + Λₙ₋₁ = 2a₂a_n²/(a_{n+1}a_{n-1}),
```

whose product is `4(X_{n+1} - X_{n-1})`, which is the difference of the two `4·ΣX` terms. -/
lemma netVieta_succ (hnet : IsEllipticNet a) (hodd : Function.Odd a) (h1 : a 1 = 1) (x b₂ : F)
    {n : ℤ} (hm2 : a (n - 2) ≠ 0) (hm1 : a (n - 1) ≠ 0) (hn : a n ≠ 0) (hp1 : a (n + 1) ≠ 0) :
    netVieta a x b₂ 1 n (-1 - n) = netVieta a x b₂ 1 (n - 1) (-1 - (n - 1)) := by
  rw [show (-1 : ℤ) - (n - 1) = -n from by ring]
  have key := transfer_key hnet hodd h1 n
  have hsn := netSlope_eq hnet hodd h1 x hn hp1 hm1
  have hsn1 := netSlope_eq hnet hodd h1 x hm1
    (by rwa [show n - 1 + 1 = n from by ring]) (by rwa [show n - 1 - 1 = n - 2 from by ring])
  rw [show n - 1 + 1 = n from by ring, show n - 1 - 1 = n - 2 from by ring,
    show 2 * (n - 1) = 2 * n - 2 from by ring] at hsn1
  have hdx := netX_sub_netX hnet h1 x hp1 hm1
  rw [show n + 1 + (n - 1) = 2 * n from by ring,
    show n + 1 - (n - 1) = (2 : ℤ) from by ring] at hdx
  have hdiff : (a 2 * a n ^ 4 - a (2 * n)) / (a n ^ 2 * (a (n + 1) * a (n - 1)))
      - (a 2 * a (n - 1) ^ 4 - a (2 * n - 2)) / (a (n - 1) ^ 2 * (a n * a (n - 2)))
      = -(2 * a (2 * n)) / (a n ^ 2 * (a (n + 1) * a (n - 1))) := by
    field_simp
    linear_combination -key
  have hsum : (a 2 * a n ^ 4 - a (2 * n)) / (a n ^ 2 * (a (n + 1) * a (n - 1)))
      + (a 2 * a (n - 1) ^ 4 - a (2 * n - 2)) / (a (n - 1) ^ 2 * (a n * a (n - 2)))
      = 2 * a 2 * a n ^ 2 / (a (n + 1) * a (n - 1)) := by
    field_simp
    linear_combination key
  have main : 4 * (netX a x (n + 1) - netX a x (n - 1))
      = ((a 2 * a n ^ 4 - a (2 * n)) / (a n ^ 2 * (a (n + 1) * a (n - 1)))) ^ 2
        - ((a 2 * a (n - 1) ^ 4 - a (2 * n - 2)) / (a (n - 1) ^ 2 * (a n * a (n - 2)))) ^ 2 := by
    rw [sq_sub_sq_of hdiff hsum, hdx]
    field_simp
    ring
  rw [netVieta, netVieta, hsn, hsn1, show (-1 : ℤ) - n = -(n + 1) from by ring,
    netX_neg hodd, netX_neg hodd]
  linear_combination main

/-! ### The induction -/

/-- Two net `x`-coordinates are distinct as soon as the two division-polynomial values that
`IsEllipticNet.netX_sub_netX` puts in the numerator are nonzero. -/
private lemma netX_sub_ne_zero (hnet : IsEllipticNet a) (h1 : a 1 = 1) (x : F) {p q : ℤ}
    (hp : a p ≠ 0) (hq : a q ≠ 0) (hs : a (p + q) ≠ 0) (hd : a (p - q) ≠ 0) :
    netX a x p - netX a x q ≠ 0 := by
  rw [netX_sub_netX hnet h1 x hp hq]
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hs hd))
    (mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ hq))

/-- **The Vieta relation holds at the triple `(1, 2, -3)`**, from the three base cases.  This is
where `τ₃` is spent, and it is spent once. -/
private lemma netVieta_two_eq_zero (hnet : IsEllipticNet a) (hodd : Function.Odd a) (h1 : a 1 = 1)
    (hτ1 : netDefect a x b₂ b₄ b₆ 1 = 0) (hτ2 : netDefect a x b₂ b₄ b₆ 2 = 0)
    (hτ3 : netDefect a x b₂ b₄ b₆ 3 = 0) (h2 : a 2 ≠ 0) (h3 : a 3 ≠ 0) (h4 : a 4 ≠ 0)
    (h5 : a 5 ≠ 0) : netVieta a x b₂ 1 2 (-1 - 2) = 0 := by
  have ha1 : a 1 ≠ 0 := by rw [h1]; exact one_ne_zero
  have ham1 : a (-1) ≠ 0 := by rw [hodd 1, h1]; norm_num
  have ham3 : a (-1 - 2) ≠ 0 := by
    rw [show (-1 : ℤ) - 2 = -3 from by norm_num, hodd]
    simpa using h3
  have e12 : netX a x 1 - netX a x 2 ≠ 0 :=
    netX_sub_ne_zero hnet h1 x ha1 h2 (by rw [show (1 : ℤ) + 2 = 3 from by norm_num]; exact h3)
      (by rw [show (1 : ℤ) - 2 = -1 from by norm_num]; exact ham1)
  have e23 : netX a x 2 - netX a x (-1 - 2) ≠ 0 :=
    netX_sub_ne_zero hnet h1 x h2 ham3
      (by rw [show (2 : ℤ) + (-1 - 2) = -1 from by norm_num]; exact ham1)
      (by rw [show (2 : ℤ) - (-1 - 2) = 5 from by norm_num]; exact h5)
  have e31 : netX a x (-1 - 2) - netX a x 1 ≠ 0 :=
    netX_sub_ne_zero hnet h1 x ham3 ha1
      (by rw [show (-1 - 2 : ℤ) + 1 = -2 from by norm_num, hodd]; simpa using h2)
      (by rw [show (-1 - 2 : ℤ) - 1 = -4 from by norm_num, hodd]; simpa using h4)
  have hcol := netDefect_collinear (b₂ := b₂) (b₄ := b₄) (b₆ := b₆) hnet hodd h1
    (by norm_num : (1 : ℤ) + 2 + (-1 - 2) = 0) ha1 h2 ham3 (sub_ne_zero.mp e12)
  rw [hτ1, hτ2, show (-1 : ℤ) - 2 = -3 from by norm_num, netDefect_neg hodd, hτ3] at hcol
  have hδ : (netX a x 1 - netX a x 2) * (netX a x 2 - netX a x (-3))
      * (netX a x (-3) - netX a x 1) ≠ 0 := by
    rw [show (-3 : ℤ) = -1 - 2 from by norm_num]
    exact mul_ne_zero (mul_ne_zero e12 e23) e31
  rw [show (-1 : ℤ) - 2 = -3 from by norm_num]
  have := hcol.symm
  simp only [zero_mul, add_zero] at this
  exact (mul_eq_zero.mp this).resolve_right hδ

/-- **The Vieta relation at every triple `(1, n, -1-n)`**, by transfer from `(1, 2, -3)`. -/
private lemma netVieta_one_eq_zero (hnet : IsEllipticNet a) (hodd : Function.Odd a) (h1 : a 1 = 1)
    (hτ1 : netDefect a x b₂ b₄ b₆ 1 = 0) (hτ2 : netDefect a x b₂ b₄ b₆ 2 = 0)
    (hτ3 : netDefect a x b₂ b₄ b₆ 3 = 0) {N : ℤ} (hN : 5 ≤ N)
    (hne : ∀ k : ℤ, 1 ≤ k → k ≤ N → a k ≠ 0) :
    ∀ n : ℤ, 2 ≤ n → n + 2 ≤ N → netVieta a x b₂ 1 n (-1 - n) = 0 := by
  refine Int.leInduction (fun _ => ?_) ?_
  · exact netVieta_two_eq_zero hnet hodd h1 hτ1 hτ2 hτ3 (hne 2 (by norm_num) (by omega))
      (hne 3 (by norm_num) (by omega)) (hne 4 (by norm_num) (by omega))
      (hne 5 (by norm_num) (by omega))
  · intro n hn ih hb
    have hsucc := netVieta_succ hnet hodd h1 x b₂ (n := n + 1)
      (by rw [show n + 1 - 2 = n - 1 from by ring]; exact hne (n - 1) (by omega) (by omega))
      (by rw [show n + 1 - 1 = n from by ring]; exact hne n (by omega) (by omega))
      (hne (n + 1) (by omega) (by omega)) (hne (n + 1 + 1) (by omega) (by omega))
    rw [hsucc, show n + 1 - 1 = n from by ring]
    exact ih (by omega)

/-- **⚠️ `#404`'s CRUX, for an abstract elliptic net.**  If the Weierstrass defect vanishes at
`n = 1, 2, 3` then it vanishes at every index in the range where the net is nonzero.

`n = 1` is the Weierstrass equation `a₂² = 4x³ + b₂x² + 2b₄x + b₆` — the only place a curve enters
— and `n = 2, 3` are the two classical duplication and triplication identities.  There is no fourth
base case, and that is a consequence of the structure rather than an accident: the points
`(Xₙ, Sₙ)` all lie on one cubic `S² = 4X³ + αX² + βX + γ`, so `τₙ` is a *fixed* quadratic in `Xₙ`,
and three vanishing values at three distinct `Xₙ` kill it.

⚠️ The range hypothesis is real.  `hne` is nondegeneracy of the net up to `N`; at a torsion point
of a curve it fails and the conclusion is genuinely unavailable there. -/
theorem netDefect_eq_zero (hnet : IsEllipticNet a) (hodd : Function.Odd a) (h1 : a 1 = 1)
    (hτ1 : netDefect a x b₂ b₄ b₆ 1 = 0) (hτ2 : netDefect a x b₂ b₄ b₆ 2 = 0)
    (hτ3 : netDefect a x b₂ b₄ b₆ 3 = 0) {N : ℤ} (hN : 5 ≤ N)
    (hne : ∀ k : ℤ, 1 ≤ k → k ≤ N → a k ≠ 0) {n : ℤ} (hn : 1 ≤ n) (hnN : n + 2 ≤ N) :
    netDefect a x b₂ b₄ b₆ n = 0 := by
  have ha1 : a 1 ≠ 0 := by rw [h1]; exact one_ne_zero
  have main : ∀ m : ℤ, 2 ≤ m → m + 2 ≤ N → netDefect a x b₂ b₄ b₆ m = 0 := by
    refine Int.leInduction (fun _ => hτ2) ?_
    intro m hm ih hb
    have hV := netVieta_one_eq_zero hnet hodd h1 hτ1 hτ2 hτ3 hN hne m hm (by omega)
    have ham : a (-1 - m) ≠ 0 := by
      rw [show (-1 : ℤ) - m = -(m + 1) from by ring, hodd]
      simpa using hne (m + 1) (by omega) (by omega)
    have hx : netX a x 1 - netX a x m ≠ 0 :=
      netX_sub_ne_zero hnet h1 x ha1 (hne m (by omega) (by omega))
        (by rw [show (1 : ℤ) + m = m + 1 from by ring]; exact hne (m + 1) (by omega) (by omega))
        (by
          rw [show (1 : ℤ) - m = -(m - 1) from by ring, hodd]
          simpa using hne (m - 1) (by omega) (by omega))
    have hcol := netDefect_collinear (b₂ := b₂) (b₄ := b₄) (b₆ := b₆) hnet hodd h1
      (show (1 : ℤ) + m + (-1 - m) = 0 from by ring) ha1 (hne m (by omega) (by omega)) ham
      (sub_ne_zero.mp hx)
    rw [hτ1, ih (by omega), hV, show (-1 : ℤ) - m = -(m + 1) from by ring,
      netDefect_neg hodd] at hcol
    simp only [zero_mul, zero_add, add_zero] at hcol
    exact (mul_eq_zero.mp hcol).resolve_right hx
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h]; exact hτ1
  · exact main n (by omega) hnN

end IsEllipticNet
