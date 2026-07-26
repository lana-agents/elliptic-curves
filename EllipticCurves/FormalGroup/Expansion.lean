/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The Weierstrass formal expansion `w(z)` near the origin

Given a Weierstrass curve `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆`, substituting the local
parameter `z = -x/y` (so `x = z/w`, `y = -1/w`) into the Weierstrass equation yields the
fixed-point equation (Silverman, *The Arithmetic of Elliptic Curves*, IV.1.1)
$$ w = z^3 + (a_1 z + a_2 z^2) w + (a_3 + a_4 z) w^2 + a_6 w^3. $$
This file constructs the unique power series `w ∈ R⟦z⟧` solving this equation, as the
`z`-adic limit of the iteration `wₙ₊₁ = T(wₙ)` starting from `w₀ = 0`, where `T` is the
order-increasing operator on the right-hand side.

## Main definitions

* `WeierstrassCurve.wOp` : the operator `T` on `R⟦X⟧`.
* `WeierstrassCurve.wIter` : the sequence of approximations `w₀ = 0`, `wₙ₊₁ = T(wₙ)`.
* `WeierstrassCurve.formalW` : the Weierstrass expansion `w(z) ∈ R⟦X⟧`.
* `WeierstrassCurve.formalWUnit` : the unit part `v(z)` of `w`, i.e. `w = z³ · v` with `v(0) = 1`.
* `WeierstrassCurve.formalX`, `WeierstrassCurve.formalY` : the "cleared" coordinate series
  `z² · x(z)` and `z³ · y(z)`, power series representing the Laurent expansions of `x(z) = z / w`
  and `y(z) = -1 / w` at the origin.

## Main results

* `WeierstrassCurve.formalW_eq` : `w` satisfies the fixed-point / functional equation.
* `WeierstrassCurve.order_formalW` : `3 ≤ order w`, i.e. `w = c₃ z³ + …`.
* `WeierstrassCurve.coeff_formalW_three` : the leading coefficient is `1`, so `w = z³ + …`.
* `WeierstrassCurve.formalW_mul_formalX` : `w · (z²·x) = z³` and
  `WeierstrassCurve.formalW_mul_formalY` : `w · (z³·y) = -z³`, the identities `x·w = z`,
  `y·w = -1` cleared of denominators. Together with `constantCoeff_formalX = 1` and
  `constantCoeff_formalY = -1` these say `x(z) = z⁻² + …` (a pole of order `2`) and
  `y(z) = -z⁻³ + …` (a pole of order `3`).

## Coordinate series

Since `w` has order `3` with leading coefficient `1`, it factors as `w = z³ · v` where the unit
part `v = formalWUnit` is a power series with `v(0) = 1`, hence invertible. The coordinate series
`x(z) = z / w` and `y(z) = -1 / w` are Laurent series with poles at the origin (of orders `2` and
`3`). Rather than leaving `PowerSeries R`, we record their "cleared" forms
`formalX = z² · x(z) = v⁻¹` and `formalY = z³ · y(z) = -v⁻¹`, which are honest power series, and the
polynomial identities `w · formalX = z³`, `w · formalY = -z³` characterising them. This suffices as
the input to the Weierstrass formal group law (parent issue #240).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

namespace WeierstrassCurve

open PowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The operator `T u = z³ + (a₁z + a₂z²) u + (a₃ + a₄z) u² + a₆ u³` whose unique
positive-order fixed point is the Weierstrass expansion `w(z)`. -/
noncomputable def wOp (u : R⟦X⟧) : R⟦X⟧ :=
  X ^ 3 + (C W.a₁ * X + C W.a₂ * X ^ 2) * u
    + (C W.a₃ + C W.a₄ * X) * u ^ 2 + C W.a₆ * u ^ 3

/-- The sequence of approximations to `w(z)`: `w₀ = 0`, `wₙ₊₁ = T(wₙ)`. -/
noncomputable def wIter (W : WeierstrassCurve R) : ℕ → R⟦X⟧
  | 0 => 0
  | (n + 1) => W.wOp (W.wIter n)

@[simp] lemma wIter_zero : W.wIter 0 = 0 := rfl

@[simp] lemma wIter_succ (n : ℕ) : W.wIter (n + 1) = W.wOp (W.wIter n) := rfl

/-- A three-term sum has order at least `k` if each summand does. -/
private lemma order_add₃_ge {a b c : R⟦X⟧} {k : ℕ∞}
    (ha : k ≤ a.order) (hb : k ≤ b.order) (hc : k ≤ c.order) : k ≤ (a + b + c).order :=
  le_trans (le_min (le_min ha hb) hc)
    (le_trans (min_le_min (min_order_le_order_add a b) le_rfl)
      (min_order_le_order_add (a + b) c))

/-- A four-term sum has order at least `k` if each summand does. -/
private lemma order_add₄_ge {a b c d : R⟦X⟧} {k : ℕ∞}
    (ha : k ≤ a.order) (hb : k ≤ b.order) (hc : k ≤ c.order) (hd : k ≤ d.order) :
    k ≤ (a + b + c + d).order :=
  le_trans (le_min (order_add₃_ge ha hb hc) hd) (min_order_le_order_add (a + b + c) d)

/-- The constant coefficient of `P₁ = a₁z + a₂z²` is zero, so `1 ≤ order P₁`. -/
private lemma one_le_order_P₁ : 1 ≤ (C W.a₁ * X + C W.a₂ * X ^ 2 : R⟦X⟧).order := by
  rw [one_le_order_iff_constCoeff_eq_zero]
  simp

private lemma one_le_order_of_constCoeff_zero {φ : R⟦X⟧} (h : constantCoeff φ = 0) :
    1 ≤ φ.order :=
  one_le_order_iff_constCoeff_eq_zero.mpr h

private lemma constCoeff_eq_zero_of_one_le_order {φ : R⟦X⟧} (h : 1 ≤ φ.order) :
    constantCoeff φ = 0 :=
  one_le_order_iff_constCoeff_eq_zero.mp h

/-- If the right factor has order at least `k`, so does the product. -/
private lemma le_order_mul_right {a b : R⟦X⟧} {k : ℕ∞} (hb : k ≤ b.order) :
    k ≤ (a * b).order :=
  hb.trans (le_add_self.trans (le_order_mul a b))

/-- The key contraction estimate: applying `T` increases the order of agreement by one.
If `u, v` have positive order and agree up to order `m`, then `T u, T v` agree up to
order `m + 1`. -/
lemma order_wOp_sub (u v : R⟦X⟧) (hu : 1 ≤ u.order) (hv : 1 ≤ v.order) {m : ℕ}
    (hm : (m : ℕ∞) ≤ (u - v).order) : (m : ℕ∞) + 1 ≤ (W.wOp u - W.wOp v).order := by
  have hcu : constantCoeff u = 0 := constCoeff_eq_zero_of_one_le_order hu
  have hcv : constantCoeff v = 0 := constCoeff_eq_zero_of_one_le_order hv
  -- factor the difference
  have hfac : W.wOp u - W.wOp v =
      (C W.a₁ * X + C W.a₂ * X ^ 2) * (u - v)
        + (C W.a₃ + C W.a₄ * X) * ((u + v) * (u - v))
        + C W.a₆ * ((u ^ 2 + u * v + v ^ 2) * (u - v)) := by
    simp only [wOp]; ring
  rw [hfac]
  -- order of `u + v` and `u² + uv + v²` are at least 1
  have huv : (1 : ℕ∞) ≤ (u + v).order := by
    refine one_le_order_of_constCoeff_zero ?_
    simp [hcu, hcv]
  have huv2 : (1 : ℕ∞) ≤ (u ^ 2 + u * v + v ^ 2).order := by
    refine one_le_order_of_constCoeff_zero ?_
    simp [hcu, hcv]
  refine order_add₃_ge ?_ ?_ ?_
  · -- term 1: order ≥ order P₁ + order (u - v) ≥ 1 + m
    calc (m : ℕ∞) + 1 = 1 + m := by rw [add_comm]
      _ ≤ (C W.a₁ * X + C W.a₂ * X ^ 2).order + (u - v).order :=
          add_le_add W.one_le_order_P₁ hm
      _ ≤ _ := le_order_mul _ _
  · -- term 2: order ≥ 0 + (order (u + v) + order (u - v)) ≥ 1 + m
    calc (m : ℕ∞) + 1 = 0 + (1 + m) := by rw [zero_add, add_comm]
      _ ≤ (C W.a₃ + C W.a₄ * X).order + ((u + v).order + (u - v).order) :=
          add_le_add (zero_le) (add_le_add huv hm)
      _ ≤ (C W.a₃ + C W.a₄ * X).order + ((u + v) * (u - v)).order :=
          add_le_add le_rfl (le_order_mul _ _)
      _ ≤ _ := le_order_mul _ _
  · -- term 3: order ≥ 0 + (order (u²+uv+v²) + order (u - v)) ≥ 1 + m
    calc (m : ℕ∞) + 1 = 0 + (1 + m) := by rw [zero_add, add_comm]
      _ ≤ (C W.a₆).order + ((u ^ 2 + u * v + v ^ 2).order + (u - v).order) :=
          add_le_add (zero_le) (add_le_add huv2 hm)
      _ ≤ (C W.a₆).order + ((u ^ 2 + u * v + v ^ 2) * (u - v)).order :=
          add_le_add le_rfl (le_order_mul _ _)
      _ ≤ _ := le_order_mul _ _

/-- Each approximation `wₙ` has order at least `3` (its expansion starts at `z³`). -/
lemma order_three_le_wIter (n : ℕ) : (3 : ℕ∞) ≤ (W.wIter n).order := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [wIter_succ, wOp]
    have hX3 : (3 : ℕ∞) ≤ ((X : R⟦X⟧) ^ 3).order :=
      nat_le_order _ 3 (fun i hi => by simp only [coeff_X_pow]; rw [if_neg (by omega)])
    refine order_add₄_ge hX3 ?_ ?_ ?_
    · -- (a₁z + a₂z²) · wₙ
      exact le_order_mul_right ih
    · -- (a₃ + a₄z) · wₙ²
      have h2 : (W.wIter n) ^ 2 = W.wIter n * W.wIter n := by ring
      rw [h2]
      exact le_order_mul_right (le_order_mul_right ih)
    · -- a₆ · wₙ³
      have h3 : (W.wIter n) ^ 3 = W.wIter n * W.wIter n * W.wIter n := by ring
      rw [h3]
      exact le_order_mul_right (le_order_mul_right ih)

private lemma one_le_order_wIter (n : ℕ) : (1 : ℕ∞) ≤ (W.wIter n).order :=
  le_trans (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3)) (W.order_three_le_wIter n)

/-- The iteration is `z`-adically Cauchy: `wₙ` and `wₙ₊₁` agree up to order `n`. This is the
contraction property, iterated from `w₀ = 0`. -/
lemma order_wIter_sub_succ (n : ℕ) : (n : ℕ∞) ≤ (W.wIter n - W.wIter (n + 1)).order := by
  induction n with
  | zero => exact zero_le
  | succ n ih =>
    have key := W.order_wOp_sub (W.wIter n) (W.wIter (n + 1))
      (W.one_le_order_wIter n) (W.one_le_order_wIter (n + 1)) ih
    rw [Nat.cast_succ]
    exact key

/-- The coefficients of the iterates stabilise: for `k ≥ n + 1`, the `n`-th coefficient of `wₖ`
no longer changes. -/
lemma coeff_wIter_stable {n k : ℕ} (hk : n + 1 ≤ k) :
    coeff n (W.wIter k) = coeff n (W.wIter (n + 1)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge (n + 1) (k + 1) with h | h
    · have hnk : n + 1 ≤ k := by omega
      have hlt : (n : ℕ∞) < (W.wIter k - W.wIter (k + 1)).order :=
        lt_of_lt_of_le (by exact_mod_cast (show n < k by omega)) (W.order_wIter_sub_succ k)
      have hz : coeff n (W.wIter k - W.wIter (k + 1)) = 0 := coeff_of_lt_order n hlt
      rw [map_sub, sub_eq_zero] at hz
      rw [← hz]; exact ih hnk
    · have hkn : k = n := by omega
      subst hkn; rfl

/-- The Weierstrass expansion `w(z) ∈ R⟦z⟧`, the unique power series of order `≥ 3` solving the
functional equation `w = z³ + (a₁z + a₂z²)w + (a₃ + a₄z)w² + a₆w³`. It is realised as the
`z`-adic limit of the iterates `wₙ`. -/
noncomputable def formalW (W : WeierstrassCurve R) : R⟦X⟧ :=
  PowerSeries.mk fun n => coeff n (W.wIter (n + 1))

lemma coeff_formalW (n : ℕ) : coeff n W.formalW = coeff n (W.wIter (n + 1)) := by
  rw [formalW, coeff_mk]

/-- The `n`-th coefficient of `w` agrees with that of every sufficiently advanced iterate. -/
lemma coeff_formalW_eq_wIter {n k : ℕ} (hk : n + 1 ≤ k) :
    coeff n W.formalW = coeff n (W.wIter k) := by
  rw [coeff_formalW, ← W.coeff_wIter_stable hk]

/-- The expansion has order at least `3`: `w = c₃ z³ + …`. -/
lemma order_formalW : (3 : ℕ∞) ≤ W.formalW.order := by
  refine nat_le_order _ 3 (fun i hi => ?_)
  rw [coeff_formalW]
  exact coeff_of_lt_order i
    (lt_of_lt_of_le (by exact_mod_cast hi) (W.order_three_le_wIter (i + 1)))

private lemma one_le_order_formalW : (1 : ℕ∞) ≤ W.formalW.order :=
  le_trans (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3)) W.order_formalW

/-- **The Weierstrass functional equation.** The expansion `w` is a fixed point of the operator
`T`, i.e. `w = z³ + (a₁z + a₂z²)w + (a₃ + a₄z)w² + a₆w³`. -/
theorem formalW_eq : W.formalW = W.wOp W.formalW := by
  ext n
  have hm : (n : ℕ∞) ≤ (W.formalW - W.wIter n).order := by
    refine nat_le_order _ n (fun i hi => ?_)
    rw [map_sub, sub_eq_zero, coeff_formalW, W.coeff_wIter_stable (show i + 1 ≤ n by omega)]
  have key := W.order_wOp_sub W.formalW (W.wIter n) W.one_le_order_formalW
    (W.one_le_order_wIter n) hm
  have key' : ((n + 1 : ℕ) : ℕ∞) ≤ (W.wOp W.formalW - W.wOp (W.wIter n)).order := by
    rw [Nat.cast_succ]; exact key
  have hz : coeff n (W.wOp W.formalW - W.wOp (W.wIter n)) = 0 :=
    coeff_of_lt_order n (lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self n)) key')
  rw [map_sub, sub_eq_zero] at hz
  rw [hz, ← wIter_succ, coeff_formalW]

/-- If the sum of two orders exceeds `n`, the `n`-th coefficient of the product vanishes. -/
private lemma coeff_mul_eq_zero_of_lt {a b : R⟦X⟧} {n : ℕ}
    (h : (n : ℕ∞) < a.order + b.order) : coeff n (a * b) = 0 :=
  coeff_of_lt_order n (lt_of_lt_of_le h (le_order_mul a b))

/-- The leading coefficient of the expansion is `1`: `w = z³ + a₁z⁴ + …`. Combined with
`order_formalW`, this shows `w` has order exactly `3`. -/
theorem coeff_formalW_three : coeff 3 W.formalW = 1 := by
  have hP1 : coeff 3 ((C W.a₁ * X + C W.a₂ * X ^ 2) * W.formalW) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (3 : ℕ) < 1 + 3))
      (add_le_add W.one_le_order_P₁ W.order_formalW))
  have hP2 : coeff 3 ((C W.a₃ + C W.a₄ * X) * (W.formalW * W.formalW)) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (3 : ℕ) < 0 + (3 + 3)))
      (add_le_add zero_le
        (le_trans (add_le_add W.order_formalW W.order_formalW) (le_order_mul _ _))))
  have hP3 : coeff 3 (C W.a₆ * (W.formalW * W.formalW * W.formalW)) = 0 :=
    coeff_mul_eq_zero_of_lt (lt_of_lt_of_le
      (by exact_mod_cast (by norm_num : (3 : ℕ) < 0 + ((3 + 3) + 3)))
      (add_le_add zero_le
        (le_trans (add_le_add (le_trans (add_le_add W.order_formalW W.order_formalW)
          (le_order_mul _ _)) W.order_formalW) (le_order_mul _ _))))
  have hX : coeff 3 ((X : R⟦X⟧) ^ 3) = 1 := by rw [coeff_X_pow]; simp
  rw [formalW_eq, wOp,
    show W.formalW ^ 2 = W.formalW * W.formalW from by ring,
    show W.formalW ^ 3 = W.formalW * W.formalW * W.formalW from by ring]
  simp only [map_add]
  rw [hX, hP1, hP2, hP3]
  ring

/-! ### The coordinate series `x(z)` and `y(z)` -/

section Coordinate

/-- The unit part `v(z)` of the Weierstrass expansion: the power series with
`coeff n v = coeff (n + 3) w`, so that `w = z³ · v`. Since `w` has order `3` with leading
coefficient `1`, `v` has constant coefficient `1` and is therefore a unit. -/
noncomputable def formalWUnit (W : WeierstrassCurve R) : R⟦X⟧ :=
  PowerSeries.mk fun n => coeff (n + 3) W.formalW

/-- The unit part `v` recovers `w` after multiplying by `z³`: `w = z³ · v`. -/
lemma X_pow_three_mul_formalWUnit : (X : R⟦X⟧) ^ 3 * W.formalWUnit = W.formalW := by
  ext n
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [formalWUnit, PowerSeries.coeff_mk, Nat.sub_add_cancel h]
  · refine (coeff_of_lt_order n (lt_of_lt_of_le ?_ W.order_formalW)).symm
    exact_mod_cast (show n < 3 by omega)

/-- The constant coefficient of the unit part is `1`. -/
@[simp] lemma constantCoeff_formalWUnit : constantCoeff W.formalWUnit = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, formalWUnit, PowerSeries.coeff_mk]
  simpa using W.coeff_formalW_three

/-- The unit part `v` of `w` is a unit in `R⟦X⟧`. -/
lemma isUnit_formalWUnit : IsUnit W.formalWUnit :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_formalWUnit]; exact isUnit_one)

/-- The cleared `x`-coordinate series `z² · x(z) = v(z)⁻¹`, an honest power series whose Laurent
counterpart `x(z) = formalX / z²` is the expansion of `x = z / w` at the origin (a pole of order
`2`). -/
noncomputable def formalX (W : WeierstrassCurve R) : R⟦X⟧ :=
  Ring.inverse W.formalWUnit

/-- The cleared `y`-coordinate series `z³ · y(z) = -v(z)⁻¹`, an honest power series whose Laurent
counterpart `y(z) = formalY / z³` is the expansion of `y = -1 / w` at the origin (a pole of order
`3`). -/
noncomputable def formalY (W : WeierstrassCurve R) : R⟦X⟧ :=
  -W.formalX

lemma formalWUnit_mul_formalX : W.formalWUnit * W.formalX = 1 :=
  Ring.mul_inverse_cancel _ W.isUnit_formalWUnit

/-- The cleared identity `x · w = z`: as power series, `w · (z²·x) = z³`. -/
lemma formalW_mul_formalX : W.formalW * W.formalX = X ^ 3 := by
  rw [← W.X_pow_three_mul_formalWUnit, mul_assoc, W.formalWUnit_mul_formalX, mul_one]

/-- The cleared identity `y · w = -1`: as power series, `w · (z³·y) = -z³`. -/
lemma formalW_mul_formalY : W.formalW * W.formalY = -X ^ 3 := by
  rw [formalY, mul_neg, formalW_mul_formalX]

/-- The leading coefficient of `x(z)` is `1`: `x(z) = z⁻² + …`. -/
@[simp] lemma constantCoeff_formalX : constantCoeff W.formalX = 1 := by
  have h := congrArg constantCoeff W.formalWUnit_mul_formalX
  rwa [map_mul, constantCoeff_formalWUnit, one_mul, map_one] at h

/-- The leading coefficient of `y(z)` is `-1`: `y(z) = -z⁻³ + …`. -/
@[simp] lemma constantCoeff_formalY : constantCoeff W.formalY = -1 := by
  rw [formalY, map_neg, constantCoeff_formalX]

end Coordinate

end WeierstrassCurve
