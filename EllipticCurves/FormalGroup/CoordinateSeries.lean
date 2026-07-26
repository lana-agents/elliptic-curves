/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.LaurentSeries
import EllipticCurves.FormalGroup.Expansion

/-!
# The coordinate Laurent series `x(z)` and `y(z)` of a Weierstrass curve

Building on the Weierstrass expansion `w = W.formalW ∈ R⟦z⟧` constructed in
`EllipticCurves.FormalGroup.Expansion` — the unique order-`3` solution of the functional equation
`w = z³ + (a₁z + a₂z²)w + (a₃ + a₄z)w² + a₆w³` — this file constructs the affine coordinate series
in the local parameter `z = -x/y` near the origin `O` (Silverman, *The Arithmetic of Elliptic
Curves*, IV.1):
$$ x(z) = \frac{z}{w(z)}, \qquad y(z) = \frac{-1}{w(z)}. $$
These have poles at `z = 0` (`x` of order `2`, `y` of order `3`), so they naturally live in the
Laurent series ring `R⸨X⸩`.

The construction is elementary once one observes that `w = z³ · v` where `v` is a *unit* power
series (its constant term is the leading coefficient `1` of `w`). Concretely `v = W.wCofactor`, and
`x(z) = z⁻² · v⁻¹`, `y(z) = -z⁻³ · v⁻¹`, with `v⁻¹ = PowerSeries.invOfUnit v 1`. This avoids any
division in a non-field ring: everything is a product of `HahnSeries.single` monomials with
coercions of honest power series.

## Main definitions

* `WeierstrassCurve.wCofactor` : the unit power series `v` with `w = z³ · v`.
* `WeierstrassCurve.formalX`, `WeierstrassCurve.formalY` : the coordinate Laurent series `x(z)`,
  `y(z) ∈ R⸨X⸩`.

## Main results

* `WeierstrassCurve.formalW_eq_X_pow_mul_wCofactor` : `w = z³ · v`.
* `WeierstrassCurve.isUnit_wCofactor`, `WeierstrassCurve.isUnit_coe_formalW` : `v` and (hence) `w`
  are units (the latter in `R⸨X⸩`).
* `WeierstrassCurve.order_formalW_eq` : `order w = 3` (over a nontrivial ring).
* `WeierstrassCurve.formalX_mul_coe_formalW` : `x(z) · w(z) = z`.
* `WeierstrassCurve.formalY_mul_coe_formalW` : `y(z) · w(z) = -1`.
* `WeierstrassCurve.single_one_mul_formalY` : `z · y(z) = -x(z)`, i.e. `z = -x/y`.
* `WeierstrassCurve.coeff_formalX_neg_two`, `WeierstrassCurve.coeff_formalY_neg_three` : the leading
  (polar) coefficients `1` and `-1`, and `coeff_formalX_of_lt`, `coeff_formalY_of_lt` pin the pole
  orders (`2` and `3`).

The point-on-curve identity — that `(x(z), y(z))` satisfies the Weierstrass equation as Laurent
series — is the algebraic reformulation of `formalW_eq` and is deferred to a follow-up.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

namespace WeierstrassCurve

open PowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The unit cofactor `v` with `w = z³ · v` -/

/-- The power series `v` obtained by dividing the Weierstrass expansion `w` by `z³`; it satisfies
`w = z³ · v` and has constant term `1`, so it is a unit. -/
noncomputable def wCofactor (W : WeierstrassCurve R) : R⟦X⟧ :=
  PowerSeries.mk fun n => coeff (n + 3) W.formalW

lemma coeff_wCofactor (n : ℕ) : coeff n W.wCofactor = coeff (n + 3) W.formalW := by
  rw [wCofactor, coeff_mk]

/-- The Weierstrass expansion factors as `w = z³ · v` with `v = W.wCofactor`. -/
theorem formalW_eq_X_pow_mul_wCofactor : W.formalW = X ^ 3 * W.wCofactor := by
  ext m
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_wCofactor, Nat.sub_add_cancel h]
  · exact coeff_of_lt_order m
      (lt_of_lt_of_le (by exact_mod_cast Nat.not_le.mp h) W.order_formalW)

/-- The constant term of the cofactor `v` is the leading coefficient `1` of `w`. -/
@[simp]
theorem constantCoeff_wCofactor : constantCoeff W.wCofactor = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_wCofactor, zero_add, coeff_formalW_three]

/-- The cofactor `v` is a unit power series. -/
theorem isUnit_wCofactor : IsUnit W.wCofactor :=
  isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_wCofactor]; exact isUnit_one)

/-- The chosen inverse `v⁻¹` of the cofactor, via `PowerSeries.invOfUnit`. -/
theorem wCofactor_mul_invOfUnit : W.wCofactor * invOfUnit W.wCofactor 1 = 1 :=
  mul_invOfUnit W.wCofactor 1 (by rw [constantCoeff_wCofactor, Units.val_one])

/-- Over a nontrivial ring the expansion has order exactly `3`: `w = z³ + …`. -/
theorem order_formalW_eq [Nontrivial R] : W.formalW.order = 3 :=
  le_antisymm (order_le 3 (by rw [coeff_formalW_three]; exact one_ne_zero)) W.order_formalW

/-! ### The coordinate Laurent series -/

open scoped LaurentSeries

/-- The image of `w` in the Laurent series ring factors as `z³ · v`. -/
theorem coe_formalW_eq :
    (W.formalW : R⸨X⸩) = HahnSeries.single (3 : ℤ) 1 * (W.wCofactor : R⸨X⸩) := by
  rw [W.formalW_eq_X_pow_mul_wCofactor, coe_mul, coe_pow, HahnSeries.ofPowerSeries_X,
    HahnSeries.single_pow]
  norm_num

/-- In the Laurent series ring, `w` is a unit (its leading monomial `z³` and the unit factor `v`
are both invertible). This is the key input to the formal group law. -/
theorem isUnit_coe_formalW : IsUnit (W.formalW : R⸨X⸩) := by
  rw [coe_formalW_eq]
  refine IsUnit.mul ?_ (W.isUnit_wCofactor.map (HahnSeries.ofPowerSeries ℤ R))
  exact ⟨⟨HahnSeries.single (3 : ℤ) 1, HahnSeries.single (-3 : ℤ) 1, by
    simp [HahnSeries.single_mul_single], by simp [HahnSeries.single_mul_single]⟩, rfl⟩

/-- The coordinate series `x(z) = z / w(z) = z⁻² · v⁻¹ ∈ R⸨X⸩`. It has a pole of order `2` at the
origin with leading coefficient `1`. -/
noncomputable def formalX (W : WeierstrassCurve R) : R⸨X⸩ :=
  HahnSeries.single (-2 : ℤ) 1 * ((invOfUnit W.wCofactor 1 : R⟦X⟧) : R⸨X⸩)

/-- The coordinate series `y(z) = -1 / w(z) = -z⁻³ · v⁻¹ ∈ R⸨X⸩`. It has a pole of order `3` at the
origin with leading coefficient `-1`. -/
noncomputable def formalY (W : WeierstrassCurve R) : R⸨X⸩ :=
  HahnSeries.single (-3 : ℤ) (-1) * ((invOfUnit W.wCofactor 1 : R⟦X⟧) : R⸨X⸩)

/-- **Defining identity for `x(z)`:** `x(z) · w(z) = z`. -/
theorem formalX_mul_coe_formalW :
    W.formalX * (W.formalW : R⸨X⸩) = HahnSeries.single (1 : ℤ) 1 := by
  rw [formalX, coe_formalW_eq, mul_mul_mul_comm, HahnSeries.single_mul_single,
    ← coe_mul, mul_comm (invOfUnit W.wCofactor 1) W.wCofactor,
    W.wCofactor_mul_invOfUnit, coe_one, mul_one]
  norm_num

/-- **Defining identity for `y(z)`:** `y(z) · w(z) = -1`. -/
theorem formalY_mul_coe_formalW :
    W.formalY * (W.formalW : R⸨X⸩) = -1 := by
  rw [formalY, coe_formalW_eq, mul_mul_mul_comm, HahnSeries.single_mul_single,
    ← coe_mul, mul_comm (invOfUnit W.wCofactor 1) W.wCofactor,
    W.wCofactor_mul_invOfUnit, coe_one, mul_one,
    show ((-3 : ℤ) + 3) = 0 from by norm_num, show ((-1 : R) * 1) = -(1 : R) from by ring,
    HahnSeries.single_neg, HahnSeries.single_zero_one]

/-- The relation `z · y(z) = -x(z)`, i.e. `z = -x(z)/y(z)`: the local parameter is recovered from
the coordinates. -/
theorem single_one_mul_formalY :
    HahnSeries.single (1 : ℤ) 1 * W.formalY = -W.formalX := by
  rw [formalY, formalX, ← mul_assoc, HahnSeries.single_mul_single,
    show ((1 : ℤ) + -3) = -2 from by norm_num, show ((1 : R) * -1) = -(1 : R) from by ring,
    HahnSeries.single_neg, neg_mul]

/-! ### Leading terms and pole orders -/

/-- Negative-index coefficients of a coerced power series vanish. -/
theorem coe_powerSeries_coeff_of_neg (p : R⟦X⟧) {g : ℤ} (hg : g < 0) :
    (p : R⸨X⸩).coeff g = 0 := by
  change (HahnSeries.ofPowerSeries ℤ R p).coeff g = 0
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
  rintro ⟨n, hn⟩
  simp only [Nat.castOrderEmbedding, OrderEmbedding.coe_ofStrictMono] at hn
  omega

/-- The leading coefficient of `x(z)` is `1`, at the pole `z⁻²`. -/
@[simp]
theorem coeff_formalX_neg_two : W.formalX.coeff (-2) = 1 := by
  rw [formalX, HahnSeries.coeff_single_mul,
    show ((-2 : ℤ) - (-2)) = ((0 : ℕ) : ℤ) from by norm_num,
    LaurentSeries.coeff_coe_powerSeries]
  simp

/-- The leading coefficient of `y(z)` is `-1`, at the pole `z⁻³`. -/
@[simp]
theorem coeff_formalY_neg_three : W.formalY.coeff (-3) = -1 := by
  rw [formalY, HahnSeries.coeff_single_mul,
    show ((-3 : ℤ) - (-3)) = ((0 : ℕ) : ℤ) from by norm_num,
    LaurentSeries.coeff_coe_powerSeries]
  simp

/-- `x(z)` has a pole of order exactly `2`: coefficients below `z⁻²` vanish. -/
theorem coeff_formalX_of_lt {g : ℤ} (hg : g < -2) : W.formalX.coeff g = 0 := by
  rw [formalX, HahnSeries.coeff_single_mul, one_mul]
  exact coe_powerSeries_coeff_of_neg _ (by omega)

/-- `y(z)` has a pole of order exactly `3`: coefficients below `z⁻³` vanish. -/
theorem coeff_formalY_of_lt {g : ℤ} (hg : g < -3) : W.formalY.coeff g = 0 := by
  rw [formalY, HahnSeries.coeff_single_mul]
  rw [coe_powerSeries_coeff_of_neg _ (by omega), mul_zero]

end WeierstrassCurve
