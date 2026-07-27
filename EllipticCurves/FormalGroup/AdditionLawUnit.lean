/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.AdditionLaw

/-!
# `IsUnit (formalYThree)`: the analytic core of the Weierstrass formal group law

This file proves that the third `y`-coordinate `y₃ = W.formalYThree ∈ R⸨z₁⸩⸨z₂⸩` of the
Weierstrass addition law (constructed in `EllipticCurves.FormalGroup.AdditionLaw`) is a **unit**.
This is the analytic heart of the formal group law (Silverman, *The Arithmetic of Elliptic
Curves*, IV.1, Theorem 1.1): it is what makes the formal group series `F_E := -x₃·y₃⁻¹`
well-defined.

## Strategy

Everything is a `z₂`-order (outer-grading) computation in the iterated Laurent ring
`R⸨z₁⸩⸨z₂⸩`, with `z₂`-coefficients lying in `R⸨z₁⸩ = R⸨X⸩`. Write `X₁ := W.formalX`,
`Y₁ := W.formalY ∈ R⸨X⸩` (these are `W.biX₁.coeff 0`, `W.biY₁.coeff 0`).

The denominator `d := x₂ - x₁` is a unit of `z₂`-order `-2` with leading coefficient `1`, so its
inverse `d⁻¹` has `z₂`-order `2`. The slope `λ = (y₂ - y₁)·d⁻¹` therefore has `z₂`-order `-1`.
We compute the **principal part** of `λ` explicitly,
`Λ := z₂⁻¹·(-1) + z₂·(-X₁) + z₂²·(-Y₁ - a₁X₁)`, by showing `n - Λ·d` (where `n := y₂ - y₁`) has
`z₂`-order `≥ 1`, whence `λ - Λ = (n - Λ·d)·d⁻¹` has `z₂`-order `≥ 3`. Reducing every product to
`single`-multiplications (`coeff_single_mul`), all coefficients we need come out by hand, with the
higher-order corrections killed by the order bound. Finally

`y₃.coeff g = 0` for `g < 0` and `y₃.coeff 0 = Y₁`,

so `y₃` has `z₂`-order `0` with leading coefficient the unit `Y₁ = W.formalY`, and is a unit by
`HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder`.

## Main results

* `WeierstrassCurve.isUnit_formalYThree` : `IsUnit W.formalYThree`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

open scoped LaurentSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### `formalY` is a unit of `R⸨X⸩` -/

/-- The coordinate series `y(z)` is a unit of `R⸨X⸩` (from `y·w = -1`). -/
theorem isUnit_formalY : IsUnit W.formalY :=
  IsUnit.of_mul_eq_one _ (by rw [mul_neg, W.formalY_mul_coe_formalW, neg_neg])

/-! ### Constant `z₂`-coefficients of `x₁, y₁` and the coefficients of `y₂` -/

/-- The order-`0` `z₂`-coefficient of `x₁ = x(z₁)` is `x(z₁) = W.formalX`. -/
theorem coeff_biX₁_zero : W.biX₁.coeff 0 = W.formalX := by
  rw [biX₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_single_same]

/-- The order-`0` `z₂`-coefficient of `y₁ = y(z₁)` is `y(z₁) = W.formalY`. -/
theorem coeff_biY₁_zero : W.biY₁.coeff 0 = W.formalY := by
  rw [biY₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_single_same]

/-- The series `y₁ = y(z₁)` is supported in `z₂`-degree `0` only. -/
theorem coeff_biY₁_of_ne {g : ℤ} (h : g ≠ 0) : W.biY₁.coeff g = 0 := by
  rw [biY₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h]

/-- The `z₂`-coefficients of `y₂ = y(z₂)`: the `z₁`-constant coefficient `C (y(z)-coeff)`. -/
theorem coeff_biY₂ (g : ℤ) : W.biY₂.coeff g = HahnSeries.C (W.formalY.coeff g) := by
  rw [biY₂, cLaurentRingHom, HahnSeries.mapRingHom_apply, HahnSeries.map_coeff]

/-! ### Closed forms for the `z₂`-coefficients of `d = x₂ - x₁` and `n = y₂ - y₁` -/

private lemma coeff_d_neg_one : (W.biX₂ - W.biX₁).coeff (-1) = -HahnSeries.C W.a₁ := by
  rw [HahnSeries.coeff_sub, coeff_biX₂, coeff_formalX_neg_one, W.coeff_biX₁_of_ne (by norm_num),
    sub_zero, map_neg]

private lemma coeff_d_zero :
    (W.biX₂ - W.biX₁).coeff 0 = -HahnSeries.C W.a₂ - W.formalX := by
  rw [HahnSeries.coeff_sub, coeff_biX₂, coeff_formalX_zero, W.coeff_biX₁_zero, map_neg]

private lemma coeff_d_one : (W.biX₂ - W.biX₁).coeff 1 = -HahnSeries.C W.a₃ := by
  rw [HahnSeries.coeff_sub, coeff_biX₂, coeff_formalX_one, W.coeff_biX₁_of_ne (by norm_num),
    sub_zero, map_neg]

private lemma coeff_n_neg_three : (W.biY₂ - W.biY₁).coeff (-3) = -1 := by
  rw [HahnSeries.coeff_sub, coeff_biY₂, coeff_formalY_neg_three, W.coeff_biY₁_of_ne (by norm_num),
    sub_zero, map_neg, map_one]

private lemma coeff_n_neg_two : (W.biY₂ - W.biY₁).coeff (-2) = HahnSeries.C W.a₁ := by
  rw [HahnSeries.coeff_sub, coeff_biY₂, coeff_formalY_neg_two, W.coeff_biY₁_of_ne (by norm_num),
    sub_zero]

private lemma coeff_n_neg_one : (W.biY₂ - W.biY₁).coeff (-1) = HahnSeries.C W.a₂ := by
  rw [HahnSeries.coeff_sub, coeff_biY₂, coeff_formalY_neg_one, W.coeff_biY₁_of_ne (by norm_num),
    sub_zero]

private lemma coeff_n_zero :
    (W.biY₂ - W.biY₁).coeff 0 = HahnSeries.C W.a₃ - W.formalY := by
  rw [HahnSeries.coeff_sub, coeff_biY₂, coeff_formalY_zero, W.coeff_biY₁_zero]

private lemma coeff_n_of_lt {g : ℤ} (hg : g < -3) : (W.biY₂ - W.biY₁).coeff g = 0 := by
  rw [HahnSeries.coeff_sub, coeff_biY₂, W.coeff_formalY_of_lt hg, map_zero,
    W.coeff_biY₁_of_ne (by omega), sub_zero]

/-! ### The order and inverse-order of `d = x₂ - x₁` -/

private lemma orderTop_d [Nontrivial R] :
    (W.biX₂ - W.biX₁).orderTop = ((-2 : ℤ) : WithTop ℤ) := by
  refine le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero ?_) ?_
  · rw [W.coeff_biX₂_sub_biX₁_neg_two]; exact one_ne_zero
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro j hj
    exact W.coeff_biX₂_sub_biX₁_of_lt (by exact_mod_cast hj)

private lemma d_ne_zero [Nontrivial R] : (W.biX₂ - W.biX₁) ≠ 0 :=
  W.isUnit_biX₂_sub_biX₁.ne_zero

private lemma order_d [Nontrivial R] : (W.biX₂ - W.biX₁).order = -2 := by
  have : ((W.biX₂ - W.biX₁).order : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ) := by
    rw [HahnSeries.order_eq_orderTop_of_ne_zero W.d_ne_zero, W.orderTop_d]
  exact_mod_cast this

private lemma leadingCoeff_d [Nontrivial R] : (W.biX₂ - W.biX₁).leadingCoeff = 1 := by
  rw [HahnSeries.leadingCoeff_eq, W.order_d, W.coeff_biX₂_sub_biX₁_neg_two]

private lemma orderTop_inv_d [Nontrivial R] :
    (Ring.inverse (W.biX₂ - W.biX₁)).orderTop = ((2 : ℤ) : WithTop ℤ) := by
  have hmul : (W.biX₂ - W.biX₁) * Ring.inverse (W.biX₂ - W.biX₁) = 1 :=
    Ring.mul_inverse_cancel _ W.isUnit_biX₂_sub_biX₁
  have hinv0 : Ring.inverse (W.biX₂ - W.biX₁) ≠ 0 := by
    obtain ⟨u, hu⟩ := W.isUnit_biX₂_sub_biX₁
    rw [← hu, Ring.inverse_unit]; exact u⁻¹.ne_zero
  have hlc : (W.biX₂ - W.biX₁).leadingCoeff *
      (Ring.inverse (W.biX₂ - W.biX₁)).leadingCoeff ≠ 0 := by
    rw [W.leadingCoeff_d, one_mul]; exact HahnSeries.leadingCoeff_ne_zero.mpr hinv0
  have h := HahnSeries.orderTop_mul_of_ne_zero hlc
  rw [hmul, HahnSeries.orderTop_one, W.orderTop_d] at h
  -- `h : 0 = ↑(-2) + orderTop (inv)`
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
    (HahnSeries.orderTop_ne_top.mpr hinv0)
  rw [← hk] at h ⊢
  rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at h
  rw [WithTop.coe_eq_coe]
  omega

/-! ### The principal part of the slope `λ` -/

/-- The principal part `Λ = z₂⁻¹·(-1) + z₂·(-x₁) + z₂²·(-y₁ - a₁x₁)` of the slope `λ`, matching
`λ` in `z₂`-degrees `< 3`. -/
private noncomputable def lambdaPrincipal (W : WeierstrassCurve R) : (R⸨X⸩)⸨X⸩ :=
  HahnSeries.single (-1) (-1)
    + HahnSeries.single 1 (-W.formalX)
    + HahnSeries.single 2 (-W.formalY - HahnSeries.C W.a₁ * W.formalX)

/-- `Λ · y` coefficient, reduced to `single`-multiplications (no antidiagonal). -/
private lemma coeff_lambdaPrincipal_mul (y : (R⸨X⸩)⸨X⸩) (g : ℤ) :
    (W.lambdaPrincipal * y).coeff g
      = (-1) * y.coeff (g + 1)
        + (-W.formalX) * y.coeff (g - 1)
        + (-W.formalY - HahnSeries.C W.a₁ * W.formalX) * y.coeff (g - 2) := by
  rw [lambdaPrincipal, add_mul, add_mul, HahnSeries.coeff_add, HahnSeries.coeff_add,
    HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul,
    sub_neg_eq_add]

private lemma orderTop_n_sub_lambdaPrincipal_mul_d [Nontrivial R] :
    ((1 : ℤ) : WithTop ℤ) ≤
      ((W.biY₂ - W.biY₁) - W.lambdaPrincipal * (W.biX₂ - W.biX₁)).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro g hg
  have hg1 : g < 1 := by exact_mod_cast hg
  rw [HahnSeries.coeff_sub, W.coeff_lambdaPrincipal_mul]
  rcases lt_or_ge g (-3 : ℤ) with hlt | hge
  · rw [W.coeff_n_of_lt hlt, W.coeff_biX₂_sub_biX₁_of_lt (show g + 1 < -2 by omega),
      W.coeff_biX₂_sub_biX₁_of_lt (show g - 1 < -2 by omega),
      W.coeff_biX₂_sub_biX₁_of_lt (show g - 2 < -2 by omega)]
    ring
  · have hz3 : (W.biX₂ - W.biX₁).coeff (-3) = 0 := W.coeff_biX₂_sub_biX₁_of_lt (by norm_num)
    have hz4 : (W.biX₂ - W.biX₁).coeff (-4) = 0 := W.coeff_biX₂_sub_biX₁_of_lt (by norm_num)
    have hz5 : (W.biX₂ - W.biX₁).coeff (-5) = 0 := W.coeff_biX₂_sub_biX₁_of_lt (by norm_num)
    interval_cases g <;>
      simp only [W.coeff_n_neg_three, W.coeff_n_neg_two, W.coeff_n_neg_one, W.coeff_n_zero,
        W.coeff_biX₂_sub_biX₁_neg_two, W.coeff_d_neg_one, W.coeff_d_zero, W.coeff_d_one,
        hz3, hz4, hz5, show (-3 : ℤ) + 1 = -2 by norm_num,
        show (-3 : ℤ) - 1 = -4 by norm_num, show (-3 : ℤ) - 2 = -5 by norm_num,
        show (-2 : ℤ) + 1 = -1 by norm_num, show (-2 : ℤ) - 1 = -3 by norm_num,
        show (-2 : ℤ) - 2 = -4 by norm_num, show (-1 : ℤ) + 1 = 0 by norm_num,
        show (-1 : ℤ) - 1 = -2 by norm_num, show (-1 : ℤ) - 2 = -3 by norm_num,
        show (0 : ℤ) + 1 = 1 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num,
        show (0 : ℤ) - 2 = -2 by norm_num] <;> ring

/-- The slope `λ` agrees with its principal part `Λ` in `z₂`-degrees `< 3`. -/
private lemma orderTop_lambda_sub_principal [Nontrivial R] :
    ((3 : ℤ) : WithTop ℤ) ≤ (W.formalLambda - W.lambdaPrincipal).orderTop := by
  have hmul : (W.biX₂ - W.biX₁) * Ring.inverse (W.biX₂ - W.biX₁) = 1 :=
    Ring.mul_inverse_cancel _ W.isUnit_biX₂_sub_biX₁
  have hfac : ((W.biY₂ - W.biY₁) - W.lambdaPrincipal * (W.biX₂ - W.biX₁))
      * Ring.inverse (W.biX₂ - W.biX₁) = W.formalLambda - W.lambdaPrincipal := by
    rw [formalLambda, sub_mul, mul_assoc, hmul, mul_one]
  calc ((3 : ℤ) : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) + ((2 : ℤ) : WithTop ℤ) := by
        rw [← WithTop.coe_add]; norm_num
    _ ≤ ((W.biY₂ - W.biY₁) - W.lambdaPrincipal * (W.biX₂ - W.biX₁)).orderTop
          + (Ring.inverse (W.biX₂ - W.biX₁)).orderTop :=
        add_le_add W.orderTop_n_sub_lambdaPrincipal_mul_d (le_of_eq W.orderTop_inv_d.symm)
    _ ≤ _ := by rw [← hfac]; exact HahnSeries.orderTop_add_le_mul

/-! ### Coefficients and orders of the principal-part powers -/

/-- `(C(Ca) * x).coeff g = Ca * x.coeff g` (the constant `C(Ca)` is a `single 0`). -/
private lemma coeff_CC_mul (a : R) (x : (R⸨X⸩)⸨X⸩) (g : ℤ) :
    (HahnSeries.C (HahnSeries.C a) * x).coeff g = HahnSeries.C a * x.coeff g := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero]

/-- `(C(Ca)).coeff 0 = Ca`. -/
private lemma coeff_CC_zero (a : R) :
    (HahnSeries.C (HahnSeries.C a) : (R⸨X⸩)⸨X⸩).coeff 0 = HahnSeries.C a := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]

/-- `(C(Ca)).coeff g = 0` for `g ≠ 0`. -/
private lemma coeff_CC_of_ne (a : R) {g : ℤ} (hg : g ≠ 0) :
    (HahnSeries.C (HahnSeries.C a) : (R⸨X⸩)⸨X⸩).coeff g = 0 := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hg]

/-! Coefficients of the principal part `Λ` (support `{-1, 1, 2}`). -/

private lemma coeff_lamP_of_lt {g : ℤ} (hg : g < -1) : W.lambdaPrincipal.coeff g = 0 := by
  rw [lambdaPrincipal, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  ring

private lemma coeff_lamP_neg_one : W.lambdaPrincipal.coeff (-1) = -1 := by
  rw [lambdaPrincipal, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, if_pos rfl, if_neg (by norm_num),
    if_neg (by norm_num)]
  ring

private lemma coeff_lamP_zero : W.lambdaPrincipal.coeff 0 = 0 := by
  rw [lambdaPrincipal, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, if_neg (by norm_num), if_neg (by norm_num),
    if_neg (by norm_num)]
  ring

private lemma coeff_lamP_one : W.lambdaPrincipal.coeff 1 = -W.formalX := by
  rw [lambdaPrincipal, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, if_neg (by norm_num), if_pos rfl,
    if_neg (by norm_num)]
  ring

private lemma coeff_lamP_two :
    W.lambdaPrincipal.coeff 2 = -W.formalY - HahnSeries.C W.a₁ * W.formalX := by
  rw [lambdaPrincipal, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, if_neg (by norm_num), if_neg (by norm_num),
    if_pos rfl]
  ring

private lemma orderTop_lamP : ((-1 : ℤ) : WithTop ℤ) ≤ W.lambdaPrincipal.orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro g hg
  exact W.coeff_lamP_of_lt (by exact_mod_cast hg)

private lemma orderTop_lamP_sq : ((-2 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal ^ 2).orderTop := by
  rw [sq]
  refine le_trans ?_ HahnSeries.orderTop_add_le_mul
  rw [show ((-2 : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) by
    rw [← WithTop.coe_add]; norm_num]
  exact add_le_add W.orderTop_lamP W.orderTop_lamP

private lemma orderTop_lamP_cube : ((-3 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal ^ 3).orderTop := by
  rw [show W.lambdaPrincipal ^ 3 = W.lambdaPrincipal ^ 2 * W.lambdaPrincipal by ring]
  refine le_trans ?_ HahnSeries.orderTop_add_le_mul
  rw [show ((-3 : ℤ) : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) by
    rw [← WithTop.coe_add]; norm_num]
  exact add_le_add W.orderTop_lamP_sq W.orderTop_lamP

private lemma coeff_lamP_sq_of_lt {g : ℤ} (hg : g < -2) : (W.lambdaPrincipal ^ 2).coeff g = 0 := by
  rw [sq, W.coeff_lambdaPrincipal_mul, W.coeff_lamP_of_lt (by omega), W.coeff_lamP_of_lt (by omega),
    W.coeff_lamP_of_lt (by omega)]
  ring

private lemma coeff_lamP_sq_neg_two : (W.lambdaPrincipal ^ 2).coeff (-2) = 1 := by
  rw [sq, W.coeff_lambdaPrincipal_mul, show (-2 : ℤ) + 1 = -1 by norm_num,
    show (-2 : ℤ) - 1 = -3 by norm_num, show (-2 : ℤ) - 2 = -4 by norm_num, W.coeff_lamP_neg_one,
    W.coeff_lamP_of_lt (by norm_num), W.coeff_lamP_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_sq_neg_one : (W.lambdaPrincipal ^ 2).coeff (-1) = 0 := by
  rw [sq, W.coeff_lambdaPrincipal_mul, show (-1 : ℤ) + 1 = 0 by norm_num,
    show (-1 : ℤ) - 1 = -2 by norm_num, show (-1 : ℤ) - 2 = -3 by norm_num, W.coeff_lamP_zero,
    W.coeff_lamP_of_lt (by norm_num), W.coeff_lamP_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_sq_zero : (W.lambdaPrincipal ^ 2).coeff 0 = 2 * W.formalX := by
  rw [sq, W.coeff_lambdaPrincipal_mul, show (0 : ℤ) + 1 = 1 by norm_num,
    show (0 : ℤ) - 1 = -1 by norm_num, show (0 : ℤ) - 2 = -2 by norm_num, W.coeff_lamP_one,
    W.coeff_lamP_neg_one, W.coeff_lamP_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_sq_one :
    (W.lambdaPrincipal ^ 2).coeff 1 = 2 * W.formalY + 2 * HahnSeries.C W.a₁ * W.formalX := by
  rw [sq, W.coeff_lambdaPrincipal_mul, show (1 : ℤ) + 1 = 2 by norm_num,
    show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) - 2 = -1 by norm_num, W.coeff_lamP_two,
    W.coeff_lamP_zero, W.coeff_lamP_neg_one]
  ring

private lemma coeff_lamP_cube_neg_three : (W.lambdaPrincipal ^ 3).coeff (-3) = -1 := by
  rw [show W.lambdaPrincipal ^ 3 = W.lambdaPrincipal * W.lambdaPrincipal ^ 2 by ring,
    W.coeff_lambdaPrincipal_mul, show (-3 : ℤ) + 1 = -2 by norm_num,
    show (-3 : ℤ) - 1 = -4 by norm_num, show (-3 : ℤ) - 2 = -5 by norm_num, W.coeff_lamP_sq_neg_two,
    W.coeff_lamP_sq_of_lt (by norm_num), W.coeff_lamP_sq_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_cube_neg_two : (W.lambdaPrincipal ^ 3).coeff (-2) = 0 := by
  rw [show W.lambdaPrincipal ^ 3 = W.lambdaPrincipal * W.lambdaPrincipal ^ 2 by ring,
    W.coeff_lambdaPrincipal_mul, show (-2 : ℤ) + 1 = -1 by norm_num,
    show (-2 : ℤ) - 1 = -3 by norm_num, show (-2 : ℤ) - 2 = -4 by norm_num, W.coeff_lamP_sq_neg_one,
    W.coeff_lamP_sq_of_lt (by norm_num), W.coeff_lamP_sq_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_cube_neg_one : (W.lambdaPrincipal ^ 3).coeff (-1) = -3 * W.formalX := by
  rw [show W.lambdaPrincipal ^ 3 = W.lambdaPrincipal * W.lambdaPrincipal ^ 2 by ring,
    W.coeff_lambdaPrincipal_mul, show (-1 : ℤ) + 1 = 0 by norm_num,
    show (-1 : ℤ) - 1 = -2 by norm_num, show (-1 : ℤ) - 2 = -3 by norm_num, W.coeff_lamP_sq_zero,
    W.coeff_lamP_sq_neg_two, W.coeff_lamP_sq_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_cube_zero :
    (W.lambdaPrincipal ^ 3).coeff 0 = -3 * W.formalY - 3 * HahnSeries.C W.a₁ * W.formalX := by
  rw [show W.lambdaPrincipal ^ 3 = W.lambdaPrincipal * W.lambdaPrincipal ^ 2 by ring,
    W.coeff_lambdaPrincipal_mul, show (0 : ℤ) + 1 = 1 by norm_num,
    show (0 : ℤ) - 1 = -1 by norm_num, show (0 : ℤ) - 2 = -2 by norm_num, W.coeff_lamP_sq_one,
    W.coeff_lamP_sq_neg_one, W.coeff_lamP_sq_neg_two]
  ring

private lemma coeff_biX₂_neg_two : W.biX₂.coeff (-2) = 1 := by
  rw [coeff_biX₂, coeff_formalX_neg_two, map_one]

private lemma coeff_biX₂_neg_one : W.biX₂.coeff (-1) = -HahnSeries.C W.a₁ := by
  rw [coeff_biX₂, coeff_formalX_neg_one, map_neg]

private lemma coeff_biX₂_zero : W.biX₂.coeff 0 = -HahnSeries.C W.a₂ := by
  rw [coeff_biX₂, coeff_formalX_zero, map_neg]

private lemma coeff_biX₂_one : W.biX₂.coeff 1 = -HahnSeries.C W.a₃ := by
  rw [coeff_biX₂, coeff_formalX_one, map_neg]

private lemma coeff_biX₂_of_lt {g : ℤ} (hg : g < -2) : W.biX₂.coeff g = 0 := by
  rw [coeff_biX₂, W.coeff_formalX_of_lt hg, map_zero]

/-- `(Λ * x₁).coeff g = Λ.coeff g * x(z₁)` (since `x₁` is `z₂`-constant). -/
private lemma coeff_lamP_mul_biX₁ (g : ℤ) :
    (W.lambdaPrincipal * W.biX₁).coeff g = W.lambdaPrincipal.coeff g * W.formalX := by
  rw [biX₁, cConstRingHom, HahnSeries.C_apply, HahnSeries.coeff_mul_single, sub_zero]

private lemma coeff_lamP_mul_biX₂_neg_three : (W.lambdaPrincipal * W.biX₂).coeff (-3) = -1 := by
  rw [W.coeff_lambdaPrincipal_mul, show (-3 : ℤ) + 1 = -2 by norm_num,
    show (-3 : ℤ) - 1 = -4 by norm_num, show (-3 : ℤ) - 2 = -5 by norm_num, W.coeff_biX₂_neg_two,
    W.coeff_biX₂_of_lt (by norm_num), W.coeff_biX₂_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_mul_biX₂_neg_two :
    (W.lambdaPrincipal * W.biX₂).coeff (-2) = HahnSeries.C W.a₁ := by
  rw [W.coeff_lambdaPrincipal_mul, show (-2 : ℤ) + 1 = -1 by norm_num,
    show (-2 : ℤ) - 1 = -3 by norm_num, show (-2 : ℤ) - 2 = -4 by norm_num, W.coeff_biX₂_neg_one,
    W.coeff_biX₂_of_lt (by norm_num), W.coeff_biX₂_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_mul_biX₂_neg_one :
    (W.lambdaPrincipal * W.biX₂).coeff (-1) = HahnSeries.C W.a₂ - W.formalX := by
  rw [W.coeff_lambdaPrincipal_mul, show (-1 : ℤ) + 1 = 0 by norm_num,
    show (-1 : ℤ) - 1 = -2 by norm_num, show (-1 : ℤ) - 2 = -3 by norm_num, W.coeff_biX₂_zero,
    W.coeff_biX₂_neg_two, W.coeff_biX₂_of_lt (by norm_num)]
  ring

private lemma coeff_lamP_mul_biX₂_zero :
    (W.lambdaPrincipal * W.biX₂).coeff 0 = HahnSeries.C W.a₃ - W.formalY := by
  rw [W.coeff_lambdaPrincipal_mul, show (0 : ℤ) + 1 = 1 by norm_num,
    show (0 : ℤ) - 1 = -1 by norm_num, show (0 : ℤ) - 2 = -2 by norm_num, W.coeff_biX₂_one,
    W.coeff_biX₂_neg_one, W.coeff_biX₂_neg_two]
  ring

private lemma orderTop_biX₂ : ((-2 : ℤ) : WithTop ℤ) ≤ W.biX₂.orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro g hg
  rw [coeff_biX₂, W.coeff_formalX_of_lt (show g < -2 by exact_mod_cast hg), map_zero]

private lemma orderTop_biX₁ : ((0 : ℤ) : WithTop ℤ) ≤ W.biX₁.orderTop := by
  rw [biX₁, cConstRingHom, HahnSeries.C_apply]; exact HahnSeries.orderTop_single_le

private lemma orderTop_biY₁ : ((0 : ℤ) : WithTop ℤ) ≤ W.biY₁.orderTop := by
  rw [biY₁, cConstRingHom, HahnSeries.C_apply]; exact HahnSeries.orderTop_single_le

private lemma orderTop_CC (a : R) :
    ((0 : ℤ) : WithTop ℤ) ≤ (HahnSeries.C (HahnSeries.C a) : (R⸨X⸩)⸨X⸩).orderTop := by
  rw [HahnSeries.C_apply]; exact HahnSeries.orderTop_single_le

/-- `orderTop (C(Ca) * x) ≥ orderTop x`. -/
private lemma le_orderTop_CC_mul (a : R) (x : (R⸨X⸩)⸨X⸩) :
    x.orderTop ≤ (HahnSeries.C (HahnSeries.C a) * x).orderTop := by
  refine le_trans ?_ HahnSeries.orderTop_add_le_mul
  simpa using add_le_add (orderTop_CC a) (le_refl x.orderTop)

/-- `orderTop (Λ * y) ≥ -1 + orderTop y`. -/
private lemma le_orderTop_lamP_mul (y : (R⸨X⸩)⸨X⸩) :
    ((-1 : ℤ) : WithTop ℤ) + y.orderTop ≤ (W.lambdaPrincipal * y).orderTop :=
  le_trans (add_le_add W.orderTop_lamP (le_refl y.orderTop)) HahnSeries.orderTop_add_le_mul

private lemma le_orderTop_add' {a b : (R⸨X⸩)⸨X⸩} {c : WithTop ℤ}
    (ha : c ≤ a.orderTop) (hb : c ≤ b.orderTop) : c ≤ (a + b).orderTop :=
  le_trans (le_min ha hb) HahnSeries.min_orderTop_le_orderTop_add

private lemma le_orderTop_sub' {a b : (R⸨X⸩)⸨X⸩} {c : WithTop ℤ}
    (ha : c ≤ a.orderTop) (hb : c ≤ b.orderTop) : c ≤ (a - b).orderTop := by
  rw [sub_eq_add_neg]
  exact le_orderTop_add' ha (by rwa [HahnSeries.orderTop_neg])

/-! ### The `Λ`-only part `Zpure` and the `h`-cofactor `Q` of `y₃ - biY₁` -/

/-- The `Λ`-only part of `y₃ - y(z₁)` (the Vieta expansion with `λ` replaced by its principal part
`Λ`). Written without numeric multipliers to ease the order bookkeeping. -/
private noncomputable def zpureY (W : WeierstrassCurve R) : (R⸨X⸩)⸨X⸩ :=
  -W.lambdaPrincipal ^ 3
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal ^ 2
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal ^ 2
    + HahnSeries.C (HahnSeries.C W.a₂) * W.lambdaPrincipal
    - HahnSeries.C (HahnSeries.C W.a₁) * (HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal)
    + W.lambdaPrincipal * W.biX₁ + W.lambdaPrincipal * W.biX₁ + W.lambdaPrincipal * W.biX₂
    + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₁ + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂
    + HahnSeries.C (HahnSeries.C W.a₁) * HahnSeries.C (HahnSeries.C W.a₂)
    - W.biY₁ - W.biY₁ - HahnSeries.C (HahnSeries.C W.a₃)

/-- The cofactor `Q` with `y₃ - y(z₁) = Zpure + (λ - Λ)·Q`. -/
private noncomputable def qY (W : WeierstrassCurve R) : (R⸨X⸩)⸨X⸩ :=
  -W.lambdaPrincipal ^ 2 - W.lambdaPrincipal ^ 2 - W.lambdaPrincipal ^ 2
    - W.lambdaPrincipal * (W.formalLambda - W.lambdaPrincipal)
    - W.lambdaPrincipal * (W.formalLambda - W.lambdaPrincipal)
    - W.lambdaPrincipal * (W.formalLambda - W.lambdaPrincipal)
    - (W.formalLambda - W.lambdaPrincipal) * (W.formalLambda - W.lambdaPrincipal)
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal
    - HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal
    - HahnSeries.C (HahnSeries.C W.a₁) * (W.formalLambda - W.lambdaPrincipal)
    - HahnSeries.C (HahnSeries.C W.a₁) * (W.formalLambda - W.lambdaPrincipal)
    + HahnSeries.C (HahnSeries.C W.a₂)
    - HahnSeries.C (HahnSeries.C W.a₁) * HahnSeries.C (HahnSeries.C W.a₁)
    + W.biX₁ + W.biX₁ + W.biX₂

private lemma formalYThree_sub_biY₁_eq :
    W.formalYThree - W.biY₁
      = W.zpureY + (W.formalLambda - W.lambdaPrincipal) * W.qY := by
  unfold formalYThree formalXThree formalNu zpureY qY
  ring

/-- Each summand of `Zpure` has `z₂`-order `≥ -3`, hence so does `Zpure`. -/
private lemma orderTop_zpureY_ge [Nontrivial R] :
    ((-3 : ℤ) : WithTop ℤ) ≤ W.zpureY.orderTop := by
  have hCCL2 : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal ^ 2).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ -2))
      (le_trans W.orderTop_lamP_sq (le_orderTop_CC_mul _ _))
  have hCC2L : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₂) * W.lambdaPrincipal).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ -1))
      (le_trans W.orderTop_lamP (le_orderTop_CC_mul _ _))
  have hCC1CC1L : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) *
          (HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal)).orderTop :=
    le_trans (le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ -1))
      (le_trans W.orderTop_lamP (le_orderTop_CC_mul _ _))) (le_orderTop_CC_mul _ _)
  have hLbiX1 : ((-3 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal * W.biX₁).orderTop := by
    refine le_trans ?_ (W.le_orderTop_lamP_mul W.biX₁)
    rw [show ((-3 : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) + ((-2 : ℤ) : WithTop ℤ) by
      rw [← WithTop.coe_add]; norm_num]
    exact add_le_add (le_refl _)
      (le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0)) W.orderTop_biX₁)
  have hLbiX2 : ((-3 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal * W.biX₂).orderTop := by
    refine le_trans ?_ (W.le_orderTop_lamP_mul W.biX₂)
    rw [show ((-3 : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) + ((-2 : ℤ) : WithTop ℤ) by
      rw [← WithTop.coe_add]; norm_num]
    exact add_le_add (le_refl _) W.orderTop_biX₂
  have hCC1biX1 : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * W.biX₁).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ 0))
      (le_trans W.orderTop_biX₁ (le_orderTop_CC_mul _ _))
  have hCC1biX2 : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ -2))
      (le_trans W.orderTop_biX₂ (le_orderTop_CC_mul _ _))
  have hCC1CC2 : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * HahnSeries.C (HahnSeries.C W.a₂)
          : (R⸨X⸩)⸨X⸩).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ 0))
      (le_trans (orderTop_CC _) (le_orderTop_CC_mul _ _))
  have hbiY1 : ((-3 : ℤ) : WithTop ℤ) ≤ W.biY₁.orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ 0)) W.orderTop_biY₁
  have hCC3 : ((-3 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₃) : (R⸨X⸩)⸨X⸩).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-3 : ℤ) ≤ 0)) (orderTop_CC _)
  have hL3 : ((-3 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal ^ 3).orderTop := W.orderTop_lamP_cube
  unfold zpureY
  refine le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_add' (le_orderTop_add'
    (le_orderTop_add' (le_orderTop_add' (le_orderTop_add' (le_orderTop_add' (le_orderTop_sub'
    (le_orderTop_add' (le_orderTop_sub' (le_orderTop_sub' ?_ hCCL2) hCCL2) hCC2L) hCC1CC1L)
    hLbiX1) hLbiX1) hLbiX2) hCC1biX1) hCC1biX2) hCC1CC2) hbiY1) hbiY1) hCC3
  rw [HahnSeries.orderTop_neg]; exact hL3

/-- Each summand of `Q` has `z₂`-order `≥ -2`, hence so does `Q`. -/
private lemma orderTop_qY_ge [Nontrivial R] : ((-2 : ℤ) : WithTop ℤ) ≤ W.qY.orderTop := by
  have hh : ((3 : ℤ) : WithTop ℤ) ≤ (W.formalLambda - W.lambdaPrincipal).orderTop :=
    W.orderTop_lambda_sub_principal
  have hL2 : ((-2 : ℤ) : WithTop ℤ) ≤ (W.lambdaPrincipal ^ 2).orderTop := W.orderTop_lamP_sq
  have hLh : ((-2 : ℤ) : WithTop ℤ)
      ≤ (W.lambdaPrincipal * (W.formalLambda - W.lambdaPrincipal)).orderTop := by
    refine le_trans ?_ (W.le_orderTop_lamP_mul _)
    exact le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ -1 + 3))
      (add_le_add (le_refl _) hh)
  have hhh : ((-2 : ℤ) : WithTop ℤ)
      ≤ ((W.formalLambda - W.lambdaPrincipal) * (W.formalLambda - W.lambdaPrincipal)).orderTop := by
    refine le_trans ?_ HahnSeries.orderTop_add_le_mul
    exact le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 3 + 3)) (add_le_add hh hh)
  have hCCL : ((-2 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * W.lambdaPrincipal).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ -1))
      (le_trans W.orderTop_lamP (le_orderTop_CC_mul _ _))
  have hCCh : ((-2 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * (W.formalLambda - W.lambdaPrincipal)).orderTop :=
    le_trans (le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 3)) hh)
      (le_orderTop_CC_mul _ _)
  have hCC2 : ((-2 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₂) : (R⸨X⸩)⸨X⸩).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0)) (orderTop_CC _)
  have hCC1CC1 : ((-2 : ℤ) : WithTop ℤ)
      ≤ (HahnSeries.C (HahnSeries.C W.a₁) * HahnSeries.C (HahnSeries.C W.a₁)
          : (R⸨X⸩)⸨X⸩).orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0))
      (le_trans (orderTop_CC _) (le_orderTop_CC_mul _ _))
  have hbiX1 : ((-2 : ℤ) : WithTop ℤ) ≤ W.biX₁.orderTop :=
    le_trans (by exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0)) W.orderTop_biX₁
  have hbiX2 : ((-2 : ℤ) : WithTop ℤ) ≤ W.biX₂.orderTop := W.orderTop_biX₂
  unfold qY
  refine le_orderTop_add' (le_orderTop_add' (le_orderTop_add' (le_orderTop_sub' (le_orderTop_add'
    (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub'
    (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub' (le_orderTop_sub'
    (le_orderTop_sub' (le_orderTop_sub' ?_ hL2) hL2) hLh) hLh) hLh) hhh) hCCL) hCCL) hCCL) hCCL)
    hCCh) hCCh) hCC2) hCC1CC1) hbiX1) hbiX1) hbiX2
  rw [HahnSeries.orderTop_neg]; exact hL2

/-- `Zpure.coeff g = 0` for `g < 1` (its low coefficients cancel; `Silverman AEC IV.1`). -/
private lemma coeff_zpureY_of_lt [Nontrivial R] {g : ℤ} (hg : g < 1) : W.zpureY.coeff g = 0 := by
  rcases lt_or_ge g (-3) with hlt | hge
  · exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (by exact_mod_cast hlt) W.orderTop_zpureY_ge)
  · have hg1 : g ≤ 0 := by omega
    unfold zpureY
    interval_cases g <;>
      simp only [HahnSeries.coeff_sub, HahnSeries.coeff_add, HahnSeries.coeff_neg, coeff_CC_mul,
        W.coeff_lamP_sq_of_lt (show (-3 : ℤ) < -2 by norm_num),
        W.coeff_lamP_of_lt (show (-3 : ℤ) < -1 by norm_num),
        W.coeff_lamP_of_lt (show (-2 : ℤ) < -1 by norm_num),
        W.coeff_biX₂_of_lt (show (-3 : ℤ) < -2 by norm_num),
        W.coeff_biX₁_of_ne (show (-3 : ℤ) ≠ 0 by norm_num),
        W.coeff_biX₁_of_ne (show (-2 : ℤ) ≠ 0 by norm_num),
        W.coeff_biX₁_of_ne (show (-1 : ℤ) ≠ 0 by norm_num),
        W.coeff_biY₁_of_ne (show (-3 : ℤ) ≠ 0 by norm_num),
        W.coeff_biY₁_of_ne (show (-2 : ℤ) ≠ 0 by norm_num),
        W.coeff_biY₁_of_ne (show (-1 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₂ (show (-3 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₂ (show (-2 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₂ (show (-1 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₃ (show (-3 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₃ (show (-2 : ℤ) ≠ 0 by norm_num),
        coeff_CC_of_ne W.a₃ (show (-1 : ℤ) ≠ 0 by norm_num),
        W.coeff_lamP_mul_biX₁, W.coeff_lamP_cube_neg_three, W.coeff_lamP_cube_neg_two,
        W.coeff_lamP_cube_neg_one, W.coeff_lamP_cube_zero, W.coeff_lamP_sq_neg_two,
        W.coeff_lamP_sq_neg_one, W.coeff_lamP_sq_zero, W.coeff_lamP_neg_one, W.coeff_lamP_zero,
        W.coeff_lamP_mul_biX₂_neg_three, W.coeff_lamP_mul_biX₂_neg_two,
        W.coeff_lamP_mul_biX₂_neg_one, W.coeff_lamP_mul_biX₂_zero, W.coeff_biX₁_zero,
        W.coeff_biX₂_neg_two, W.coeff_biX₂_neg_one, W.coeff_biX₂_zero, W.coeff_biY₁_zero,
        coeff_CC_zero] <;> ring

/-! ### `y₃` is a unit -/

private lemma orderTop_formalYThree_sub_biY₁ [Nontrivial R] :
    ((1 : ℤ) : WithTop ℤ) ≤ (W.formalYThree - W.biY₁).orderTop := by
  rw [W.formalYThree_sub_biY₁_eq]
  refine le_orderTop_add' ?_ ?_
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro g hg
    exact W.coeff_zpureY_of_lt (by exact_mod_cast hg)
  · refine le_trans ?_ HahnSeries.orderTop_add_le_mul
    rw [show ((1 : ℤ) : WithTop ℤ) = ((3 : ℤ) : WithTop ℤ) + ((-2 : ℤ) : WithTop ℤ) by
      rw [← WithTop.coe_add]; norm_num]
    exact add_le_add W.orderTop_lambda_sub_principal W.orderTop_qY_ge

/-- **The analytic core of the Weierstrass formal group law.** The third `y`-coordinate `y₃` is a
unit of `R⸨z₁⸩⸨z₂⸩`. Its `z₂`-order is `0` with leading coefficient the unit `y(z₁) = W.formalY`,
which makes the formal group series `F_E := -x₃·y₃⁻¹` well-defined. (Silverman AEC IV.1.) -/
theorem isUnit_formalYThree : IsUnit W.formalYThree := by
  obtain _ | _ := subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton _
  · have hbiord : W.biY₁.orderTop = ((0 : ℤ) : WithTop ℤ) := by
      rw [biY₁, cConstRingHom, HahnSeries.C_apply,
        HahnSeries.orderTop_single W.isUnit_formalY.ne_zero]
    have hlt : W.biY₁.orderTop < (W.formalYThree - W.biY₁).orderTop := by
      rw [hbiord]
      exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (0 : ℤ) < 1))
        W.orderTop_formalYThree_sub_biY₁
    refine HahnSeries.isUnit_of_isUnit_leadingCoeff_AddUnitOrder ?_ (AddGroup.isAddUnit _)
    have hlc : W.formalYThree.leadingCoeff = W.formalY := by
      rw [show W.formalYThree = W.biY₁ + (W.formalYThree - W.biY₁) by ring,
        HahnSeries.leadingCoeff_add_eq_left hlt, biY₁, cConstRingHom, HahnSeries.C_apply,
        HahnSeries.leadingCoeff_of_single]
    rw [hlc]
    exact W.isUnit_formalY

end WeierstrassCurve
