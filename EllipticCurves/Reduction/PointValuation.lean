/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Valuation of affine point coordinates over a DVR and the `E₁(K)` predicate

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and residue field `k`, and let
`W : WeierstrassCurve K` be given by an **integral** Weierstrass equation (`IsIntegral R W`, so all
coefficients `aᵢ` lie in `R`).  Following Silverman (AEC VII.2 Prop 2.1) we analyse the valuations
of the coordinates of an affine point `P = (x, y)` on `W`, and define the predicate that `P`
**reduces to the origin** — the eventual membership relation of the kernel of reduction `E₁(K)`.

We use the multiplicative `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`-valued valuation
`valuation K (maximalIdeal R)` (exactly the one used by Mathlib's `EllipticCurve/Reduction.lean`),
where for `r : R` one has `v (algebraMap R K r) ≤ 1`, and `v z < 1` means `z` reduces into the
maximal ideal `𝔪`.

## Main results

* `valuation_pow_two_eq_pow_three_of_one_lt` — the **Newton-polygon dichotomy**: if `P = (x, y)`
  lies on an integral `W` and `x` has a pole (`1 < v x`), then `1 < v y` and `(v y) ^ 2 = (v x) ^ 3`
  (i.e. `2·ord y = 3·ord x`).
* `valuation_lt_of_one_lt` — in the pole regime `v x < v y`, hence the local parameter `z = -x/y`
  has `v (-x/y) < 1` (`valuation_neg_x_div_y_lt_one`), i.e. `z` reduces into `𝔪`.
* `WeierstrassCurve.ReducesToZero` — the predicate `P ∈ E₁(K)` (`P` reduces to the origin): either
  `P = 0`, or `P = some x y` with `1 < v x`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.1, VII.2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum WithZero Multiplicative

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Valuations of the coefficients of an integral model -/

/-- Every coefficient of an integral Weierstrass model has valuation `≤ 1`. -/
theorem valuation_a₁_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.a₁ ≤ 1 := by
  rw [← integralModel_a₁_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₂_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.a₂ ≤ 1 := by
  rw [← integralModel_a₂_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₃_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.a₃ ≤ 1 := by
  rw [← integralModel_a₃_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₄_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.a₄ ≤ 1 := by
  rw [← integralModel_a₄_eq R W]; exact valuation_le_one (maximalIdeal R) _

theorem valuation_a₆_le_one (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.a₆ ≤ 1 := by
  rw [← integralModel_a₆_eq R W]; exact valuation_le_one (maximalIdeal R) _

/-! ### The Newton-polygon dichotomy for a point with a pole -/

/-- **Newton-polygon dichotomy (Silverman AEC VII.2 Prop 2.1).**  If `P = (x, y)` lies on an
integral Weierstrass curve `W` and the `x`-coordinate has a pole (`1 < v x`), then the
`y`-coordinate also has a pole and `(v y) ^ 2 = (v x) ^ 3` — the multiplicative form of
`2·ord y = 3·ord x`.

The proof takes the valuation of both sides of the Weierstrass equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`.  Since `1 < v x` and every `v aᵢ ≤ 1`, the right side is
dominated by `x³` (all other terms have strictly smaller valuation), so `v (RHS) = (v x) ^ 3`.  On
the left, first show `1 < v y` (else `v (LHS) ≤ v x < (v x)^3`), then a trichotomy on `(v y)^2`
versus the valuation of `a₁xy + a₃y` shows `(v y)^2` is the strictly dominant term and equals
`(v x)^3`. -/
theorem valuation_pow_two_eq_pow_three_of_one_lt (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} (heqn : W.toAffine.Equation x y) (hx : 1 < valuation K (maximalIdeal R) x) :
    1 < valuation K (maximalIdeal R) y ∧
      (valuation K (maximalIdeal R) y) ^ 2 = (valuation K (maximalIdeal R) x) ^ 3 := by
  -- Abbreviations for the valuation and the coordinate/coefficient valuations.
  set v : Valuation K ℤᵐ⁰ := valuation K (maximalIdeal R) with hv
  set a : ℤᵐ⁰ := v x with ha
  set b : ℤᵐ⁰ := v y with hb
  have ha1 : v W.a₁ ≤ 1 := valuation_a₁_le_one R W
  have ha2 : v W.a₂ ≤ 1 := valuation_a₂_le_one R W
  have ha3 : v W.a₃ ≤ 1 := valuation_a₃_le_one R W
  have ha4 : v W.a₄ ≤ 1 := valuation_a₄_le_one R W
  have ha6 : v W.a₆ ≤ 1 := valuation_a₆_le_one R W
  -- The Weierstrass equation, valuation of both sides.
  rw [Affine.equation_iff] at heqn
  -- Powers of `a = v x` are increasing since `1 < a`.
  have ha0 : (0 : ℤᵐ⁰) < a := zero_lt_one.trans hx
  have h1a3 : (1 : ℤᵐ⁰) < a ^ 3 := one_lt_pow₀ hx (by norm_num)
  have ha2a3 : a ^ 2 < a ^ 3 := pow_lt_pow_right₀ hx (by norm_num)
  have haa3 : a < a ^ 3 := by
    calc a = a ^ 1 := (pow_one a).symm
      _ < a ^ 3 := pow_lt_pow_right₀ hx (by norm_num)
  -- `v (RHS) = a ^ 3`: the term `x ^ 3` strictly dominates.
  have hva2x2 : v (W.a₂ * x ^ 2) < a ^ 3 := by
    rw [map_mul, map_pow]
    calc v W.a₂ * a ^ 2 ≤ 1 * a ^ 2 := by gcongr
      _ = a ^ 2 := one_mul _
      _ < a ^ 3 := ha2a3
  have hva4x : v (W.a₄ * x) < a ^ 3 := by
    rw [map_mul]
    calc v W.a₄ * a ≤ 1 * a := by gcongr
      _ = a := one_mul _
      _ < a ^ 3 := haa3
  have hva6 : v W.a₆ < a ^ 3 := lt_of_le_of_lt ha6 h1a3
  have hvx3 : v (x ^ 3) = a ^ 3 := by rw [map_pow]
  have hRHS : v (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = a ^ 3 := by
    have hgroup : x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
        = x ^ 3 + (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by ring
    have htail : v (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) < a ^ 3 :=
      Valuation.map_add_lt _ (Valuation.map_add_lt _ hva2x2 hva4x) hva6
    rw [hgroup, Valuation.map_add_eq_of_lt_left _ (hvx3.symm ▸ htail), hvx3]
  -- Step 1: `1 < b`.  Otherwise every term of the LHS has valuation `≤ a < a ^ 3`.
  have hb1 : 1 < b := by
    by_contra hcon
    rw [not_lt] at hcon  -- hcon : b ≤ 1
    have hvy2 : v (y ^ 2) < a ^ 3 := by
      rw [map_pow]
      calc b ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ zero_le hcon 2
        _ = 1 := one_pow 2
        _ < a ^ 3 := h1a3
    have hva1xy : v (W.a₁ * x * y) < a ^ 3 := by
      rw [map_mul, map_mul]
      calc v W.a₁ * a * b ≤ 1 * a * 1 := by gcongr
        _ = a := by rw [one_mul, mul_one]
        _ < a ^ 3 := haa3
    have hva3y : v (W.a₃ * y) < a ^ 3 := by
      rw [map_mul]
      calc v W.a₃ * b ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
        _ < a ^ 3 := h1a3
    have hLHS : v (y ^ 2 + W.a₁ * x * y + W.a₃ * y) < a ^ 3 :=
      Valuation.map_add_lt _ (Valuation.map_add_lt _ hvy2 hva1xy) hva3y
    rw [heqn, hRHS] at hLHS
    exact lt_irrefl _ hLHS
  -- Step 2: `(v y)^2 = (v x)^3`.  Trichotomy on `b ^ 2` versus `v (a₁xy + a₃y)`.
  refine ⟨hb1, ?_⟩
  -- `v (a₁xy) ≤ a * b` and `v (a₃y) ≤ b`.
  have hva1xy_le : v (W.a₁ * x * y) ≤ a * b := by
    rw [map_mul, map_mul]
    calc v W.a₁ * a * b ≤ 1 * a * b := by gcongr
      _ = a * b := by rw [one_mul]
  have hva3y_le : v (W.a₃ * y) ≤ b := by
    rw [map_mul]
    calc v W.a₃ * b ≤ 1 * b := by gcongr
      _ = b := one_mul _
  -- Let `T = a₁xy + a₃y`; then `v T ≤ a * b` and `v (LHS) = v (y² + T)`.
  set T : K := W.a₁ * x * y + W.a₃ * y with hT
  have hbab : b ≤ a * b := by
    calc b = 1 * b := (one_mul _).symm
      _ ≤ a * b := mul_le_mul_left hx.le b
  have hvT : v T ≤ a * b :=
    le_trans (Valuation.map_add _ _ _) (max_le hva1xy_le (le_trans hva3y_le hbab))
  -- `v (LHS)` in terms of `b ^ 2` and `v T`.
  have hLHS_eq : v (y ^ 2 + T) = a ^ 3 := by
    have : y ^ 2 + W.a₁ * x * y + W.a₃ * y = y ^ 2 + T := by rw [hT]; ring
    rw [← this, heqn, hRHS]
  -- Trichotomy on `b ^ 2` vs `v T`.
  rcases lt_trichotomy (v T) (b ^ 2) with hlt | heq | hgt
  · -- `v T < b ^ 2`: `y²` dominates, so `v (LHS) = b ^ 2 = a ^ 3`.
    have : v (y ^ 2 + T) = b ^ 2 := by
      rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_pow]; exact hlt), map_pow]
    rw [hLHS_eq] at this
    exact this.symm
  · -- `v T = b ^ 2`: then `a ^ 3 = v (LHS) ≤ b ^ 2` and `b ^ 2 = v T ≤ a * b ⟹ b ≤ a`,
    -- giving `a ^ 3 ≤ b ^ 2 ≤ a ^ 2 < a ^ 3`, contradiction.
    exfalso
    have hb2ab : b ^ 2 ≤ a * b := by rw [← heq]; exact hvT
    have hb0 : (0 : ℤᵐ⁰) < b := zero_lt_one.trans hb1
    have hba : b ≤ a := by
      rw [pow_two] at hb2ab
      exact (mul_le_mul_iff_left₀ hb0).mp hb2ab
    have hle : a ^ 3 ≤ b ^ 2 := by
      have hmax : v (y ^ 2 + T) ≤ b ^ 2 := by
        refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (le_of_eq heq))
        rw [map_pow]
      rw [hLHS_eq] at hmax; exact hmax
    have hb2a2 : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ zero_le hba 2
    exact absurd (lt_of_le_of_lt (le_trans hle hb2a2) ha2a3) (lt_irrefl _)
  · -- `b ^ 2 < v T`: then `v (LHS) = v T = a ^ 3 ≤ a * b`, so `a ^ 2 ≤ b`, hence
    -- `a ^ 4 ≤ b ^ 2 < a ^ 3`, contradicting `a ^ 3 < a ^ 4`.
    exfalso
    have hLHS_T : v (y ^ 2 + T) = v T := by
      rw [Valuation.map_add_eq_of_lt_right _ (by rw [map_pow]; exact hgt)]
    rw [hLHS_eq] at hLHS_T  -- hLHS_T : a ^ 3 = v T
    have ha3ab : a ^ 3 ≤ a * b := by rw [hLHS_T]; exact hvT
    have hb2a3 : b ^ 2 < a ^ 3 := by rw [hLHS_T]; exact hgt
    have ha2b : a ^ 2 ≤ b := by
      have h : a * a ^ 2 ≤ a * b := by rw [← pow_succ']; exact ha3ab
      exact (mul_le_mul_iff_right₀ ha0).mp h
    have ha4b2 : a ^ 4 ≤ b ^ 2 := by
      calc a ^ 4 = (a ^ 2) ^ 2 := by rw [← pow_mul]
        _ ≤ b ^ 2 := pow_le_pow_left₀ zero_le ha2b 2
    have ha4a3 : a ^ 4 < a ^ 3 := lt_of_le_of_lt ha4b2 hb2a3
    have ha3a4 : a ^ 3 < a ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    exact absurd ha4a3 (not_lt.mpr (le_of_lt ha3a4))

/-- In the pole regime `1 < v x`, the `y`-pole strictly dominates: `v x < v y`. -/
theorem valuation_lt_of_one_lt (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} (heqn : W.toAffine.Equation x y) (hx : 1 < valuation K (maximalIdeal R) x) :
    valuation K (maximalIdeal R) x < valuation K (maximalIdeal R) y := by
  obtain ⟨hb1, hrel⟩ := valuation_pow_two_eq_pow_three_of_one_lt R W heqn hx
  set a : ℤᵐ⁰ := valuation K (maximalIdeal R) x
  set b : ℤᵐ⁰ := valuation K (maximalIdeal R) y
  -- `b ^ 2 = a ^ 3 > a ^ 2`, so `b > a`.
  have ha2a3 : a ^ 2 < a ^ 3 := pow_lt_pow_right₀ hx (by norm_num)
  have hab : a ^ 2 < b ^ 2 := by rw [hrel]; exact ha2a3
  exact lt_of_pow_lt_pow_left₀ 2 zero_le hab

/-- The local parameter `z = -x/y` of a point with a pole reduces into the maximal ideal:
`v (-x / y) < 1`. -/
theorem valuation_neg_x_div_y_lt_one (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} (heqn : W.toAffine.Equation x y) (hx : 1 < valuation K (maximalIdeal R) x) :
    valuation K (maximalIdeal R) (-x / y) < 1 := by
  have hlt := valuation_lt_of_one_lt R W heqn hx
  set v : Valuation K ℤᵐ⁰ := valuation K (maximalIdeal R) with hv
  have hvx_pos : 0 < v x := lt_trans one_pos hx
  have hvy_pos : 0 < v y := lt_trans hvx_pos hlt
  rw [v.map_div, v.map_neg]
  exact (div_lt_one₀ hvy_pos).mpr hlt

/-! ### The `E₁(K)` predicate: points reducing to the origin -/

/-- A point `P` of `W` over `K` **reduces to the origin** (the eventual `E₁(K)` membership): either
`P = 0`, or `P = some x y` whose `x`-coordinate has a pole (`1 < v x`).  For a point on an integral
model this is equivalent to reducing to `Õ` on the reduced curve (Silverman AEC VII.2). -/
def ReducesToZero (W : WeierstrassCurve K) [IsIntegral R W] : W.toAffine.Point → Prop
  | .zero => True
  | .some x _ _ => 1 < valuation K (maximalIdeal R) x

@[simp] theorem reducesToZero_zero (W : WeierstrassCurve K) [IsIntegral R W] :
    ReducesToZero R W .zero := trivial

theorem reducesToZero_some_iff (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} {h : W.toAffine.Nonsingular x y} :
    ReducesToZero R W (.some x y h) ↔ 1 < valuation K (maximalIdeal R) x := Iff.rfl

/-- An integral point (`v x ≤ 1`) does not reduce to the origin. -/
theorem not_reducesToZero_of_valuation_le_one (W : WeierstrassCurve K) [IsIntegral R W]
    {x y : K} {h : W.toAffine.Nonsingular x y} (hx : valuation K (maximalIdeal R) x ≤ 1) :
    ¬ ReducesToZero R W (.some x y h) := by
  rw [reducesToZero_some_iff]; exact not_lt.mpr hx

end WeierstrassCurve
