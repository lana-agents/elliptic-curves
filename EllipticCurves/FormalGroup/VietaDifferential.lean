/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.LaurentDerivation
import EllipticCurves.FormalGroup.InvariantDifferentialInvariance
import EllipticCurves.FormalGroup.AdditionLaw

/-!
# The explicit Vieta Laurent differential identity `hdiff` (issue #338, feeding #315's `(★)`)

This file proves the outer-variable (`z₂`) derivative of the third `x`-coordinate `x₃` of the
Weierstrass addition law, in the explicit Laurent coordinates:
`∂_{z₂} x₃ = ω̃₂ · (2·y₃ + a₁·x₃ + a₃)`,
the hypothesis `hdiff` carried by the merged consumer
`WeierstrassCurve.formalLog_subst_formalGroupZW_of_hWF_hdiff`
(`EllipticCurves.FormalGroup.LogAdditivityStarClose`, PR #62).  Here `ω̃₂` is the outer invariant
differential `(ω_E : R⸨X⸩).map HahnSeries.C`.

This is the classical translation-invariance of the invariant differential (Silverman AEC IV.4,
Thm 4.2; IV.5, Prop 5.2), rendered as a mechanical computation on the Vieta addition formulas:
after substituting the univariate coordinate relation (`∂ x = ω · (2y + a₁x + a₃)`, itself the
pole-cleared invariant-differential identity `invariantDifferential_mul_clear`) it reduces to a pure
algebraic identity of the addition formulas modulo the point-on-curve relations, cleared by the unit
`x₂ − x₁` (the same Vieta division as `weierstrass_thirdInt`).

## References
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4 Thm 4.2, IV.5.2.
-/

open scoped LaurentSeries
open PowerSeries (derivativeFun)

namespace HahnSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The outer Laurent derivative commutes with a coefficientwise ring-hom map. -/
theorem derivative_mapRingHom (g : R →+* S) (f : R⸨X⸩) :
    LaurentSeries.derivative ℤ (mapRingHom g f)
      = mapRingHom g (LaurentSeries.derivative ℤ f) := by
  rw [← HahnSeries.coeff_inj]
  funext n
  rw [LaurentSeries.coeff_derivative, mapRingHom_apply, HahnSeries.map_coeff, mapRingHom_apply,
    HahnSeries.map_coeff, LaurentSeries.coeff_derivative, map_zsmul]

end HahnSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### Univariate coordinate derivatives (the invariant-differential relations) -/

/-- The coercion `R⟦X⟧ → R⸨X⸩` intertwines the two derivatives. -/
theorem derivative_ofPowerSeries (f : PowerSeries R) :
    LaurentSeries.derivative ℤ (f : R⸨X⸩) = (derivativeFun f : R⸨X⸩) := by
  rw [← HahnSeries.coeff_inj]
  funext n
  rw [LaurentSeries.coeff_derivative]
  rcases lt_or_ge n 0 with hn | hn
  · rw [coe_powerSeries_coeff_of_neg _ hn]
    rcases lt_or_ge (n + 1) 0 with hn1 | hn1
    · rw [coe_powerSeries_coeff_of_neg _ hn1, smul_zero]
    · obtain rfl : n = -1 := by omega
      simp
  · lift n to ℕ using hn with m
    have hidx : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hidx, LaurentSeries.coeff_coe_powerSeries, LaurentSeries.coeff_coe_powerSeries,
      PowerSeries.coeff_derivativeFun, zsmul_eq_mul]
    push_cast
    ring

/-- `∂_z z = 1` for the local parameter `z = single 1 1`. -/
theorem derivative_single_one :
    LaurentSeries.derivative ℤ (HahnSeries.single (1 : ℤ) (1 : R)) = 1 := by
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_single, Ring.choose_one_right]
  simp

/-- **UNIV-X.** The invariant-differential relation `∂_z x = ω_E · (2y + a₁x + a₃)` in `R⸨X⸩`. -/
theorem derivative_formalX [Algebra ℚ R] :
    LaurentSeries.derivative ℤ W.formalX
      = (W.invariantDifferential : R⸨X⸩)
        * (2 * W.formalY + HahnSeries.C W.a₁ * W.formalX + HahnSeries.C W.a₃) := by
  have hx : W.formalX * (W.formalW : R⸨X⸩) = HahnSeries.single (1 : ℤ) 1 :=
    W.formalX_mul_coe_formalW
  have hy : W.formalY * (W.formalW : R⸨X⸩) = -1 := W.formalY_mul_coe_formalW
  have hDw : LaurentSeries.derivative ℤ (W.formalW : R⸨X⸩)
      = (derivativeFun W.formalW : R⸨X⸩) := derivative_ofPowerSeries W.formalW
  have hdx : W.formalX * LaurentSeries.derivative ℤ (W.formalW : R⸨X⸩)
      + LaurentSeries.derivative ℤ W.formalX * (W.formalW : R⸨X⸩) = 1 := by
    have h := congrArg (LaurentSeries.derivative ℤ) hx
    rwa [LaurentSeries.derivative_mul, derivative_single_one] at h
  have hΩ : (W.invariantDifferential : R⸨X⸩)
        * ((W.formalW : R⸨X⸩)
          * (-2 + HahnSeries.C W.a₁ * HahnSeries.single (1 : ℤ) 1
            + HahnSeries.C W.a₃ * (W.formalW : R⸨X⸩)))
      = (W.formalW : R⸨X⸩)
        - HahnSeries.single (1 : ℤ) 1 * LaurentSeries.derivative ℤ (W.formalW : R⸨X⸩) := by
    have h := congrArg (HahnSeries.ofPowerSeries ℤ R) W.invariantDifferential_mul_clear
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X] at h
    rw [hDw]
    exact h
  have hGw : (2 * W.formalY + HahnSeries.C W.a₁ * W.formalX + HahnSeries.C W.a₃)
        * (W.formalW : R⸨X⸩)
      = -2 + HahnSeries.C W.a₁ * HahnSeries.single (1 : ℤ) 1
        + HahnSeries.C W.a₃ * (W.formalW : R⸨X⸩) := by
    linear_combination 2 * hy + HahnSeries.C W.a₁ * hx
  have hDxw : LaurentSeries.derivative ℤ W.formalX * (W.formalW : R⸨X⸩)
      = 1 - W.formalX * LaurentSeries.derivative ℤ (W.formalW : R⸨X⸩) := by
    linear_combination hdx
  refine ((W.isUnit_coe_formalW.pow 2).mul_left_inj).mp ?_
  have hLHS : LaurentSeries.derivative ℤ W.formalX * (W.formalW : R⸨X⸩) ^ 2
      = (W.formalW : R⸨X⸩)
        - HahnSeries.single (1 : ℤ) 1 * LaurentSeries.derivative ℤ (W.formalW : R⸨X⸩) := by
    linear_combination (W.formalW : R⸨X⸩) * hDxw
      - LaurentSeries.derivative ℤ (W.formalW : R⸨X⸩) * hx
  have hRHS : (W.invariantDifferential : R⸨X⸩)
        * (2 * W.formalY + HahnSeries.C W.a₁ * W.formalX + HahnSeries.C W.a₃)
        * (W.formalW : R⸨X⸩) ^ 2
      = (W.formalW : R⸨X⸩)
        - HahnSeries.single (1 : ℤ) 1 * LaurentSeries.derivative ℤ (W.formalW : R⸨X⸩) := by
    linear_combination (W.invariantDifferential : R⸨X⸩) * (W.formalW : R⸨X⸩) * hGw + hΩ
  rw [hLHS, hRHS]

/-- **UNIV-Y.** The invariant-differential relation `∂_z y = ω_E · (3x² + 2a₂x + a₄ − a₁y)`. -/
theorem derivative_formalY [Algebra ℚ R] :
    LaurentSeries.derivative ℤ W.formalY
      = (W.invariantDifferential : R⸨X⸩)
        * (3 * W.formalX ^ 2 + 2 * HahnSeries.C W.a₂ * W.formalX
          + HahnSeries.C W.a₄ - HahnSeries.C W.a₁ * W.formalY) := by
  have hdenPS : IsUnit ((-2 + PowerSeries.C W.a₁ * PowerSeries.X
      + PowerSeries.C W.a₃ * W.formalW : PowerSeries R)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp only [map_add, map_neg, map_mul, map_ofNat, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, W.constantCoeff_formalW, mul_zero, add_zero]
    rw [← negTwoUnit_val R]
    exact (negTwoUnit R).isUnit
  have hden : IsUnit (-2 + HahnSeries.C W.a₁ * HahnSeries.single (1 : ℤ) 1
      + HahnSeries.C W.a₃ * (W.formalW : R⸨X⸩)) := by
    have hu := hdenPS.map (HahnSeries.ofPowerSeries ℤ R)
    simpa only [map_add, map_neg, map_mul, map_ofNat, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X] using hu
  have hGw : (2 * W.formalY + HahnSeries.C W.a₁ * W.formalX + HahnSeries.C W.a₃)
        * (W.formalW : R⸨X⸩)
      = -2 + HahnSeries.C W.a₁ * HahnSeries.single (1 : ℤ) 1
        + HahnSeries.C W.a₃ * (W.formalW : R⸨X⸩) := by
    linear_combination 2 * W.formalY_mul_coe_formalW
      + HahnSeries.C W.a₁ * W.formalX_mul_coe_formalW
  have hGwUnit : IsUnit ((2 * W.formalY + HahnSeries.C W.a₁ * W.formalX + HahnSeries.C W.a₃)
      * (W.formalW : R⸨X⸩)) := by rw [hGw]; exact hden
  have hdW_clean : (2 * W.formalY + HahnSeries.C W.a₁ * W.formalX + HahnSeries.C W.a₃)
        * LaurentSeries.derivative ℤ W.formalY
      = (3 * W.formalX ^ 2 + 2 * HahnSeries.C W.a₂ * W.formalX + HahnSeries.C W.a₄
          - HahnSeries.C W.a₁ * W.formalY) * LaurentSeries.derivative ℤ W.formalX := by
    have hW' : W.formalY * W.formalY + HahnSeries.C W.a₁ * W.formalX * W.formalY
          + HahnSeries.C W.a₃ * W.formalY
        = W.formalX * W.formalX * W.formalX + HahnSeries.C W.a₂ * (W.formalX * W.formalX)
          + HahnSeries.C W.a₄ * W.formalX + HahnSeries.C W.a₆ := by
      linear_combination W.formalX_formalY_weierstrass
    have hdW := congrArg (LaurentSeries.derivative ℤ) hW'
    simp only [LaurentSeries.derivative_mul, map_add, LaurentSeries.derivative_C,
      zero_mul, add_zero] at hdW
    linear_combination hdW
  rw [W.derivative_formalX] at hdW_clean
  refine (hGwUnit.mul_right_inj).mp ?_
  linear_combination (W.formalW : R⸨X⸩) * hdW_clean

/-! ### Base-changed derivatives on the `z₂`-axis -/

/-- `∂_{z₂} x₁ = 0` (`x₁` is constant in `z₂`). -/
theorem derivative_biX₁ : LaurentSeries.derivative ℤ W.biX₁ = 0 :=
  LaurentSeries.derivative_C W.formalX

/-- `∂_{z₂} y₁ = 0` (`y₁` is constant in `z₂`). -/
theorem derivative_biY₁ : LaurentSeries.derivative ℤ W.biY₁ = 0 :=
  LaurentSeries.derivative_C W.formalY

/-- `∂_{z₂} x₂ = ω̃₂ · (2y₂ + a₁x₂ + a₃)`. -/
theorem derivative_biX₂ [Algebra ℚ R] :
    LaurentSeries.derivative ℤ W.biX₂
      = (W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩)
        * (2 * W.biY₂ + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂
          + HahnSeries.C (HahnSeries.C W.a₃)) := by
  have h : LaurentSeries.derivative ℤ W.biX₂
      = cLaurentRingHom R (LaurentSeries.derivative ℤ W.formalX) :=
    HahnSeries.derivative_mapRingHom (HahnSeries.C : R →+* R⸨X⸩) W.formalX
  rw [h, W.derivative_formalX]
  simp only [map_mul, map_add, map_ofNat, cLaurentRingHom_C]
  rfl

/-- `∂_{z₂} y₂ = ω̃₂ · (3x₂² + 2a₂x₂ + a₄ − a₁y₂)`. -/
theorem derivative_biY₂ [Algebra ℚ R] :
    LaurentSeries.derivative ℤ W.biY₂
      = (W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩)
        * (3 * W.biX₂ ^ 2 + 2 * HahnSeries.C (HahnSeries.C W.a₂) * W.biX₂
          + HahnSeries.C (HahnSeries.C W.a₄) - HahnSeries.C (HahnSeries.C W.a₁) * W.biY₂) := by
  have h : LaurentSeries.derivative ℤ W.biY₂
      = cLaurentRingHom R (LaurentSeries.derivative ℤ W.formalY) :=
    HahnSeries.derivative_mapRingHom (HahnSeries.C : R →+* R⸨X⸩) W.formalY
  rw [h, W.derivative_formalY]
  simp only [map_mul, map_add, map_sub, map_ofNat, map_pow, cLaurentRingHom_C]
  rfl

/-! ### The main identity -/

/-- **`hdiff` (issue #338).** The explicit Vieta Laurent differential identity
`∂_{z₂} x₃ = ω̃₂ · (2·y₃ + a₁·x₃ + a₃)`, feeding `formalLog_subst_formalGroupZW_of_hWF_hdiff`. -/
theorem derivative_formalXThree [Algebra ℚ R] :
    LaurentSeries.derivative ℤ W.formalXThree
      = (W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩)
        * (2 * W.formalYThree + HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree
          + HahnSeries.C (HahnSeries.C W.a₃)) := by
  -- (a) derivative of `x₃`.
  have hx3 : LaurentSeries.derivative ℤ W.formalXThree
      = (2 * W.formalLambda + HahnSeries.C (HahnSeries.C W.a₁))
          * LaurentSeries.derivative ℤ W.formalLambda
        - LaurentSeries.derivative ℤ W.biX₂ := by
    have hxeq : W.formalXThree
        = W.formalLambda * W.formalLambda
          + HahnSeries.C (HahnSeries.C W.a₁) * W.formalLambda
          - HahnSeries.C (HahnSeries.C W.a₂) - W.biX₁ - W.biX₂ := by
      unfold formalXThree; ring
    rw [hxeq]
    simp only [map_sub, map_add, LaurentSeries.derivative_mul, LaurentSeries.derivative_C,
      W.derivative_biX₁, zero_mul, add_zero, sub_zero]
    ring
  -- (b) differentiate the slope relation `λ·(x₂ − x₁) = y₂ − y₁`.
  have hlam : LaurentSeries.derivative ℤ W.formalLambda * (W.biX₂ - W.biX₁)
      = LaurentSeries.derivative ℤ W.biY₂
        - W.formalLambda * LaurentSeries.derivative ℤ W.biX₂ := by
    have h := congrArg (LaurentSeries.derivative ℤ) W.formalLambda_mul_biX_sub
    rw [LaurentSeries.derivative_mul, map_sub, map_sub, W.derivative_biX₁,
      W.derivative_biY₁] at h
    linear_combination h
  -- (c) collect: `u · ∂x₃ = ω̃₂ · P` with the substituted derivatives.
  have eqA : (W.biX₂ - W.biX₁) * LaurentSeries.derivative ℤ W.formalXThree
      = ((W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩))
        * ((2 * W.formalLambda + HahnSeries.C (HahnSeries.C W.a₁))
            * (3 * W.biX₂ ^ 2 + 2 * HahnSeries.C (HahnSeries.C W.a₂) * W.biX₂
                + HahnSeries.C (HahnSeries.C W.a₄) - HahnSeries.C (HahnSeries.C W.a₁) * W.biY₂
              - W.formalLambda * (2 * W.biY₂ + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂
                + HahnSeries.C (HahnSeries.C W.a₃)))
          - (W.biX₂ - W.biX₁) * (2 * W.biY₂ + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂
              + HahnSeries.C (HahnSeries.C W.a₃))) := by
    rw [hx3]
    linear_combination
      (2 * W.formalLambda + HahnSeries.C (HahnSeries.C W.a₁)) * hlam
      + (-(W.biX₂ - W.biX₁)
          - (2 * W.formalLambda + HahnSeries.C (HahnSeries.C W.a₁)) * W.formalLambda)
        * W.derivative_biX₂
      + (2 * W.formalLambda + HahnSeries.C (HahnSeries.C W.a₁)) * W.derivative_biY₂
  -- (d) the Vieta division: `P = u · K`, the algebraic core cleared by the unit `x₂ − x₁`.
  have hP : (2 * W.formalLambda + HahnSeries.C (HahnSeries.C W.a₁))
          * (3 * W.biX₂ ^ 2 + 2 * HahnSeries.C (HahnSeries.C W.a₂) * W.biX₂
              + HahnSeries.C (HahnSeries.C W.a₄) - HahnSeries.C (HahnSeries.C W.a₁) * W.biY₂
            - W.formalLambda * (2 * W.biY₂ + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂
              + HahnSeries.C (HahnSeries.C W.a₃)))
        - (W.biX₂ - W.biX₁) * (2 * W.biY₂ + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂
            + HahnSeries.C (HahnSeries.C W.a₃))
      = (W.biX₂ - W.biX₁)
        * (2 * W.formalYThree + HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree
          + HahnSeries.C (HahnSeries.C W.a₃)) := by
    refine (W.isUnit_biX₂_sub_biX₁.mul_right_inj).mp ?_
    have h1 := W.biX₁_biY₁_weierstrass
    have h2 := W.biX₂_biY₂_weierstrass
    rw [W.biY₁_eq] at h1
    rw [W.biY₂_eq] at h2
    rw [W.biY₂_eq]
    simp only [formalYThree, formalXThree]
    linear_combination (2 * W.formalLambda + HahnSeries.C (HahnSeries.C W.a₁)) * h1
      - (2 * W.formalLambda + HahnSeries.C (HahnSeries.C W.a₁)) * h2
  -- Assemble by cancelling the unit `x₂ − x₁`.
  refine (W.isUnit_biX₂_sub_biX₁.mul_right_inj).mp ?_
  rw [eqA, hP]
  ring

end WeierstrassCurve
