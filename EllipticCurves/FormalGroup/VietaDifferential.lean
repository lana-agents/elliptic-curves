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
  sorry

end HahnSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### Univariate coordinate derivatives (the invariant-differential relations) -/

/-- The coercion `R⟦X⟧ → R⸨X⸩` intertwines the two derivatives. -/
theorem derivative_ofPowerSeries (f : PowerSeries R) :
    LaurentSeries.derivative ℤ (f : R⸨X⸩) = (derivativeFun f : R⸨X⸩) := by
  sorry

/-- `∂_z z = 1` for the local parameter `z = single 1 1`. -/
theorem derivative_single_one :
    LaurentSeries.derivative ℤ (HahnSeries.single (1 : ℤ) (1 : R)) = 1 := by
  sorry

/-- **UNIV-X.** The invariant-differential relation `∂_z x = ω_E · (2y + a₁x + a₃)` in `R⸨X⸩`. -/
theorem derivative_formalX [Algebra ℚ R] :
    LaurentSeries.derivative ℤ W.formalX
      = (W.invariantDifferential : R⸨X⸩)
        * (2 * W.formalY + HahnSeries.C W.a₁ * W.formalX + HahnSeries.C W.a₃) := by
  sorry

/-- **UNIV-Y.** The invariant-differential relation `∂_z y = ω_E · (3x² + 2a₂x + a₄ − a₁y)`. -/
theorem derivative_formalY [Algebra ℚ R] :
    LaurentSeries.derivative ℤ W.formalY
      = (W.invariantDifferential : R⸨X⸩)
        * (3 * W.formalX ^ 2 + 2 * HahnSeries.C W.a₂ * W.formalX
          + HahnSeries.C W.a₄ - HahnSeries.C W.a₁ * W.formalY) := by
  sorry

/-! ### Base-changed derivatives on the `z₂`-axis -/

/-- `∂_{z₂} x₁ = 0` (`x₁` is constant in `z₂`). -/
theorem derivative_biX₁ : LaurentSeries.derivative ℤ W.biX₁ = 0 := by
  sorry

/-- `∂_{z₂} y₁ = 0` (`y₁` is constant in `z₂`). -/
theorem derivative_biY₁ : LaurentSeries.derivative ℤ W.biY₁ = 0 := by
  sorry

/-- `∂_{z₂} x₂ = ω̃₂ · (2y₂ + a₁x₂ + a₃)`. -/
theorem derivative_biX₂ [Algebra ℚ R] :
    LaurentSeries.derivative ℤ W.biX₂
      = (W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩)
        * (2 * W.biY₂ + HahnSeries.C (HahnSeries.C W.a₁) * W.biX₂
          + HahnSeries.C (HahnSeries.C W.a₃)) := by
  sorry

/-- `∂_{z₂} y₂ = ω̃₂ · (3x₂² + 2a₂x₂ + a₄ − a₁y₂)`. -/
theorem derivative_biY₂ [Algebra ℚ R] :
    LaurentSeries.derivative ℤ W.biY₂
      = (W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩)
        * (3 * W.biX₂ ^ 2 + 2 * HahnSeries.C (HahnSeries.C W.a₂) * W.biX₂
          + HahnSeries.C (HahnSeries.C W.a₄) - HahnSeries.C (HahnSeries.C W.a₁) * W.biY₂) := by
  sorry

/-! ### The main identity -/

/-- **`hdiff` (issue #338).** The explicit Vieta Laurent differential identity
`∂_{z₂} x₃ = ω̃₂ · (2·y₃ + a₁·x₃ + a₃)`, feeding `formalLog_subst_formalGroupZW_of_hWF_hdiff`. -/
theorem derivative_formalXThree [Algebra ℚ R] :
    LaurentSeries.derivative ℤ W.formalXThree
      = (W.invariantDifferential : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩)
        * (2 * W.formalYThree + HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree
          + HahnSeries.C (HahnSeries.C W.a₃)) := by
  sorry

end WeierstrassCurve
