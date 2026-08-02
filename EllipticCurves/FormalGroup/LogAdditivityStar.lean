/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FormalGroup.InvariantDifferentialInvariance
import EllipticCurves.FormalGroup.GenuineLawTransfer
import EllipticCurves.FormalGroup.LaurentDerivation
import EllipticCurves.FormalGroup.WThreeFunctionalEq

/-!
# Route B towards the invariant-differential invariance `(★)` (`hstar`) of issue #315

This file carries the reduction of the invariant-differential invariance
`(★)  (ω_E ∘ F)·∂_{z₂}F = ω_E(z₂)`   (`hstar`)
into the double Laurent ring `(R⸨X⸩)⸨X⸩` via the injective ring homomorphism
`HahnSeries.embedDoubleLaurent`, where the pole-carrying cofactor of the local reduction becomes a
unit and can be cancelled.  See `EllipticCurves.FormalGroup.InvariantDifferentialInvariance` for the
local reduction `Eq.A`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4, Theorem 4.2; IV.5,
  Proposition 5.2.
-/

open scoped LaurentSeries

namespace HahnSeries

variable {R : Type*} [CommRing R]

/-- **Injectivity of the double-Laurent writer.**  `embedDoubleLaurent` has the read-back map
`ofDoubleLaurent` as a left inverse (`ofDoubleLaurent_embedDoubleLaurent`), hence is injective. -/
theorem embedDoubleLaurent_injective :
    Function.Injective
      (embedDoubleLaurent : MvPowerSeries (Fin 2) R → (R⸨X⸩)⸨X⸩) := by
  intro a b h
  have h2 := congrArg ofDoubleLaurent h
  rwa [ofDoubleLaurent_embedDoubleLaurent, ofDoubleLaurent_embedDoubleLaurent] at h2

end HahnSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### Laurent-side derivative and cofactor identities -/

/-- **The `POLYSTAR` numerator on the Laurent side.**  With `x₃ = formalXThree`,
`y₃ = formalYThree`, `F_E = formalGroupLaurent = -x₃·y₃⁻¹`, `W₃ = formalWThree = -y₃⁻¹`,
the Leibniz/quotient calculus
collapses `W₃·F_E' − F_E·W₃'` to `y₃⁻²·x₃'` (all derivatives w.r.t. the outer variable `z₂`). -/
theorem formalWThree_mul_derivative_formalGroupLaurent_sub :
    W.formalWThree * LaurentSeries.derivative ℤ W.formalGroupLaurent
        - W.formalGroupLaurent * LaurentSeries.derivative ℤ W.formalWThree
      = (Ring.inverse W.formalYThree) ^ 2 * LaurentSeries.derivative ℤ W.formalXThree := by
  have hyi := LaurentSeries.derivative_inverse W.isUnit_formalYThree
  have hDW3 : LaurentSeries.derivative ℤ W.formalWThree
      = Ring.inverse W.formalYThree * LaurentSeries.derivative ℤ W.formalYThree
          * Ring.inverse W.formalYThree := by
    rw [formalWThree, map_neg, hyi]
    ring
  have hDFL : LaurentSeries.derivative ℤ W.formalGroupLaurent
      = W.formalXThree * Ring.inverse W.formalYThree * LaurentSeries.derivative ℤ W.formalYThree
          * Ring.inverse W.formalYThree
        - LaurentSeries.derivative ℤ W.formalXThree * Ring.inverse W.formalYThree := by
    rw [formalGroupLaurent, neg_mul, map_neg, LaurentSeries.derivative_mul, hyi]
    ring
  rw [hDW3, hDFL, formalWThree, formalGroupLaurent]
  ring

/-- **The `POLYSTAR` cofactor on the Laurent side factors through the unit `y₃⁻²`.**
`W₃·(-2 + a₁·F_E + a₃·W₃) = y₃⁻²·(2·y₃ + a₁·x₃ + a₃)`. -/
theorem formalWThree_mul_cofactor :
    W.formalWThree
        * (-2 + HahnSeries.C (HahnSeries.C W.a₁) * W.formalGroupLaurent
          + HahnSeries.C (HahnSeries.C W.a₃) * W.formalWThree)
      = (Ring.inverse W.formalYThree) ^ 2
        * (2 * W.formalYThree + HahnSeries.C (HahnSeries.C W.a₁) * W.formalXThree
          + HahnSeries.C (HahnSeries.C W.a₃)) := by
  have hyy : W.formalYThree * Ring.inverse W.formalYThree = 1 := W.formalYThree_mul_inverse
  rw [formalWThree, formalGroupLaurent]
  linear_combination (-2 * Ring.inverse W.formalYThree) * hyy

end WeierstrassCurve
