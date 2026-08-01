/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.PowerSeries.Substitution
import EllipticCurves.FormalGroup.Logarithm

/-!
# The formal exponential of a Weierstrass curve

Over a `ℚ`-algebra the formal logarithm `log_E(z) = z + O(z²)` (`WeierstrassCurve.formalLog`,
`EllipticCurves.FormalGroup.Logarithm`) has an invertible linear coefficient, so it admits a
compositional inverse. This file defines the **formal exponential**

`exp_E(z) := log_E⁻¹(z) ∈ R⟦z⟧`

as that compositional inverse (via Mathlib's `PowerSeries.substInvOfIsUnit`) and proves it is a
genuine two-sided inverse of `log_E` with the normalisation `exp_E(z) = z + O(z²)`:

* `log_E ∘ exp_E = id` and `exp_E ∘ log_E = id`,
* `exp_E(0) = 0` and the `z`-coefficient of `exp_E` is `1`.

This is the univariate part of Silverman AEC IV.5–IV.6; it needs only `log_E`, not the bivariate
formal group law. Over a `ℚ`-algebra `log_E` and `exp_E` together exhibit the additive isomorphism
`Ê(𝔪) ≅ 𝔾ₐ`; the multiplicativity `log_E(F_E(z₁,z₂)) = log_E z₁ + log_E z₂` (the bivariate half)
is treated separately (it needs the inner pole-freeness of `F_E`).

## Main definitions

* `WeierstrassCurve.formalExp` : the formal exponential `exp_E(z) ∈ R⟦z⟧` (over a `ℚ`-algebra).

## Main results

* `WeierstrassCurve.formalLog_subst_formalExp` : `log_E ∘ exp_E = id` (`log_E(exp_E(z)) = z`).
* `WeierstrassCurve.formalExp_subst_formalLog` : `exp_E ∘ log_E = id` (`exp_E(log_E(z)) = z`).
* `WeierstrassCurve.constantCoeff_formalExp` : `exp_E(0) = 0`.
* `WeierstrassCurve.coeff_one_formalExp` : the `z`-coefficient of `exp_E` is `1`, i.e.
  `exp_E(z) = z + O(z²)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5–IV.6.
-/

namespace WeierstrassCurve

open PowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The `z`-coefficient of the formal logarithm is a unit (it is `1`, `coeff_one_formalLog`), so
`log_E` has a compositional inverse. -/
theorem isUnit_coeff_one_formalLog [Algebra ℚ R] : IsUnit (coeff 1 W.formalLog) := by
  rw [W.coeff_one_formalLog]; exact isUnit_one

/-- **The formal exponential** `exp_E(z) ∈ R⟦z⟧` of a Weierstrass curve over a `ℚ`-algebra:
the compositional inverse of the formal logarithm `log_E` (Silverman AEC IV.5–IV.6). -/
noncomputable def formalExp [Algebra ℚ R] : R⟦X⟧ :=
  W.formalLog.substInvOfIsUnit W.isUnit_coeff_one_formalLog

/-- **`log_E ∘ exp_E = id`.** `log_E(exp_E(z)) = z`. -/
theorem formalLog_subst_formalExp [Algebra ℚ R] :
    W.formalLog.subst W.formalExp = X :=
  W.formalLog.subst_substInvOfIsUnit_right W.constantCoeff_formalLog W.isUnit_coeff_one_formalLog

/-- **`exp_E ∘ log_E = id`.** `exp_E(log_E(z)) = z`. -/
theorem formalExp_subst_formalLog [Algebra ℚ R] :
    W.formalExp.subst W.formalLog = X :=
  W.formalLog.subst_substInvOfIsUnit_left W.constantCoeff_formalLog W.isUnit_coeff_one_formalLog

/-- **`exp_E(0) = 0`.** The formal exponential has no constant term. -/
@[simp]
theorem constantCoeff_formalExp [Algebra ℚ R] : constantCoeff W.formalExp = 0 :=
  W.formalLog.constantCoeff_substInvOfIsUnit W.isUnit_coeff_one_formalLog

/-- **`exp_E(z) = z + O(z²)`.** The `z`-coefficient of the formal exponential is `1`. -/
@[simp]
theorem coeff_one_formalExp [Algebra ℚ R] : coeff 1 W.formalExp = 1 := by
  rw [formalExp, coeff_one_substInvOfIsUnit]
  have hu : W.isUnit_coeff_one_formalLog.unit = 1 := by
    apply Units.ext
    rw [IsUnit.unit_spec, W.coeff_one_formalLog, Units.val_one]
  rw [hu, inv_one, Units.val_one]

end WeierstrassCurve
