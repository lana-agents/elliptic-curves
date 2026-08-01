/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Mathlib.RingTheory.PowerSeries.Derivative
import EllipticCurves.FormalGroup.CoordinateSeries

/-!
# The invariant differential and the formal logarithm of a Weierstrass curve

For a Weierstrass curve `E` the invariant differential is
`ω = dx / (2y + a₁x + a₃)`. Expressed in the formal parameter `z = -x/y` near the origin `O`
(so `x = z/w`, `y = -1/w` with `w = W.formalW ∈ R⟦z⟧`), a direct computation shows `ω = ω_E(z) dz`
with `ω_E(z)` a genuine **power series** with constant term `1`: writing `x = z/w`,
`x'(z) = (w - z·w')/w²`, and `2y + a₁x + a₃ = (-2 + a₁z + a₃w)/w`, so
$$ ω_E(z) = \frac{x'(z)}{2y(z)+a_1 x(z)+a_3}
          = \frac{w - z\,w'}{w\,(-2 + a_1 z + a_3 w)} . $$
Substituting `w = z³·v` with `v = W.wCofactor` (`v(0) = 1`), the pole `z³` cancels between
numerator and denominator explicitly:
$$ ω_E(z) = \frac{-(2v + z\,v')}{v\,(-2 + a_1 z + a_3 w)} \in R⟦z⟧ , \qquad ω_E(0) = 1 . $$
This is the *unblocked* univariate part of Silverman AEC IV.5: it needs only the coordinate series
`w = W.formalW`, not the bivariate formal group law.

Over a `ℚ`-algebra we may then integrate `ω_E` term by term to obtain the **formal logarithm**
`log_E(z) = z + O(z²)`, the unique power series with `log_E'(z) = ω_E(z)` and no constant term.

## Main definitions

* `WeierstrassCurve.invariantDifferential` : the invariant-differential coefficient series
  `ω_E(z) ∈ R⟦z⟧` (over a `ℚ`-algebra).
* `WeierstrassCurve.formalLog` : the formal logarithm `log_E(z) ∈ R⟦z⟧` (over a `ℚ`-algebra).

## Main results

* `WeierstrassCurve.constantCoeff_invariantDifferential` : `ω_E(0) = 1`.
* `WeierstrassCurve.derivativeFun_formalLog` : `log_E'(z) = ω_E(z)`.
* `WeierstrassCurve.constantCoeff_formalLog` : `log_E(0) = 0`.
* `WeierstrassCurve.coeff_one_formalLog` : the `z`-coefficient of `log_E` is `1`, i.e.
  `log_E(z) = z + O(z²)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5.
-/

namespace WeierstrassCurve

open PowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The invariant differential -/

/-- The numerator of the invariant differential after cancelling the pole:
`-(2·v + z·v')` with `v = W.wCofactor`. It has constant term `-2`. -/
noncomputable def invDiffNum : R⟦X⟧ :=
  -(2 * W.wCofactor + X * derivativeFun W.wCofactor)

/-- The denominator of the invariant differential after cancelling the pole:
`v · (-2 + a₁ z + a₃ w)` with `v = W.wCofactor`, `w = W.formalW`. It has constant term `-2`. -/
noncomputable def invDiffDen : R⟦X⟧ :=
  W.wCofactor * (-2 + C W.a₁ * X + C W.a₃ * W.formalW)

@[simp]
theorem constantCoeff_invDiffNum : constantCoeff W.invDiffNum = -2 := by
  simp only [invDiffNum, map_neg, map_add, map_mul, constantCoeff_X, zero_mul, add_zero,
    map_ofNat, constantCoeff_wCofactor, mul_one]

theorem constantCoeff_formalW : constantCoeff W.formalW = 0 := by
  rw [formalW_eq_X_pow_mul_wCofactor, map_mul, map_pow, constantCoeff_X, zero_pow (by norm_num),
    zero_mul]

@[simp]
theorem constantCoeff_invDiffDen : constantCoeff W.invDiffDen = -2 := by
  simp only [invDiffDen, map_mul, map_add, map_neg, map_ofNat, constantCoeff_C, constantCoeff_X,
    constantCoeff_wCofactor, W.constantCoeff_formalW, mul_zero, add_zero, one_mul]

/-- The constant `-2` is a unit in a `ℚ`-algebra `R` (packaged as `Rˣ`). -/
noncomputable def negTwoUnit (R : Type*) [CommRing R] [Algebra ℚ R] : Rˣ :=
  (IsUnit.map (algebraMap ℚ R) (Ne.isUnit (by norm_num : (-2 : ℚ) ≠ 0))).unit

@[simp]
theorem negTwoUnit_val (R : Type*) [CommRing R] [Algebra ℚ R] :
    (negTwoUnit R : R) = -2 := by
  rw [negTwoUnit, IsUnit.unit_spec]
  simp only [map_neg, map_ofNat]

/-- **The invariant differential** `ω_E(z) ∈ R⟦z⟧` of a Weierstrass curve over a `ℚ`-algebra,
expressed in the formal parameter `z = -x/y`: `ω_E = dx / (2y + a₁x + a₃)` read as a power series,
`ω_E = invDiffNum · invDiffDen⁻¹`. It has constant term `1` (Silverman AEC IV.5). -/
noncomputable def invariantDifferential [Algebra ℚ R] : R⟦X⟧ :=
  W.invDiffNum * invOfUnit W.invDiffDen (negTwoUnit R)

/-- **`ω_E(0) = 1`.** The invariant differential is a genuine power series with constant term `1`,
i.e. `ω_E(z) = 1 + a₁ z + ⋯`. -/
@[simp]
theorem constantCoeff_invariantDifferential [Algebra ℚ R] :
    constantCoeff W.invariantDifferential = 1 := by
  rw [invariantDifferential, map_mul, constantCoeff_invDiffNum, constantCoeff_invOfUnit,
    ← negTwoUnit_val R]
  exact (negTwoUnit R).mul_inv

/-- **Defining identity of the invariant differential.**
`ω_E · (v·(-2 + a₁z + a₃w)) = -(2v + z·v')`, the cleared-denominators form of
`ω_E = dx / (2y + a₁x + a₃)`. -/
theorem invariantDifferential_mul_invDiffDen [Algebra ℚ R] :
    W.invariantDifferential * W.invDiffDen = W.invDiffNum := by
  rw [invariantDifferential, mul_assoc,
    mul_comm (invOfUnit W.invDiffDen (negTwoUnit R)) W.invDiffDen,
    mul_invOfUnit W.invDiffDen (negTwoUnit R)
      (by rw [constantCoeff_invDiffDen, negTwoUnit_val]), mul_one]

/-- **The formal logarithm** `log_E(z) ∈ R⟦z⟧` of a Weierstrass curve over a `ℚ`-algebra:
the term-by-term integral of the invariant differential, `log_E(z) = z + O(z²)`, characterised by
`log_E'(z) = ω_E(z)` and `log_E(0) = 0` (Silverman AEC IV.5). -/
noncomputable def formalLog [Algebra ℚ R] : R⟦X⟧ :=
  PowerSeries.mk fun n : ℕ =>
    if n = 0 then 0 else algebraMap ℚ R ((n : ℚ)⁻¹) * coeff (n - 1) W.invariantDifferential

theorem coeff_formalLog_succ [Algebra ℚ R] (n : ℕ) :
    coeff (n + 1) W.formalLog
      = algebraMap ℚ R ((n + 1 : ℚ)⁻¹) * coeff n W.invariantDifferential := by
  simp only [formalLog, coeff_mk]
  rw [if_neg (by omega : ¬ (n + 1 = 0)), Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]

/-- **`log_E'(z) = ω_E(z)`.** The formal logarithm is a primitive of the invariant differential. -/
theorem derivativeFun_formalLog [Algebra ℚ R] :
    derivativeFun W.formalLog = W.invariantDifferential := by
  ext n
  rw [coeff_derivativeFun, coeff_formalLog_succ]
  have key : algebraMap ℚ R ((n : ℚ) + 1)⁻¹ * ((n : R) + 1) = 1 := by
    rw [show ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1) by push_cast; ring, ← map_mul,
      inv_mul_cancel₀ (by positivity : ((n : ℚ) + 1) ≠ 0), map_one]
  rw [mul_right_comm, key, one_mul]

/-- **`log_E(0) = 0`.** The formal logarithm has no constant term. -/
@[simp]
theorem constantCoeff_formalLog [Algebra ℚ R] : constantCoeff W.formalLog = 0 := by
  rw [← coeff_zero_eq_constantCoeff, formalLog, coeff_mk, if_pos rfl]

/-- **`log_E(z) = z + O(z²)`.** The `z`-coefficient of the formal logarithm is `1`. -/
@[simp]
theorem coeff_one_formalLog [Algebra ℚ R] : coeff 1 W.formalLog = 1 := by
  have := W.coeff_formalLog_succ 0
  rw [zero_add] at this
  rw [this, Nat.cast_zero, zero_add, inv_one, map_one, one_mul, coeff_zero_eq_constantCoeff,
    constantCoeff_invariantDifferential]

end WeierstrassCurve
