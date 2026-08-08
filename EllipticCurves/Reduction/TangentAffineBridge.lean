/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.FormalGroupTangent
import EllipticCurves.Reduction.ChordAffineBridge

/-!
# The affine↔formal tangent line bridge (issue #367, doubling case)

Let `R` be a complete DVR with fraction field `K = Frac R` and `W : WeierstrassCurve K` an elliptic
curve with an integral model.  This file is the **doubling (tangent) analog** of
`Reduction/ChordAffineBridge.lean`: it transports the diagonal formal chord line to the affine
`(x, y)`-plane in the doubling case `z₁ = z₂ = z` (the point `P = Q`), where the chord line is the
**tangent** to the `(z, w)`-curve at the double point.

On the diagonal the formal chord data specialise to `λ = chordSlope ![z, z]` (which equals the
formal derivative `w′(z)`, `chordSlope_diag`) and `ν = chordIntercept ![z, z]`, and the tangent
line `w = λ z + ν` transports (under `x = z / w`, `y = -1 / w`) to the affine tangent line through
the single recovered point `(xParam z, yParam z)`.

* `WeierstrassCurve.slope_xParam_tangent` — **the affine tangent slope is `λ / ν`**: Mathlib's
  doubling slope `W.slope x x y y` (the tangent of `W` at the recovered point) equals
  `chordSlope / chordIntercept`, exactly as in the secant case (`slope_xParam_secant`).  The proof
  is the doubling analog: in place of the secant's two collinearity relations it combines the single
  collinearity `wParam_eq_chordLine₀`, the tangency relation `wParamDeriv_tangency` (with
  `λ = chordSlope`, via `chordSlope_diag`), and the value equation `wParam_functional_eq`.

This is the load-bearing bridge identity the doubling affine-matching rung of issue #367 consumes
(the tangent analog of the merged `localParam_add_secant`), carrying the non-vanishing side
conditions `ν ≠ 0` and `y ≠ negY x y` (i.e. `2P ≠ O`) as hypotheses, mirroring how the secant chain
carried its side conditions before discharging them.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] {z : R}

open Classical in
/-- **The affine tangent slope is `λ / ν`** (doubling case).  On the diagonal `z₁ = z₂ = z`, the
recovered point is the single point `(xParam z, yParam z) = (z / w, -1 / w)`, and Mathlib's doubling
slope `W.slope x x y y` (the tangent of `W` at that point) equals `chordSlope / chordIntercept`.
Requires `z ≠ 0`, the intercept non-vanishing `ν ≠ 0`, and the tangent-defined condition
`y ≠ negY x y` (equivalently `2P ≠ O`, so the tangent is not vertical).

The certificate is the doubling analog of `slope_xParam_secant`: after clearing the `w` denominators
the cross-multiplied identity `P_num · ν = λ · w · P_den` (with `P_num = 3z² + 2a₂zw + a₄w² + a₁w`,
`P_den = a₁z + a₃w - 2`) is `3λ·(value equation) − w·(tangency) − P_num·(collinearity)`. -/
theorem slope_xParam_tangent (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
    (hν : algebraMap R K (chordIntercept R W (PowerSeries.diag_mem _ hz)) ≠ 0)
    (hY : yParam R W hz ≠ W.toAffine.negY (xParam R W hz) (yParam R W hz)) :
    W.toAffine.slope (xParam R W hz) (xParam R W hz) (yParam R W hz) (yParam R W hz)
      = algebraMap R K (chordSlope R W (PowerSeries.diag_mem _ hz))
        / algebraMap R K (chordIntercept R W (PowerSeries.diag_mem _ hz)) := by
  have hwne : algebraMap R K (wParam R W hz) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (wParam_ne_zero R W hz hz0)
  -- value equation (K image)
  have hV := congrArg (algebraMap R K) (wParam_functional_eq R W hz)
  simp only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
    integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] at hV
  -- tangency relation (K image), with `λ = chordSlope` via `chordSlope_diag`
  have hTr := wParamDeriv_tangency R W hz
  rw [← chordSlope_diag R W hz] at hTr
  have hT := congrArg (algebraMap R K) hTr
  simp only [map_add, map_mul, map_pow, map_ofNat, integralModel_a₁_eq, integralModel_a₂_eq,
    integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] at hT
  -- collinearity `w = λ z + ν` (K image)
  have hC := congrArg (algebraMap R K) (wParam_eq_chordLine₀ R W (PowerSeries.diag_mem _ hz) hz)
  rw [map_add, map_mul] at hC
  have hYne : yParam R W hz - W.toAffine.negY (xParam R W hz) (yParam R W hz) ≠ 0 :=
    sub_ne_zero.mpr hY
  rw [Affine.slope_of_Y_ne rfl hY, div_eq_div_iff hYne hν, xParam, yParam, Affine.negY]
  field_simp
  linear_combination (3 * algebraMap R K (chordSlope R W (PowerSeries.diag_mem _ hz))) * hV
    - algebraMap R K (wParam R W hz) * hT
    - (3 * algebraMap R K z ^ 2
        + 2 * W.a₂ * algebraMap R K z * algebraMap R K (wParam R W hz)
        + W.a₄ * algebraMap R K (wParam R W hz) ^ 2
        + W.a₁ * algebraMap R K (wParam R W hz)) * hC

end WeierstrassCurve
