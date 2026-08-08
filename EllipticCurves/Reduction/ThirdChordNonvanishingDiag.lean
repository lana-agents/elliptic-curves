/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.AdditivityValuation
import EllipticCurves.Reduction.TangentThirdChordAffine

/-!
# Non-vanishing of the doubling third chord point (`w₃ ≠ 0`, issue #367)

Let `R` be a complete DVR with fraction field `K = Frac R` and `W : WeierstrassCurve K` an elliptic
curve with an integral model.  This file is the **doubling (tangent) analog** of
`Reduction/ThirdChordNonvanishing.lean`: for a single parameter `z ∈ 𝔪` (the point `P = Q`, tangent
case, diagonal family `![z, z]`) the formal-side addition law produces the third tangent point
`(t, w₃)` in the `(z, w)`-plane, with `t = thirdRootNum` the Vieta double-root third point and
`w₃ = thirdChordW = λ t + ν`.

The doubling coordinate identity `localParam_add_diag` / the point-level `localParam_add_of_X_eq`
(`Reduction/TangentThirdChordAffine.lean`) carry a hypothesis `hw : w₃ ≠ 0` (geometrically: the
third tangent point is not at infinity, i.e. `2P ≠ O`).  This file **discharges** it in the doubling
case, alongside the intercept non-vanishing `ν ≠ 0` (`chordIntercept_ne_zero_diag`).

The argument mirrors the secant one: `(t, w₃)` solves the same numeric Weierstrass functional
equation as the coordinate expansion `wParam`, and both `t, w₃` lie in `𝔪`; by uniqueness of the
small solution (`wFunctionalEq_unique`) one has `w₃ = wParam t`.  This turns `w₃ ≠ 0` into `t ≠ 0`
(as `wParam z = z³ · unit`).  Finally `t = 0` would force `w₃ = ν = 0`, contradicting
`chordIntercept_ne_zero_diag`.  The intercept non-vanishing itself uses the tangency: if `ν = 0`
then the collinearity `w = λ z + ν` forces `λ x = 1` (so `λ ≠ 0`), and the cross-identity
`P_num · ν = λ · w · P_den` (the numerator of the tangent-slope identity, `slope_xParam_tangent`)
forces `P_den = a₁ z + a₃ w - 2 = 0`; but `P_den = w · (y - negY x y) ≠ 0` when `2P ≠ O`.

## Main results

* `WeierstrassCurve.chordIntercept_ne_zero_diag` — **`ν ≠ 0`** in the doubling case (from `2P ≠ O`).
* `WeierstrassCurve.thirdChordW_eq_wParam_diag` — `w₃ = wParam t` (diagonal).
* `WeierstrassCurve.thirdRootNum_ne_zero_diag` — `t ≠ 0` in the doubling case.
* `WeierstrassCurve.thirdChordW_ne_zero_diag` — **`w₃ ≠ 0`** in the doubling case (discharges `hw`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] {z : R}

/-- **The chord intercept is nonzero (doubling case).**  On the diagonal `z₁ = z₂ = z`, if the
intercept `ν = chordIntercept ![z, z] = 0` then the collinearity `w = λ z + ν` gives `λ x = 1`, so
`λ ≠ 0`; feeding this into the tangent cross-identity `P_num · ν = λ · w · P_den` (the numerator of
the tangent-slope identity of `slope_xParam_tangent`) forces `P_den = a₁ z + a₃ w - 2 = 0`.  But
`P_den = w · (y - negY x y)`, and `w ≠ 0`, `y ≠ negY x y` (i.e. `2P ≠ O`), a contradiction.  This is
the doubling analog of `chordIntercept_ne_zero_secant`; the tangent hypothesis `y ≠ negY x y`
replaces the secant `x(z₁) ≠ x(z₂)`. -/
theorem chordIntercept_ne_zero_diag (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
    (hY : yParam R W hz ≠ W.toAffine.negY (xParam R W hz) (yParam R W hz)) :
    algebraMap R K (chordIntercept R W (PowerSeries.diag_mem _ hz)) ≠ 0 := by
  intro hν
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
  -- the tangent cross-identity `P_num · ν = λ · w · P_den`
  have hcross : (3 * algebraMap R K z ^ 2
        + 2 * W.a₂ * algebraMap R K z * algebraMap R K (wParam R W hz)
        + W.a₄ * algebraMap R K (wParam R W hz) ^ 2
        + W.a₁ * algebraMap R K (wParam R W hz))
        * algebraMap R K (chordIntercept R W (PowerSeries.diag_mem _ hz))
      = algebraMap R K (chordSlope R W (PowerSeries.diag_mem _ hz))
          * algebraMap R K (wParam R W hz)
          * (W.a₁ * algebraMap R K z + W.a₃ * algebraMap R K (wParam R W hz) - 2) := by
    linear_combination
      (3 * algebraMap R K (chordSlope R W (PowerSeries.diag_mem _ hz))) * hV
      - algebraMap R K (wParam R W hz) * hT
      - (3 * algebraMap R K z ^ 2
          + 2 * W.a₂ * algebraMap R K z * algebraMap R K (wParam R W hz)
          + W.a₄ * algebraMap R K (wParam R W hz) ^ 2
          + W.a₁ * algebraMap R K (wParam R W hz)) * hC
  -- `ν = 0` in the collinearity gives `λ x = 1`, hence `λ ≠ 0`
  have hc := collinear₀ R W (PowerSeries.diag_mem _ hz) hz hz0
  rw [hν, zero_mul, sub_zero] at hc
  have hlam : algebraMap R K (chordSlope R W (PowerSeries.diag_mem _ hz)) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hc; exact one_ne_zero hc.symm
  -- `ν = 0` in the cross-identity forces `λ · w · P_den = 0`
  rw [hν, mul_zero] at hcross
  have hprod : algebraMap R K (chordSlope R W (PowerSeries.diag_mem _ hz))
      * algebraMap R K (wParam R W hz)
      * (W.a₁ * algebraMap R K z + W.a₃ * algebraMap R K (wParam R W hz) - 2) = 0 := hcross.symm
  -- but `P_den = w · (y - negY x y) ≠ 0`
  have hpden : W.a₁ * algebraMap R K z + W.a₃ * algebraMap R K (wParam R W hz) - 2
      = algebraMap R K (wParam R W hz)
        * (yParam R W hz - W.toAffine.negY (xParam R W hz) (yParam R W hz)) := by
    rw [xParam, yParam, Affine.negY]
    field_simp
    ring
  rcases mul_eq_zero.mp hprod with hlw | hpd
  · rcases mul_eq_zero.mp hlw with hl | hw'
    · exact hlam hl
    · exact hwne hw'
  · rw [hpden] at hpd
    rcases mul_eq_zero.mp hpd with h | h
    · exact hwne h
    · exact hY (sub_eq_zero.mp h)

/-- **The doubling third chord `w`-value is the coordinate expansion `wParam t`.**  Both
`thirdChordW ![z, z]` (the `(z, w)`-plane value of the tangent line at the Vieta double-root third
point `t`) and `wParam t` solve the numeric Weierstrass functional equation with parameter
`t = thirdRootNum` and lie in `𝔪`; by uniqueness of the small solution (`wFunctionalEq_unique`) they
coincide.  Diagonal analog of `thirdChordW_eq_wParam`. -/
theorem thirdChordW_eq_wParam_diag (hz : z ∈ (maximalIdeal R).asIdeal) :
    thirdChordW R W (PowerSeries.diag_mem _ hz)
      = wParam R W (thirdRootNum_mem R W (PowerSeries.diag_mem _ hz)) := by
  refine IsFractionRing.injective R K ?_
  have hZlt : valuation K (maximalIdeal R)
      (algebraMap R K (thirdRootNum R W (PowerSeries.diag_mem _ hz))) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr
      (thirdRootNum_mem R W (PowerSeries.diag_mem _ hz))
  have hW1lt : valuation K (maximalIdeal R)
      (algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz))) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr
      (thirdChordW_mem R W (PowerSeries.diag_mem _ hz))
  have hwm : wParam R W (thirdRootNum_mem R W (PowerSeries.diag_mem _ hz))
      ∈ (maximalIdeal R).asIdeal := by
    rw [wParam_eq_cube_mul]
    refine Ideal.mul_mem_right _ _ ?_
    rw [pow_succ, pow_two]
    exact Ideal.mul_mem_left _ _ (thirdRootNum_mem R W (PowerSeries.diag_mem _ hz))
  have hW2lt : valuation K (maximalIdeal R)
      (algebraMap R K (wParam R W (thirdRootNum_mem R W (PowerSeries.diag_mem _ hz)))) < 1 :=
    (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mpr hwm
  refine wFunctionalEq_unique R W hZlt hW1lt hW2lt ?_ ?_
  · have h := congrArg (algebraMap R K) (thirdChord_functional_eq_diag R W hz)
    simpa only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] using h
  · have h := congrArg (algebraMap R K)
      (wParam_functional_eq R W (thirdRootNum_mem R W (PowerSeries.diag_mem _ hz)))
    simpa only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
      integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] using h

/-- **The Vieta third root is nonzero (doubling case).**  If `t = thirdRootNum = 0` then
`w₃ = λ·0 + ν = ν`, while `w₃ = wParam 0 = 0³ · unit = 0`; so `ν = 0`, contradicting
`chordIntercept_ne_zero_diag`.  Geometrically: `t = 0` would place the third tangent point at the
origin (`2P = O`), impossible when `2P ≠ O` (`y ≠ negY x y`). -/
theorem thirdRootNum_ne_zero_diag (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
    (hY : yParam R W hz ≠ W.toAffine.negY (xParam R W hz) (yParam R W hz)) :
    thirdRootNum R W (PowerSeries.diag_mem _ hz) ≠ 0 := by
  intro ht0
  have hν : chordIntercept R W (PowerSeries.diag_mem _ hz) ≠ 0 := fun hc =>
    chordIntercept_ne_zero_diag R W hz hz0 hY (by rw [hc, map_zero])
  have h1 : thirdChordW R W (PowerSeries.diag_mem _ hz)
      = chordIntercept R W (PowerSeries.diag_mem _ hz) := by
    rw [thirdChordW, ht0, mul_zero, zero_add]
  have h2 : thirdChordW R W (PowerSeries.diag_mem _ hz)
      = wParam R W (thirdRootNum_mem R W (PowerSeries.diag_mem _ hz)) :=
    thirdChordW_eq_wParam_diag R W hz
  have h3 : wParam R W (thirdRootNum_mem R W (PowerSeries.diag_mem _ hz)) = 0 := by
    rw [wParam_eq_cube_mul]
    exact mul_eq_zero_of_left (by rw [ht0]; ring) _
  rw [h2, h3] at h1
  exact hν h1.symm

/-- **The doubling third chord point is not at infinity (`w₃ ≠ 0`, doubling case).**  Since
`w₃ = wParam t` (`thirdChordW_eq_wParam_diag`) and `t ≠ 0` (`thirdRootNum_ne_zero_diag`), the
factorisation `wParam t = t³ · unit` gives `w₃ ≠ 0`.  This discharges the `hw` hypothesis of the
doubling coordinate additivity `localParam_add_diag` / `localParam_add_of_X_eq`. -/
theorem thirdChordW_ne_zero_diag (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
    (hY : yParam R W hz ≠ W.toAffine.negY (xParam R W hz) (yParam R W hz)) :
    thirdChordW R W (PowerSeries.diag_mem _ hz) ≠ 0 := by
  rw [thirdChordW_eq_wParam_diag R W hz]
  exact wParam_ne_zero R W _ (thirdRootNum_ne_zero_diag R W hz hz0 hY)

end WeierstrassCurve
