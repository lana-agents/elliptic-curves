/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.ThirdChordAffine
import EllipticCurves.Reduction.TangentAffineBridge

/-!
# The third chord point on the affine curve and the doubling coordinate identity (issue #367)

Let `R` be a complete DVR with fraction field `K = Frac R` and `W : WeierstrassCurve K` an elliptic
curve with an integral model.  This file is the **doubling (tangent) analog** of the `Secant`
section of `Reduction/ThirdChordAffine.lean`: it transports the diagonal formal third-chord point to
the affine `(x, y)`-plane in the doubling case `z₁ = z₂ = z` (the point `P = Q`), where the chord
line is the **tangent** to the `(z, w)`-curve at the double point, and identifies the affine image
with Mathlib's doubling third-intersection point `addX`/`addY`.

Writing `X₃ = t / w₃`, `Y₃ = -1 / w₃` for the affine image of the third chord point `(t, w₃)`
(with `t = thirdRootNum`, `w₃ = thirdChordW` evaluated on the diagonal `![z, z]`):

* `WeierstrassCurve.thirdChord_functional_eq_diag` — the diagonal restatement of the numeric
  functional equation for `(t, w₃)` in terms of `thirdChordW` (the doubling analog of
  `thirdChord_functional_eq`, consuming the merged `thirdChordPoint_functional_eq_diag`, PR #94).
* `WeierstrassCurve.equation_thirdChordPoint_diag` — `(X₃, Y₃)` lies on the affine curve (numeric
  transport of the diagonal functional equation, mirroring `equation_thirdChordPoint`).
* `WeierstrassCurve.thirdChord_on_tangentLine` — `(X₃, Y₃)` lies on the affine **tangent** line at
  the single recovered point `(xParam z, yParam z)`, i.e. `Y₃ = ℓ (X₃ - x) + y` with
  `ℓ = W.slope x x y y` the affine doubling slope (`= λ / ν`, `slope_xParam_tangent`, PR #96).
* `WeierstrassCurve.addX_eq_thirdChordX_diag` — **the coordinate identity `addX = X₃`** in the
  doubling case: Mathlib's doubling `addX` of the recovered point equals `X₃`, via the tangent
  factorization `addPolynomial_slope = -((X - x)² (X - addX))` (the double root at `x`).
* `WeierstrassCurve.localParam_add_tangent` — **the coordinate-level doubling additivity**:
  `-addX / addY = z ⊕ z` in `K`, where `z ⊕ z = adicEvalMv 𝔪 ![z, z] formalGroupZW` is the formal
  group law of the parameters on the diagonal.

These carry the non-vanishing side conditions `w₃ ≠ 0` (`2P ≠ O`), `ν ≠ 0`, `y ≠ negY x y`
(the tangent is not vertical), `X₃ ≠ x`, and `den ≠ 0` as hypotheses, mirroring how the secant
chain carried its side conditions before discharging them.  The remaining work for the doubling rung
of #367 is the point-level assembly (`P + P = some (addX) (addY)` via `Point.add_of_Y_ne` and the
`ReducesToZero` subgroup closure).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries Polynomial

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] {z : R}

/-- **The diagonal third chord point satisfies the Weierstrass functional equation.**  The doubling
analog of `thirdChord_functional_eq`: at the third-root point `(t, w₃)` on the diagonal
`z₁ = z₂ = z` the pair lies on the `(z, w)`-curve.  Restates the merged
`thirdChordPoint_functional_eq_diag` (PR #94) in terms of `thirdChordW`. -/
theorem thirdChord_functional_eq_diag (hz : z ∈ (maximalIdeal R).asIdeal) :
    thirdChordW R W (PowerSeries.diag_mem _ hz)
      = thirdRootNum R W (PowerSeries.diag_mem _ hz) ^ 3
        + ((integralModel R W).a₁ * thirdRootNum R W (PowerSeries.diag_mem _ hz)
            + (integralModel R W).a₂ * thirdRootNum R W (PowerSeries.diag_mem _ hz) ^ 2)
              * thirdChordW R W (PowerSeries.diag_mem _ hz)
        + ((integralModel R W).a₃
            + (integralModel R W).a₄ * thirdRootNum R W (PowerSeries.diag_mem _ hz))
              * thirdChordW R W (PowerSeries.diag_mem _ hz) ^ 2
        + (integralModel R W).a₆ * thirdChordW R W (PowerSeries.diag_mem _ hz) ^ 3 := by
  rw [thirdChordW]
  exact thirdChordPoint_functional_eq_diag R W hz

/-- **The affine diagonal third chord point lies on the curve.**  The transported point
`(X₃, Y₃) = (t / w₃, -1 / w₃)` satisfies the Weierstrass equation of `W`.  Numeric transport of
`thirdChord_functional_eq_diag`, the doubling analog of `equation_thirdChordPoint`.  Requires
`w₃ ≠ 0` (the third point is not at infinity, i.e. `2P ≠ O`). -/
theorem equation_thirdChordPoint_diag (hz : z ∈ (maximalIdeal R).asIdeal)
    (hw : thirdChordW R W (PowerSeries.diag_mem _ hz) ≠ 0) :
    W.toAffine.Equation
        (algebraMap R K (thirdRootNum R W (PowerSeries.diag_mem _ hz))
          / algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)))
        (-1 / algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz))) := by
  have hwne : algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hw
  have hfe := congrArg (algebraMap R K) (thirdChord_functional_eq_diag R W hz)
  simp only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
    integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] at hfe
  rw [Affine.equation_iff]
  field_simp
  linear_combination hfe

section Doubling

variable (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
  (hw : thirdChordW R W (PowerSeries.diag_mem _ hz) ≠ 0)
  (hν : algebraMap R K (chordIntercept R W (PowerSeries.diag_mem _ hz)) ≠ 0)
  (hY : yParam R W hz ≠ W.toAffine.negY (xParam R W hz) (yParam R W hz))

include hz0 hw hν hY in
open Classical in
/-- **The affine diagonal third chord point lies on the tangent line** at the recovered point.
Writing `X₃ = t / w₃`, `Y₃ = -1 / w₃` and `ℓ = W.slope x x y y` (the affine tangent slope `= λ / ν`,
`slope_xParam_tangent`), one has `Y₃ = ℓ (X₃ - x) + y`.  The doubling analog of
`thirdChord_on_secantLine`: combines the single collinearity relation (`collinear₀`) and
`thirdChord_line_num`. -/
theorem thirdChord_on_tangentLine :
    -1 / algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz))
      = W.toAffine.slope (xParam R W hz) (xParam R W hz) (yParam R W hz) (yParam R W hz)
          * (X₃ R W (PowerSeries.diag_mem _ hz) - xParam R W hz)
        + yParam R W hz := by
  rw [slope_xParam_tangent R W hz hz0 hν hY, X₃_def]
  have hwne : algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hw
  have hc0 := collinear₀ R W (PowerSeries.diag_mem _ hz) hz hz0
  have hnum := thirdChord_line_num R W (PowerSeries.diag_mem _ hz)
  field_simp
  linear_combination
    algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) * hc0 - hnum

include hz0 hw hν hY in
open Classical in
/-- **The coordinate identity `addX = X₃` (doubling case).**  In the doubling case (`z₁ = z₂ = z`,
`2P ≠ O`, and the transported third `x`-coordinate `X₃ = t / w₃` distinct from `x`), Mathlib's
doubling third-intersection `x`-coordinate `addX` of the recovered point equals `X₃`.  The tangent
line meets the curve in a double point at `x` and the third point `(X₃, Y₃)`: the addition
polynomial factors as `-((X - x)² (X - addX))`, so its root `X₃ ≠ x` forces `addX = X₃`. -/
theorem addX_eq_thirdChordX_diag (hd : X₃ R W (PowerSeries.diag_mem _ hz) ≠ xParam R W hz) :
    W.toAffine.addX (xParam R W hz) (xParam R W hz)
        (W.toAffine.slope (xParam R W hz) (xParam R W hz) (yParam R W hz) (yParam R W hz))
      = X₃ R W (PowerSeries.diag_mem _ hz) := by
  have h₁ := equation_xParam_yParam R W hz hz0
  have hxy : ¬(xParam R W hz = xParam R W hz ∧
      yParam R W hz = W.toAffine.negY (xParam R W hz) (yParam R W hz)) := fun h => hY h.2
  have hline := thirdChord_on_tangentLine R W hz hz0 hw hν hY
  have hcurve : W.toAffine.Equation (X₃ R W (PowerSeries.diag_mem _ hz))
      (-1 / algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz))) := by
    rw [X₃_def]; exact equation_thirdChordPoint_diag R W hz hw
  have hroot := W.toAffine.addPolynomial_eval_eq_zero_of_equation hline hcurve
  rw [W.toAffine.addPolynomial_slope h₁ h₁ hxy] at hroot
  simp only [eval_neg, eval_mul, eval_sub, eval_X, eval_C, neg_eq_zero] at hroot
  rcases mul_eq_zero.mp hroot with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (sub_eq_zero.mp h') hd
    · exact absurd (sub_eq_zero.mp h') hd
  · exact (sub_eq_zero.mp h).symm

include hz hz0 hw hν hY in
open Classical in
/-- **The coordinate-level additivity of the local parameter (doubling case).**
`-addX / addY = z ⊕ z` in `K`, where the left side is the local parameter `-x/y` of the affine
double `P + P` of the recovered point `(xParam z, yParam z)`, and the right side is the formal
group law `z ⊕ z = adicEvalMv 𝔪 ![z, z] formalGroupZW` of the parameters on the diagonal.  The
doubling analog of `localParam_add_secant`: combines the coordinate identity `addX = t / w₃`
(`addX_eq_thirdChordX_diag`) with the numeric inversion `den · (z ⊕ z) = -t`
(`formalGroupDen_mul_adicEvalMv_formalGroupZW`).  Hypotheses: the doubling non-degeneracy
(`2P ≠ O` via `w₃ ≠ 0`, `ν ≠ 0`, `y ≠ negY x y`, `X₃ ≠ x`) and `den ≠ 0` (`addY ≠ 0`). -/
theorem localParam_add_tangent (hd : X₃ R W (PowerSeries.diag_mem _ hz) ≠ xParam R W hz)
    (hden : adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
        (integralModel R W).formalGroupDen ≠ 0) :
    -(W.toAffine.addX (xParam R W hz) (xParam R W hz)
          (W.toAffine.slope (xParam R W hz) (xParam R W hz) (yParam R W hz) (yParam R W hz)))
        / W.toAffine.addY (xParam R W hz) (xParam R W hz) (yParam R W hz)
            (W.toAffine.slope (xParam R W hz) (xParam R W hz) (yParam R W hz) (yParam R W hz))
      = algebraMap R K
          (adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
            (integralModel R W).formalGroupZW) := by
  set ℓ := W.toAffine.slope (xParam R W hz) (xParam R W hz) (yParam R W hz) (yParam R W hz)
    with hℓ
  have hwne : algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hw
  have hdenne : algebraMap R K
      (adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
        (integralModel R W).formalGroupDen) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hden
  have haddX := addX_eq_thirdChordX_diag R W hz hz0 hw hν hY hd
  have hline := thirdChord_on_tangentLine R W hz hz0 hw hν hY
  rw [← hℓ] at haddX hline
  -- the negated `y`-coordinate of the double is `-1 / w₃`
  have hnegAddY : W.toAffine.negAddY (xParam R W hz) (xParam R W hz) (yParam R W hz) ℓ
      = -1 / algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) := by
    rw [Affine.negAddY, haddX, ← hline]
  -- the `den`-closed form, folded through `thirdChordW`
  have hden_R : adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
        (integralModel R W).formalGroupDen
      = 1 - (integralModel R W).a₁ * thirdRootNum R W (PowerSeries.diag_mem _ hz)
        - (integralModel R W).a₃ * thirdChordW R W (PowerSeries.diag_mem _ hz) := by
    rw [adicEvalMv_formalGroupDen, thirdChordW]
  have hden_closed : algebraMap R K
        (adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
          (integralModel R W).formalGroupDen)
      = 1 - W.a₁ * algebraMap R K (thirdRootNum R W (PowerSeries.diag_mem _ hz))
        - W.a₃ * algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) := by
    have h := congrArg (algebraMap R K) hden_R
    simpa only [map_sub, map_mul, map_one, integralModel_a₁_eq, integralModel_a₃_eq] using h
  -- `addY = den / w₃`
  have haddY : W.toAffine.addY (xParam R W hz) (xParam R W hz) (yParam R W hz) ℓ
      = algebraMap R K
          (adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
            (integralModel R W).formalGroupDen)
        / algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) := by
    rw [Affine.addY, Affine.negY, hnegAddY, haddX, X₃_def, hden_closed]
    field_simp
  -- the numeric inversion `den · (z ⊕ z) = -t`
  have hZW := congrArg (algebraMap R K)
    (formalGroupDen_mul_adicEvalMv_formalGroupZW R W (PowerSeries.diag_mem _ hz))
  rw [map_mul, map_neg] at hZW
  rw [haddX, haddY, X₃_def]
  field_simp
  linear_combination -hZW

end Doubling

end WeierstrassCurve
