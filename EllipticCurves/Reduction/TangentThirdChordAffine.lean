/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.ThirdChordAffine
import EllipticCurves.Reduction.TangentAffineBridge

/-!
# The third tangent point on the affine curve and the doubling coordinate identity (issue #367)

Let `R` be a complete DVR with fraction field `K = Frac R` and `W : WeierstrassCurve K` an elliptic
curve with an integral model.  This file is the **doubling (tangent) analog** of
`Reduction/ThirdChordAffine.lean` (its `section Secant` and the point-level
`localParam_add_of_X_ne`): the doubling case `z₁ = z₂ = z` (the point `P = Q`) of issue #367's
affine-matching additivity.

On the diagonal the formal chord line is the **tangent** to the `(z, w)`-curve at the double point,
and the formal-side addition law produces the **third tangent point** `(t, w₃)` with
`t = thirdRootNum` the Vieta double-root complement and `w₃ = λ t + ν = thirdChordW` the value of
the tangent line there (all data at the diagonal family `![z, z]`,
`ha := PowerSeries.diag_mem _ hz`).
This file transports that point to the **affine** `(x, y)`-plane and identifies it with Mathlib's
affine third-intersection point `addX`/`addY`, closing the coordinate-level doubling additivity of
the local parameter.

Writing `X₃ = t / w₃`, `Y₃ = -1 / w₃` for the affine image (via `x = z/w`, `y = -1/w`):

* `WeierstrassCurve.thirdChord_functional_eq_diag` — the third tangent point `(t, w₃)` lies on the
  `(z, w)`-curve (diagonal restatement of `thirdChordPoint_functional_eq_diag` in terms of
  `thirdChordW`, mirroring `thirdChord_functional_eq`).
* `WeierstrassCurve.equation_thirdChordPoint_diag` — `(X₃, Y₃)` lies on the affine curve (numeric
  transport, mirroring `equation_thirdChordPoint`; no `z₁ ≠ z₂` hypothesis is needed here).
* `WeierstrassCurve.thirdChord_on_tangentLine` — `(X₃, Y₃)` lies on the affine tangent line through
  the single recovered point `(xParam z, yParam z)`, i.e. `Y₃ = ℓ (X₃ - x) + y` with
  `ℓ = W.slope x x y y` the affine doubling slope (`= λ / ν`, `slope_xParam_tangent`).
* `WeierstrassCurve.addX_eq_thirdChordX_diag` — **the coordinate identity `addX = X₃`**: Mathlib's
  affine doubling `addX` of the recovered point equals the transported third-root `x`-coordinate
  `X₃ = t / w₃` (in the case `X₃ ≠ x`).
* `WeierstrassCurve.localParam_add_diag` — **the coordinate-level doubling additivity**:
  `-addX / addY = z ⊕ z` in `K`, where `z ⊕ z = adicEvalMv 𝔪 ![z, z] formalGroupZW` is the formal
  group law of the parameter.
* `WeierstrassCurve.localParam_add_of_X_eq` — the point-level doubling: for a point `P` reducing to
  the origin with `2P ≠ O` (`y ≠ negY x y`) and `P + P` also reducing to the origin,
  `z(P + P) = z(P) ⊕ z(P)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries Polynomial

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] {z : R}

/-- **The third tangent point satisfies the Weierstrass functional equation** (doubling case).  In
the form of the numeric functional equation, but at the third-root point `(t, w₃)` on the diagonal:
this is the statement that `(t, w₃)` lies on the `(z, w)`-curve
(`thirdChordPoint_functional_eq_diag`, restated in terms of `thirdChordW`).  The diagonal analog of
`thirdChord_functional_eq`; no `z₁ ≠ z₂` hypothesis is needed. -/
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
  simp only [thirdChordW]
  linear_combination thirdChordPoint_functional_eq_diag R W hz

/-- The `K`-image of the numeric functional equation for the third tangent point, in the curve's own
coefficients `W.aᵢ = algebraMap R K (integralModel R W).aᵢ`.  Diagonal analog of
`algebraMap_thirdChord_functional_eq`. -/
private theorem algebraMap_thirdChord_functional_eq_diag (hz : z ∈ (maximalIdeal R).asIdeal) :
    algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz))
      = algebraMap R K (thirdRootNum R W (PowerSeries.diag_mem _ hz)) ^ 3
      + (W.a₁ * algebraMap R K (thirdRootNum R W (PowerSeries.diag_mem _ hz))
          + W.a₂ * algebraMap R K (thirdRootNum R W (PowerSeries.diag_mem _ hz)) ^ 2)
        * algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz))
      + (W.a₃ + W.a₄ * algebraMap R K (thirdRootNum R W (PowerSeries.diag_mem _ hz)))
        * algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) ^ 2
      + W.a₆ * algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) ^ 3 := by
  have h := congrArg (algebraMap R K) (thirdChord_functional_eq_diag R W hz)
  simp only [map_add, map_mul, map_pow, integralModel_a₁_eq, integralModel_a₂_eq,
    integralModel_a₃_eq, integralModel_a₄_eq, integralModel_a₆_eq] at h
  exact h

/-- **The affine third tangent point lies on the curve** (doubling case).  The transported point
`(X₃, Y₃) = (t / w₃, -1 / w₃)` satisfies the Weierstrass equation of `W`.  Numeric transport of
`thirdChordPoint_functional_eq_diag`, mirroring `equation_thirdChordPoint`.  Requires `w₃ ≠ 0` (the
third point is not at infinity, i.e. `P + P ≠ O`).  Unlike the secant case, no `z₁ ≠ z₂` hypothesis
is needed. -/
theorem equation_thirdChordPoint_diag (hz : z ∈ (maximalIdeal R).asIdeal)
    (hw : thirdChordW R W (PowerSeries.diag_mem _ hz) ≠ 0) :
    W.toAffine.Equation
        (algebraMap R K (thirdRootNum R W (PowerSeries.diag_mem _ hz))
          / algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)))
      (-1 / algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz))) := by
  have hwne : algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hw
  have hfe := algebraMap_thirdChord_functional_eq_diag R W hz
  rw [Affine.equation_iff]
  field_simp
  linear_combination hfe

open Classical in
/-- **The affine third tangent point lies on the tangent line** through the recovered point.
Writing `X₃ = t / w₃`, `Y₃ = -1 / w₃` and `ℓ = W.slope x x y y` (the affine doubling slope
`= λ / ν`), one has `Y₃ = ℓ (X₃ - x) + y`.  Consequence of the single collinearity relation
(`collinear₀`, `thirdChord_line_num`) and `slope_xParam_tangent`.  Diagonal analog of
`thirdChord_on_secantLine`. -/
theorem thirdChord_on_tangentLine (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
    (hw : thirdChordW R W (PowerSeries.diag_mem _ hz) ≠ 0)
    (hν : algebraMap R K (chordIntercept R W (PowerSeries.diag_mem _ hz)) ≠ 0)
    (hY : yParam R W hz ≠ W.toAffine.negY (xParam R W hz) (yParam R W hz)) :
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
  linear_combination algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) * hc0 - hnum

open Classical in
/-- **The coordinate identity `addX = X₃` (doubling case).**  In the doubling case (the transported
third `x`-coordinate `X₃ = t / w₃` distinct from `x`), Mathlib's affine third-intersection
`x`-coordinate `addX` of the recovered point (with the doubling slope) equals `X₃`.  Diagonal analog
of `addX_eq_thirdChordX`, with a single distinctness hypothesis `hd : X₃ ≠ x`. -/
theorem addX_eq_thirdChordX_diag (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
    (hw : thirdChordW R W (PowerSeries.diag_mem _ hz) ≠ 0)
    (hν : algebraMap R K (chordIntercept R W (PowerSeries.diag_mem _ hz)) ≠ 0)
    (hY : yParam R W hz ≠ W.toAffine.negY (xParam R W hz) (yParam R W hz))
    (hd : X₃ R W (PowerSeries.diag_mem _ hz) ≠ xParam R W hz) :
    W.toAffine.addX (xParam R W hz) (xParam R W hz)
        (W.toAffine.slope (xParam R W hz) (xParam R W hz) (yParam R W hz) (yParam R W hz))
      = X₃ R W (PowerSeries.diag_mem _ hz) := by
  have h := equation_xParam_yParam R W hz hz0
  have hxy : ¬(xParam R W hz = xParam R W hz ∧
      yParam R W hz = W.toAffine.negY (xParam R W hz) (yParam R W hz)) := fun hh => hY hh.2
  have hline : (-1 / algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)))
      = W.toAffine.slope (xParam R W hz) (xParam R W hz) (yParam R W hz) (yParam R W hz)
          * (X₃ R W (PowerSeries.diag_mem _ hz) - xParam R W hz) + yParam R W hz :=
    thirdChord_on_tangentLine R W hz hz0 hw hν hY
  have hcurve : W.toAffine.Equation (X₃ R W (PowerSeries.diag_mem _ hz))
      (-1 / algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz))) :=
    equation_thirdChordPoint_diag R W hz hw
  have hroot := W.toAffine.addPolynomial_eval_eq_zero_of_equation hline hcurve
  rw [W.toAffine.addPolynomial_slope h h hxy] at hroot
  simp only [eval_neg, eval_mul, eval_sub, eval_X, eval_C, neg_eq_zero] at hroot
  rcases mul_eq_zero.mp hroot with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd (sub_eq_zero.mp h'') hd
    · exact absurd (sub_eq_zero.mp h'') hd
  · exact (sub_eq_zero.mp h').symm

open Classical in
/-- **The coordinate-level additivity of the local parameter (doubling case).**
`-addX / addY = z ⊕ z` in `K`, where the left side is the local parameter `-x/y` of the affine
doubling sum point `(addX, addY)` of the recovered point `(xParam z, yParam z)`, and the right side
is the formal group law `z ⊕ z = adicEvalMv 𝔪 ![z, z] formalGroupZW` of the parameter.  Diagonal
analog of `localParam_add_secant`, combining `addX_eq_thirdChordX_diag` with the numeric inversion
`den · (z ⊕ z) = -t` (`formalGroupDen_mul_adicEvalMv_formalGroupZW`).  Hypotheses: the doubling
non-degeneracy (`X₃ ≠ x`, `w₃ ≠ 0`, `ν ≠ 0`, `y ≠ negY x y`) and `den ≠ 0`. -/
theorem localParam_add_diag (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
    (hw : thirdChordW R W (PowerSeries.diag_mem _ hz) ≠ 0)
    (hν : algebraMap R K (chordIntercept R W (PowerSeries.diag_mem _ hz)) ≠ 0)
    (hY : yParam R W hz ≠ W.toAffine.negY (xParam R W hz) (yParam R W hz))
    (hd : X₃ R W (PowerSeries.diag_mem _ hz) ≠ xParam R W hz)
    (hden : adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
      (integralModel R W).formalGroupDen ≠ 0) :
    -(W.toAffine.addX (xParam R W hz) (xParam R W hz)
          (W.toAffine.slope (xParam R W hz) (xParam R W hz) (yParam R W hz) (yParam R W hz)))
        / W.toAffine.addY (xParam R W hz) (xParam R W hz) (yParam R W hz)
            (W.toAffine.slope (xParam R W hz) (xParam R W hz) (yParam R W hz) (yParam R W hz))
      = algebraMap R K (adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
          (integralModel R W).formalGroupZW) := by
  set ℓ := W.toAffine.slope (xParam R W hz) (xParam R W hz) (yParam R W hz) (yParam R W hz)
    with hℓ
  have hwne : algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hw
  have hdenne : algebraMap R K (adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
      (integralModel R W).formalGroupDen) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hden
  have haddX := addX_eq_thirdChordX_diag R W hz hz0 hw hν hY hd
  have hline := thirdChord_on_tangentLine R W hz hz0 hw hν hY
  rw [← hℓ] at haddX hline
  -- the negated `y`-coordinate of the sum is `-1 / w₃`
  have hnegAddY : W.toAffine.negAddY (xParam R W hz) (xParam R W hz) (yParam R W hz) ℓ
      = -1 / algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) := by
    rw [Affine.negAddY, haddX, ← hline]
  -- the `den`-closed form, folded through `thirdChordW`
  have hden_R : adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
        (integralModel R W).formalGroupDen
      = 1 - (integralModel R W).a₁ * thirdRootNum R W (PowerSeries.diag_mem _ hz)
        - (integralModel R W).a₃ * thirdChordW R W (PowerSeries.diag_mem _ hz) := by
    rw [adicEvalMv_formalGroupDen, thirdChordW]
  have hden_closed : algebraMap R K (adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
        (integralModel R W).formalGroupDen)
      = 1 - W.a₁ * algebraMap R K (thirdRootNum R W (PowerSeries.diag_mem _ hz))
        - W.a₃ * algebraMap R K (thirdChordW R W (PowerSeries.diag_mem _ hz)) := by
    have h := congrArg (algebraMap R K) hden_R
    simpa only [map_sub, map_mul, map_one, integralModel_a₁_eq, integralModel_a₃_eq] using h
  -- `addY = den / w₃`
  have haddY : W.toAffine.addY (xParam R W hz) (xParam R W hz) (yParam R W hz) ℓ
      = algebraMap R K (adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
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

open Classical in
/-- **Point-level doubling additivity of the local parameter.**  For a point `P = (x, y)` reducing
to the origin with `2P ≠ O` (`y ≠ negY x y`, the doubling case), whose affine double `P + P` also
reduces to the origin, the local parameter of the sum equals the formal group law of the parameter:
`z(P + P) = z(P) ⊕ z(P) = adicEvalMv 𝔪 ![z, z] formalGroupZW`, where `z = localParamR R W P`.
Combining Mathlib's affine doubling (`Point.add_self_of_Y_ne`, the sum is `(addX, addY)`) with the
coordinate identity `localParam_add_diag`.  Conditional on the non-degeneracy hypotheses of that
identity (`w₃ ≠ 0`, `X₃ ≠ x`, `ν ≠ 0`, `den ≠ 0`) and on the sum reducing to the origin. -/
theorem localParam_add_of_X_eq [W.IsElliptic]
    {x y : K} {h : W.toAffine.Nonsingular x y} (hR : ReducesToZero R W (.some x y h))
    (hred : ReducesToZero R W (.some x y h + .some x y h))
    (hY : y ≠ W.toAffine.negY x y)
    (hw : thirdChordW R W (PowerSeries.diag_mem _ (localParamR_mem R W hR)) ≠ 0)
    (hd : X₃ R W (PowerSeries.diag_mem _ (localParamR_mem R W hR))
      ≠ xParam R W (localParamR_mem R W hR))
    (hν : algebraMap R K
      (chordIntercept R W (PowerSeries.diag_mem _ (localParamR_mem R W hR))) ≠ 0)
    (hden : adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ (localParamR_mem R W hR))
      (integralModel R W).formalGroupDen ≠ 0) :
    localParam R W (.some x y h + .some x y h)
      = algebraMap R K (adicEvalMv (maximalIdeal R).asIdeal
          (PowerSeries.diag_mem _ (localParamR_mem R W hR)) (integralModel R W).formalGroupZW) := by
  -- the parameter is nonzero
  have hz0 : localParamR R W (.some x y h) ≠ 0 := localParamR_ne_zero_of_reduces R W hR
  -- the recovered coordinates are the original ones
  have hcoord : xParam R W (localParamR_mem R W hR) = x
      ∧ yParam R W (localParamR_mem R W hR) = y := by
    have hpt := pointOfParam_localParamR R W hR hz0
    simpa only [pointOfParam, Affine.Point.some.injEq] using hpt
  obtain ⟨hx, hy⟩ := hcoord
  -- the doubling condition, phrased in the recovered coordinates
  have hYparam : yParam R W (localParamR_mem R W hR)
      ≠ W.toAffine.negY (xParam R W (localParamR_mem R W hR))
          (yParam R W (localParamR_mem R W hR)) := by
    rw [hx, hy]
    exact hY
  -- Mathlib's affine doubling is the third tangent point `(addX, addY)`; on the origin-reducing
  -- locus the local parameter takes its `-addX/addY` branch
  rw [Affine.Point.add_self_of_Y_ne hY] at hred ⊢
  have hpos : 1 < valuation K (maximalIdeal R) (W.toAffine.addX x x (W.toAffine.slope x x y y)) :=
    hred
  rw [localParam_some, if_pos hpos]
  have key := localParam_add_diag R W (localParamR_mem R W hR) hz0 hw hν hYparam hd hden
  rw [hx, hy] at key
  exact key

end WeierstrassCurve
