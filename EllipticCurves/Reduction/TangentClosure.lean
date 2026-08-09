/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.TangentAdditivityClean

/-!
# Doubling closure of the reduction kernel `E₁(K)` (issue #367, partial)

Let `R` be a complete discrete valuation ring with fraction field `K = Frac R` and
`W : WeierstrassCurve K` an elliptic curve with an integral model.  Working towards the fact that
the reduction kernel `E₁(K) = {P // ReducesToZero R W P}` is closed under addition (issue #367),
this file discharges the **non-degenerate doubling case**: for `P = (x, y) ∈ E₁(K)` with
`2P ≠ O` (`y ≠ negY x y`, the tangent/doubling case) and honestly-geometric distinctness
`X₃ ≠ x`, the affine double `P + P` again reduces to the origin.

This is the doubling analog of the merged secant closure
`reducesToZero_add_of_X_ne_of_distinct` (`Reduction/SecantClosure.lean`).  The merged doubling
additivity `localParam_add_of_X_eq_clean` (`Reduction/TangentAdditivityClean.lean`) takes
`ReducesToZero R W (P + P)` as a *hypothesis* (`hred`); here we **prove** that hypothesis in the
doubling case, so the additivity identity holds without assuming closure a priori.

## The closure argument

Mathlib's affine double in the tangent case is `P + P = some (addX x x ℓ) (addY …)`
(`add_self_of_Y_ne`), so `ReducesToZero R W (P + P)` unfolds to `1 < v(addX x x ℓ)`.  Now, exactly
as in the secant case but with the diagonal (`z₁ = z₂ = z`) bricks:

* `addX x x ℓ = X₃` — Mathlib's affine third-intersection `x`-coordinate is the transported Vieta
  third tangent point (`addX_eq_thirdChordX_diag`, needing the distinctness `X₃ ≠ x`, together with
  the unconditional doubling side conditions `w₃ ≠ 0`, `ν ≠ 0`);
* `X₃ = t / w₃ = t / wParam t = xParam t` where `t = thirdRootNum` — the third chord `w`-value is
  the coordinate expansion `wParam t` (`thirdChordW_eq_wParam_diag`);
* `1 < v(xParam t)` for `t ≠ 0` (`one_lt_valuation_xParam`, with `t ≠ 0` from
  `thirdRootNum_ne_zero_diag`), i.e. the recovered third tangent point has a pole.

Hence `1 < v(addX)`, so `P + P ∈ E₁(K)`.  **No new analytic machinery is needed** — the valuation
control comes entirely from the merged coordinate-recovery bricks; in particular the closure does
*not* pass through the cancellation-sensitive direct slope-valuation route (Silverman AEC VII.2).

## Main results

* `WeierstrassCurve.reducesToZero_add_of_X_eq_of_distinct` — `P = (x, y) ∈ E₁(K)`, `2P ≠ O`,
  `X₃ ≠ x` ⇒ `P + P ∈ E₁(K)` (the doubling add-closure).
* `WeierstrassCurve.localParam_add_doubling_of_distinct` — the doubling additivity of the local
  parameter `localParam (P + P) = z(P) ⊕ z(P)` **without** the `hred` hypothesis, obtained by
  feeding the closure lemma into `localParam_add_of_X_eq_clean`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W]

open Classical in
/-- **Doubling add-closure of the reduction kernel.**  For a point `P = (x, y)` reducing to the
origin with `2P ≠ O` (`y ≠ negY x y`, the doubling case) and the honestly-geometric distinctness
`X₃ ≠ x`, the affine double `P + P` again reduces to the origin.

This discharges the `hred` hypothesis of `localParam_add_of_X_eq_clean` in the non-degenerate
doubling case: the affine third-intersection `x`-coordinate `addX = X₃ = xParam t`
(`t = thirdRootNum`) has a pole (`1 < v(xParam t)` for `t ≠ 0`), which is exactly the
`ReducesToZero` condition.  The excluded distinctness failure `X₃ = x` is the degenerate `3P = O`
configuration, where closure holds by `reducesToZero_neg` instead.  Doubling analog of the merged
secant `reducesToZero_add_of_X_ne_of_distinct`. -/
theorem reducesToZero_add_of_X_eq_of_distinct [W.IsElliptic]
    {x y : K} {h : W.toAffine.Nonsingular x y} (hR : ReducesToZero R W (.some x y h))
    (hY : y ≠ W.toAffine.negY x y)
    (hd : X₃ R W (PowerSeries.diag_mem _ (localParamR_mem R W hR))
      ≠ xParam R W (localParamR_mem R W hR)) :
    ReducesToZero R W (.some x y h + .some x y h) := by
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
    rw [hx, hy]; exact hY
  -- the doubling side conditions and the Vieta root are unconditional in the doubling case
  have hw : thirdChordW R W (PowerSeries.diag_mem _ (localParamR_mem R W hR)) ≠ 0 :=
    thirdChordW_ne_zero_diag R W (localParamR_mem R W hR) hz0 hYparam
  have hν : algebraMap R K
      (chordIntercept R W (PowerSeries.diag_mem _ (localParamR_mem R W hR))) ≠ 0 :=
    chordIntercept_ne_zero_diag R W (localParamR_mem R W hR) hz0 hYparam
  have htne : thirdRootNum R W (PowerSeries.diag_mem _ (localParamR_mem R W hR)) ≠ 0 :=
    thirdRootNum_ne_zero_diag R W (localParamR_mem R W hR) hz0 hYparam
  -- `addX = X₃` (the diagonal affine matching), and `X₃ = xParam t` (recovered third tangent point)
  have haddX :=
    addX_eq_thirdChordX_diag R W (localParamR_mem R W hR) hz0 hw hν hYparam hd
  have hX3eq : X₃ R W (PowerSeries.diag_mem _ (localParamR_mem R W hR))
      = xParam R W (thirdRootNum_mem R W (PowerSeries.diag_mem _ (localParamR_mem R W hR))) := by
    rw [X₃_def, xParam, thirdChordW_eq_wParam_diag R W (localParamR_mem R W hR)]
  -- rephrase the affine matching in the original coordinates
  rw [hx, hy] at haddX
  -- the recovered third tangent point has a pole: `1 < v(addX)`
  have hfinal : 1 < valuation K (maximalIdeal R)
      (W.toAffine.addX x x (W.toAffine.slope x x y y)) := by
    rw [haddX, hX3eq]
    exact one_lt_valuation_xParam R W (thirdRootNum_mem R W _) htne
  -- Mathlib's affine double is the tangent point `(addX, addY)`; `ReducesToZero` is `1 < v(addX)`
  rw [Affine.Point.add_self_of_Y_ne hY]
  exact hfinal

open Classical in
/-- **Doubling additivity of the local parameter, closure discharged.**  For `P = (x, y) ∈ E₁(K)`
with `2P ≠ O` and `X₃ ≠ x`, `localParam (P + P) = z(P) ⊕ z(P)` in `K` — the merged
`localParam_add_of_X_eq_clean` with its `ReducesToZero (P + P)` hypothesis supplied by
`reducesToZero_add_of_X_eq_of_distinct`.  The only remaining hypotheses are the honest doubling
geometry (`2P ≠ O`, `X₃ ≠ x`). -/
theorem localParam_add_doubling_of_distinct [W.IsElliptic]
    {x y : K} {h : W.toAffine.Nonsingular x y} (hR : ReducesToZero R W (.some x y h))
    (hY : y ≠ W.toAffine.negY x y)
    (hd : X₃ R W (PowerSeries.diag_mem _ (localParamR_mem R W hR))
      ≠ xParam R W (localParamR_mem R W hR)) :
    localParam R W (.some x y h + .some x y h)
      = algebraMap R K (adicEvalMv (maximalIdeal R).asIdeal
          (PowerSeries.diag_mem _ (localParamR_mem R W hR)) (integralModel R W).formalGroupZW) :=
  localParam_add_of_X_eq_clean R W hR
    (reducesToZero_add_of_X_eq_of_distinct R W hR hY hd) hY hd

end WeierstrassCurve
