/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.NegationGroup
import EllipticCurves.Reduction.ThirdChordNonvanishingDiag
import EllipticCurves.Reduction.FormalGroupAdditivity
import EllipticCurves.Reduction.AdditivityValuation
import EllipticCurves.Reduction.FormalGroupTangent
import EllipticCurves.Reduction.ChordAffineBridge
import EllipticCurves.Reduction.KernelBijection

/-!
# The unconditional formal-inverse compatibility (issue #377)

Let `R` be a complete discrete valuation ring with fraction field `K = Frac R` and
`W : WeierstrassCurve K` an elliptic curve with an integral model.  Working in the genuine
formal-group carrier `Ê(𝔪) = FormalGroup.OnIdeal (integralModel R W).formalGroup 𝔪`
(`Reduction/KernelFormalGroup.lean`), this file removes the `P ≠ -P` hypothesis from the
formal-inverse compatibility `z ∘ [-1] = i(z)` (Silverman AEC IV.1):

```
zParamHatEquiv (-P) = - zParamHatEquiv P     in Ê(𝔪),   for all P ∈ E₁(K).
```

The non-`2`-torsion case is the existing `WeierstrassCurve.zParamHatEquiv_neg`
(`Reduction/NegationGroup.lean`), whose analytic core is the **vertical additivity**
`adicEvalMv 𝔪 ![z(P), z(-P)] formalGroupZW = 0` for two points with a common `x`-coordinate.

This file handles the remaining corner `P = -P`: the identity `O` and the genuine `2`-torsion
points.  For `P = -P` one has `negReduces R W P = P`, so the statement reduces to
`z(P) ⊕ z(P) = 0`, i.e. the **doubling vertical additivity**
`adicEvalMv 𝔪 ![z, z] formalGroupZW = 0` at a `2`-torsion parameter (`z = z(P)`).  Geometrically the
tangent line at a `2`-torsion point is *vertical* (it meets the curve again only at `O`), so the
chord through the "double point" passes through the origin: its intercept `ν` vanishes, the third
Vieta root `t` vanishes, and `z ⊕ z = 0`.  The `P = O` sub-corner is trivial (`z = 0`,
`z ⊕ z = 0`).

The doubling analysis mirrors the secant vertical case
`Reduction/InverseAdditivity.lean`, with the tangency relation (`wParamDeriv_tangency`,
`chordSlope_diag`) replacing the second known intersection, exactly as in
`Reduction/ThirdChordNonvanishingDiag.lean` (whose intercept non-vanishing `ν ≠ 0` we here *invert*
at `2`-torsion, where `ν = 0`).

## Main results

* `WeierstrassCurve.chordIntercept_eq_zero_diag_of_two_torsion` — `ν = 0` at a `2`-torsion point.
* `WeierstrassCurve.thirdRootNum_eq_zero_diag_of_chordIntercept_zero` — `t = 0` when `ν = 0`.
* `WeierstrassCurve.adicEvalMv_formalGroupZW_eq_zero_diag_of_two_torsion` — doubling vertical
  additivity `z ⊕ z = 0` at a `2`-torsion point.
* `WeierstrassCurve.zParamHatEquiv_neg_uncond` — the **unconditional** formal-inverse compatibility.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2 Prop 2.2.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]
variable {z : R}

omit [W.IsElliptic] in
/-- **The chord intercept vanishes at a `2`-torsion point (doubling case).**  This is the inverse of
`chordIntercept_ne_zero_diag`: on the diagonal `z₁ = z₂ = z`, if the recovered point is `2`-torsion
(`y = negY x y`, i.e. `2P = O`), then the tangent numerator `P_den = a₁ z + a₃ w - 2 = w·(y − negY x
y)` vanishes, so the tangent cross-identity `P_num · ν = λ · w · P_den` forces `P_num · ν = 0`.  The
tangent-`X`-numerator `P_num = w² · (a₁ y − (3x² + 2a₂x + a₄)) = -w² · W_X(x, y)` is nonzero
(`w ≠ 0` and, since `W_Y(x, y) = 2y + a₁x + a₃ = y − negY x y = 0` at `2`-torsion, nonsingularity
gives `W_X(x, y) ≠ 0`), whence `ν = 0`. -/
theorem chordIntercept_eq_zero_diag_of_two_torsion (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
    {x y : K} (h : W.toAffine.Nonsingular x y)
    (hxP : xParam R W hz = x) (hyP : yParam R W hz = y)
    (hY2 : y = W.toAffine.negY x y) :
    chordIntercept R W (PowerSeries.diag_mem _ hz) = 0 := by
  apply IsFractionRing.injective R K
  rw [map_zero]
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
  -- `P_den = w · (y − negY x y)`
  have hpden0 : W.a₁ * algebraMap R K z + W.a₃ * algebraMap R K (wParam R W hz) - 2
      = algebraMap R K (wParam R W hz)
        * (yParam R W hz - W.toAffine.negY (xParam R W hz) (yParam R W hz)) := by
    rw [xParam, yParam, Affine.negY]
    field_simp
    ring
  -- at `2`-torsion `y = negY x y`, hence `P_den = 0`
  have hzero : yParam R W hz - W.toAffine.negY (xParam R W hz) (yParam R W hz) = 0 := by
    rw [hxP, hyP]
    exact sub_eq_zero.mpr hY2
  have hpd0 : W.a₁ * algebraMap R K z + W.a₃ * algebraMap R K (wParam R W hz) - 2 = 0 := by
    rw [hpden0, hzero, mul_zero]
  -- `P_num = -w² · W_X(x, y)`
  have hPnum : (3 * algebraMap R K z ^ 2
        + 2 * W.a₂ * algebraMap R K z * algebraMap R K (wParam R W hz)
        + W.a₄ * algebraMap R K (wParam R W hz) ^ 2
        + W.a₁ * algebraMap R K (wParam R W hz))
      = -(algebraMap R K (wParam R W hz) ^ 2 * W.toAffine.polynomialX.evalEval x y) := by
    rw [Affine.evalEval_polynomialX, ← hxP, ← hyP, xParam, yParam]
    field_simp
    ring
  -- `P_num ≠ 0`: `w ≠ 0` and `W_X(x, y) ≠ 0` (from nonsingularity, since `W_Y(x, y) = 0`)
  have hPnum_ne : (3 * algebraMap R K z ^ 2
        + 2 * W.a₂ * algebraMap R K z * algebraMap R K (wParam R W hz)
        + W.a₄ * algebraMap R K (wParam R W hz) ^ 2
        + W.a₁ * algebraMap R K (wParam R W hz)) ≠ 0 := by
    rw [hPnum]
    refine neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hwne) ?_)
    rcases h.2 with hX | hY
    · exact hX
    · refine absurd ?_ hY
      rw [Affine.evalEval_polynomialY]
      have hY2' := hY2
      rw [Affine.negY] at hY2'
      linear_combination hY2'
  -- conclude `ν = 0`
  rw [hpd0, mul_zero] at hcross
  rcases mul_eq_zero.mp hcross with hp | hnu
  · exact absurd hp hPnum_ne
  · exact hnu

omit [W.IsElliptic] in
/-- **The third Vieta root vanishes when the intercept vanishes (doubling case).**  Diagonal analog
of `thirdRootNum_eq_zero_of_X_eq`: with `ν = 0` the coordinate expansion lies on the line `w = λ z`,
so the value equation gives `A z² + S z − λ = 0` and the tangency relation upgrades this to the
double-root sum `A·(2z) + S = 0`.  Vieta `A·(t + 2z) + S = 0` then forces `A·t = 0`, and `A` is a
unit, so `t = 0`. -/
theorem thirdRootNum_eq_zero_diag_of_chordIntercept_zero
    (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
    (hnu : chordIntercept R W (PowerSeries.diag_mem _ hz) = 0) :
    thirdRootNum R W (PowerSeries.diag_mem _ hz) = 0 := by
  -- the chord line, with `ν = 0`, is `w = λ z`
  have hw : wParam R W hz = chordSlope R W (PowerSeries.diag_mem _ hz) * z := by
    rw [wParam_eq_chordLine₀ R W (PowerSeries.diag_mem _ hz) hz, hnu, add_zero]
  -- value equation on the line `w = λ z`
  have hV := wParam_functional_eq R W hz
  rw [hw] at hV
  -- tangency relation on the line `w = λ z`, with `w′ = λ`
  have hT := wParamDeriv_tangency R W hz
  rw [← chordSlope_diag R W hz, hw] at hT
  -- the double-root sum relation `A·(2z) + S = 0`
  have hsum : (1 + (integralModel R W).a₂ * chordSlope R W (PowerSeries.diag_mem _ hz)
        + (integralModel R W).a₄ * chordSlope R W (PowerSeries.diag_mem _ hz) ^ 2
        + (integralModel R W).a₆ * chordSlope R W (PowerSeries.diag_mem _ hz) ^ 3) * (2 * z)
      + ((integralModel R W).a₁ * chordSlope R W (PowerSeries.diag_mem _ hz)
          + (integralModel R W).a₃ * chordSlope R W (PowerSeries.diag_mem _ hz) ^ 2) = 0 := by
    have hkey : z ^ 2 * ((1 + (integralModel R W).a₂ * chordSlope R W (PowerSeries.diag_mem _ hz)
          + (integralModel R W).a₄ * chordSlope R W (PowerSeries.diag_mem _ hz) ^ 2
          + (integralModel R W).a₆ * chordSlope R W (PowerSeries.diag_mem _ hz) ^ 3) * (2 * z)
        + ((integralModel R W).a₁ * chordSlope R W (PowerSeries.diag_mem _ hz)
            + (integralModel R W).a₃ * chordSlope R W (PowerSeries.diag_mem _ hz) ^ 2)) = 0 := by
      linear_combination hV - z * hT
    exact (mul_eq_zero.mp hkey).resolve_left (pow_ne_zero 2 hz0)
  -- Vieta on the diagonal, with the closed forms of `A`, `S` and `ν = 0`
  have hVieta := formalThirdRoot_vieta R W (PowerSeries.diag_mem _ hz)
  rw [adicEvalMv_formalGroupLead R W (PowerSeries.diag_mem _ hz),
    adicEvalMv_formalGroupSub R W (PowerSeries.diag_mem _ hz), hnu] at hVieta
  -- subtract to get `A·t = 0`
  have hAt : (1 + (integralModel R W).a₂ * chordSlope R W (PowerSeries.diag_mem _ hz)
        + (integralModel R W).a₄ * chordSlope R W (PowerSeries.diag_mem _ hz) ^ 2
        + (integralModel R W).a₆ * chordSlope R W (PowerSeries.diag_mem _ hz) ^ 3)
      * thirdRootNum R W (PowerSeries.diag_mem _ hz) = 0 := by
    linear_combination hVieta - hsum
  -- `A ≠ 0` (it is a unit)
  have hAne : (1 + (integralModel R W).a₂ * chordSlope R W (PowerSeries.diag_mem _ hz)
      + (integralModel R W).a₄ * chordSlope R W (PowerSeries.diag_mem _ hz) ^ 2
      + (integralModel R W).a₆ * chordSlope R W (PowerSeries.diag_mem _ hz) ^ 3) ≠ 0 := by
    rw [← adicEvalMv_formalGroupLead R W (PowerSeries.diag_mem _ hz)]
    intro h0
    have hlead := (integralModel R W).ringHom_formalGroupLead_mul_inv
      (adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz))
    rw [h0, zero_mul] at hlead
    exact one_ne_zero hlead.symm
  rcases mul_eq_zero.mp hAt with h | h
  · exact absurd h hAne
  · exact h

omit [W.IsElliptic] in
/-- **Doubling vertical additivity at a `2`-torsion point.**  For a nonzero parameter `z = z(P)`
whose recovered point is `2`-torsion (`y = negY x y`, i.e. `2P = O`), the formal-group sum of `z`
with itself vanishes: `adicEvalMv 𝔪 ![z, z] formalGroupZW = 0`.  Equivalently `z ⊕ z = 0` in `Ê(𝔪)`,
matching the affine fact `P + P = O`.  The intercept vanishes
(`chordIntercept_eq_zero_diag_of_two_torsion`), hence the third Vieta root vanishes
(`thirdRootNum_eq_zero_diag_of_chordIntercept_zero`), and `den · (z ⊕ z) = -t = 0` with `den ≠ 0`
gives the result. -/
theorem adicEvalMv_formalGroupZW_eq_zero_diag_of_two_torsion
    (hz : z ∈ (maximalIdeal R).asIdeal) (hz0 : z ≠ 0)
    {x y : K} (h : W.toAffine.Nonsingular x y)
    (hxP : xParam R W hz = x) (hyP : yParam R W hz = y)
    (hY2 : y = W.toAffine.negY x y) :
    adicEvalMv (maximalIdeal R).asIdeal (PowerSeries.diag_mem _ hz)
      (integralModel R W).formalGroupZW = 0 := by
  have ht : thirdRootNum R W (PowerSeries.diag_mem _ hz) = 0 :=
    thirdRootNum_eq_zero_diag_of_chordIntercept_zero R W hz hz0
      (chordIntercept_eq_zero_diag_of_two_torsion R W hz hz0 h hxP hyP hY2)
  have hden := formalGroupDen_mul_adicEvalMv_formalGroupZW R W (PowerSeries.diag_mem _ hz)
  rw [ht, neg_zero] at hden
  rcases mul_eq_zero.mp hden with h' | h'
  · exact absurd h' (adicEvalMv_formalGroupDen_ne_zero R W (PowerSeries.diag_mem _ hz))
  · exact h'

/-- **The unconditional formal-inverse compatibility `z ∘ [-1] = i(z)` (Silverman AEC IV.1).**  For
every `P ∈ E₁(K)`, the local parameter of `-P` is the formal-group inverse of the local parameter of
`P`: `zParamHatEquiv (-P) = - zParamHatEquiv P` in `Ê(𝔪)`.  This drops the `P ≠ -P` hypothesis of
`zParamHatEquiv_neg`: for `P = -P` (the identity and the `2`-torsion points) one has
`negReduces R W P = P`, so the statement becomes `z(P) ⊕ z(P) = 0`, the doubling vertical additivity
`adicEvalMv_formalGroupZW_eq_zero_diag_of_two_torsion`. -/
theorem zParamHatEquiv_neg_uncond
    (P : {P : W.toAffine.Point // ReducesToZero R W P}) :
    zParamHatEquiv R W (negReduces R W P) = - zParamHatEquiv R W P := by
  by_cases hne : P.1 = -P.1
  · -- `P = -P`: the identity or a `2`-torsion point
    obtain ⟨Pt, hPt⟩ := P
    have hNP : negReduces R W ⟨Pt, hPt⟩ = ⟨Pt, hPt⟩ :=
      Subtype.ext (by rw [negReduces_val]; exact hne.symm)
    rw [hNP]
    cases Pt with
    | zero =>
      have h0 : zParamHatEquiv R W (⟨(.zero : W.toAffine.Point), hPt⟩) = 0 :=
        zParamHatEquiv_zero R W
      rw [h0, neg_zero]
    | some x y h =>
      refine eq_neg_of_add_eq_zero_right ?_
      apply FormalGroup.OnIdeal.ext
      rw [zParamHatEquiv_add_val, FormalGroup.OnIdeal.zero_val]
      have hval : 1 < valuation K (maximalIdeal R) x := hPt
      have hz : localParamR R W (.some x y h) ∈ (maximalIdeal R).asIdeal := localParamR_mem R W hPt
      have hz0 : localParamR R W (.some x y h) ≠ 0 := localParamR_ne_zero_of_reduces R W hval
      have hxy := pointOfParam_localParamR R W hval hz0
      rw [pointOfParam, Affine.Point.some.injEq] at hxy
      rw [Affine.Point.neg_some, Affine.Point.some.injEq] at hne
      exact adicEvalMv_formalGroupZW_eq_zero_diag_of_two_torsion R W hz hz0 h hxy.1 hxy.2 hne.2
  · -- `P ≠ -P`: the existing non-`2`-torsion case
    exact zParamHatEquiv_neg R W P hne

end WeierstrassCurve
