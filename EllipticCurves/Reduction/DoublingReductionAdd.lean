/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.SecantReductionAdd

/-!
# `redPt` additivity: the reduced-doubling (tangent) case (issue #381)

Let `R` be a discrete valuation ring with fraction field `K = Frac R` and residue field
`k = ResidueField R`, and let `W : WeierstrassCurve K` have good reduction.  This file handles the
**reduced-doubling** rung of the point-reduction homomorphism property (parent #360): when the
reduced point `(x̄, ȳ)` is **non-vertical** (`ȳ ≠ negY x̄ ȳ`, i.e. not `2`-torsion on the reduced
curve), the reduced sum uses the *tangent* (doubling) slope, whose denominator
`2ȳ + a₁x̄ + a₃ = ȳ - negY x̄ ȳ` is nonzero, hence a unit of the residue field.

The crux (mirroring the secant slope lemma `exists_lift_slope_of_reduced_X_ne`, #379) is that on an
integral point whose reduction is non-vertical, the *tangent* `K`-slope is integral and its residue
is the reduced-curve tangent slope: the denominator `y - negY x y` lifts to a **unit** of `R` (its
residue is the nonzero reduced denominator), so the difference quotient stays in `R` and `residue R`
— a ring homomorphism — commutes with it.  We then assemble the `P = Q` doubling case of
`redPt`-additivity exactly as in the secant rung (`redPt_add_of_reduced_X_ne`, #380), using the
ring-hom-commuting `Affine.map_addX`/`map_addY`.

## Main results

* `WeierstrassCurve.exists_lift_tangent_slope_of_reduced_nonvertical` — integral lift of the tangent
  `K`-slope with residue the reduced-curve tangent slope.
* `WeierstrassCurve.redPt_add_self_of_reduced_nonvertical` — the `P = Q` reduced-doubling case of
  `redPt`-additivity: `redPt (P + P) = redPt P + redPt P`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2 Prop 2.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum IsLocalRing

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open Classical in
/-- **Integral-slope reduction compatibility (tangent / doubling case).**  Let `P = (x, y)` be a
point of `W` with integral lifts `x₀, y₀ : R`, and suppose its reduction is **non-vertical**:
`residue y₀ ≠ (reduction R W).negY (residue x₀) (residue y₀)` (equivalently the reduced tangent
denominator `2ȳ + a₁x̄ + a₃ ≠ 0`).  Then the tangent slope `W.slope x x y y` is **integral**: it has
a lift `s : R` whose residue is exactly the tangent slope of the reduced curve at the reduced point.

The denominator `y₀ - (integralModel R W).negY x₀ y₀` reduces to the nonzero reduced denominator, so
it is a unit of the local ring `R`; the numerator `3x₀² + 2a₂x₀ + a₄ - a₁y₀` is integral, so the
difference quotient stays in `R` and `residue R` commutes with it — no injectivity needed. -/
theorem exists_lift_tangent_slope_of_reduced_nonvertical (W : WeierstrassCurve K)
    [HasGoodReduction R W] {x y : K} {x₀ y₀ : R}
    (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y)
    (hnv : residue R y₀ ≠ (reduction R W).toAffine.negY (residue R x₀) (residue R y₀)) :
    ∃ s : R, algebraMap R K s = W.toAffine.slope x x y y ∧
      residue R s = (reduction R W).toAffine.slope
        (residue R x₀) (residue R x₀) (residue R y₀) (residue R y₀) := by
  -- the integral model base-changes to `W`; used to lift `negY` and the a-invariants from `R` to K.
  have hcurve : (integralModel R W).toAffine.map (algebraMap R K) = W.toAffine :=
    baseChange_integralModel_eq R W
  -- the integral tangent denominator and numerator.
  set d₀ : R := y₀ - (integralModel R W).toAffine.negY x₀ y₀ with hd₀
  set n₀ : R := 3 * x₀ ^ 2 + 2 * (integralModel R W).a₂ * x₀ + (integralModel R W).a₄
    - (integralModel R W).a₁ * y₀ with hn₀
  -- residue of the denominator = reduced tangent denominator (via `map_negY` for `residue R`).
  have hnegY_res : residue R ((integralModel R W).toAffine.negY x₀ y₀)
      = (reduction R W).toAffine.negY (residue R x₀) (residue R y₀) :=
    (Affine.map_negY (residue R) x₀ y₀).symm
  have hd₀_res : residue R d₀
      = residue R y₀ - (reduction R W).toAffine.negY (residue R x₀) (residue R y₀) := by
    rw [hd₀, map_sub, hnegY_res]
  -- ...hence `d₀` is a unit (its residue is nonzero, so `d₀ ∉ 𝔪`).
  have hd₀_unit : IsUnit d₀ := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, hd₀_res, sub_eq_zero]
    exact hnv
  obtain ⟨u, hu⟩ := hd₀_unit
  -- `algebraMap d₀ = y - W.negY x y`, the K-side tangent denominator.
  have hd₀_K : algebraMap R K d₀ = y - W.toAffine.negY x y := by
    rw [hd₀, map_sub, hy, ← Affine.map_negY (algebraMap R K), hcurve, hx, hy]
  -- the reduced point is non-vertical over K too (else `d₀ = 0`, contradicting the unit).
  have hyK : y ≠ W.toAffine.negY x y := by
    intro h
    have hd0K0 : algebraMap R K d₀ = 0 := by rw [hd₀_K]; exact sub_eq_zero.mpr h
    have hd0 : d₀ = 0 := IsFractionRing.injective R K (by rw [hd0K0, map_zero])
    exact u.ne_zero (hu.trans hd0)
  -- `algebraMap n₀ = 3x² + 2a₂x + a₄ - a₁y`, the K-side tangent numerator.
  have hn₀_K : algebraMap R K n₀ = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hn₀]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, integralModel_a₁_eq,
      integralModel_a₂_eq, integralModel_a₄_eq, hx, hy]
  -- residue of `n₀` = the reduced tangent numerator (via `map_a₁/a₂/a₄` on `reduction`).
  have hn₀_res : residue R n₀
      = 3 * residue R x₀ ^ 2 + 2 * (reduction R W).a₂ * residue R x₀ + (reduction R W).a₄
        - (reduction R W).a₁ * residue R y₀ := by
    rw [hn₀]
    simp only [reduction, map_sub, map_add, map_mul, map_pow, map_ofNat, map_a₁, map_a₂, map_a₄]
  refine ⟨n₀ * (u⁻¹ : Rˣ), ?_, ?_⟩
  · -- over `K`: the difference quotient equals the tangent slope.
    rw [Affine.slope_of_Y_ne rfl hyK, eq_div_iff (sub_ne_zero.mpr hyK), ← hd₀_K, ← hu, ← map_mul,
      mul_assoc, Units.inv_mul, mul_one, hn₀_K]
  · -- over `k`: the same computation with `residue R`, giving the reduced tangent slope.
    rw [Affine.slope_of_Y_ne rfl hnv, eq_div_iff (sub_ne_zero.mpr hnv), ← hd₀_res, ← hu, ← map_mul,
      mul_assoc, Units.inv_mul, mul_one, hn₀_res]

open Classical in
/-- **`redPt` additivity, `P = Q` reduced-doubling case.**  If the reduced point of an integral
point `P = (x, y)` is non-vertical (`residue y₀ ≠ negY …`, so `redPt P + redPt P` is a genuine
reduced tangent doubling, not the origin), then `redPt (P + P) = redPt P + redPt P`.

Lifting the integral-model `addX`/`addY` at the integral tangent slope
(`exists_lift_tangent_slope_of_reduced_nonvertical`) through `algebraMap R K` and reducing them
through `residue R` — both commuting with the ring homomorphisms via `Affine.map_addX`/`map_addY` —
identifies the reduced coordinates of `P + P` with those of `redPt P + redPt P`.  Mirrors
`redPt_add_of_reduced_X_ne` (#380). -/
theorem redPt_add_self_of_reduced_nonvertical (W : WeierstrassCurve K) [HasGoodReduction R W]
    {x y : K} {h : W.toAffine.Nonsingular x y} {x₀ y₀ : R}
    (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y)
    (hnv : residue R y₀ ≠ (reduction R W).toAffine.negY (residue R x₀) (residue R y₀)) :
    redPt R W (.some x y h + .some x y h)
      = redPt R W (.some x y h) + redPt R W (.some x y h) := by
  haveI : (reduction R W).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
  have hcurve : (integralModel R W).toAffine.map (algebraMap R K) = W.toAffine :=
    baseChange_integralModel_eq R W
  -- over `K`, the point is non-vertical (else the reduced denominator would vanish).
  have hyK : y ≠ W.toAffine.negY x y := by
    intro hcon
    apply hnv
    have hlift : algebraMap R K ((integralModel R W).toAffine.negY x₀ y₀)
        = W.toAffine.negY x y := by rw [← Affine.map_negY (algebraMap R K), hcurve, hx, hy]
    have hy0 : y₀ = (integralModel R W).toAffine.negY x₀ y₀ :=
      IsFractionRing.injective R K (by rw [hy, hcon, hlift])
    calc residue R y₀
        = residue R ((integralModel R W).toAffine.negY x₀ y₀) := by rw [← hy0]
      _ = (reduction R W).toAffine.negY (residue R x₀) (residue R y₀) :=
          (Affine.map_negY (residue R) x₀ y₀).symm
  obtain ⟨s, hs, hs_res⟩ :=
    exists_lift_tangent_slope_of_reduced_nonvertical R W hx hy hnv
  -- nonsingularity of the reduced coordinates of `P` (Equation transfers K → R → k).
  have hEqP : (integralModel R W).toAffine.Equation x₀ y₀ := by
    rw [← Affine.map_equation (W := (integralModel R W).toAffine)
      (IsFractionRing.injective R K) x₀ y₀, hx, hy, hcurve]; exact h.1
  have hnsP : (reduction R W).toAffine.Nonsingular (residue R x₀) (residue R y₀) :=
    (Affine.equation_iff_nonsingular).mp (hEqP.map (residue R))
  -- lifts through `algebraMap R K` of the sum's coordinates (tangent slope `s`).
  have haddX : algebraMap R K ((integralModel R W).toAffine.addX x₀ x₀ s)
      = W.toAffine.addX x x (W.toAffine.slope x x y y) := by
    rw [← Affine.map_addX (algebraMap R K), hcurve, hx, hs]
  have haddY : algebraMap R K ((integralModel R W).toAffine.addY x₀ x₀ y₀ s)
      = W.toAffine.addY x x y (W.toAffine.slope x x y y) := by
    rw [← Affine.map_addY (algebraMap R K), hcurve, hx, hy, hs]
  -- residues through `residue R` (reduction form; `map_addY` argument order is `x₁ y₁ x₂ ℓ`).
  have hredX : residue R ((integralModel R W).toAffine.addX x₀ x₀ s)
      = (reduction R W).toAffine.addX (residue R x₀) (residue R x₀) (residue R s) :=
    (Affine.map_addX (residue R) x₀ x₀ s).symm
  have hredY : residue R ((integralModel R W).toAffine.addY x₀ x₀ y₀ s)
      = (reduction R W).toAffine.addY (residue R x₀) (residue R x₀) (residue R y₀) (residue R s) :=
    (Affine.map_addY (residue R) x₀ y₀ x₀ s).symm
  have hns_sum : (reduction R W).toAffine.Nonsingular
      (residue R ((integralModel R W).toAffine.addX x₀ x₀ s))
      (residue R ((integralModel R W).toAffine.addY x₀ x₀ y₀ s)) := by
    rw [hredX, hredY, hs_res]
    exact Affine.nonsingular_add hnsP hnsP (fun hxy => hnv hxy.right)
  -- assemble: `add_self_of_Y_ne` opens the K-doubling; `redPt_some_eq` on both sides; match coords.
  rw [Affine.Point.add_self_of_Y_ne hyK, redPt_some_eq R W haddX haddY hns_sum,
    redPt_some_eq R W hx hy hnsP, Affine.Point.add_self_of_Y_ne hnv]
  simp only [hredX, hredY, hs_res]

end WeierstrassCurve
