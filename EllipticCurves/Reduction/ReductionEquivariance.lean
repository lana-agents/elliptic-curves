/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.PointReduction
import EllipticCurves.Reduction.ReductionInjectivity
import EllipticCurves.TateModule.GaloisAction

/-!
# Inertia-invariance of the point-reduction map (the NOS good ⇒ unramified bridge)

Let `R` be a DVR with fraction field `K = Frac R` and residue field `k = ResidueField R`, let `S` be
a base field with a compatible tower `S → R → K`, and let `W'` be a Weierstrass curve over `S` whose
base change `W'⁄K` has good reduction over `R`.  An `S`-algebra automorphism `σ : K ≃ₐ[S] K` acts on
the points of `W'⁄K` by functoriality (`σ • P = Point.map σ P`, from `GaloisAction`).

If `σ` lies in the **decomposition group** — it preserves the DVR `R`, i.e. restricts to a ring
endomorphism `σ_R : R →+* R` with `σ ∘ algebraMap R K = algebraMap R K ∘ σ_R`, and preserves the
valuation — then reduction is compatible with `σ` and its induced residue action.  Specialising to
**inertia** — `σ` acts trivially on the residue field, `residue (σ_R r) = residue r` — the reduction
map is outright `σ`-invariant:
```
redPt R (W'⁄K) (σ • P) = redPt R (W'⁄K) P .
```
Combined with the injectivity of reduction on prime-to-`p` torsion (`reduction_injOn_torsion`,
Silverman AEC VII.3.1(a)), this gives `σ • P = P` for every prime-to-`p` torsion point `P`: the
inertia group acts trivially on `E[m]` for `m` prime to the residue characteristic.  This is the
**good ⇒ unramified** half of the Néron–Ogg–Shafarevich criterion (Silverman AEC VII.7.1).

## Main statements

* `WeierstrassCurve.redPt_galois_smul_of_inertia` — `redPt (σ • P) = redPt P` for a
  decomposition-group `σ` acting trivially on the residue field.
* `WeierstrassCurve.eq_of_galois_smul_of_isUnit_nsmul` — the inertia group fixes prime-to-`p`
  torsion: `σ • P = P` when `IsUnit (m : R)` and `m • P = 0`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.3 Prop 3.1, VII.7 Theorem 7.1.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum
  WeierstrassCurve.Affine.Point

namespace WeierstrassCurve

variable {S : Type*} [Field S]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [Algebra S K]
variable (W' : WeierstrassCurve S) [HasGoodReduction R (W'⁄K)]

open Classical in
/-- **Inertia-invariance of point reduction.**  Let `σ : K ≃ₐ[S] K` preserve the DVR `R` (via a ring
endomorphism `σ_R : R →+* R` with `hcompat`) and the valuation (`hval`), and act trivially on the
residue field (`hinertia : residue (σ_R r) = residue r`).  Then reduction is `σ`-invariant. -/
theorem redPt_galois_smul_of_inertia (σ : K ≃ₐ[S] K) (σ_R : R →+* R)
    (hcompat : ∀ r : R, σ (algebraMap R K r) = algebraMap R K (σ_R r))
    (hval : ∀ x : K, valuation K (maximalIdeal R) (σ x) = valuation K (maximalIdeal R) x)
    (hinertia : ∀ r : R, residue R (σ_R r) = residue R r)
    (P : (W'⁄K).toAffine.Point) :
    redPt R (W'⁄K) (σ • P) = redPt R (W'⁄K) P := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [Affine.Point.galois_smul_def, Affine.Point.map_some]
    by_cases hx : valuation K (maximalIdeal R) x ≤ 1
    · -- Integral branch: `σ_R x₀, σ_R y₀` are integral lifts of `σ x, σ y`.
      obtain ⟨x₀, hx₀⟩ := exists_lift_of_le_one hx
      obtain ⟨y₀, hy₀⟩ := exists_lift_of_le_one (valuation_y_le_one_of_le_one R (W'⁄K) h.1 hx)
      have hσx₀ : algebraMap R K (σ_R x₀) = (σ : K →ₐ[S] K) x := by
        rw [← hcompat, hx₀]; rfl
      have hσy₀ : algebraMap R K (σ_R y₀) = (σ : K →ₐ[S] K) y := by
        rw [← hcompat, hy₀]; rfl
      -- Nonsingularity of the reduced coordinates of both points (built for these lifts).
      have hcurve : (integralModel R (W'⁄K)).toAffine.map (algebraMap R K) = (W'⁄K).toAffine :=
        baseChange_integralModel_eq R (W'⁄K)
      have hnsP : (reduction R (W'⁄K)).toAffine.Nonsingular (residue R x₀) (residue R y₀) := by
        have hInt : (integralModel R (W'⁄K)).toAffine.Equation x₀ y₀ := by
          rw [← Affine.map_equation (W := (integralModel R (W'⁄K)).toAffine)
            (IsFractionRing.injective R K) x₀ y₀, hx₀, hy₀, hcurve]
          exact h.1
        haveI : (reduction R (W'⁄K)).IsElliptic :=
          (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
        exact (Affine.equation_iff_nonsingular).mp (hInt.map (residue R))
      rw [redPt_some_eq R (W'⁄K) hσx₀ hσy₀ (by rw [hinertia x₀, hinertia y₀]; exact hnsP),
        redPt_some_eq R (W'⁄K) hx₀ hy₀ hnsP]
      simp only [hinertia]
    · -- Pole branch: both sides are `0`.
      have hσx : ¬ valuation K (maximalIdeal R) ((σ : K →ₐ[S] K) x) ≤ 1 := by
        rw [show ((σ : K →ₐ[S] K) x) = σ x from rfl, hval]; exact hx
      rw [redPt_some_of_one_lt R (W'⁄K) (not_le.mp hσx),
        redPt_some_of_one_lt R (W'⁄K) (not_le.mp hx)]

open Classical in
/-- **The inertia group fixes prime-to-`p` torsion.**  If `σ` is a decomposition-group element
acting trivially on the residue field, then it fixes every point of order prime to the residue
characteristic (`IsUnit (m : R)`, `m • P = 0`).  This is the good ⇒ unramified direction of
Néron–Ogg–Shafarevich. -/
theorem eq_of_galois_smul_of_isUnit_nsmul
    [IsAdicComplete (IsDiscreteValuationRing.maximalIdeal R).asIdeal R]
    [(W'⁄K).IsElliptic] (σ : K ≃ₐ[S] K) (σ_R : R →+* R)
    (hcompat : ∀ r : R, σ (algebraMap R K r) = algebraMap R K (σ_R r))
    (hval : ∀ x : K, valuation K (maximalIdeal R) (σ x) = valuation K (maximalIdeal R) x)
    (hinertia : ∀ r : R, residue R (σ_R r) = residue R r)
    {m : ℕ} (hm : IsUnit (m : R)) {P : (W'⁄K).toAffine.Point}
    (hP : m • P = 0) :
    σ • P = P := by
  have hσP : m • (σ • P) = 0 := by
    rw [← Affine.Point.galois_smul_nsmul, hP, smul_zero]
  exact eq_of_redPt_eq_of_isUnit_nsmul R (W'⁄K) hm hσP hP
    (redPt_galois_smul_of_inertia R W' σ σ_R hcompat hval hinertia P)

end WeierstrassCurve
