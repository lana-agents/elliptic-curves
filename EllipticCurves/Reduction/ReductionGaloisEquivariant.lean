/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.ReductionInjectivity
import EllipticCurves.TateModule.GaloisAction

/-!
# Reduction is equivariant under residue-trivial automorphisms (issue #390)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, residue field
`k = ResidueField R` and residue characteristic `p`, and let `W' : WeierstrassCurve S` be a
Weierstrass curve over a subfield `S ⊆ K` whose base change `W'⁄K` has good reduction over `R`.
An `S`-algebra automorphism `σ` of `K` that preserves the valuation ring — concretely, one that is
compatible with a ring automorphism `σR : R ≃+* R` (`hcompat`) — acts on the points of `W'⁄K` by
functoriality (`EllipticCurves/TateModule/GaloisAction.lean`).

This file proves the analytic heart of the *good ⇒ unramified* direction of the
Néron–Ogg–Shafarevich criterion (Silverman AEC VII.7, Theorem 7.1):

* if `σ` induces the **identity on the residue field** (`hres : residue (σR r) = residue r`), then
  reduction is `σ`-invariant, `redPt (σ • P) = redPt P` (`redPt_galois_smul_of_residue_trivial`);
* consequently `σ` **fixes every prime-to-`p` torsion point**: for `IsUnit (m : R)` and
  `m • P = 0`, `σ • P = P` (`galois_smul_eq_of_isUnit_nsmul_of_residue_trivial`).

The key simplification is that in the residue-trivial (inertia) case `redPt (σ • P)` and `redPt P`
land in the **same** reduced curve `reduction R (W'⁄K)`, and their coordinate residues coincide by
`hres`, so no action of the induced residue automorphism on the reduced curve is ever needed. The
whole argument stays over the *fixed* DVR `R`; the base change to `K̄`/`K^unr` and the
identification of the inertia group are separate, heavier downstream rungs (issue #73).

## Main results

* `WeierstrassCurve.redPt_galois_smul_of_residue_trivial` — reduction is invariant under a
  residue-trivial automorphism.
* `WeierstrassCurve.galois_smul_eq_of_isUnit_nsmul_of_residue_trivial` — such an automorphism fixes
  every prime-to-`p` torsion point.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.7, Theorem 7.1; VII.3.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum IsLocalRing

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {S K : Type*} [Field S] [Field K] [Algebra S K]
variable [Algebra R K] [IsFractionRing R K]

open Classical in
/-- **Reduction is equivariant under a residue-trivial automorphism.**  Let `σ : K ≃ₐ[S] K` be
compatible with a ring automorphism `σR : R ≃+* R` of the valuation ring (`hcompat`) that induces
the identity on the residue field (`hres`).  Then reduction is `σ`-invariant:
`redPt (σ • P) = redPt P`.

Both sides land in the same reduced curve `reduction R (W'⁄K)`; on integral points the coordinate
residues agree by `hres`, and the pole locus is preserved because `σR` restricts an automorphism to
`R`. -/
theorem redPt_galois_smul_of_residue_trivial (W' : WeierstrassCurve S)
    [HasGoodReduction R (W'⁄K)] (σ : K ≃ₐ[S] K) (σR : R ≃+* R)
    (hcompat : ∀ r : R, algebraMap R K (σR r) = σ (algebraMap R K r))
    (hres : ∀ r : R, residue R (σR r) = residue R r)
    (P : (W'⁄K).toAffine.Point) :
    redPt R (W'⁄K) (σ • P) = redPt R (W'⁄K) P := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [Affine.Point.galois_smul_def, Affine.Point.map_some]
    simp only [AlgEquiv.coe_toAlgHom]
    by_cases hx : valuation K (maximalIdeal R) x ≤ 1
    · -- Integral branch: choose lifts `x₀, y₀ : R` of `x, y`; then `σR x₀, σR y₀` lift `σ x, σ y`.
      obtain ⟨x₀, hx₀⟩ := exists_lift_of_le_one hx
      obtain ⟨y₀, hy₀⟩ := exists_lift_of_le_one (valuation_y_le_one_of_le_one R (W'⁄K) h.1 hx)
      have hxσ : algebraMap R K (σR x₀) = σ x := by rw [hcompat, hx₀]
      have hyσ : algebraMap R K (σR y₀) = σ y := by rw [hcompat, hy₀]
      -- Nonsingularity of the reduced coordinates for the chosen lifts (the library lemma is stated
      -- for the canonical `Classical.choose` lifts; identify them with `x₀, y₀` by injectivity).
      have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
      have hnsP : (reduction R (W'⁄K)).toAffine.Nonsingular (residue R x₀) (residue R y₀) := by
        have e1 : (exists_lift_of_le_one hx).choose = x₀ :=
          hinj (by rw [(exists_lift_of_le_one hx).choose_spec, hx₀])
        have e2 : (exists_lift_of_le_one
            (valuation_y_le_one_of_le_one R (W'⁄K) h.1 hx)).choose = y₀ :=
          hinj (by rw [(exists_lift_of_le_one
            (valuation_y_le_one_of_le_one R (W'⁄K) h.1 hx)).choose_spec, hy₀])
        have hns := reduction_nonsingular_of_le_one R (W'⁄K) h.1 hx
        rwa [e1, e2] at hns
      rw [redPt_some_eq R (W'⁄K) hx₀ hy₀ hnsP,
        redPt_some_eq R (W'⁄K) hxσ hyσ (by simp only [hres]; exact hnsP)]
      simp only [hres]
    · -- Pole branch: `1 < v x` forces `1 < v (σ x)`, so both sides reduce to the origin.
      rw [not_le] at hx
      have hxσ : 1 < valuation K (maximalIdeal R) (σ x) := by
        by_contra hcon
        rw [not_lt] at hcon
        obtain ⟨w, hw⟩ := exists_lift_of_le_one hcon
        have hxlift : algebraMap R K (σR.symm w) = x := by
          have hc := hcompat (σR.symm w)
          rw [RingEquiv.apply_symm_apply, hw] at hc
          exact σ.injective hc.symm
        exact absurd (hxlift ▸ valuation_le_one (maximalIdeal R) (σR.symm w)) (not_le.mpr hx)
      rw [redPt_some_of_one_lt R (W'⁄K) hxσ, redPt_some_of_one_lt R (W'⁄K) hx]

open Classical in
/-- **A residue-trivial automorphism fixes prime-to-`p` torsion.**  If `σ` is compatible with a
residue-trivial automorphism `σR` of `R` (the inertia condition), then it fixes every `m`-torsion
point for `m` prime to `p` (`IsUnit (m : R)`).  This is the *good ⇒ unramified* step of
Néron–Ogg–Shafarevich (Silverman AEC VII.7.1): `redPt (σ • P) = redPt P` by
`redPt_galois_smul_of_residue_trivial`, `σ • P` is again `m`-torsion, and reduction is injective on
`m`-torsion (`eq_of_redPt_eq_of_isUnit_nsmul`), so `σ • P = P`. -/
theorem galois_smul_eq_of_isUnit_nsmul_of_residue_trivial
    [IsAdicComplete (IsDiscreteValuationRing.maximalIdeal R).asIdeal R] (W' : WeierstrassCurve S)
    [HasGoodReduction R (W'⁄K)] [(W'⁄K).IsElliptic] (σ : K ≃ₐ[S] K) (σR : R ≃+* R)
    (hcompat : ∀ r : R, algebraMap R K (σR r) = σ (algebraMap R K r))
    (hres : ∀ r : R, residue R (σR r) = residue R r)
    {m : ℕ} (hm : IsUnit (m : R)) {P : (W'⁄K).toAffine.Point} (hP : m • P = 0) :
    σ • P = P := by
  refine eq_of_redPt_eq_of_isUnit_nsmul R (W'⁄K) hm ?_ hP ?_
  · rw [← Affine.Point.galois_smul_nsmul, hP, smul_zero]
  · exact redPt_galois_smul_of_residue_trivial R W' σ σR hcompat hres P

end WeierstrassCurve
