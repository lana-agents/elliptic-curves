/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.ReductionGaloisEquivariant
import EllipticCurves.Galois.Unramified
import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Prime-to-`p` torsion of a good-reduction curve is unramified (NOS good ⇒ unramified, rung B)

Let `K` be a field, `L / K` a field extension, and `A ⊆ L` a valuation subring of `L` lying over a
base DVR (here `A` itself is taken to be a complete discrete valuation ring — the situation of the
maximal unramified/strictly-henselian tower `R^{ur} ⊆ K^{ur}` over the base DVR `R = A ∩ K`).  Let
`W'` be a Weierstrass curve over `K` whose base change `W'⁄L` has good reduction over `A`.

The **inertia subgroup** `A.inertiaSubgroup K ≤ A.decompositionSubgroup K ≤ (L ≃ₐ[K] L)` consists of
the automorphisms `σ` fixing `A` and inducing the identity on the residue field
`k = ResidueField A` (`Mathlib.RingTheory.Valuation.RamificationGroup`).  This file bridges that
representation-theoretic *inertia* vocabulary to the analytic payload of issue #390
(`EllipticCurves/Reduction/ReductionGaloisEquivariant.lean`): each inertia element supplies exactly
the residue-trivial automorphism data `(σR, hcompat, hres)` that #390 consumes, and hence fixes
every prime-to-`p` torsion point.  Packaged in the `IsUnramified` /
`ValuationSubring.IsUnramifiedAt`
vocabulary of `EllipticCurves/Galois/Unramified.lean` (issue #241), the conclusion is that the
`m`-torsion `E[m]` is **unramified at `A`** whenever `m` is invertible in `A`:
```
A.IsUnramifiedAt (K := K) ((W'⁄L).toAffine.torsion m) .
```

This is **rung B** of the good ⇒ unramified ladder of Néron–Ogg–Shafarevich (Silverman AEC VII.7.1).
The abstract `(L, A)` hypotheses are kept general so the statement applies verbatim once the
`K^{ur}` / strict-henselisation tower (a separate, Mathlib-absent rung) is constructed and fed in as
`(L, A)`.

## Main statements

* `ValuationSubring.decompositionSubgroup_algebraMap_smul` — a decomposition element `σ` and the
  ring automorphism `σR := σ • ·` of `A` it induces are compatible with `algebraMap A L`.
* `ValuationSubring.inertiaSubgroup_smul_residue` — an inertia element acts trivially on
  `ResidueField A`, i.e. `residue A (σ • a) = residue A a`.
* `WeierstrassCurve.torsion_isUnramifiedAt` — for `IsUnit (m : A)` and good reduction, the
  `m`-torsion `E[m]` is unramified at `A`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.7 Theorem 7.1; VII.3.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- The ring automorphism `σR := (σ • ·) : A ≃+* A` induced by a decomposition-group element `σ` is
compatible with the inclusion `algebraMap A L`: `algebraMap A L (σR a) = σ (algebraMap A L a)`. -/
theorem decompositionSubgroup_algebraMap_smul (σ : A.decompositionSubgroup K) (a : A) :
    algebraMap A L (MulSemiringAction.toRingAut (A.decompositionSubgroup K) A σ a) =
      (σ : L ≃ₐ[K] L) (algebraMap A L a) := by
  change ((σ • a : A) : L) = (σ : L ≃ₐ[K] L) (a : L)
  rw [show ((σ • a : A) : L) = (σ : A.decompositionSubgroup K) • (a : L) from rfl,
    Subgroup.smul_def, AlgEquiv.smul_def]

/-- An **inertia** element acts trivially on the residue field `ResidueField A`: for `σ` in the
kernel of the residue action, `σ • y = y`. -/
theorem inertiaSubgroup_smul_residue (σ : A.decompositionSubgroup K)
    (hσ : σ ∈ A.inertiaSubgroup K) (y : IsLocalRing.ResidueField A) : σ • y = y := by
  have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) σ = 1 := MonoidHom.mem_ker.mp hσ
  calc σ • y
      = MulSemiringAction.toRingAut (A.decompositionSubgroup K)
          (IsLocalRing.ResidueField A) σ y := rfl
    _ = (1 : RingAut (IsLocalRing.ResidueField A)) y := by rw [h1]
    _ = y := rfl

/-- An inertia element induces the identity on residues: `residue A (σ • a) = residue A a`. This is
the `hres` hypothesis of #390 (`redPt_galois_smul_of_residue_trivial`). -/
theorem inertiaSubgroup_residue_smul (σ : A.decompositionSubgroup K)
    (hσ : σ ∈ A.inertiaSubgroup K) (a : A) :
    residue A (MulSemiringAction.toRingAut (A.decompositionSubgroup K) A σ a) = residue A a := by
  change residue A (σ • a) = residue A a
  rw [IsLocalRing.ResidueField.residue_smul]
  exact inertiaSubgroup_smul_residue A σ hσ (residue A a)

end ValuationSubring

namespace WeierstrassCurve

open ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
variable [IsDiscreteValuationRing A]
variable (W' : WeierstrassCurve K)

open Classical in
/-- **Prime-to-`p` torsion of a good-reduction curve is unramified at `A`.**  If `W'⁄L` has good
reduction over the complete DVR `A ⊆ L` and `m` is invertible in `A` (so prime to the residue
characteristic), then every element of the inertia subgroup `A.inertiaSubgroup K` fixes every
`m`-torsion point: `A.IsUnramifiedAt (K := K) (E[m])`.

Each inertia element `σ` restricts to the residue-trivial automorphism `σR := (σ • ·)` of `A`
(`decompositionSubgroup_algebraMap_smul`, `inertiaSubgroup_residue_smul`), which #390's
`galois_smul_eq_of_isUnit_nsmul_of_residue_trivial` turns into `σ • P = P` on prime-to-`p` torsion.
This is the good ⇒ unramified direction of Néron–Ogg–Shafarevich (Silverman AEC VII.7.1). -/
theorem torsion_isUnramifiedAt
    [IsAdicComplete (IsDiscreteValuationRing.maximalIdeal A).asIdeal A]
    [HasGoodReduction A (W'⁄L)] [(W'⁄L).IsElliptic]
    {m : ℕ} (hm : IsUnit (m : A)) :
    A.IsUnramifiedAt (K := K) ((W'⁄L).toAffine.torsion m) := by
  intro σ hσ P
  change (σ : L ≃ₐ[K] L) • P = P
  refine Subtype.ext ?_
  rw [Affine.torsion_galois_smul_coe]
  exact galois_smul_eq_of_isUnit_nsmul_of_residue_trivial A W' (σ : L ≃ₐ[K] L)
    (MulSemiringAction.toRingAut (A.decompositionSubgroup K) A σ)
    (decompositionSubgroup_algebraMap_smul A σ)
    (inertiaSubgroup_residue_smul A σ hσ) hm (Affine.mem_torsion_iff.mp P.2)

end WeierstrassCurve
