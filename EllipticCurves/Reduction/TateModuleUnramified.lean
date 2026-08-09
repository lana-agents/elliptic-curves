/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.ReductionUnramified
import EllipticCurves.TateModule.GaloisAction

/-!
# The Tate module `T_ℓ E` is unramified at `A` (NOS good ⇒ unramified, rung E)

Let `K` be a field, `L / K` a field extension, and `A ⊆ L` a valuation subring lying over the base
DVR `R = A ∩ K` (here `A` itself is a complete discrete valuation ring — the situation of the
maximal unramified / strictly-henselian tower over `R`).  Let `W'` be a Weierstrass curve over `K`
whose base change `W'⁄L` has good reduction over `A`.

Building on the levelwise statement of issue #392
(`EllipticCurves/Reduction/ReductionUnramified.lean`), that *each* prime-to-`p` torsion group
`E[ℓ^k]` is unramified at `A`, this file assembles the **Tate-module** form: the whole
`T_ℓ E = tateModule (W'⁄L) ℓ` is unramified at `A` whenever `ℓ` is invertible in `A` (so `ℓ` is
prime to the residue characteristic).  This is **rung E** of the good ⇒ unramified ladder of
Néron–Ogg–Shafarevich (Silverman AEC VII.7 Theorem 7.1) — the capstone of the abstract-`A` line.

The assembly is pure `IsUnramified` bookkeeping and needs no new heavy infrastructure: the Tate
module embeds `Galois`-equivariantly into the product `∏ₖ E[ℓ^k]` of its levels via the projections
`tateModule.proj k` (injective by `tateModule.ext`, equivariant by `tateModule.proj_galois_smul`),
and `IsUnramified` transports along injective equivariant maps (`IsUnramified.of_injective`) out of
products (`IsUnramified.pi`).

## Main statement

* `WeierstrassCurve.tateModule_isUnramifiedAt` — for `IsUnit (ℓ : A)` and good reduction, `T_ℓ E` is
  unramified at `A`, i.e. `A.IsUnramifiedAt (K := K) ((W'⁄L).toAffine.tateModule ℓ)`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.7 Theorem 7.1; VII.3.
-/

open IsDiscreteValuationRing IsLocalRing

namespace WeierstrassCurve

open ValuationSubring Affine

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
variable [IsDiscreteValuationRing A]
variable (W' : WeierstrassCurve K)

open Classical in
/-- **The Tate module `T_ℓ E` of a good-reduction curve is unramified at `A`.**  If `W'⁄L` has good
reduction over the complete DVR `A ⊆ L` and `ℓ` is invertible in `A` (so prime to the residue
characteristic), then every element of the inertia subgroup `A.inertiaSubgroup K` fixes every
element of the Tate module: `A.IsUnramifiedAt (K := K) (T_ℓ E)`.

Assembled from the levelwise #392 statement `torsion_isUnramifiedAt` (each `E[ℓ^k]` is unramified at
`A`) via the equivariant embedding `T_ℓ E ↪ ∏ₖ E[ℓ^k]` of projections.  This is the Tate-module form
of the good ⇒ unramified direction of Néron–Ogg–Shafarevich (Silverman AEC VII.7.1).  In the
intended application `ℓ` is a prime `≠ char (ResidueField A)`. -/
theorem tateModule_isUnramifiedAt
    [IsAdicComplete (IsDiscreteValuationRing.maximalIdeal A).asIdeal A]
    [HasGoodReduction A (W'⁄L)] [(W'⁄L).IsElliptic]
    {ℓ : ℕ} (hℓ : IsUnit (ℓ : A)) :
    A.IsUnramifiedAt (K := K) ((W'⁄L).toAffine.tateModule ℓ) := by
  -- Each level `E[ℓ^k]` is unramified at `A` (issue #392), since `ℓ^k` is a unit in `A`.
  have hlevel : ∀ k : ℕ,
      IsUnramified (A.inertiaSubgroup K) ((W'⁄L).toAffine.torsion (ℓ ^ k)) := fun k =>
    torsion_isUnramifiedAt A W' (m := ℓ ^ k) (by push_cast; exact hℓ.pow k)
  -- Transport unramifiedness of `∏ₖ E[ℓ^k]` along the injective equivariant embedding
  -- `T_ℓ E ↪ ∏ₖ E[ℓ^k]`, `t ↦ (proj k t)ₖ`.
  refine (IsUnramified.pi hlevel).of_injective
    (f := fun t k => tateModule.proj k t) ?_ ?_
  · -- Injectivity: an element of `T_ℓ E` is determined by all its level projections.
    intro s t hst
    apply tateModule.ext
    intro k
    exact Subtype.ext_iff.mp (congrFun hst k)
  · -- Equivariance: `proj k` commutes with the Galois action (`proj_galois_smul`).
    intro σ t
    funext k
    exact tateModule.proj_galois_smul ℓ (σ : L ≃ₐ[K] L) t k

end WeierstrassCurve
