/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.TateModuleUnramified

/-!
# Néron–Ogg–Shafarevich, good ⇒ unramified: the Galois representation is unramified

Let `K` be a field, `L / K` a field extension, and `A ⊆ L` a valuation subring that is itself a
complete discrete valuation ring lying over the base DVR `R = A ∩ K` — the situation of the maximal
unramified / strictly-henselian tower over `R`.  Let `W'` be a Weierstrass curve over `K` whose base
change `W'⁄L` has good reduction over `A`, and let `ℓ` be a prime invertible in `A` (so prime to the
residue characteristic).

This file records the **good ⇒ unramified** direction of the Néron–Ogg–Shafarevich criterion
(Silverman AEC VII.7, Theorem 7.1) in its standard **representation-theoretic form**: the ℓ-adic
Galois representation `ρ_ℓ = galoisRep` and its mod-`ℓ` companion `galoisRepMod` are *trivial on the
inertia subgroup* — i.e. `ρ_ℓ σ = 1` for every `σ` in the inertia subgroup `A.inertiaSubgroup K`.

This is the linear-automorphism packaging of the merged elementwise statements

* `WeierstrassCurve.tateModule_isUnramifiedAt` (`Reduction/TateModuleUnramified.lean`, rung E), the
  inertia subgroup fixes every element of the Tate module `T_ℓ E`, and
* `WeierstrassCurve.torsion_isUnramifiedAt` (`Reduction/ReductionUnramified.lean`, rung B/#392), the
  inertia subgroup fixes every prime-to-`p` torsion point `E[m]`.

Reading "`σ` fixes every vector" as "`ρ_ℓ σ` is the identity linear automorphism" turns these into
the customary statement that *the representation is unramified* — the form in which
Néron–Ogg–Shafarevich is usually quoted and consumed.

## Main results

* `WeierstrassCurve.Affine.neronOggShafarevich_galoisRep_eq_one` — the ℓ-adic representation
  `ρ_ℓ : (L ≃ₐ[K] L) →* (T_ℓ E ≃ₗ[ℤ_[ℓ]] T_ℓ E)` is trivial on inertia: `galoisRep ℓ σ = 1`.
* `WeierstrassCurve.Affine.neronOggShafarevich_galoisRepMod_eq_one` — the mod-`ℓ` representation
  `ρ̄_ℓ : (L ≃ₐ[K] L) →* (E[ℓ] ≃ₗ[ℤ] E[ℓ])` is trivial on inertia: `galoisRepMod ℓ σ = 1`.

## Scope

This is the *abstract-`A`* form of the criterion, phrased for an arbitrary complete DVR `A ⊆ L`
containing `K` with `A.inertiaSubgroup K` as the inertia group.  Two further pieces of the full
criterion (#73) are deliberately **out of scope** here and remain larger, separate efforts:

* the *classical local-field* form — a curve `E / K` over a local field with inertia realised inside
  `Gal(K^{ur}/K)` — needs the maximal-unramified-extension / strict-henselisation tower over `R`,
  which is absent from Mathlib on this pin;
* the *converse* direction, unramified ⇒ good reduction.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.7, Theorem 7.1.
-/

open IsDiscreteValuationRing IsLocalRing

namespace WeierstrassCurve.Affine

open ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A] (W' : Affine K)

open Classical in
/-- **Néron–Ogg–Shafarevich, good ⇒ unramified (ℓ-adic representation form).**  If `W'⁄L` has good
reduction over the complete DVR `A ⊆ L` and `ℓ` is a prime invertible in `A` (so prime to the
residue characteristic), then the ℓ-adic Galois representation `ρ_ℓ = galoisRep` on the Tate module
`T_ℓ E` is *trivial on the inertia subgroup* `A.inertiaSubgroup K`:

```
∀ σ ∈ A.inertiaSubgroup K,   galoisRep ℓ σ = 1.
```

This is the representation-theoretic packaging of `tateModule_isUnramifiedAt` (inertia fixes every
element of `T_ℓ E`): `galoisRep ℓ σ` acts as `f ↦ σ • f` (`galoisRep_apply_coe`), which is the
identity precisely because `σ • f = f` for every `f` (Silverman AEC VII.7.1). -/
theorem neronOggShafarevich_galoisRep_eq_one
    [IsAdicComplete (IsDiscreteValuationRing.maximalIdeal A).asIdeal A]
    [HasGoodReduction A (W'⁄L)] [(W'⁄L).IsElliptic]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : A))
    {σ : A.decompositionSubgroup K} (hσ : σ ∈ A.inertiaSubgroup K) :
    galoisRep (W' := W') ℓ (σ : L ≃ₐ[K] L) = 1 := by
  have hunr := tateModule_isUnramifiedAt A W' hℓ
  refine LinearEquiv.ext fun f => ?_
  rw [galoisRep_apply_coe]
  exact hunr σ hσ f

open Classical in
/-- **Néron–Ogg–Shafarevich, good ⇒ unramified (mod-`ℓ` representation form).**  Under the same
hypotheses, the mod-`ℓ` Galois representation `ρ̄_ℓ = galoisRepMod` on the `ℓ`-torsion `E[ℓ]` is
*trivial on the inertia subgroup*:

```
∀ σ ∈ A.inertiaSubgroup K,   galoisRepMod ℓ σ = 1.
```

The mirror of `neronOggShafarevich_galoisRep_eq_one` at the single level `E[ℓ]`, packaging
`torsion_isUnramifiedAt` (inertia fixes every `ℓ`-torsion point): `galoisRepMod ℓ σ` acts as
`P ↦ σ • P` (`galoisRepMod_apply_coe`), the identity since `σ • P = P` for every `P`. -/
theorem neronOggShafarevich_galoisRepMod_eq_one
    [IsAdicComplete (IsDiscreteValuationRing.maximalIdeal A).asIdeal A]
    [HasGoodReduction A (W'⁄L)] [(W'⁄L).IsElliptic]
    {ℓ : ℕ} (hℓ : IsUnit (ℓ : A))
    {σ : A.decompositionSubgroup K} (hσ : σ ∈ A.inertiaSubgroup K) :
    galoisRepMod (W' := W') ℓ (σ : L ≃ₐ[K] L) = 1 := by
  have hunr := torsion_isUnramifiedAt A W' hℓ
  refine LinearEquiv.ext fun P => ?_
  rw [galoisRepMod_apply_coe]
  exact hunr σ hσ P

end WeierstrassCurve.Affine
