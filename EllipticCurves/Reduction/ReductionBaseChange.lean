/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.GoodReductionBaseChange

/-!
# Reduction commutes with base change to a DVR extension (issue #395)

Let `R` be a discrete valuation ring with fraction field `K = Frac R`, and let `A` be a second
discrete valuation ring with fraction field `L = Frac A`, lying over `R` (compatible scalar towers
`R → A → L` and `R → K → L`, and — crucially for the residue-field map — `algebraMap R A` a local
homomorphism, `[IsLocalHom (algebraMap R A)]`; this is the situation of a finite extension `L / K`
with `A` the corresponding valuation ring). Building on issue #393
(`EllipticCurves/Reduction/GoodReductionBaseChange.lean`), which shows good reduction is *stable*
under base change, this file identifies the *reduced curve* of the base change with the base change
of the reduced curve, along the residue-field extension
`ResidueField.map (algebraMap R A) : ResidueField R →+* ResidueField A`.

This is the **"reduction commutes with base change"** brick of the Néron–Ogg–Shafarevich ladder
(parent issue #73; Silverman AEC VII.5, VII.7 Theorem 7.1) — the functoriality input consumed by
the remaining rungs (D `K^ur` / strict-henselisation, and the general σ̄-equivariant `redPt` form).

## The canonical-model form (why not a literal equality of `reduction`s)

Mathlib's `WeierstrassCurve.reduction R W = (integralModel R W).map (residue R)` is defined through
`integralModel R W = hW.integral.choose`, a *`Classical.choice`* of an integral model. The two
integral models `integralModel A (W⁄L)` and `(integralModel R W)⁄A` of `W⁄L` over `A` are therefore
only equal *after base change to `L`* (they are related by an `A`-integral `VariableChange`), so
their reductions are isomorphic but **not equal on the nose**. Consequently the naïve statement
`(W⁄L).reduction A = (W.reduction R).map (ResidueField.map (algebraMap R A))`
is *not* provable as an equality.

The meaningful, canonical statement — and the one downstream rungs actually consume — pins the
integral model on the left to the base-changed model `(integralModel R W)⁄A` (which #393's
`isIntegral_baseChange` exhibits as an integral model of `W⁄L`), rather than to the opaque
`integralModel A (W⁄L)`:

* `WeierstrassCurve.reduction_baseChange_integralModel_eq` — equating
  `((integralModel R W)⁄A).map (residue A)`
  with `(W.reduction R).map (ResidueField.map (algebraMap R A))`.

Both sides unfold to `(integralModel R W).map ((residue A).comp (algebraMap R A))` — the left via
`WeierstrassCurve.map_map`, the right via `WeierstrassCurve.map_map` together with
`IsLocalRing.ResidueField.map_comp_residue` (the residue functor is definitionally compatible with
`residue`). No `choose` mismatch arises because the integral model is fixed on both sides.

## Remaining gap (Part C, deliberately not attempted here)

Connecting the canonical form to the literal `(W⁄L).reduction A` would require identifying the two
minimal integral models `integralModel A (W⁄L)` and `(integralModel R W)⁄A` up to an `A`-integral
`VariableChange` (uniqueness of the minimal model up to unit variable change) and pushing that
variable change through `residue A`. Mathlib currently exposes no "minimal models agree up to a
unit `VariableChange`" API for this, so the honest statement there is an *isomorphism*, not an
equality. That is left as a follow-up; the canonical-model equality below is the reusable content
the ladder needs.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5, VII.7 Theorem 7.1.
-/

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

variable {R A K L : Type*}
variable [CommRing R] [CommRing A] [Field K] [Field L]
variable [Algebra R K] [Algebra A L] [Algebra R A] [Algebra K L] [Algebra R L]
variable [IsScalarTower R A L] [IsScalarTower R K L]
variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L]

variable (R A) in
/-- **Reduction commutes with base change (canonical-model form).** If `algebraMap R A` is a local
homomorphism of DVRs lying over one another and `W` is minimal over `R`, then reducing the
base-changed integral model `(integralModel R W)⁄A` modulo the maximal ideal of `A` agrees with
base-changing the reduced curve `W.reduction R` along the residue-field extension
`ResidueField.map (algebraMap R A) : ResidueField R →+* ResidueField A`:
`((integralModel R W)⁄A).map (residue A) = (W.reduction R).map (ResidueField.map (algebraMap R A))`.

Both sides equal `(integralModel R W).map ((residue A).comp (algebraMap R A))`: the left by
`WeierstrassCurve.map_map`, the right by `WeierstrassCurve.map_map` and
`IsLocalRing.ResidueField.map_comp_residue`. Pinning the integral model to `(integralModel R W)⁄A`
(rather than the `Classical.choice`-defined `integralModel A (W⁄L)`) is what makes this a genuine
equality; see the module docstring. -/
theorem reduction_baseChange_integralModel_eq [IsLocalHom (algebraMap R A)]
    (W : WeierstrassCurve K) [IsMinimal R W] :
    ((integralModel R W)⁄A).map (residue A)
      = (W.reduction R).map (ResidueField.map (algebraMap R A)) := by
  simp only [reduction, baseChange, WeierstrassCurve.map_map,
    IsLocalRing.ResidueField.map_comp_residue]

end WeierstrassCurve
