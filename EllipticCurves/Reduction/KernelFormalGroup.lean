/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.Reduction.KernelBijection
import EllipticCurves.FormalGroup.PointsOnIdeal
import EllipticCurves.FormalGroup.GroupLawBundleGeneral

/-!
# The reduction kernel and the genuine formal-group carrier `Ê(𝔪)` (issue #368, partial)

Let `R` be a **complete** discrete valuation ring (`IsAdicComplete (maximalIdeal R).asIdeal R`) with
fraction field `K = Frac R`, and let `W : WeierstrassCurve K` be an elliptic curve (`W.IsElliptic`)
with an integral model (`IsIntegral R W`).

The sibling files `Reduction/LocalParameter.lean` … `Reduction/KernelBijection.lean` built the
local parameter `zParam : E₁(K) → 𝔪` and proved it is a **set bijection**
`zParamEquiv : E₁(K) ≃ 𝔪` (with `E₁(K) = {P // ReducesToZero R W P}` the kernel of reduction and
`𝔪 = (maximalIdeal R).asIdeal`).  The target group of the full identification is however
`Ê(𝔪) = FormalGroup.OnIdeal (integralModel R W).formalGroup 𝔪`
(`EllipticCurves/FormalGroup/PointsOnIdeal.lean`), whose carrier is a `{val, property}` **struct**
copy of `𝔪` with the formal-group addition `x ⊕ y = F_E(x, y)` (via `adicEvalMv`), not the raw
ideal subtype that `zParam` lands in.

This file supplies the **carrier reconciliation** and the **set-level identification** with the
genuine formal-group carrier — the packaging groundwork of issue #368:

* `WeierstrassCurve.formalGroupOnMaximal` — the abbreviation `Ê(𝔪)` for this curve.
* `WeierstrassCurve.onIdealEquiv` — the trivial `Equiv` between the ideal subtype `↥𝔪` and the
  `OnIdeal` structure carrier (both are copies of `𝔪`).
* `WeierstrassCurve.zParamHatEquiv` — the set bijection `E₁(K) ≃ Ê(𝔪)` (compose `zParamEquiv` with
  `onIdealEquiv`) and its `zParamHatEquiv_zero`.
* `WeierstrassCurve.zParamHatEquiv_add_val` — the group operation `⊕` on the images, unfolded to the
  `𝔪`-adic evaluation of the genuine pole-free law `formalGroupZW`.  This is the exact object the
  addition-law compatibility (issue #367) must identify with `zParam (P + Q)`.

Upgrading `zParamHatEquiv` to a **group isomorphism** `E₁(K) ≃+ Ê(𝔪)` needs the addition-law
compatibility `zParam (P + Q) = zParam P ⊕ zParam Q` (issue #367, AEC IV.1 / VII.2.2), which
simultaneously makes `E₁(K)` an `AddSubgroup`.  ⚠️ That was called *"the remaining content of issue
#368"* here and is **merged**: `WeierstrassCurve.zParamHatEquiv_map_add` and
`WeierstrassCurve.E₁AddEquiv` (`EllipticCurves/Reduction/KernelFormalGroupIso.lean`), with
the subgroup `WeierstrassCurve.E₁` in `EllipticCurves/Reduction/KernelAddClosure.lean`.  Nothing in
*this* file depends on that heart; it is set-level packaging over the merged sorry-free bricks.

## References

Silverman, *The Arithmetic of Elliptic Curves*, VII.2 Prop 2.1/2.2, IV.1.
-/

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum PowerSeries

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]

/-- **`Ê(𝔪)`** for the curve `W`: the abelian group of the Weierstrass formal group law of the
integral model `integralModel R W`, on the maximal ideal `𝔪 = (maximalIdeal R).asIdeal` of the
complete DVR `R`.  Its carrier is a `{val, property}` copy of `𝔪`, with `x ⊕ y = F_E(x, y)` the
`𝔪`-adic evaluation of the formal group law (`FormalGroup.OnIdeal`). -/
abbrev formalGroupOnMaximal (W : WeierstrassCurve K) [IsIntegral R W] : Type _ :=
  FormalGroup.OnIdeal (integralModel R W).formalGroup (maximalIdeal R).asIdeal

/-- **The carrier bridge.**  The maximal ideal `𝔪` viewed as a subtype of `R` (the codomain of
`zParam`) is `Equiv` to the underlying `{val, property}` structure of `Ê(𝔪)`.  Both are copies of
`𝔪`; this trivial repackaging reconciles the codomain of `zParam` with the formal-group carrier. -/
def onIdealEquiv (W : WeierstrassCurve K) [IsIntegral R W] :
    (maximalIdeal R).asIdeal ≃ formalGroupOnMaximal R W where
  toFun x := ⟨x.1, x.2⟩
  invFun y := ⟨y.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsFractionRing R K] in
@[simp]
theorem onIdealEquiv_val (W : WeierstrassCurve K) [IsIntegral R W]
    (x : (maximalIdeal R).asIdeal) : (onIdealEquiv R W x).val = (x : R) := rfl

omit [IsFractionRing R K] in
@[simp]
theorem onIdealEquiv_symm_coe (W : WeierstrassCurve K) [IsIntegral R W]
    (y : formalGroupOnMaximal R W) :
    (((onIdealEquiv R W).symm y : (maximalIdeal R).asIdeal) : R) = y.val := rfl

/-- **The set bijection `E₁(K) ≃ Ê(𝔪)`** of the kernel of reduction with the genuine formal-group
carrier, obtained by composing the local-parameter set bijection `zParamEquiv : E₁(K) ≃ 𝔪`
(`KernelBijection.lean`) with the carrier bridge `onIdealEquiv`.  Upgrading this to a group
isomorphism `E₁(K) ≃+ Ê(𝔪)` requires the addition-law compatibility `zParam (P + Q) = zParam P ⊕
zParam Q` (issue #367); this file supplies the set-level identification and its `map_zero`. -/
noncomputable def zParamHatEquiv (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic] :
    {P : W.toAffine.Point // ReducesToZero R W P} ≃ formalGroupOnMaximal R W :=
  (zParamEquiv R W).trans (onIdealEquiv R W)

@[simp]
theorem zParamHatEquiv_val (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]
    (P : {P : W.toAffine.Point // ReducesToZero R W P}) :
    (zParamHatEquiv R W P).val = localParamR R W P.1 := rfl

/-- The set bijection sends the identity `O ∈ E₁(K)` to `0 ∈ Ê(𝔪)` (`map_zero`). -/
@[simp]
theorem zParamHatEquiv_zero (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic] :
    zParamHatEquiv R W ⟨.zero, reducesToZero_zero R W⟩ = 0 := by
  apply FormalGroup.OnIdeal.ext
  rw [zParamHatEquiv_val, FormalGroup.OnIdeal.zero_val, localParamR_zero]

/-- The formal-group operation `⊕` on the images of `zParamHatEquiv`, unfolded to the `𝔪`-adic
evaluation of the genuine **pole-free** Weierstrass law `formalGroupZW` at the two local parameters.
This is exactly the object the addition-law compatibility (issue #367) must identify with
`zParam (P + Q)`: proving
`(zParamHatEquiv R W (P + Q)).val = (zParamHatEquiv R W P + zParamHatEquiv R W Q).val`
is precisely `z(P + Q) = F_E(z P, z Q)`. -/
theorem zParamHatEquiv_add_val (W : WeierstrassCurve K) [IsIntegral R W] [W.IsElliptic]
    (P Q : {P : W.toAffine.Point // ReducesToZero R W P}) :
    (zParamHatEquiv R W P + zParamHatEquiv R W Q).val =
      adicEvalMv (maximalIdeal R).asIdeal
        (FormalGroup.OnIdeal.memFin2 (maximalIdeal R).asIdeal
          (zParamHatEquiv R W P).property (zParamHatEquiv R W Q).property)
        (integralModel R W).formalGroupZW := by
  rw [FormalGroup.OnIdeal.add_val, formalGroup_toPowerSeries]

end WeierstrassCurve
